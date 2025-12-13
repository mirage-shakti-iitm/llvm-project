/* TODO: Should do realloc, calloc any other allocator functions */
/* TODO: Should do global objects */ 
/* TODO: Should do other allocator functions like calloc, reallocarray, memalign etc...  */

#include "llvm/ADT/Statistic.h"
#include "llvm/IR/Instructions.h"
#include "llvm/Pass.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/DataLayout.h"
#include "llvm/IR/DerivedTypes.h"
#include "llvm/IR/InstrTypes.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/AbstractCallSite.h"
#include "llvm/Transforms/Utils/BasicBlockUtils.h"
#include "llvm/IR/IntrinsicsRISCV.h"
#include <stack>
#include <map>
#include <set>
#include <fstream>
#include <cstdlib>
#include <string>
#include "llvm/IR/Dominators.h"
#include "llvm/Analysis/PostDominators.h"
#include "llvm/Analysis/LoopInfo.h"
#include "llvm/Analysis/ScalarEvolution.h"
#include "llvm/ADT/DenseMap.h"


#include "llvm/Support/CommandLine.h"
#include "llvm/IR/LegacyPassManager.h"
#include "llvm/Transforms/IPO/PassManagerBuilder.h"
#include "llvm/InitializePasses.h"


using namespace llvm;

#define DEBUG_PRINT(msg) \
    do { \
        auto now = std::chrono::steady_clock::now().time_since_epoch(); \
        auto ms = std::chrono::duration_cast<std::chrono::milliseconds>(now).count(); \
        errs() << "[" << ms << " ms] " << msg << "\n"; \
    } while(0)

static cl::opt<std::string> CapFile(
    "cap-file",
    cl::desc("Path where function-compartment mapping (.cap) file is present."),
    cl::Hidden);

static cl::opt<bool>
    EnableBoundsCheck("enable-fides-bounds-check",
                 cl::desc("Enable S/W bounds checking"), cl::init(false), cl::Hidden);

static cl::opt<bool>
    EnableStripAddressCompatibility("enable-strip-trusted-code",
                 cl::desc("Enable stripping even in trusted code for compatibility"), cl::init(false), cl::Hidden);

static cl::opt<int> DefaultCompartment(
    "default-compartment",
    cl::desc("Default compartment id. Alternate way to set this, is \":<default_compartment_id>\" at the start of the .cap file."),
    cl::init(266), // currently 0-255 valid compartment range
    cl::Hidden);

static cl::opt<bool> AllEntry(
    "all-entry",
    cl::desc("Instrument every function as valid entry point"),
    cl::init(false),
    cl::Hidden);

std::map <std::string, int> compartment_map;
std::map <std::string, int> checkcap_map;

// Replace '/' with "__"
std::string sanitize(std::string name, char ch){
  std::string new_name = "";
  for (std::string::size_type i = 0; i < name.size(); i++) {
    if(name[i] == ch){
      new_name.append(2, '_');
    }
    else{
      new_name.append(1, name[i]);
    }
  }
 return new_name;
}

void fides_initialize_compartment_map(std::string source_filename_with_ext){
  if (!CapFile.empty()) {
    errs()<<CapFile<<"\n";
    std::string cap_filename(CapFile);
    cap_filename.append("/");
    std::string source_filename = source_filename_with_ext.substr(0, source_filename_with_ext.find_last_of("."));
    cap_filename.append(source_filename);
    errs()<<"\n source_filename: "<<source_filename<<"\n";
    cap_filename.append(".cap");
    std::ifstream CapFile;
    errs()<<"\nCap filename:"<<cap_filename;
    CapFile.open(cap_filename);
    std::string myText;
    bool default_set = 0;
    // Use a while loop together with the getline() function to read the file line by line
    if(CapFile){
      errs()<<"PAssed\n";
      while (getline (CapFile, myText)) {
        if(default_set == 0){
          std::size_t pos = myText.find_last_of(":");
          if(pos == 0){
            DefaultCompartment = std::stoi(myText.substr(myText.find_last_of(":")+1));
            
         }
         default_set = 1;
        }
        else{
          int checkcap_enable = std::stoi(myText.substr(myText.find_last_of(":")+1));
          std::string func_name_id_str = myText.substr(0, myText.find_last_of(":"));
          std::string function_name = func_name_id_str.substr(0, func_name_id_str.find_last_of(":"));
          int compartment_id = std::stoi(func_name_id_str.substr(func_name_id_str.find_last_of(":")+1));
          compartment_map.insert(std::pair<std::string, int>(function_name, compartment_id));
          if(checkcap_enable){
            checkcap_map.insert(std::pair<std::string, int>(function_name, 1));
          }
        }
      }
    }
    CapFile.close();
  }
}


/*
Instruction sequence for check:
index = Shift right 32 bits (po)
offset = shift left 3 bits (index)
metadataAddr = add offset, boundsTableAddr
metadata = *metadataAddr
strippedPtr = mask(upper 32 bits, po)
base = mask(upper 32 bits, metadata)
bound = shift right 32 bits (metadata)
diff1 = strippedPtr - base
diff2 = bound - strippedPtr
diff = diff1 || diff2
maskedDiff = mask(lower 32 bits, diff)
loadPtr = strippedPtr || maskedDiff
*/


namespace {
	struct FidesPass : public ModulePass
	{
		static char ID;
  void getAnalysisUsage(AnalysisUsage &AU) const override {
    AU.addRequired<DominatorTreeWrapperPass>();
    AU.addRequired<PostDominatorTreeWrapperPass>();
  }
		DenseMap<Instruction*, Instruction*> FDCEmap;  // target -> dominating check
    	DominatorTree *DT;
    	PostDominatorTree *PDT;

// private:
    void bbDerefCheck(Function *F) {
        FDCEmap.clear();
        int nrofloadstores = 0, nrofredundant = 0;
        
        for (BasicBlock &BB : *F) {
            for (Instruction &I : BB) {
                LoadInst *LI = dyn_cast<LoadInst>(&I);
                StoreInst *SI = dyn_cast<StoreInst>(&I);
                if (!LI && !SI) continue;
                
                Value *pointer = LI ? LI->getPointerOperand() : SI->getPointerOperand();
                if (FDCEmap.count(&I)) {
                    nrofredundant++;
                    continue;
                }
                
                nrofloadstores++;
                findRedundantChecks(&I, pointer, false);
            }
        }
        errs() << "FDCE[" << F->getName() << "]: " << nrofloadstores 
               << " LS, " << nrofredundant << " skipped\n";
    }
    
    void findRedundantChecks(Instruction *checked, Value *pointer, bool goneThroughGEP) {
        for (User *U : pointer->users()) {
            GEPOperator *GEP = dyn_cast<GEPOperator>(U);
            if (GEP) {
                findRedundantChecks(checked, GEP, true);
                continue;
            }
            
            Instruction *loadstore = dyn_cast<Instruction>(U);
            if (!loadstore || (!isa<LoadInst>(loadstore) && !isa<StoreInst>(loadstore)))
                continue;
            
            StoreInst *SI = dyn_cast<StoreInst>(loadstore);
            if (SI && SI->getPointerOperand() != pointer) continue;
            
            // Safety checks (simplified)
            if (goneThroughGEP && !PDT->dominates(loadstore->getParent(), checked->getParent()))
                continue;
            if (!DT->dominates(checked, loadstore))
                continue;
            if (hasInterveningCall(checked, loadstore))
                continue;
                
            if (!FDCEmap.count(loadstore))
                FDCEmap[loadstore] = checked;
        }
    }
    
    bool hasInterveningCall(Instruction *start, Instruction *end) {
        // Simple forward scan (conservative)
        for (Instruction *I = start->getNextNode(); I && I != end; I = I->getNextNode()) {
            if (dyn_cast<CallBase>(I)) return true;
        }
        return false;
    }


		FidesPass() : ModulePass(ID) {initializeFidesPassPass(*PassRegistry::getPassRegistry());}

// Helper function to check if function has specific annotation
        bool hasAnnotation(Function &F, StringRef annotationStr) {
            Module *M = F.getParent();
            GlobalVariable *annotations = M->getGlobalVariable("llvm.global.annotations");
            
            if(F.getName().contains("fides") || F.getName().contains("llvm") || F.getName().contains("memcpy") || F.getName().contains("realloc")){
            	return true;
            }

            auto malloc_names = {"malloc", "_Znam", "_Znwm", "_ZnamRKSt9nothrow_t",
	                       "_ZnwmRKSt9nothrow_t"};
	 		auto free_names = {"free", "_ZdaPv", "_ZdlPv", "_ZdaPvRKSt9nothrow_t",
	                     "_ZdlPvRKSt9nothrow_t"};

	        for (auto name : free_names) {
    			if(F.getName().contains(name)){
    				return true;
    			}
    		}

    		for (auto name : malloc_names) {
    			if(F.getName().contains(name)){
    				return true;
    			}
    		}

            if (!annotations)
                return false;

            ConstantArray *CA = dyn_cast<ConstantArray>(annotations->getOperand(0));
            if (!CA)
                return false;

            for (unsigned i = 0; i < CA->getNumOperands(); i++) {
                ConstantStruct *CS = dyn_cast<ConstantStruct>(CA->getOperand(i));
                if (!CS)
                    continue;

                // First operand is the annotated value
                Value *annotatedValue = dyn_cast<Function>(CS->getOperand(0)->stripPointerCasts());
                if (annotatedValue != &F)
                    continue;

                // Second operand is the annotation string
                GlobalVariable *annotationGV = 
                    dyn_cast<GlobalVariable>(CS->getOperand(1)->stripPointerCasts());
                if (!annotationGV)
                    continue;

                ConstantDataSequential *annotationData = 
                    dyn_cast<ConstantDataSequential>(annotationGV->getInitializer());
                if (!annotationData)
                    continue;

                StringRef annotation = annotationData->getAsCString();
                if (annotation == annotationStr)
                    return true;
            }
            return false;
        }


		virtual bool runOnModule(Module &M)
		{	

			if(!EnableBoundsCheck){
				return true;
			}

			errs()<<"Welcome to FIDES PASS\n";

			bool moduleHasFunctions = false;

			std::set<std::string> func_name;
			for (auto &F : M){
				if (!F.isDeclaration()) {
						
					moduleHasFunctions = true;
					break;
				}
			}

			bool modified=false;

			// Skipping pass if the no functions present in the module
			if(moduleHasFunctions == false){
				return modified	;
			}

			auto &Ctx = M.getContext();

			if(EnableBoundsCheck){
				/* Replace allocator functions with safe variant */
				auto malloc_names = {"malloc", "_Znam", "_Znwm", "_ZnamRKSt9nothrow_t",
	                       "_ZnwmRKSt9nothrow_t"};
	 			auto free_names = {"free", "_ZdaPv", "_ZdlPv", "_ZdaPvRKSt9nothrow_t",
	                     "_ZdlPvRKSt9nothrow_t"};
	      auto realloc_names = {"realloc"};

   			auto FidesReallocFn = M.getOrInsertFunction("__fides_realloc", FunctionType::get(Type::getInt8PtrTy(Ctx), {Type::getInt8PtrTy(Ctx), Type::getInt64Ty(Ctx)}, false)); 
        auto FidesMallocFn = M.getOrInsertFunction("__fides_malloc", FunctionType::get(Type::getInt8PtrTy(Ctx), {Type::getInt64Ty(Ctx)}, false));
        auto FidesFreeFn = M.getOrInsertFunction("__fides_free", FunctionType::get(Type::getVoidTy(Ctx), {Type::getInt8PtrTy(Ctx)}, false));
        for (auto name : malloc_names) {
    			M.getOrInsertFunction(name, FunctionType::get(Type::getInt8PtrTy(Ctx), {Type::getInt64Ty(Ctx)}, false)).getCallee()->replaceAllUsesWith(FidesMallocFn.getCallee());
    		}
    		for (auto name : free_names) {
    			M.getOrInsertFunction(name, FunctionType::get(Type::getVoidTy(Ctx), {Type::getInt8PtrTy(Ctx)}, false)).getCallee()->replaceAllUsesWith(FidesFreeFn.getCallee());
    		}
    		for (auto name : realloc_names) {
    			M.getOrInsertFunction(name, FunctionType::get(Type::getInt8PtrTy(Ctx), {Type::getInt8PtrTy(Ctx), Type::getInt64Ty(Ctx)}, false)).getCallee()->replaceAllUsesWith(FidesReallocFn.getCallee());
    		}
			}
    		
    				/* Declare global variable which stores the bounds metadata table */
    		std::string boundsTableStr = "__fides_bounds_table";
    		StringRef boundsTable = StringRef(boundsTableStr);
    		// auto boundsTableGV = M.getOrInsertGlobal(boundsTable,Type::getInt64Ty(Ctx));

    		Value *boundsTableAddr = M.getOrInsertGlobal(boundsTable, Type::getInt64Ty(Ctx));

    	// Build FDCE maps for all functions first
    	
    	
    	int total_insns = 0;
    	int skipped_insns = 0;
    	int insert_insns = 0;

    	/* Instrument Load-Store instructions. Don't instrument instructions accessing int/float objects */
    	for (auto &F : M){
    		// errs()<<"HI SAI 1\n";
    		Module *m = F.getParent();
    		if (hasAnnotation(F, "skip_fides_pass") || F.isDeclaration()) {
    			// skip function processing
    			continue;
			}
			DT = &this->getAnalysis<DominatorTreeWrapperPass>(F).getDomTree();
        	PDT = &this->getAnalysis<PostDominatorTreeWrapperPass>(F).getPostDomTree();
        	bbDerefCheck(&F);  // Populates FDCEmap
    		Function *val_memcheck = Intrinsic::getDeclaration(m, Intrinsic::riscv_validate);	// get hash intrinsic declaration

    		errs()<<"Here 1\n";

    		for (auto &B : F)
				{
					// Iterate over Instrs in BB
					for (auto &I : B)
					{		
							// errs()<<"HI SAI 21: "<<I<<"\n";
							
							// If instruction is load instruction apply bounds check
							if (LoadInst *LI = dyn_cast<LoadInst>(&I)){
                                total_insns++;
								Value *po = LI->getPointerOperand();
								if(EnableBoundsCheck){	
									bool insert_check = true;
									if (auto *AI = dyn_cast<AllocaInst>(LI->getPointerOperand())){
    								Type *pt = LI->getPointerOperandType();
    								// errs()<<*LI<<" :: "<<*LI->getOperand(0)<<" :: "<<*LI->getPointerOperandType()<<"\n";
    								if(dyn_cast<PointerType>(pt)){
											// errs()<<*pt->getPointerElementType()<<"::"<<pt->getPointerElementType()->isArrayTy()<<"::"<<*AI->getAllocatedType()<<"\n";
											if(!pt->getPointerElementType()->isPointerTy()){
												insert_check = false;
											}
										}	
    							}

    							// llvm::Constant *zeroConstant = llvm::ConstantInt::get(Type::getInt64Ty(Ctx), 0x80000000ULL, false);
    							llvm::Constant *zeroConstant = llvm::ConstantInt::get(Type::getInt64Ty(Ctx), 0x0ULL, false);
									// llvm::Constant *temporalCheck = llvm::ConstantInt::get(Type::getInt64Ty(Ctx), 0x2ULL, false);
									// llvm::Constant *spatialCheck = llvm::ConstantInt::get(Type::getInt64Ty(Ctx), 0x1ULL, false);

									// std::vector<Value *> args1;
									// std::vector<Value *> args2;
									std::vector<Value *> args1;

									// args1.push_back(po);
									// args1.push_back(spatialCheck);
									
									// args2.push_back(po);
									// args2.push_back(temporalCheck);

									// ArrayRef<Value *> args_ref1(args1);
									// ArrayRef<Value *> args_ref2(args2);

									args1.push_back(zeroConstant);
									args1.push_back(po);

									ArrayRef<Value *> args_ref1(args1);

									if(FDCEmap.count(LI)){
                                        skipped_insns++;
										continue;
									}

									if(insert_check){
										insert_insns++;
										// Create call to intrinsic
										IRBuilder<> Builder(LI);
										Builder.SetInsertPoint(LI);
										Builder.CreateCall(val_memcheck, args_ref1,"");
										// Builder.CreateCall(val_memcheck, args_ref1,"");
										// Builder.CreateCall(val_memcheck, args_ref2,"");
									}
								}
							}
							if (StoreInst *SI = dyn_cast<StoreInst>(&I)){
                                total_insns++;
								Value *po = SI->getPointerOperand();
								if(EnableBoundsCheck){
									bool insert_check = true;
									// errs()<<"SAI 0"<<SI->getPointerOperand()<<"\n";
									if(auto *AI = dyn_cast<AllocaInst>(SI->getPointerOperand())){
    								Type *pt = SI->getPointerOperandType();
    								// errs()<<"SAI 1 "<<*SI<<" :: "<<*SI->getOperand(1)<<" :: "<<*SI->getPointerOperandType()<<"\n";
    								if(dyn_cast<PointerType>(pt)){
											// errs()<<"SAI 2 "<<*pt->getPointerElementType()<<"::"<<pt->getPointerElementType()->isArrayTy()<<"::"<<*AI->getAllocatedType()<<"\n";
											if(!pt->getPointerElementType()->isPointerTy()){
												insert_check = false;
											}
										}	
    								}

    							// llvm::Constant *zeroConstant = llvm::ConstantInt::get(Type::getInt64Ty(Ctx), 0x80000000ULL, false);
    							llvm::Constant *zeroConstant = llvm::ConstantInt::get(Type::getInt64Ty(Ctx), 0x0ULL, false);
									// llvm::Constant *temporalCheck = llvm::ConstantInt::get(Type::getInt64Ty(Ctx), 0x2ULL, false);
									// llvm::Constant *spatialCheck = llvm::ConstantInt::get(Type::getInt64Ty(Ctx), 0x1ULL, false);

									// std::vector<Value *> args1;
									// std::vector<Value *> args2;
									// args1.push_back(po);
									// args1.push_back(spatialCheck);
									
									// args2.push_back(po);
									// args2.push_back(temporalCheck);

									// ArrayRef<Value *> args_ref1(args1);
									// ArrayRef<Value *> args_ref2(args2);

									std::vector<Value *> args1;
									
									args1.push_back(zeroConstant);
									args1.push_back(po);

									ArrayRef<Value *> args_ref1(args1);

									if(FDCEmap.count(SI)){
                                        skipped_insns++;
										continue;
									}

									if(insert_check){
										insert_insns++;
										// Create call to intrinsic
										IRBuilder<> Builder(SI);
										Builder.SetInsertPoint(SI);
										Builder.CreateCall(val_memcheck, args_ref1);
										// Builder.CreateCall(val_memcheck, args_ref1,"");
										// Builder.CreateCall(val_memcheck, args_ref2,"");
									}
								}
							}
							// if (StoreInst *SI = dyn_cast<StoreInst>(&I)){
							// 	Value *po = SI->getPointerOperand();
							// 	if(EnableBoundsCheck){
							// 		Value *V = stripCheckPointer(SI, po, boundsTableAddr, Ctx);
							// 		SI->setOperand(1, V);
							// 	}
							// }
	    			}
    			}
    		}

    	errs()<<"Total LD/ST insns = "<<total_insns<<"\n";
    	errs()<<"Inserted insns = "<<insert_insns<<"\n";
        errs()<<"Skipped insns = "<<skipped_insns<<"\n";
    	// if(insert_insns){
	    	// errs()<<"Efficiency = "<<(double)(total_insns-insert_insns)/(double)(total_insns)*100<<"\n";
		// }
    	// errs()<<"Here 2\n";

    	if(!EnableBoundsCheck){
    		return 0;
    	}

    	std::vector<CallInst*> CIToInstrument;
    	for (auto &F : M){
    		Module *m = F.getParent();

    		errs()<<"function name: "<<F.getName()<<" : "<<hasAnnotation(F, "skip_fides_pass")<<"\n";
    		if (hasAnnotation(F, "skip_fides_pass")) {
    			// skip function processing
    			// errs()<<"Skipped\n";
    			continue;
			}
			// errs()<<"Not Skipped\n";	
    		for (auto &B : F)
				{
					// Iterate over Instrs in BB
					for (auto &I : B)
					{
						// errs()<<"Inside BB\n";
						if(auto *CI = dyn_cast<CallInst>(&I)){
							auto *callee = CI->getCalledFunction();
							if(!callee){
								Value *calledOp = CI->getCalledOperand();
								 if (!dyn_cast<InlineAsm>(calledOp)){
									// errs()<<"Insert : "<<*CI<<"\n";
								// errs()<<CI->getCalledFunction()->getName()<<"\n";
									CIToInstrument.push_back(CI);
								}
								continue;
							}
							if(!(CI->getCalledFunction()->getName().contains("fides") || CI->getCalledFunction()->getName().contains("llvm") || 
								CI->getCalledFunction()->getName().contains("memcpy"))){
								// errs()<<"Insert : "<<*CI<<"\n";
								errs()<<CI->getCalledFunction()->getName()<<"\n";
								CIToInstrument.push_back(CI);
							}
						}
					}
				}
			}

			auto FidesStackObjCreate = M.getOrInsertFunction("__fides_stack_metadata_update", FunctionType::get(Type::getInt64Ty(Ctx), {Type::getInt64Ty(Ctx), Type::getInt64Ty(Ctx)}, false));
			auto FidesMaxStackIdWrite = M.getOrInsertFunction("__fides_max_stack_id_write", FunctionType::get(Type::getVoidTy(Ctx), {Type::getInt64Ty(Ctx)}, false));
			auto FidesMaxStackIdRead = M.getOrInsertFunction("__fides_max_stack_id_read", FunctionType::get(Type::getInt64Ty(Ctx), {Type::getVoidTy(Ctx)}, false));

			Value *maxStackID = NULL;

			errs()<<"Now in stack insertion\n";

    	for (auto &F : M){
    		Module *m = F.getParent();
    		// errs()<<"function name: "<<F.getName()<<" : "<<hasAnnotation(F, "skip_fides_pass")<<"\n";
    		if (hasAnnotation(F, "skip_fides_pass")) {
    			// skip function processing
    			continue;
				}
    		for (auto &B : F)
				{
					// Iterate over Instrs in BB
					for (auto &I : B)
					{
						if(auto *AI = dyn_cast<AllocaInst>(&I)){
							// errs()<<"\n";
							int i = 0;
							if(auto *AI_next = (dyn_cast<AllocaInst>(AI->getNextNode()))){
								i = 1;
								// errs()<<*(AI->getNextNode())<<" not last: "<<*AI->getAllocatedType()<<":"<<*AI->getType()<<" : isArray = "<<AI->getAllocatedType()->isArrayTy()<<" : isStruct = "<<AI->getAllocatedType()->isStructTy()<<" : isAggregate = "<<AI->getAllocatedType()->isAggregateType()<<" : size = "<<(AI->getAllocationSizeInBits(m->getDataLayout())).getValue()/8<<"\n";
							}
							else{
								i = 2;
								IRBuilder<> Builder(AI->getNextNode());
								// std::vector<Value *> args;
								// ArrayRef<Value *> args_ref(args);
								maxStackID = Builder.CreateCall(FidesMaxStackIdRead, {}, "");
								// errs()<<*(AI->getNextNode())<<"\n last:\n "<<*AI->getAllocatedType()<<":"<<*AI->getType()<<" : isArray = "<<AI->getAllocatedType()->isArrayTy()<<" : isStruct = "<<AI->getAllocatedType()->isStructTy()<<" : isAggregate = "<<AI->getAllocatedType()->isAggregateType()<<" : size = "<<(AI->getAllocationSizeInBits(m->getDataLayout())).getValue()/8<<"\n";
								for (auto *CI : CIToInstrument){
									if((CI->getParent()->getParent()) == &F){
										IRBuilder<> Builder(CI->getNextNode());
										// errs()<<"Insert before : "<<*CI<<" : "<<*CI->getNextNode()<<"\n";
										std::vector<Value *> args_stack_id;
										args_stack_id.push_back(maxStackID);
										ArrayRef<Value *> args_ref_stack_id(args_stack_id);
										Builder.CreateCall(FidesMaxStackIdWrite, args_ref_stack_id,"");
									}
								}

							}
						}
					}
				}
			}

		errs()<<"Now in tagged stack pointer \n";
    	for (auto &F : M){
    		Module *m = F.getParent();
    		if (hasAnnotation(F, "skip_fides_pass")) {
    			// skip function processing
    			continue;
			}
			errs()<<"\nConverting stack pointers in Function "<<F.getName();
    		for (auto &B : F)
			{		
					// Iterate over Instrs in BB
					for (auto &I : B)
					{
						if(auto *AI = dyn_cast<AllocaInst>(&I)){
							// Insert metadata if stack object allocated is an Aggregate type(union, struct, array)
							errs()<<"HEre\n";
							IRBuilder<> Builder(AI->getNextNode());

							if(AI->getAllocatedType()->isAggregateType()){
								
								std::vector<User*> Users(AI->user_begin(), AI->user_end());
								
								auto allocSizeBytes = (AI->getAllocationSizeInBits(m->getDataLayout())).getValue()/8;
								Value* allocSizeLoad = llvm::ConstantInt::get(Type::getInt64Ty(Ctx),allocSizeBytes);
								Value *stackPointerInt = Builder.CreatePtrToInt(AI, Type::getInt64Ty(Ctx), "");

								std::vector<Value *> args;
								args.push_back(stackPointerInt);
								args.push_back(allocSizeLoad);

								ArrayRef<Value *> args_ref(args);

								Value *taggedStackPointerInt = Builder.CreateCall(FidesStackObjCreate, args_ref,"");
								Value *taggedStackPointer = Builder.CreateIntToPtr(taggedStackPointerInt, AI->getType(), "");
							
								errs()<<*(AI)<<" : "<<*AI->getAllocatedType()<<":"<<*AI->getType()<<" : isArray = "<<AI->getAllocatedType()->isArrayTy()<<" : isStruct = "<<AI->getAllocatedType()->isStructTy()<<" : isAggregate = "<<AI->getAllocatedType()->isAggregateType()<<" : size = "<<(AI->getAllocationSizeInBits(m->getDataLayout())).getValue()/8<<"\n";
								for (User *U : Users){
									errs()<<*U<<" <--> ";
        					U->replaceUsesOfWith(AI, taggedStackPointer);
								}

								/* 	TIP: Do not use this AI->replaceAllUsesWith, 
										because it will replace even where we really need AI to create fat pointer 
										So the correct way, is to get the Users of that specific instruction in 
										this case, AI, and store it separately. And use that in replaceAllUsesWith. 
										Getting the USers list after inserting instructions is also wrong since, 
										the isnerted instructions also are part of Users then.
								*/

							}
							// auto allocSizeBits = AI->getAllocationSizeInBits(m->getDataLayout());
							// auto allocSizeBytes = allocSizeBits/8;
							// Function *csrw = Intrinsic::getDeclaration(m, Intrinsic::CSRRW);

						}
					}
				}
			}

            int cmp_ops = 0;
            
            // Stripping icmp instruction metadata
            for (auto &F : M){
                Module *m = F.getParent();
                if (hasAnnotation(F, "skip_fides_pass")) {
                    // skip function processing
                    continue;
                }
                errs()<<"\nConverting stack pointers in Function "<<F.getName();
                for (auto &B : F)
                {   
                    for(auto &I : B){
                        if (auto *CMPI = dyn_cast<ICmpInst>(&I)){
                            Value *po1 = CMPI->getOperand(0);
                            Value *po2 = CMPI->getOperand(1);
                            if(dyn_cast<PointerType>(po1->getType())){
                                cmp_ops++;
                                IRBuilder<> Builder(CMPI);
                                Builder.SetInsertPoint(CMPI);
                                
                                llvm::Constant *stripUpperMask = llvm::ConstantInt::get(Type::getInt64Ty(Ctx), 0x00000000FFFFFFFFULL, false);
                                llvm::Constant *stripLowerMask = llvm::ConstantInt::get(Type::getInt64Ty(Ctx), 0xFFFFFFFF00000000ULL, false);

                                auto addressInt = Builder.CreatePtrToInt(po1, Type::getInt64Ty(Ctx), "addressInt");
                                auto strippedAddress = Builder.CreateAnd(addressInt, stripUpperMask, "strippedAddress");
                                auto resultAddress = Builder.CreateIntToPtr(strippedAddress, po1->getType(), "resultAddr");

                                CMPI->setOperand(0, resultAddress);
                            }
                            if(dyn_cast<PointerType>(po2->getType())){
                                cmp_ops++;
                                IRBuilder<> Builder(CMPI);
                                Builder.SetInsertPoint(CMPI);
                                
                                llvm::Constant *stripUpperMask = llvm::ConstantInt::get(Type::getInt64Ty(Ctx), 0x00000000FFFFFFFFULL, false);
                                llvm::Constant *stripLowerMask = llvm::ConstantInt::get(Type::getInt64Ty(Ctx), 0xFFFFFFFF00000000ULL, false);

                                auto addressInt = Builder.CreatePtrToInt(po2, Type::getInt64Ty(Ctx), "addressInt");
                                auto strippedAddress = Builder.CreateAnd(addressInt, stripUpperMask, "strippedAddress");
                                auto resultAddress = Builder.CreateIntToPtr(strippedAddress, po2->getType(), "resultAddr");

                                CMPI->setOperand(1, resultAddress);
                            }
                        }
                    }
                }
            }
        


            errs()<<"Total incompatible comparison operation : "<<cmp_ops<<"\n";
			errs()<<"Finished Fides ms pass\n";

			// for (int i =0; i<low_contours; i++){
			// 	i =
			// }


			// for (auto &F : M){
    	// 	Module *m = F.getParent();

    	// 	for (auto &B : F)
			// 	{
			// 		// Iterate over Instrs in BB
			// 		for (auto &I : B)
			// 		{
			// 			if(auto *CI = dyn_cast<CallInst>(&I)){
			// 				/* 	Update the maxStackId CSR with the value 
			// 						stored locally in the function prologue 
			// 						Do this onlfy for non-fides functions. This is sort of an optimization.
			// 						The fides wrappers are anyway trusted.
			// 						We can go further and remove the updates for memcpy etc.. but lets not do
			// 						that now.
			// 				*/
			// 				errs()<<CI->getCalledFunction()->getName()<<"\n";
			// 				if(!(CI->getCalledFunction()->getName().contains("fides") || CI->getCalledFunction()->getName().contains("llvm"))){
			// 					errs()<<CI->getCalledFunction()->getName()<<" : ss\n\n\n";
			// 					IRBuilder<> Builder(CI->getNextNode());
			// 					std::vector<Value *> args_stack_id;
			// 					args_stack_id.push_back(maxStackID);
			// 					ArrayRef<Value *> args_ref_stack_id(args_stack_id);
			// 					Builder.CreateCall(FidesMaxStackIdWrite, args_ref_stack_id,"");
			// 				}
			// 				// Builder.CreateCall();
			// 			}
			// 		}
			// 	}
			// }
    		/* Setting code compartment metadata */
    		
/*
    		std::string source_filename_with_ext(M.getSourceFileName());
			std::string source_filename(M.getSourceFileName());
			fides_initialize_compartment_map(sanitize(source_filename_with_ext, '/'));

			for (auto &F : M){
				int compartment_id = DefaultCompartment;
			   	bool checkcap_insert = false;
			  	std::map <std::string, int>::iterator it;
			  	auto functionName = F.getName().str();
			  	it  = compartment_map.find(functionName);
			  	if(it != compartment_map.end()){
			    	compartment_id = compartment_map.at(functionName);
			  	}

	 			it  = checkcap_map.find(functionName);
			  	if(it != checkcap_map.end()){
			    	checkcap_insert = true;
			  	}
				std::string ts = ".text.c.";
			  	ts.append(std::to_string(compartment_id));
			  	F.setSection(StringRef(ts));
			 	
			  	if(checkcap_insert || AllEntry){
			    	Constant* compartmentPrefix = ConstantInt::get(Type::getInt64Ty(Ctx), compartment_id, false);
			    	F.setPrefixData(compartmentPrefix);
			  	}
			}
*/
    		// modified =  true
    		errs()<<"Good bye\n";
			return true;
		}
	};
}

char FidesPass::ID = 0;

// static RegisterStandardPasses Y(
//     PassManagerBuilder::EP_EnabledOnOptLevel0,
//     [](const PassManagerBuilder &Builder,
//        legacy::PassManagerBase &PM) { PM.add(new FidesPass()); });

INITIALIZE_PASS_BEGIN(FidesPass,
                      "fides",
                      "Memory safety transforms", false, false)
INITIALIZE_PASS_DEPENDENCY(ADCELegacyPass)
INITIALIZE_PASS_DEPENDENCY(DominatorTreeWrapperPass)
INITIALIZE_PASS_DEPENDENCY(PostDominatorTreeWrapperPass)
INITIALIZE_PASS_END(FidesPass,
                      "fides",
                      "Memory safety transforms", false, false)

namespace llvm {
	ModulePass *createFidesPass() {
			errs()<<"HI\n";
  		return new FidesPass();
	}
} // namespace llvm
