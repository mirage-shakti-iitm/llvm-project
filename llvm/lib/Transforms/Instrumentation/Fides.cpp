/* TODO: Should do realloc, calloc any other allocator functions */
/* TODO: Should do global objects */ 

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

#include "llvm/Support/CommandLine.h"
#include "llvm/IR/LegacyPassManager.h"
#include "llvm/Transforms/IPO/PassManagerBuilder.h"
#include "llvm/InitializePasses.h"


using namespace llvm;

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
		FidesPass() : ModulePass(ID) {initializeFidesPassPass(*PassRegistry::getPassRegistry());}

		

		virtual bool runOnModule(Module &M)
		{	

			errs()<<"Welcome\n";

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

	            auto FidesMallocFn = M.getOrInsertFunction("__fides_malloc", FunctionType::get(Type::getInt8PtrTy(Ctx), {Type::getInt64Ty(Ctx)}, false));
	            auto FidesFreeFn = M.getOrInsertFunction("__fides_free", FunctionType::get(Type::getVoidTy(Ctx), {Type::getInt8PtrTy(Ctx)}, false));

	            for (auto name : malloc_names) {
	    			M.getOrInsertFunction(name, FunctionType::get(Type::getInt8PtrTy(Ctx), {Type::getInt64Ty(Ctx)}, false)).getCallee()->replaceAllUsesWith(FidesMallocFn.getCallee());
	    		}
	    		for (auto name : free_names) {
	    			M.getOrInsertFunction(name, FunctionType::get(Type::getVoidTy(Ctx), {Type::getInt8PtrTy(Ctx)}, false)).getCallee()->replaceAllUsesWith(FidesFreeFn.getCallee());
	    		}
			}
    		
    	/* Instrument Load-Store instructions. Don't instrument instructions accessing int/float objects */
    	for (auto &F : M){
    		// errs()<<"HI SAI 1\n";
    		Module *m = F.getParent();
    		Function *val = Intrinsic::getDeclaration(m, Intrinsic::riscv_validate);	// get hash intrinsic declaration

    		for (auto &B : F)
				{
					// Iterate over Instrs in BB
					for (auto &I : B)
					{
							// errs()<<"HI SAI 21: "<<I<<"\n";
							
							// If instruction is load instruction apply bounds check
							if (LoadInst *LI = dyn_cast<LoadInst>(&I)){
								Value *po = LI->getPointerOperand();
								// errs()<<"HI SAI 12\n";
								if(EnableBoundsCheck){
									// errs()<<"HI SAI 2\n";
									
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

									llvm::Constant *temporalCheck = llvm::ConstantInt::get(Type::getInt64Ty(Ctx), 0x2ULL, false);
									llvm::Constant *spatialCheck = llvm::ConstantInt::get(Type::getInt64Ty(Ctx), 0x1ULL, false);

									std::vector<Value *> args1;
									std::vector<Value *> args2;
									args1.push_back(po);
									args1.push_back(spatialCheck);
									
									args2.push_back(po);
									args2.push_back(temporalCheck);

									ArrayRef<Value *> args_ref1(args1);
									ArrayRef<Value *> args_ref2(args2);

									if(insert_check){
										// Create call to intrinsic
										IRBuilder<> Builder(LI);
										Builder.SetInsertPoint(LI);
										Builder.CreateCall(val, args_ref1,"");
										Builder.CreateCall(val, args_ref2,"");
									}
								}
							}
							if (StoreInst *SI = dyn_cast<StoreInst>(&I)){
								Value *po = SI->getPointerOperand();
								if(EnableBoundsCheck){
									bool insert_check = true;
									if (auto *AI = dyn_cast<AllocaInst>(SI->getPointerOperand())){
    								Type *pt = SI->getPointerOperandType();
    								// errs()<<*SI<<" :: "<<*SI->getOperand(1)<<" :: "<<*SI->getPointerOperandType()<<"\n";
    								if(dyn_cast<PointerType>(pt)){
											// errs()<<*pt->getPointerElementType()<<"::"<<pt->getPointerElementType()->isArrayTy()<<"::"<<*AI->getAllocatedType()<<"\n";
											if(!pt->getPointerElementType()->isPointerTy()){
												insert_check = false;
											}
										}	
    							}

									llvm::Constant *temporalCheck = llvm::ConstantInt::get(Type::getInt64Ty(Ctx), 0x2ULL, false);
									llvm::Constant *spatialCheck = llvm::ConstantInt::get(Type::getInt64Ty(Ctx), 0x1ULL, false);

									std::vector<Value *> args1;
									std::vector<Value *> args2;
									args1.push_back(po);
									args1.push_back(spatialCheck);
									
									args2.push_back(po);
									args2.push_back(temporalCheck);

									ArrayRef<Value *> args_ref1(args1);
									ArrayRef<Value *> args_ref2(args2);

									if(insert_check){
										// Create call to intrinsic
										IRBuilder<> Builder(SI);
										Builder.SetInsertPoint(SI);
										Builder.CreateCall(val, args_ref1,"");
										Builder.CreateCall(val, args_ref2,"");
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

    	if(!EnableBoundsCheck){
    		return 0;
    	}

    	std::vector<CallInst*> CIToInstrument;
    	for (auto &F : M){
    		Module *m = F.getParent();
    		for (auto &B : F)
				{
					// Iterate over Instrs in BB
					for (auto &I : B)
					{
						if(auto *CI = dyn_cast<CallInst>(&I)){
							if(!(CI->getCalledFunction()->getName().contains("fides") || CI->getCalledFunction()->getName().contains("llvm"))){
								errs()<<"Insert : "<<*CI<<"\n";
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

    	for (auto &F : M){
    		Module *m = F.getParent();

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
							}
						}
					}
				}
			}

    	for (auto &F : M){
    		Module *m = F.getParent();

    		for (auto &B : F)
				{
					// Iterate over Instrs in BB
					for (auto &I : B)
					{
						if(auto *AI = dyn_cast<AllocaInst>(&I)){
							// Insert metadata if stack object allocated is an Aggregate type(union, struct, array)
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
							
								// errs()<<*(AI)<<" : "<<*AI->getAllocatedType()<<":"<<*AI->getType()<<" : isArray = "<<AI->getAllocatedType()->isArrayTy()<<" : isStruct = "<<AI->getAllocatedType()->isStructTy()<<" : isAggregate = "<<AI->getAllocatedType()->isAggregateType()<<" : size = "<<(AI->getAllocationSizeInBits(m->getDataLayout())).getValue()/8<<"\n";
								for (User *U : Users){
									// errs()<<*U<<" <--> ";
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

			for (auto *CI : CIToInstrument){
				IRBuilder<> Builder(CI->getNextNode());
				errs()<<"Insert before : "<<*CI->getNextNode()<<"\n";
				std::vector<Value *> args_stack_id;
				args_stack_id.push_back(maxStackID);
				ArrayRef<Value *> args_ref_stack_id(args_stack_id);
				Builder.CreateCall(FidesMaxStackIdWrite, args_ref_stack_id,"");
			}


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

    		// modified =  true
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
INITIALIZE_PASS_END(FidesPass,
                      "fides",
                      "Memory safety transforms", false, false)

namespace llvm {
	ModulePass *createFidesPass() {
			errs()<<"HI\n";
  		return new FidesPass();
	}
} // namespace llvm
