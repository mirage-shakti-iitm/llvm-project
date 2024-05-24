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

#include "llvm/Support/CommandLine.h"
#include "llvm/IR/LegacyPassManager.h"
#include "llvm/Transforms/IPO/PassManagerBuilder.h"
#include "llvm/InitializePasses.h"

#define debug_spass
// #define debug_spass_dmodule
// #define debug_sms_pass_2
// #define debug_sms_pass_5
// #define debug_craft_fat_pointer
// #define debug_is_local

using namespace llvm;

static cl::opt<bool>
    EnableShaktiMS("enable-shakti-ms",
                 cl::desc("Enable-ShaktiMS Pass"), cl::init(false), cl::Hidden);

static cl::opt<std::string>
    IgnoreFilesShaktiMS("ignore-files-shakti-ms",
                 cl::desc("Enable-ShaktiMS Pass"), cl::init(""), cl::Hidden);

Type* resolveFunctionPointers(FunctionType *func_type, LLVMContext &Ctx);
void resolveGetElementPtr(GetElementPtrInst *GI,DataLayout *D,LLVMContext &Context,std::map <StructType*, StructType*> rep_structs);
Value* resolveGEPOperator(GEPOperator *GI,DataLayout *D,LLVMContext &Context);
void staticLoadStore(GEPOperator* operand,Instruction *I,Function *F,std::string str,LLVMContext &Ctx);
bool isLocal(Instruction *ins);
void craftFatPointer(Instruction *ins, unsigned int i, FunctionCallee craftFunc,DataLayout *D,LLVMContext &Ctx,PtrToIntInst *ptr_to_st_cook,TruncInst *ptr_to_st_hash,GlobalVariable *rodata_cookie,unsigned long ro_hash);
namespace {
	struct shaktiPass : public ModulePass
	{
		static char ID;
		shaktiPass() : ModulePass(ID) {initializeshaktiPassPass(*PassRegistry::getPassRegistry());}

		std::map <StructType*, StructType*> rep_structs;

		virtual bool runOnModule(Module &M)
		{	

			if(EnableShaktiMS == false){
				return 0;
			}

			errs()<<"Source File Name : "<<M.getSourceFileName()<<"\n";
			errs()<<"IgnoreFiles : "<<IgnoreFilesShaktiMS<<"\n";

			
			std::string source_filename = M.getSourceFileName();
			size_t pos_sf = source_filename.find_last_of("/");
			if(source_filename.find_last_of("/") == std::string::npos){
				pos_sf = -1;
			}
			std::string sanitize_source_filename = source_filename.substr(pos_sf + 1);
			// errs()<<"Sasddai : "<<pos_sf<<" : "<<sanitize_source_filename<<"\n";

		
			std::string del = ",";
			int start = 0;
    		int end = IgnoreFilesShaktiMS.find(del);
    		std::string ignore_file;
    		int ignore_matches = 0;
    		while (end != -1) {
    			ignore_file = IgnoreFilesShaktiMS.substr(start, end - start);
        		// errs() << ignore_file << "\n";
        		start = end + del.size();
        		end = IgnoreFilesShaktiMS.find(del, start);
        		if(ignore_file.compare(sanitize_source_filename) == 0){
        			ignore_matches = 1;
        		}
    		}
    		ignore_file = IgnoreFilesShaktiMS.substr(start, end - start);
    		// errs() << ignore_file << "\n";
    		if(ignore_file.compare(sanitize_source_filename) == 0){
        			ignore_matches = 1;
        	}
    		if(ignore_matches){
    			errs()<<"No Shakti-MS pass"<<"\n";
    			return 0;
    		}

			errs()<<"********************************************\n";
			// To skip the Shakti-MS pass if the no functions present in the module
			bool moduleHasFunctions = false;

		// if(EnableShaktiMS == 1){
			/* before doing anything check whether pointer decrements are there or not in any function. */
			std::set<std::string> func_name;
			for (auto &F : M){
				if (!F.isDeclaration()) {
					
					moduleHasFunctions = true;
					
					for (auto &B : F){
						for (auto &I : B){
							if(GetElementPtrInst *GI = dyn_cast<GetElementPtrInst>(&I)){
								if(ConstantInt *CI = dyn_cast<ConstantInt>(GI->getOperand(1))){
									if(CI->isNegative()){

										//errs() << "!!!!!!!!!!!Warning Pointer Decrement in function  : " << F.getName() << "!!!!!!!!!!!!!!!!!!!\n" ;
										//errs() << *GI->getOperand(0) << "\n" ;
										// errs() << F.getName() ;
										func_name.insert(F.getName().str());

									}
								}else{
									if(Instruction *I = dyn_cast<Instruction>(GI->getOperand(1))){
										if(I->getOpcode() == Instruction::Sub){

											//errs() << "!!!!!!!!!!!Warning Pointer Decrement in function  : " << F.getName() << "!!!!!!!!!!!!!!!!!!!\n" ;
											//errs() << *GI->getOperand(0) << "\n" ;
											func_name.insert(F.getName().str());
										}
									}
								}

							}
						}
					}
				}
			}
			if(!func_name.empty()) {
				errs () << " !!!!!!!!!!! Warning Pointer Decrement in function \n" ;
				std::set<std::string>:: iterator itr;
				for (itr = func_name.begin(); itr != func_name.end(); ++itr)
			    {
   				    // errs() << " Here \n" ;
			        errs() << *itr << " : " ;
       			    // errs() << " Here \n" ;

			    }
			    errs() << " !!!!!!!!!!!!!!!!!!! \n" ;
			}
			/*checking for pointer decrement ends here .*/

			bool modified=false;

			// Skipping Shakti-MS pass if the no functions present in the module
			if(moduleHasFunctions == false){
				return modified	;
			}

			unsigned long long ro_cook = 0xdeadbeef1337c0d3;
			unsigned long ro_hash = 0xcd9a7e3c;
			// First pass creates duplicate definitions of structs with pointers
			std::vector< StructType * > structs = M.getIdentifiedStructTypes();
			for(auto &def : structs)
			{
				errs()<<*def<<"\n";
				LLVMContext &GCtx = def->getContext();
				bool flag = false;
				std::vector<Type *> elems_vec;
				for(StructType::element_iterator i = def->element_begin(), end = def->element_end(); i!= end; ++i)
				{
					Type *ty = dyn_cast<Type>(*i);
					// errs()<<*ty<<"\n";
					bool isFnArr = false;
					//if element type is of function pointers then dont make any changes.
					if(dyn_cast<PointerType>(ty)){
						isFnArr = dyn_cast<PointerType>(ty)->getElementType()->isFunctionTy();
					}
					
					// Array within struct
					


					if(ty->isPointerTy())
					{
						//convert normal pointers to i128 leave function pointers.
						//but check each elements of function pointers and if they have pointers then convert them to i128
						if(!isFnArr){
							elems_vec.push_back(Type::getInt128Ty(GCtx));
						}else{
							// errs()<<"Here\n";
							FunctionType *func_type = dyn_cast<FunctionType>(dyn_cast<PointerType>(ty)->getElementType());
							std::vector<Type*> fParamTypes;
							
							Type *func_ret_type = func_type->getReturnType();
							// errs()<<"Here 3 : "<<*func_ret_type<<"\n";
							Type *fRetType;
							if(func_type->getReturnType()->isPointerTy()){
								if((dyn_cast<PointerType>(func_ret_type)->getElementType()->isFunctionTy()))
									fRetType = resolveFunctionPointers(dyn_cast<FunctionType>(dyn_cast<PointerType>(func_ret_type)->getElementType()), GCtx);
								else
									fRetType = Type::getInt128Ty(GCtx);
							}
							else{
								fRetType = func_ret_type;
							}
							// errs()<<"Here 4 : "<<*fRetType<<"\n";
							for(FunctionType::param_iterator k = func_type->param_begin(), endp = func_type->param_end(); k != endp; ++k){
								bool argIsFnArr = 0;
								errs()<<**k<<"\n";
								if(dyn_cast<PointerType>(*k)){
									argIsFnArr = dyn_cast<PointerType>(*k)->getElementType()->isFunctionTy();
								}
								if((*k)->isPointerTy()){
									if(!argIsFnArr)
										fParamTypes.push_back(Type::getInt128Ty(GCtx));		
									else{
										FunctionType *org_func_type = dyn_cast<FunctionType>(dyn_cast<PointerType>(*k)->getElementType());
										Type *newSubType = resolveFunctionPointers(org_func_type, GCtx);
										fParamTypes.push_back(newSubType);
									}
								}
							}
							// errs()<<"Here\n";
							FunctionType *newFuncType = FunctionType::get(fRetType,fParamTypes,func_type->isVarArg());
							// errs() << "new function type : " << *newFuncType->getPointerTo() << "\n" ;
							Type *newType = resolveFunctionPointers(func_type, GCtx);
							elems_vec.push_back(newType);
						}
						flag = 1;
					}
					/*else if(ty->isArrayTy())
					{
						.
					}*/
					else
					{
						elems_vec.push_back(ty);
					}
				}
				if(flag)
				{
					//errs()<<dyn_cast<StructType>(def)<<"\n";
					ArrayRef<Type *> elems(elems_vec);
					StructType *frm = dyn_cast<StructType>(def);
					StructType *to = StructType::create(elems,frm->getStructName(),frm->isPacked());

					DataLayout *D = new DataLayout(&M);
					const StructLayout *SL_to = D->getStructLayout(to);
					const StructLayout *SL_from = D->getStructLayout(frm);
					unsigned long long to_sz = SL_to->getSizeInBytes();
					unsigned long long from_sz = SL_from->getSizeInBytes();
					errs()<<"------------------\nINSERTING "<<*frm<<" : size = "<<from_sz<<"\nTO "<<*to<<" : size = "<<to_sz<<"\n------------------\n";
					rep_structs.insert(std::make_pair(frm, to));
				}
			}
			int global_count = 0;
			std::map <GlobalVariable*, Constant*> glob_var;
			for(Module::global_iterator j = M.global_begin(), end = M.global_end(); j != end; ++j)
			{
				global_count++;
				GlobalVariable *glob = dyn_cast<GlobalVariable>(j);
				LLVMContext &GCtx = glob->getContext();
				if(!glob->getType()->isPointerTy())
				{
					continue;
					//errs()<<*glob->getType()<<"\n";
				}
				//errs()<<*glob<<" : "<<glob->isConstant()<<"\n";
				if(glob->isConstant())
					continue;
				if(glob->hasInitializer())
				{
					//todo
					if(!glob->getValueType()->isPointerTy())
						continue;
						//errs()<<"HERE"<<*glob<<"\n";
					//glob->mutateType(Type::getInt128Ty(GCtx));

					//errs() << *glob << " : "  << dyn_cast<PointerType>(glob->getValueType())->getElementType()->isFunctionTy() << "\n " ;
					if(dyn_cast<PointerType>(glob->getValueType())->getElementType()->isFunctionTy()){
						FunctionType *func_type = dyn_cast<FunctionType>(dyn_cast<PointerType>(glob->getValueType())->getElementType());
						std::vector<Type*> fParamTypes;

						Type *func_ret_type = func_type->getReturnType();
						Type *fRetType = (func_type->getReturnType()->isPointerTy() && !(dyn_cast<PointerType>(func_ret_type)->getElementType()->isFunctionTy()) ? Type::getInt128Ty(GCtx) : func_ret_type);
						for(FunctionType::param_iterator k = func_type->param_begin(), endp = func_type->param_end(); k != endp; ++k){
							bool argIsFnArr = 0;
							if(dyn_cast<PointerType>(*k)){
								argIsFnArr = dyn_cast<PointerType>(*k)->getElementType()->isFunctionTy();
							}
							if((*k)->isPointerTy() && !argIsFnArr){
								fParamTypes.push_back(Type::getInt128Ty(GCtx));
							}
							else
								fParamTypes.push_back(*k);
						}
						FunctionType *newFuncType = FunctionType::get(fRetType,fParamTypes,func_type->isVarArg());
					//	errs() << "new function type : " << *newFuncType->getPointerTo() << "\n" ;
						Type *newType = newFuncType->getPointerTo() ;
						//elems_vec.push_back(newType);
						Constant *null_val = ConstantPointerNull::getNullValue(newType);
						GlobalVariable *glob2 = new GlobalVariable
						(
							M,
							newType,
							glob->isConstant(),
							glob->getLinkage(),
							null_val,
							"fpr_"+glob->getName(),
							glob
						);
						glob->replaceAllUsesWith(glob2);
						j--;
						glob->dropAllReferences();
						glob->eraseFromParent();
						continue;
					}

					//reach here  only if its a pointer and not a global function pointer

					//if a global pointer is initialised directly as ptr = &val.
					//then in main first store this value in the new global variable created.

					GlobalVariable *glob2 = new GlobalVariable
					(
						M,
						Type::getInt128Ty(GCtx),
						glob->isConstant(),
						glob->getLinkage(),
						llvm::ConstantInt::get(Type::getInt128Ty(GCtx),0),
						"fpr_"+glob->getName(),
						glob
					);
					//errs()<<"CTXT: "<<&(glob->getContext())<<"\t"<<&(glob2->getContext())<<"\n";
					glob->replaceAllUsesWith(glob2);
					if(!glob->getInitializer()->isNullValue()){
						glob_var.insert(std::make_pair(glob2, glob->getInitializer()));
					}
					//glob2->setParent(glob->getParent());
					//errs()<<*glob<<"\n"<<*glob2<<"\n";
					j--;
					glob->dropAllReferences();
					glob->eraseFromParent();
				}
				else
				{
					//glob->mutateType(Type::getInt128Ty(GCtx));
					//errs()<<*glob<<"\n";
				}
			}

			GlobalVariable *rodata_cookie;
			//to add the rodata_cookie at the beginning of all the global variables.
			if(global_count != 0){
				GlobalVariable *first_global_var = dyn_cast<GlobalVariable>(M.global_begin());

				rodata_cookie = new GlobalVariable(M, Type::getInt64Ty(M.getContext()), true, GlobalValue::LinkageTypes::PrivateLinkage, ConstantInt::get(Type::getInt64Ty(M.getContext()),ro_cook), "ro_cookie",first_global_var);
			}else{
				rodata_cookie = new GlobalVariable(M, Type::getInt64Ty(M.getContext()), true, GlobalValue::LinkageTypes::PrivateLinkage, ConstantInt::get(Type::getInt64Ty(M.getContext()),ro_cook), "ro_cookie");
			}
			#ifdef debug_spass
				errs()<<"First pass done\n";
			#endif

			// Second pass replaces malloc and free
			Value *mallocFunc;
			Value *freeFunc;
			Value *reallocFunc;
			FunctionCallee mallocFC;
			FunctionCallee freeFC;
			FunctionCallee reallocFC;

			for (auto &F : M)
			{
				modified=false;
				// Get the safemalloc function to call from the new library.
				LLVMContext &Ctx = F.getContext();
				DataLayout *D = new DataLayout(&M);
				// Malloc arg is just one unsigned long
				std::vector<Type*> mallocParamTypes = {Type::getInt64Ty(Ctx)};
				std::vector<Type*> safeMallocParamTypes = {Type::getInt64Ty(Ctx)};
				// Free arg is i8*
				std::vector<Type*> freeParamTypes = {Type::getInt8PtrTy(Ctx)};
				std::vector<Type*> safeFreeParamTypes = {Type::getInt128Ty(Ctx)};
				// Return type of malloc is i8*
				Type *mallocRetType = Type::getInt8PtrTy(Ctx);
				Type *safeMallocRetType = Type::getInt128Ty(Ctx);
				// Return type of free is void
				Type *freeRetType = Type::getVoidTy(Ctx);
				Type *safeFreeRetType = Type::getVoidTy(Ctx);
				// Put everything together to make function type i8*(i64)
				FunctionType *mallocFuncType = FunctionType::get(mallocRetType, mallocParamTypes, false);
				FunctionType *safeMallocFuncType = FunctionType::get(safeMallocRetType, safeMallocParamTypes, false);
				// Put everything together to make function type void*(i8*)
				FunctionType *freeFuncType = FunctionType::get(freeRetType, freeParamTypes, false);
				FunctionType *safeFreeFuncType = FunctionType::get(safeFreeRetType, safeFreeParamTypes, false);
				// Get function pointer for malloc
				mallocFunc = F.getParent()->getOrInsertFunction("malloc", mallocFuncType).getCallee();
				// Get function pointer for free
				freeFunc = F.getParent()->getOrInsertFunction("free", freeFuncType).getCallee();
				// Make safemalloc declaration, get pointer to it
				auto safemallocFuncAL = dyn_cast<Function>(mallocFunc)->getAttributes();
				Value* safemallocFunc = F.getParent()->getOrInsertFunction("safemalloc", safeMallocFuncType).getCallee();
				// Make safefree declaration, get pointer to it
				FunctionCallee safefreeFunc = F.getParent()->getOrInsertFunction("safefree", safeFreeFuncType);

				//adding function prototype for saferealloc and realloc
				std::vector<Type*> reallocParamTypes = {Type::getInt8PtrTy(Ctx),Type::getInt64Ty(Ctx)};
				Type *reallocRetType = Type::getInt8PtrTy(Ctx);
				FunctionType *reallocFuncType = FunctionType::get(reallocRetType, reallocParamTypes, false);
				reallocFunc = F.getParent()->getOrInsertFunction("realloc", reallocFuncType).getCallee();

				std::vector<Type*> safeReallocParamTypes = {Type::getInt128Ty(Ctx),Type::getInt64Ty(Ctx)};
				Type *safeReallocRetType = Type::getInt128Ty(Ctx);
				FunctionType *safeReallocFuncType = FunctionType::get(safeReallocRetType, safeReallocParamTypes, false);
				FunctionCallee safereallocFunc = F.getParent()->getOrInsertFunction("saferealloc", safeReallocFuncType);

				mallocFC = F.getParent()->getOrInsertFunction("malloc", mallocFuncType);
				freeFC = F.getParent()->getOrInsertFunction("free", freeFuncType);
				reallocFC = F.getParent()->getOrInsertFunction("realloc", reallocFuncType);

				// errs() << "\nMalloc Func Attributes:\n";
				// errs() <<  *safemallocFunc;
				// errs() <<  *mallocFunc;
				// errs() << "\nMalloc Func Attributes:\n";

				// Iterate over BBs in F
				for (auto &B : F)
				{
					// Iterate over Instrs in BB
					for (auto &I : B)
					{
						// If instruction is of type call
						if (auto *op = dyn_cast<CallInst>(&I))
						{
							#ifdef debug_sms_pass_2
								errs()<<op->getCalledOperand()->getName()<<" : "<<op->getCalledOperand()->hasName()<<" : "<<F.getName()<<"\n";
								if(!(op->getCalledOperand()->hasName())){
									errs() << I<<"\n";
									errs() << *op->getCalledOperand()->getType()<<"\n";
								}
							#endif

							// If call invokes malloc
							if((op->getCalledOperand() == mallocFunc) || (op->getCalledOperand() == reallocFunc))
							{
								BitCastInst *nextbc;
								// errs()<<"*******\n"<<*op<<"\n"<<*op->getNextNode()<<"\n-------\n";
								if((nextbc = dyn_cast<BitCastInst>(op->getNextNode())))
								{
									if(op == nextbc->getOperand(0))
									{
										PointerType *bcptr;
										if((bcptr = dyn_cast<PointerType>(nextbc->getDestTy())))
										{
											StructType *st;
											Type* eltype = bcptr->getElementType();
											if((st = dyn_cast<StructType>(eltype)))
											{
												if(rep_structs.find(st) != rep_structs.end())
												{
													//errs()<<"HERE: "<<*(rep_structs.at(st))<<"\n";
													StructType *to = rep_structs.at(st);
													const StructLayout *SL = D->getStructLayout(to);
													const StructLayout *SL1 = D->getStructLayout(st);
													unsigned long long new_sz = SL->getSizeInBytes();
													unsigned long long old_sz = SL1->getSizeInBytes();
													//errs()<<*op->getOperand(0)<<"\n"<<*nextbc<<"\n"<<sz<<"\n";
													//check size . if malloc then operand 0 else operand 1
													Value *getOperand;
													if(op->getCalledOperand() == mallocFunc){
														getOperand = op->getOperand(0);
													}else{ // for realloc
														getOperand = op->getOperand(1);
													}
													if(dyn_cast<ConstantInt>(getOperand)){
														unsigned long long operand_sz = dyn_cast<ConstantInt>(getOperand)->getZExtValue();
														//this check is required because if we malloc 20*sizeof(some_struct)
														//in llvm IR it is a constant value . so to check that this check is required
														if(operand_sz != old_sz){
															new_sz = new_sz * (operand_sz / old_sz) ;
														}
														//errs() << "old : " << old_sz << " new : " << new_sz << " size of operand : " << operand_sz << "\n" ;
														if(op->getCalledOperand() == mallocFunc){
															op->setOperand(0,llvm::ConstantInt::get(Type::getInt64Ty(Ctx),new_sz));
														}else{//realloc
															op->setOperand(1,llvm::ConstantInt::get(Type::getInt64Ty(Ctx),new_sz));
														}
													}
												}
											}
										}

									}
								}
								//errs()<<"\n----------------\nReplacing:\n";
								//op->print(llvm::errs(), NULL);
								//errs()<<"\nwith:\n";
								// Replace malloc with safemalloc in call

								if(op->getCalledOperand() == mallocFunc){
									// errs() << "\n" << *op;
									
									op->setCalledFunction(dyn_cast<Function>(safemallocFunc));
									// op->setCalledFunction (safeMallocFuncType, safemallocFunc);
									op->mutateType(Type::getInt128Ty(Ctx));
									
									auto AL = op->getAttributes();
									// errs() << "\n" << dyn_cast<CallBase>(&I)->hasRetAttr(Attribute::NoAlias) << "\n";
									
									AttrBuilder RetAttrs;
  									// RetAttrs.addAttribute(Attribute::SExt);
  									// RetAttrs.addAttribute(Attribute::ZExt);
  									RetAttrs.addAttribute(Attribute::NoAlias);
  									(dyn_cast<CallBase>(&I))->removeAttribute(AttributeList::ReturnIndex, Attribute::NoAlias);
									
									// errs() << "\n" << dyn_cast<CallBase>(&I)->hasRetAttr(Attribute::NoAlias) << "\n";
									// errs() << "\n" << AL.getNumAttributes() << "\n";
									// errs() << "\n" << *op << "\n";
								}else{
									// errs() << "\n" << *op;
								
									op->setCalledFunction (safereallocFunc);
									op->mutateType(Type::getInt128Ty(Ctx));
									// errs() << "\n" << *op << "\n";
								}
								//op->print(llvm::errs(), NULL);
								//errs()<<"\n----------------\n";

								// Set flag if modified
								modified=true;
							}
							else if((op->getCalledOperand()) == (freeFunc))
							{
								// errs()<<"\n----------------\nReplacing:\n";
								// op->print(llvm::errs(), NULL);
								// errs()<<"\nwith:\n";
								// Replace free with safefree in call
								// errs() << "\n" << *op;
								
								op->setCalledFunction (safefreeFunc);
								// op->print(llvm::errs(), NULL);
								// errs()<<"\n----------------\n";
								// errs() << "\n" << *op << "\n";
								// Set flag if modified
								modified=true;
							}
							
						}
					}
				}
			}
			#ifdef debug_spass
				errs()<<"Second pass done\n";
			#endif
			
			// m->replaceAllUsesWith(funcy)
			dyn_cast<Function>(mallocFunc)->dropAllReferences();
			dyn_cast<Function>(freeFunc)->dropAllReferences();
			dyn_cast<Function>(mallocFunc)->removeFromParent();
			dyn_cast<Function>(freeFunc)->removeFromParent();//*/

			// Third pass adds stack cookie
			//place the stack cookie below every variable available on stack
			//then in fifth pass when you encounter alloca's then craft fatpointer belwo this 
			Instruction *FPR;
			TruncInst *ptr_to_st_hash;
			PtrToIntInst *ptr_to_st_cook;

			std::map<std::string,std::vector<Instruction *>> mapInst;
			for (auto &F : M)
			{
				if(F.isDeclaration())
					continue;
				Instruction *AI,*RI;
				bool stack_cook_ins = false,flag = false;
				LLVMContext &Ctx = F.getContext();
				Module *m = F.getParent();
				Function *hash = Intrinsic::getDeclaration(m, Intrinsic::riscv_hash);	// get hash intrinsic declaration

				std::vector<Type*> randomParamTypes;// = {Type::getVoidTy(Ctx)};
				Type *randomRetType = Type::getInt64Ty(Ctx);
				FunctionType *randomFuncType = FunctionType::get(randomRetType, randomParamTypes, false);
				FunctionCallee randomF = F.getParent()->getOrInsertFunction("random64", randomFuncType);

				AllocaInst *st_cook;	// pointer to stack cookie
				for (auto &B : F)
				{
					if(&B == &((&F)->front()))
					{	// If BB is first

						AI = &((&B)->front());	// Get first instruction in function
					}

					for (auto &I : B){	// Iterate over instructions to get the last Alloca and Return Inst
						if (!dyn_cast<AllocaInst>(&I) && !stack_cook_ins && !flag)
						{
							AI = &I;
							flag = true;
						}
						if (dyn_cast<ReturnInst>(&I))
						{	// If return instruction
							RI = &I;
						}
					}
					if(!stack_cook_ins){
						/*if(flag)
							FPR = AI->getNextNode();	//that means there is a alloca so go to next instruction and then insert before it
						else
							FPR = AI; //no alloca inst is there. only printf. then insert before printf
*/
						FPR = AI;
						// errs() << *I << "\n";
						st_cook = new AllocaInst(Type::getInt64Ty(Ctx), 0,"stack_cookie", FPR);	// alloca stack cookie
						ptr_to_st_cook = new PtrToIntInst(st_cook,Type::getInt32Ty(Ctx), "stack_cookie_32", FPR);
						CallInst *getRandom = CallInst::Create (randomF, "", FPR);
						new StoreInst(getRandom,st_cook,FPR);

						// Set up intrinsic arguments
						std::vector<Value *> args;
						args.push_back(st_cook);
						ArrayRef<Value *> args_ref(args);

						// Create call to intrinsic
						IRBuilder<> Builder(FPR);
						Builder.SetInsertPoint(FPR);
						Value *hash64 = Builder.CreateCall(hash, args_ref,"stack_hash_long");
						ptr_to_st_hash = new TruncInst(hash64, Type::getInt32Ty(Ctx),"stack_hash", FPR);
						stack_cook_ins = true;
						modified  = true;
						errs() << "Stack Cookie Inserted \n" ;
					}
				}
				//set up arguments
				std::vector<Value *> args;
				args.push_back(st_cook);
				ArrayRef<Value *> args_ref(args);

				//Call hash again to burn the cookie
				IRBuilder<> Builder(RI);
				Builder.SetInsertPoint(RI);
				CallInst *burnRandom = CallInst::Create (randomF, "", RI);
				new StoreInst(burnRandom,st_cook,RI);
				Builder.CreateCall(hash, args_ref,"stack_cookie_burn");
				// errs() << "Adding done in function " << F.getName() << "\n" ;

				std::vector<Instruction *> storeInsPoint;
				storeInsPoint.push_back(FPR);
				storeInsPoint.push_back(ptr_to_st_cook);
				storeInsPoint.push_back(ptr_to_st_hash);
				mapInst.insert(std::pair<std::string,std::vector<Instruction *>>(F.getName().str(),storeInsPoint));

			}
			#ifdef debug_spass
				errs()<<"Third pass done\n";
			#endif

			// Fourth pass Fixes argument types in function calls within the module
			Module::FunctionListType &functions = M.getFunctionList();
			std::map<std::string, std::vector<Type*>> function_parameters;
			std::stack< Function * > to_replace_functions;
			std::stack< Function * > replace_with_functions;
			std::stack< int > argCount;

			for (Module::FunctionListType::iterator it = functions.begin(), it_end = functions.end(); it != it_end; ++it)
			{
				//Function *func = dyn_cast<Function>(it);
				Function &func = *it;

				LLVMContext &Ctx = func.getContext();
				if(func.isDeclaration())
				{
					
					if(!func.getName().contains("__gm")){
						errs()<<"\nSkipping func declaration: "<<func.getName()<<"\n";
						continue;
					}
					// errs()<<"\nChanging Func declaration: "<<func.getName()<<"\n";
				}
				//errs()<<"\n*****\nFound definition:\n"<<func<<"\n*****\n";

				std::vector<Type*> fParamTypes;
				std::vector<Type*> fOriginalParamTypes;

				bool fnHasPtr = false;
				fnHasPtr = (func.getReturnType()->isPointerTy() ? true : false);

				int arg_index = 0;

				bool isFnArr = 0;
				if(dyn_cast<PointerType>(func.getReturnType()))
				{
					isFnArr = dyn_cast<PointerType>(func.getReturnType())->getElementType()->isFunctionTy();
				}

				Type *fRetType;
				if(fnHasPtr){
					fRetType = (!(isFnArr) ? Type::getInt128Ty(Ctx) : resolveFunctionPointers(dyn_cast<FunctionType>(dyn_cast<PointerType>(func.getReturnType())->getElementType()), Ctx));
				}
				else{
					fRetType = func.getReturnType();
				}
				for(FunctionType::param_iterator k = (func.getFunctionType())->param_begin(), endp = (func.getFunctionType())->param_end(); k != endp; ++k)
				{
					arg_index++;
					bool argIsFnArr = 0;
					fOriginalParamTypes.push_back(*k);
					if(dyn_cast<PointerType>(*k))
					{
						argIsFnArr = dyn_cast<PointerType>(*k)->getElementType()->isFunctionTy();
					}
					if((*k)->isPointerTy() && !argIsFnArr)
					{
						//j->mutateType(Type::getInt128Ty(Ctx));
						fnHasPtr = true;
						fParamTypes.push_back(Type::getInt128Ty(Ctx));
						//errs()<<**k<<"\n";

						//if the function returns a structure then remove its attributes. 
						//struct return is basically function argument 1 in llvm IR
						if(func.hasStructRetAttr()){
							//errs() << "Struct type detected . so remove all attributes\n" ;
							AttributeList AL = func.getAttributes();
							AttributeList A = AL.removeParamAttributes(Ctx,0);
							func.setAttributes(A);
						}
					}
					else if(argIsFnArr){
						FunctionType *org_func_type = dyn_cast<FunctionType>(dyn_cast<PointerType>(*k)->getElementType());
						Type *newSubType = resolveFunctionPointers(org_func_type, Ctx);
						fParamTypes.push_back(newSubType);
					}
					else
						fParamTypes.push_back(*k);
					//errs()<<"\npushed "<<*(fParamTypes.back());
				}
				function_parameters[func.getName().str()] = fOriginalParamTypes;
				if(!fnHasPtr)
					continue;
				FunctionType *fType = FunctionType::get(fRetType, fParamTypes, func.getFunctionType()->isVarArg());
				Function *NF = Function::Create(fType, func.getLinkage(), func.getName());
				NF->copyAttributesFrom(&func);
				NF->getBasicBlockList().splice(NF->begin(), func.getBasicBlockList());
				to_replace_functions.push(&func);
				replace_with_functions.push(NF);
				argCount.push(arg_index);
			}
			//errs()<<"HERE\n";

			while(!to_replace_functions.empty())
			{
				Function *funcx = to_replace_functions.top();
				Function *funcy = replace_with_functions.top();
				int arg_index = argCount.top();
				// errs()<<"\nto replace: "<<*funcx<<"\n";
				// errs()<<"\nwith      : "<<*funcy<<"\n";
				to_replace_functions.pop();
				replace_with_functions.pop();
				argCount.pop();
				M.getFunctionList().push_back(funcy);
				while (!funcx->use_empty())
				{

					if(dyn_cast<CallInst>(funcx->user_back()))
					{	
						CallInst* call = dyn_cast<CallInst>(funcx->user_back());
						Function* calledFunction = call->getCalledFunction();
						StringRef to_replace_func_name = funcx->getName();
						StringRef called_func_name = call->getCalledFunction()->getName();

						// errs()<<"USER:\n"<<*(funcx->user_back())<<"\n";
						
						/*
						CallBase &CB = cast<CallBase>(*funcx->user_back());
						auto AI = CB.arg_begin();
						unsigned int ArgNo = 0;
					    for (; AI != CB.arg_end(); ++AI, ++ArgNo) {
    						// Args.push_back(*AI);
    						errs()<<"Argument "<<ArgNo<<"  :  "<<*((*AI)->getType())<<"\n";
    						if((*AI)->getName().equals(to_replace_func_name)){
    							errs()<<"FnPtr \n";
    						}
    					}
    					errs()<<"*************************************\n";
						*/
						bool isFnPtr = false;
						if(!called_func_name.equals(to_replace_func_name)){
							// errs()<<"ARG_DIFFERS : "<<*(funcx->user_back())<<"\n";	
							isFnPtr = true;
							funcx->replaceAllUsesWith(funcy);
							// errs()<<"USER:\n"<<*call<<"\n";
							continue;
						}

						std::vector< Value * > new_args;
						std::vector< Value * > args(call->arg_begin(), call->arg_end());
						for(auto& it: args){
							// errs()<<*it<<"\n";
						}

						
						
						// Instruction *call = CS->getInstruction();
						Instruction *new_call = NULL;
						const AttributeList &call_attr = call->getAttributes();
						new_call = CallInst::Create(funcy, args, "", call);
						// errs()<<*(funcy)<<"\n";
						CallInst *ci = cast< CallInst >(new_call);
						ci->setCallingConv(call->getCallingConv());
						ci->setAttributes(call_attr);
						if (ci->isTailCall())
							ci->setTailCall();
						new_call->setDebugLoc(call->getDebugLoc());
						if (!call->use_empty())
						{
							call->replaceAllUsesWith(new_call);
						}
						new_call->takeName(call);

						// errs()<<"NEW:\n"<<*(new_call)<<"\n";
						// errs()<<"NEW:\n"<<*(call)<<"\n";
						call->eraseFromParent();
					}
					else if(dyn_cast<StoreInst>(funcx->user_back()))
					{
						StoreInst *op = dyn_cast<StoreInst>(funcx->user_back());
						//errs()<<"USER:\n"<<*(funcx->user_back())<<"\n";
						//errs()<<*funcy->getType()->getPointerTo()<<"\n";
						dyn_cast<StoreInst>(funcx->user_back())->setOperand(0,funcy);
						//errs()<<*op->getOperand(1)<<"\n";
						IntToPtrInst *op2;
						if((op2 = dyn_cast<IntToPtrInst>(op->getOperand(1))))
						{
							op2->mutateType(funcy->getType()->getPointerTo());
						}
						//errs()<<*op<<"\n";
					}
					else
					{
						funcx->replaceAllUsesWith(funcy);
						continue;
					}
				}//
				Function::arg_iterator arg_i2 = funcy->arg_begin();

				for(Function::arg_iterator arg_i = funcx->arg_begin(), 
					arg_e = funcx->arg_end(); arg_i != arg_e; ++arg_i)
				{
					arg_i->replaceAllUsesWith(arg_i2);
					arg_i2->takeName(arg_i);
					++arg_i2;
					arg_index++;
				}

				// errs()<<"\n*************************************************\n";
				// errs()<<funcy->getName()<<"\n-----\n"<<*(funcy->getFunctionType());
				// errs()<<"\n*************************************************\n";
				StringRef tmp_name = funcx->getName();
				funcx->dropAllReferences();
				funcx->removeFromParent();
				funcy->setName(tmp_name);
				// errs()<<*funcy<<"\n";
			}
			#ifdef debug_spass
				errs()<<"Fourth pass done\n";
			#endif

			// Fifth pass replaces pointers, store and load
			//check the value of ptr_to_st_cook and ptr_to_st_hash
			//errs() << "size of global variable map :  " << glob_var.size() << "\n" ;
			Value *invalidStr =  NULL, *chckStr=NULL;
			for (auto &F : M)
			{
				DataLayout *D = new DataLayout(&M);
				LLVMContext &Ctx = F.getContext();
				/*std::vector<Type*> printPtrParamTypes = {Type::getInt128Ty(Ctx)};
				Type *printPtrRetType = Type::getVoidTy(Ctx);//Type::getInt128Ty(Ctx);
				FunctionType *printPtrFuncType = FunctionType::get(printPtrRetType, printPtrParamTypes, false);
				Value *printPtrFunc = F.getParent()->getOrInsertFunction("printptr", printPtrFuncType);*/

				std::vector<Type*> craftParamTypes = {Type::getInt32Ty(Ctx),Type::getInt32Ty(Ctx),Type::getInt32Ty(Ctx),Type::getInt32Ty(Ctx)};
				Type *craftRetType = Type::getInt128Ty(Ctx);
				FunctionType *craftFuncType = FunctionType::get(craftRetType, craftParamTypes, false);
				FunctionCallee craftFunc = F.getParent()->getOrInsertFunction("craft", craftFuncType);

				if(F.isDeclaration())
					continue;

				std::vector<Instruction *> getData = mapInst.find(F.getName().str())->second;
				if(getData.empty()){
					errs() << "Something is wrong with this function \n"  ;
					continue;
				}
				Instruction *insertPoint = getData[2]->getNextNode();//getData[0];
				ptr_to_st_cook = dyn_cast<PtrToIntInst>(getData[1]);
				ptr_to_st_hash = dyn_cast<TruncInst>(getData[2]);

				int nop = -1;bool f = true;Value *argc ;//BinaryOperator *res;
				for(Function::arg_iterator j = F.arg_begin(), end = F.arg_end(); j != end; ++j)
				{
					nop++;
					if(j->getType()->isPointerTy() && F.getName() != "llvm.RISCV.hash")
					{
						if(dyn_cast<PointerType>(j->getType())->getElementType()->isFunctionTy())
							continue;
						j->mutateType(Type::getInt128Ty(Ctx));
						//errs()<<*j<<"\n";
					}
					if(F.getName() == "main" && f){
						//errs() << *j << "\n" ;
						argc = j;
						f = false;
					}
					if(j->getType() == Type::getInt128Ty(Ctx) && F.getName() == "main"){
						//craft a fatpointer for that variable.
						std::vector<Value *> args;
						std::vector<Type *> originalParamTypes = function_parameters.find(F.getName().str())->second;
						//errs() << *argc << " " << *originalParamTypes.at(nop) << "\n" ;
						TruncInst *trunc = new TruncInst(j, Type::getInt32Ty(Ctx),"trunc_ptr_", insertPoint);
						args.push_back(trunc);
						args.push_back(ptr_to_st_cook);
						BinaryOperator *bound;
						if(F.getName() == "main"){
							Value *constant =  llvm::ConstantInt::get(Type::getInt32Ty(Ctx),(D->getTypeAllocSize(originalParamTypes.at(nop))));
							Value * size = BinaryOperator::Create( Instruction::Mul,argc,constant, "size", insertPoint);
							bound = BinaryOperator::Create( Instruction::Add,trunc , size , "absolute_bnd", insertPoint);
						}
						args.push_back(bound);
						args.push_back(ptr_to_st_hash);
						ArrayRef<Value *> args_ref(args);
						IRBuilder<> Builder(insertPoint);
						Builder.SetInsertPoint(insertPoint);
						Value *fpr = Builder.CreateCall(craftFunc, args_ref,j->getName()+"fpr");
						// Replace all uses of pointer with fatpointer
						j->replaceAllUsesWith(fpr);
						// except in the ptrtoint instruction that uses the pointer to make a fatpointer
						trunc->setOperand(0,j);
					}
				}//*/

				//add those initializers of global variables here
				if(!glob_var.empty() && F.getName() == "main"){
					while (!glob_var.empty()){
						//errs() << *glob_var.begin()->first << " => " << *glob_var.begin()->second << '\n';
						Value *val;
						GlobalVariable *glob_ptr = dyn_cast<GlobalVariable>(glob_var.begin()->first);
						PtrToIntInst *trunc;
						std::vector<Value *> args;
						if(dyn_cast<GEPOperator>(glob_var.begin()->second)){
							val = glob_var.begin()->second ;
							trunc = new PtrToIntInst(val, Type::getInt32Ty(Ctx),"pti1_",insertPoint);
						}else{
							val = dyn_cast<Value>(glob_var.begin()->second);
							trunc = new PtrToIntInst(val, Type::getInt32Ty(Ctx),"pti1_",insertPoint);
						}

						if(!(val->getType() == Type::getInt128Ty(Ctx))){
							//create a fat pointer out of it and then store it in gloval_var.begin()->first.
							args.push_back(trunc);//ptr
							PtrToIntInst *ptr32 = new PtrToIntInst(rodata_cookie, Type::getInt32Ty(Ctx),"ptr32_1_",insertPoint);
							args.push_back(ptr32);//base

							Value *size;
							if(dyn_cast<GEPOperator>(val)){

								GEPOperator *gep = dyn_cast<GEPOperator>(val);
								size = resolveGEPOperator(gep,D,Ctx);
							}else{
								size =  llvm::ConstantInt::get(Type::getInt32Ty(Ctx),(D->getTypeAllocSize(val->getType()))); // need to check
							}

							BinaryOperator *bound = BinaryOperator::Create( Instruction::Add, trunc , size , "absolute_bnd", insertPoint);
							args.push_back(bound);
							args.push_back(ConstantInt::get(Type::getInt32Ty(Ctx),ro_hash));//hash
							ArrayRef<Value *> args_ref(args);

							IRBuilder<> Builder(insertPoint);
							Builder.SetInsertPoint(insertPoint);
							Value *fpr = Builder.CreateCall(craftFunc, args_ref,val->getName()+"_fprz");
							new StoreInst (fpr, glob_ptr, insertPoint);
						}else{
							new StoreInst (val, glob_ptr, insertPoint);
						}
						glob_var.erase(glob_var.begin());
					}
				}

				Module *m = F.getParent();
				Function *val = Intrinsic::getDeclaration(m, Intrinsic::riscv_validate);	// get hash intrinsic declaration

				for (auto &B : F)
				{
					for(BasicBlock::iterator i = B.begin(), e = B.end(); i != e; ++i)
					{
						Instruction *I = dyn_cast<Instruction>(i);

						#ifdef debug_sms_pass_5
							errs()<<*I<<"\n";
						#endif

						if (auto *op = dyn_cast<AllocaInst>(I))
						{	
							// errs()<<"AllocaInst : "<<*I<<"\n";
							if(rep_structs.find(dyn_cast<StructType>(op->getAllocatedType())) != rep_structs.end())
							{
								op->mutateType(rep_structs.at(dyn_cast<StructType>(op->getAllocatedType()))->getPointerTo());
								op->setAllocatedType(rep_structs.at(dyn_cast<StructType>(op->getAllocatedType())));
								//errs()<<*op->getAllocatedType()<<"\n";
							}
							modified=true;
							if(op->getAllocatedType()->isFunctionTy())
							{
								//errs()<<"Ignoring function pointer "<<*op<<"\n";
								continue;
							}
							//errs()<<"\n-----------\nAlloca:\t"<<*op<<"\n-----------\n";
						 	else if(op->getAllocatedType()->isPointerTy())
							{
								// errs()<<"\n-----------\nptrAlloca:\t"<<*op<<"\n-----------\n";
								bool isFnArr = false;
								isFnArr = dyn_cast<PointerType>(op->getAllocatedType())->getElementType()->isFunctionTy();

								if(isFnArr){

									FunctionType *func_type = dyn_cast<FunctionType>(dyn_cast<PointerType>(op->getAllocatedType())->getElementType());
									std::vector<Type*> fParamTypes;

									//errs() << "function type : " << *func_type << "\n";
									Type *func_ret_type = func_type->getReturnType();
									Type *fRetType = (func_type->getReturnType()->isPointerTy() && !(dyn_cast<PointerType>(func_ret_type)->getElementType()->isFunctionTy()) ? Type::getInt128Ty(Ctx) : func_ret_type);
									for(FunctionType::param_iterator k = func_type->param_begin(), endp = func_type->param_end(); k != endp; ++k){
										//errs() << **k << "\n";
										bool argIsFnArr = 0;
										if(dyn_cast<PointerType>(*k))
										{
											argIsFnArr = dyn_cast<PointerType>(*k)->getElementType()->isFunctionTy();
										}
										if((*k)->isPointerTy() && !argIsFnArr)
										{
											//fnHasPtr = true;
											fParamTypes.push_back(Type::getInt128Ty(Ctx));
										}
										else
											fParamTypes.push_back(*k);
									}
//									FunctionType *fType =       FunctionType::get(fRetType, fParamTypes, func.getFunctionType()->isVarArg());
									FunctionType *newFuncType = FunctionType::get(fRetType,fParamTypes,func_type->isVarArg());
									//errs() << "new function type : " << *newFuncType->getPointerTo() << "\n" ;
									Type *newType = newFuncType->getPointerTo() ;
									op->setAllocatedType(newType);
									op->mutateType(newType);
									continue;
								}
								op->setAllocatedType(Type::getInt128Ty(Ctx));
								op->mutateType(Type::getIntNPtrTy(Ctx,128));
								/*for (auto &U : op->uses())
								*{
									if(!flag)
									{
										flag = true;
										continue;
									}
									User *user = U.getUser();
									users.push(user);
									pos.push(U.getOperandNo());
								}*/
							}
							else if(op->getAllocatedType()->isArrayTy())
							{
								
								ArrayType *t = dyn_cast<ArrayType>(op->getAllocatedType());
								ArrayType *rec = t;
								ArrayType *rec_old = t;
								int depth=1;
								std::stack <int> sizes;
								sizes.push(t->getArrayNumElements());
								while((rec = dyn_cast<ArrayType>(rec->getElementType())))
								{
									//errs()<<depth<<": "<<*rec<<"\n";
									sizes.push(rec->getArrayNumElements());
									rec_old = rec;
									depth++;
								}

								Type *baseTy = rec_old->getElementType();

								Type *gelType = Type::getInt128Ty(Ctx);
								while(depth)
								{
									int sz = sizes.top();
									sizes.pop();
									gelType = ArrayType::get(gelType,sz);
									depth--;
								}

								bool isFnArr = 0;
								if(dyn_cast<PointerType>(baseTy))
								{
									// errs()<<"Found array: "<<*op<<", baseTy = "<<dyn_cast<PointerType>(baseTy)->getElementType()->isFunctionTy()<<"\n";
									isFnArr = dyn_cast<PointerType>(baseTy)->getElementType()->isFunctionTy();
								}
								if(baseTy->isPointerTy() && !(isFnArr))	//Only do if array is ptr array, and not a fn ptr array
								{
									errs()<<"\n*********\nALLOCATED TYPE = "<<*op->getAllocatedType()->getArrayElementType()<<"\n\n";
									errs()<<*(ArrayType::get(Type::getInt128Ty(Ctx),op->getAllocatedType()->getArrayNumElements()))<<"\n";
									op->setAllocatedType(gelType);
									op->mutateType(gelType->getPointerTo());

								}
								errs()<<*op<<"\n";
							}
							if (op->getName() == "stack_cookie")
							{
								//ptr_to_st_cook = dyn_cast<PtrToIntInst>(op->getNextNode());
								//ptr_to_st_hash = dyn_cast<TruncInst>(op->getNextNode()->getNextNode()->getNextNode());
								continue;
							}

							//do not create a fat pointer if its a normal integer or float or double . 
							if(!op->getAllocatedType()->isIntegerTy(128) && (op->getAllocatedType()->isFloatTy() || op->getAllocatedType()->isDoubleTy() || op->getAllocatedType()->isIntegerTy())){
								// errs()<<"Not cretaing a fat pointer as it is a normal interger/float/double\n";
								continue;
							}

							//PtrToIntInst *trunc = new PtrToIntInst(op, Type::getInt32Ty(Ctx),"pti",op->getNextNode());
							PtrToIntInst *trunc = new PtrToIntInst(op, Type::getInt32Ty(Ctx),"pti",insertPoint);

							std::vector<Value *> args;
							args.push_back(trunc);
							args.push_back(ptr_to_st_cook);
							BinaryOperator *bound;
							if(dyn_cast<ConstantInt>(op->getArraySize())){
								/*args.push_back(
									llvm::ConstantInt::get(
										Type::getInt32Ty(Ctx),
										(D->getTypeAllocSize(op->getAllocatedType()))
									)
								);*/
								Value *size =  llvm::ConstantInt::get(Type::getInt32Ty(Ctx),(D->getTypeAllocSize(op->getAllocatedType())));
								bound = BinaryOperator::Create( Instruction::Add, trunc , size , "absolute_bnd", insertPoint); 
							}
							else
							{
								BinaryOperator *total_off =  BinaryOperator::Create(Instruction::Mul, op->getArraySize(), llvm::ConstantInt::get(Type::getInt64Ty(Ctx),(D->getTypeAllocSize(op->getAllocatedType()))) , "off", insertPoint);
								TruncInst *total_off_trunc = new TruncInst(total_off, Type::getInt32Ty(Ctx),"offt", insertPoint);
								bound = BinaryOperator::Create( Instruction::Add, trunc , total_off_trunc , "absolute_bnd", insertPoint); 
								//args.push_back(total_off_trunc);
							}
							args.push_back(bound);
							args.push_back(ptr_to_st_hash);
							ArrayRef<Value *> args_ref(args);

							IRBuilder<> Builder(insertPoint);
							//Builder.SetInsertPoint(trunc->getNextNode());
							Builder.SetInsertPoint(insertPoint);
							Value *fpr = Builder.CreateCall(craftFunc, args_ref,op->getName()+"fpr");

							//std::stack <User *> users;
							//std::stack <int> pos;

							// Replace all uses of pointer with fatpointer
							op->replaceAllUsesWith(fpr);
							// except in the ptrtoint instruction that uses the pointer to make a fatpointer
							trunc->setOperand(0,op);
							// errs()<<"End of AllocaInst transformation : "<<*op<<"\n";
						}

						else if (auto *op = dyn_cast<StoreInst>(I)) {
							//if(op->getParent()->getParent()->getName().contains("compressStream"))
							//	if(op->getPrevNode() != NULL)
							//		if(dyn_cast<CallInst>(op->getPrevNode()))
							//			errs()<<*op<<"\n";
							if(dyn_cast<ConstantPointerNull>(op->getOperand(0)))
							{
								//op->getOperand(0)->mutateType(Type::getInt128Ty(Ctx));
								Value* nullconst = llvm::ConstantInt::get(Type::getInt128Ty(Ctx),0);
								op->setOperand(0, nullconst);
								//errs()<<"FOUND CONSTANT\n"<<*op->getOperand(0)<<"\n"<<op->getOperand(0)->getNumUses()<<"\n";
							}
							//This happens when trying to store fatpointers to pinters inside special structs
							//errs()<<"*********\n"<<*op<<"\n"<<*op->getOperand(1)<<"\n"<<*op->getOperand(1)->getType()<<"\nxxxxxxxx\n";

							if(op->getOperand(1)->getType() != Type::getInt128Ty(Ctx))
							{
								//errs()<<*op->getOperand(0)<<"\n"<<*op->getOperand(0)->getType()<<"\n";
								// if storing non-i128 object to a regular pointer, do nothing
								//if storing non-i128 object to a i128* then create non-128 to i128
								if(op->getOperand(0)->getType() != Type::getInt128Ty(Ctx))
								{
									//means storing a non-i128 object to i128*
									if(dyn_cast<PointerType>(op->getOperand(1)->getType())->getElementType() == Type::getInt128Ty(Ctx)){
										// do something here.
										//craft fpr, store fpr
									      craftFatPointer(op,0,craftFunc,D,Ctx,ptr_to_st_cook,ptr_to_st_hash,rodata_cookie,ro_hash);
									}
									if(dyn_cast<PointerType>(op->getOperand(1)->getType())->getElementType()->isFunctionTy()){
										Type *storeptrtype = op->getOperand(1)->getType()->getPointerTo(); 
										//errs() << "store pointer type : " << *storeptrtype << "\n" ;
										op->getOperand(1)->mutateType(storeptrtype);
									}
									if(op->getOperand(0)->getType() == Type::getInt8Ty(Ctx) &&  dyn_cast<GEPOperator>(op->getOperand(1))){
										if(i == B.begin())
											continue;

										GEPOperator *operand = dyn_cast<GEPOperator>(op->getOperand(1));
										staticLoadStore(operand,I,&F,"Pointer access out of range!!!!!",Ctx);
										break;
									}
									continue;
								}
								//else if storing i128 to i128*, do nothing
								else if(dyn_cast<PointerType>(op->getOperand(1)->getType())->getElementType() == Type::getInt128Ty(Ctx))
									continue;

								//errs()<<"<HERE>\n";
								// get here only if op 0 is i128 and operand1 != i128*
								Type *op1Ty = dyn_cast<PointerType>(op->getOperand(1)->getType())->getElementType();
								//validate, truncate and store operand 0
								modified = true;
								TruncInst *tr_lo1 = new TruncInst(op->getOperand(0), Type::getInt64Ty(Ctx),"fpr_lowx", op);	// alloca stack cookie
								Value* shamt1 = llvm::ConstantInt::get(Type::getInt128Ty(Ctx),64);
								BinaryOperator *shifted1 =  BinaryOperator::Create(Instruction::LShr, op->getOperand(0), shamt1 , "fpr_hi_big", op);
								TruncInst *tr_hi1 = new TruncInst(shifted1, Type::getInt64Ty(Ctx),"fpr_hix", op);	// alloca stack cookie

								std::vector<Value *> args1;

								args1.push_back(tr_hi1);
								args1.push_back(tr_lo1);
								ArrayRef<Value *> args_ref1(args1);

								// Create call to intrinsic
								IRBuilder<> Builder(I);
								Builder.SetInsertPoint(I);
								Builder.CreateCall(val, args_ref1,"");

								Value* mask1 = llvm::ConstantInt::get(Type::getInt64Ty(Ctx),0xffffffff);
								BinaryOperator *ptr32_1 =  BinaryOperator::Create(Instruction::And, tr_lo1, mask1 , "ptr32x", op);
								IntToPtrInst *ptr1 = new IntToPtrInst(ptr32_1,op1Ty,"ptrx",op);
								//if validate is true then store it in operand directly
								//IntToPtrInst *ptr1 = new IntToPtrInst(op->getOperand(0),op1Ty,"ptrx",op);

								//new StoreInst(ptr1,op->getOperand(1),op);
								op->setOperand(0,ptr1);

								//i--;
								//i--;
								//op->dropAllReferences();
								//op->removeFromParent();
								continue;
							}

							if(op->getOperand(0)->getType()->isPointerTy())
							{
								if(!(dyn_cast<PointerType>(op->getOperand(0)->getType())->getElementType()->isFunctionTy()))
								{
									if(op->getOperand(1)->getType() == Type::getInt128Ty(Ctx))
									{
										//craft fpr, store fpr
									    craftFatPointer(op,0,craftFunc,D,Ctx,ptr_to_st_cook,ptr_to_st_hash,rodata_cookie,ro_hash);
									}
								}
							}

							modified = true;
							TruncInst *tr_lo = new TruncInst(op->getOperand(1), Type::getInt64Ty(Ctx),"fpr_low", op);	// alloca stack cookie
							Value* shamt = llvm::ConstantInt::get(Type::getInt128Ty(Ctx),64);
							BinaryOperator *shifted =  BinaryOperator::Create(Instruction::LShr, op->getOperand(1), shamt , "fpr_hi_big", op);
							TruncInst *tr_hi = new TruncInst(shifted, Type::getInt64Ty(Ctx),"fpr_hi", op);	// alloca stack cookie

							// Set up intrinsic arguments
							std::vector<Value *> args;

							args.push_back(tr_hi);
							args.push_back(tr_lo);
							ArrayRef<Value *> args_ref(args);

							// Create call to intrinsic
							IRBuilder<> Builder(I);
							Builder.SetInsertPoint(I);
							Builder.CreateCall(val, args_ref,"");

							Type *storetype = op->getOperand(0)->getType();
							bool isFnArr = 0;
							if(dyn_cast<PointerType>(storetype))
							{
								isFnArr = dyn_cast<PointerType>(storetype)->getElementType()->isFunctionTy();
							}
							if (storetype->isPointerTy() && !isFnArr)
							{
								storetype = Type::getInt128Ty(Ctx);
								op->mutateType(storetype);
							}
							Type *storeptrtype = storetype->getPointerTo();

							Value* mask = llvm::ConstantInt::get(Type::getInt64Ty(Ctx),0xffffffff);
							BinaryOperator *ptr32 =  BinaryOperator::Create(Instruction::And, tr_lo, mask , "ptr32_", op);
							IntToPtrInst *ptr = new IntToPtrInst(ptr32,storeptrtype,"ptrs",op);
							//if validate is true then directly store it in the operand
							//IntToPtrInst *ptr = new IntToPtrInst(op->getOperand(1),storeptrtype,"ptrs",op);

							//new StoreInst(op->getOperand(0),ptr,op);
							op->setOperand(1, ptr);
						}

						else if (auto *op = dyn_cast<LoadInst>(I))
						{
							//errs()<< *op << "\n";
							if(op->getOperand(0)->getType() == Type::getIntNPtrTy(Ctx,128))
							{
								op->mutateType(Type::getInt128Ty(Ctx));
								continue;
							}
							//errs()<<*op<<"\t"<<*op->getOperand(0)<<"\n";
							if(op->getOperand(0)->getType() != Type::getInt128Ty(Ctx)){

								//errs() << "load inst : " << *op->getOperand(0)->getType() << "\n" ;
								Type *base_type = op->getOperand(0)->getType() ;
								int depth = 0;
								while(dyn_cast<PointerType>(base_type)){
									base_type = base_type->getPointerElementType();
									depth++;
								}
								//errs() << "final base type : " << *base_type << "\n-------------------------\n" ;
								depth--;
								if(base_type->isFunctionTy()){
									while(depth){
										base_type  = base_type->getPointerTo();
										depth--;
									}
									op->mutateType(base_type);
								}

								//if static then it will get loaded directly
								/*if(dyn_cast<GEPOperator>(op->getOperand(0))){
									if(i == B.begin())
										continue;
									GEPOperator *operand = dyn_cast<GEPOperator>(op->getOperand(0));
									staticLoadStore(operand,I,&F,"Pointer access out of range.....",Ctx);
									break;
								}*/
								continue;
							}
							Type *loadtype = op->getType();
							bool isFnArr = 0;
							if(dyn_cast<PointerType>(loadtype))
							{
								isFnArr = dyn_cast<PointerType>(loadtype)->getElementType()->isFunctionTy();
								//errs()<<"LOADTYPE: "<<*loadtype<<"IsFn: "<<isFnArr<<"\n";
							}


							if (loadtype->isPointerTy())
							{
								if(!isFnArr){
									loadtype = Type::getInt128Ty(Ctx);
									//op->mutateType(loadtype);
								}else{
									//check elements of function type and change any pointer to i128
									FunctionType *func_type = dyn_cast<FunctionType>(dyn_cast<PointerType>(loadtype)->getElementType()) ;
									std::vector<Type*> fParamTypes;

									//errs() << "function type : " << *func_type << "\n";
									Type *func_ret_type = func_type->getReturnType();
									Type *fRetType = (func_type->getReturnType()->isPointerTy() && !(dyn_cast<PointerType>(func_ret_type)->getElementType()->isFunctionTy()) ? Type::getInt128Ty(Ctx) : func_ret_type);
									for(FunctionType::param_iterator k = func_type->param_begin(), endp = func_type->param_end(); k != endp; ++k){
										//errs() << **k << "\n";
										bool argIsFnArr = 0;
										if(dyn_cast<PointerType>(*k))
										{
											argIsFnArr = dyn_cast<PointerType>(*k)->getElementType()->isFunctionTy();
										}
										if((*k)->isPointerTy() && !argIsFnArr)
										{
											//fnHasPtr = true;
											fParamTypes.push_back(Type::getInt128Ty(Ctx));
										}
										else
											fParamTypes.push_back(*k);
									}
//									FunctionType *fType =       FunctionType::get(fRetType, fParamTypes, func.getFunctionType()->isVarArg());
									FunctionType *newFuncType = FunctionType::get(fRetType,fParamTypes,func_type->isVarArg());
									//errs() << "new function type : " << *newFuncType->getPointerTo() << "\n" ;
									Type *newType = newFuncType->getPointerTo() ;
									loadtype = newType;
								}
								//op->mutateType(loadtype);
							}

							Type *loadptrtype = loadtype->getPointerTo();
							modified = true;
							//Value *copy = op->getOperand(0);
							TruncInst *tr_lo = new TruncInst(op->getOperand(0), Type::getInt64Ty(Ctx),"fpr_low", op);	// alloca stack cookie
							Value* shamt = llvm::ConstantInt::get(Type::getInt128Ty(Ctx),64);
							BinaryOperator *shifted =  BinaryOperator::Create(Instruction::LShr, op->getOperand(0), shamt , "fpr_hi_big", op);
							TruncInst *tr_hi = new TruncInst(shifted, Type::getInt64Ty(Ctx),"fpr_hi", op);	// alloca stack cookie

							// Create call to intrinsic
							IRBuilder<> Builder(I);
							Builder.SetInsertPoint(I);

							// Set up intrinsic arguments
							std::vector<Value *> args;

							args.push_back(tr_hi);
							args.push_back(tr_lo);
							ArrayRef<Value *> args_ref(args);
							Builder.CreateCall(val, args_ref,"");

							Value* mask = llvm::ConstantInt::get(Type::getInt64Ty(Ctx),0xffffffff);//7fffffff
							BinaryOperator *ptr32 =  BinaryOperator::Create(Instruction::And, tr_lo, mask , "ptr32_", op);
							IntToPtrInst *ptr = new IntToPtrInst(ptr32,loadptrtype,"ptrl",op);

							op->setOperand(0,ptr);
							op->mutateType(loadtype);

							//Tag the loaded value as fpld if a fatpointer was loaded
							if(loadtype == Type::getInt128Ty(Ctx))//op->getType()
							{
								//errs()<<"FPR:\n"<<*op<<"\n";
								op->setName("fpld");
							}
						}

						else if (auto *op = dyn_cast<GetElementPtrInst>(I))
						{
							if(op->getOperand(0)->getType()->isPointerTy())
							{
								PointerType *pt1 = dyn_cast<PointerType>(op->getOperand(0)->getType());
								//StructType *st1 = dyn_cast<StructType>(op->getOperand(0)->getType()->getElementType());
								//errs()<<"GETELEMENTPTR name: "<<*pt1->getElementType()<<"\n";
								if(pt1->getElementType()->isStructTy())
								{
									StructType *st1 = dyn_cast<StructType>(pt1->getElementType());
									if(st1->getName().contains("_reent") || st1->getName().contains("spec_fd_t"))
									{
										//errs()<<"STRUCT NAME: "<<st1->getName()<<"\n";
										continue;
									}
								}
							}
							//temp fix
							if(op->getOperand(0)->getName().contains("spec_fd"))
							{
								continue;
							}
							if(op->getOperand(0)->getType()->isPointerTy())
							{
								continue;
							}

							modified=true;
							//errs()<<"\n-----------\n"<<*op<<"\n-----------\n";
							resolveGetElementPtr(op,D,Ctx,rep_structs);

							--i;
							op->dropAllReferences();
							op->removeFromParent();
						}
						else if (auto *op = dyn_cast<BitCastInst>(I))
						{
							if(op->getOperand(0)->getType() == Type::getInt128Ty(Ctx))
							{
								op->replaceAllUsesWith(op->getOperand(0));
								--i;
								op->dropAllReferences();
								op->removeFromParent();
							}
						}
						else if (auto *op = dyn_cast<CallInst>(I))
						{
							// errs()<<"CallInst : "<<*op<<"\n";
							//errs()<<"\n";

							if(op->getCalledFunction() ==  NULL){
								FunctionType *ftp =dyn_cast<FunctionType>(dyn_cast<PointerType>(op->getCalledOperand()->getType())->getElementType()); 
								op->mutateFunctionType(ftp);
								//continue;
							}

							for(unsigned int i=0;i<op->getNumOperands()-1;i++)
							{
								if(op->getOperand(i) != NULL)
								{
									if(op->getOperand(i)->getType()->isPointerTy())
									{
										if(dyn_cast<ConstantPointerNull>(op->getOperand(i)))
										{
											op->setOperand(i,llvm::ConstantInt::get(Type::getInt128Ty(Ctx),0));
											continue;
										}
										//check if it is not a declaration and i8* of getelement ptr or not
										if( (op->getCalledFunction()!= NULL ) &&  (!op->getCalledFunction()->isDeclaration()) ){

							 			    craftFatPointer(op,i,craftFunc,D,Ctx,ptr_to_st_cook,ptr_to_st_hash,rodata_cookie,ro_hash);
										}
									}
								}
							}
							if(op->getCalledFunction() != NULL)
							{
								if(!(op->getCalledFunction()->isDeclaration()) || (op->getCalledFunction()->getName().contains("__gm"))) // skip if definition exists in module
								{
									errs()<<"\n=************************************************\n";
									errs()<<*op<<"\n";

									//if the function 1st paramter type is i128 then remove all attribuetes of the parameter
									//this is a problem for returning structs.
									AttributeList AL = op->getAttributes();
									AttributeList A = AL.removeParamAttributes(Ctx,0);
									op->setAttributes(A);
									continue;
								}
								if(op->getCalledFunction()->getName().contains("safefree") || op->getCalledFunction()->getName().contains("saferealloc") )
								{
									//errs()<<"\n=************************************************\n";
									continue;
								}

                                //if called function is fgets, then check size < destination buffer 
                                if(op->getCalledFunction()->getName() == "fgets" ){
									bool isAllow = 1;
									if(i == B.begin())
										continue;

									//function prototype of strlen
									std::vector<Type*> strlenParamTypes = {Type::getInt8PtrTy(Ctx)};
									Type *strlenRetType = Type::getInt64Ty(Ctx);
									FunctionType *strlenFuncType = FunctionType::get(strlenRetType, strlenParamTypes, false);
									FunctionCallee strlenFunc = F.getParent()->getOrInsertFunction("strlen", strlenFuncType);
									Value *dest = op->getOperand(0);
                                                                        Value *size = op->getOperand(1);
									Value *file = op->getOperand(2);
									IntToPtrInst *destPtr,*filePtr;
									Type *ptype = Type::getInt8PtrTy(Ctx);
									TruncInst *tr_lo,*file_lo;
									Value *destLen;

									if(file->getType() != op->getFunctionType()->getParamType(2)){
										file_lo = new TruncInst(file, Type::getInt32Ty(Ctx),"fpr_low", op);
										filePtr = new IntToPtrInst(file_lo,op->getFunctionType()->getParamType(2),"ptrc",op);
										op->setOperand(2,filePtr);
										op->getOperand(2)->mutateType(op->getFunctionType()->getParamType(2));
									}
									IRBuilder<> Builder(I);
									Builder.SetInsertPoint(I);

									if(dest->getType() == Type::getInt128Ty(Ctx)){
										tr_lo = new TruncInst(dest, Type::getInt32Ty(Ctx),"fpr_low", op);
										destPtr = new IntToPtrInst(tr_lo,ptype,"ptrc",op);
										op->setOperand(0,destPtr);
										op->getOperand(0)->mutateType(ptype);

										//errs() << *dest << "\n" ;
										Instruction *ins;
										//dyn_cast<Instruction>(I->getOperand(0)->stripPointerCasts())
										//stripPointerCasts() : required because all getOperand(0) is not instructions.
										// it might be a global variable as well.
										while(dyn_cast<Instruction>(dest)){
											ins = dyn_cast<Instruction>(dest);
											if(dyn_cast<AllocaInst>(ins)){
												break;
											}
											dest = ins->getOperand(0)->stripPointerCasts();
										}

										if(dyn_cast<Instruction>(dest) == NULL ){ // global varibale found
											if(dest->getType()->isArrayTy()){
												std::vector<Value *> args;
												args.push_back(destPtr);
												ArrayRef<Value *> args_ref(args);
												destLen = Builder.CreateCall(strlenFunc, args_ref,"dest_len");
											}else{
												isAllow = 0;
											}
										}
										else if(!(dyn_cast<AllocaInst>(ins)->getAllocatedType() == Type::getInt128Ty(Ctx))){
											uint64_t len = dyn_cast<AllocaInst>(ins)->getAllocatedType()->getArrayNumElements();
											destLen = llvm::ConstantInt::get(Type::getInt64Ty(Ctx),len);

										}else{
											std::vector<Value *> args;
											args.push_back(destPtr);
											ArrayRef<Value *> args_ref(args);
											destLen = Builder.CreateCall(strlenFunc, args_ref,"dest_len");
										}
									}
									if(isAllow){

									Value *res = Builder.CreateICmpULT (destLen, size,"check_len");
									Instruction *ter = SplitBlockAndInsertIfThen(res, I,true);

									Value *zero = llvm::ConstantInt::get(Type::getInt32Ty(Ctx),0);

									//creating function call prototype to exit(0)
									std::vector<Type*> exitParamTypes = {Type::getInt32Ty(Ctx)};
									Type *exitRetType = Type::getVoidTy(Ctx);
									FunctionType *exitFuncType = FunctionType::get(exitRetType, exitParamTypes, false);
									FunctionCallee exitF = F.getParent()->getOrInsertFunction("exit", exitFuncType);

									//creating a function call prototype to printf to print "Invalid Size"
									std::vector<Type*> printParamTypes = {Type::getInt8PtrTy(Ctx)};
									Type *printRetType = Type::getInt32Ty(Ctx);
									FunctionType *printFuncType = FunctionType::get(printRetType, printParamTypes, true);
									FunctionCallee printF = F.getParent()->getOrInsertFunction("printf", printFuncType);
									if(invalidStr == NULL)
										invalidStr = Builder.CreateGlobalStringPtr("Size greater than destination length\n");
									Builder.SetInsertPoint(ter);
									Builder.CreateCall(printF,invalidStr);
									Builder.CreateCall(exitF,zero);
									break;
									}
                                                                }
                                                                //if called function is strcpy then check check length of both destination and source
								//if strlen(destination) <  strlen(source) then exit 
								if(op->getCalledFunction()->getName() == "strcpy") {
									//errs() << "strcpy() " << *op << op->getParent()->getParent()->getName() << "\n" ;
									bool isAllow = 1;
									if(i == B.begin())
										continue;
									//function prototype of strlen
									std::vector<Type*> strlenParamTypes = {Type::getInt8PtrTy(Ctx)};
									Type *strlenRetType = Type::getInt64Ty(Ctx);
									FunctionType *strlenFuncType = FunctionType::get(strlenRetType, strlenParamTypes, false);
									FunctionCallee strlenFunc = F.getParent()->getOrInsertFunction("strlen", strlenFuncType);

									Value *dest = op->getOperand(0);
									Value *source = op->getOperand(1);
									IntToPtrInst *destPtr, *sourcePtr;
									Type *ptype = Type::getInt8PtrTy(Ctx);
									TruncInst *tr_lo;
									Value *destLen,*sourceLen;

									IRBuilder<> Builder(I);
									Builder.SetInsertPoint(I);

									if(dest->getType() == Type::getInt128Ty(Ctx)){
										tr_lo = new TruncInst(dest, Type::getInt32Ty(Ctx),"fpr_low", op);
										destPtr = new IntToPtrInst(tr_lo,ptype,"ptrc",op);
										op->setOperand(0,destPtr);
										op->getOperand(0)->mutateType(ptype);

										//errs() << *dest << "\n" ;
										Instruction *ins;
										//dyn_cast<Instruction>(I->getOperand(0)->stripPointerCasts())
										//stripPointerCasts() : required because all getOperand(0) is not instructions.
										// it might be a global variable as well.
										while(dyn_cast<Instruction>(dest)){
											ins = dyn_cast<Instruction>(dest);
											if(dyn_cast<AllocaInst>(ins)){
												break;
											}
											dest = ins->getOperand(0)->stripPointerCasts();
										}

										if(dyn_cast<Instruction>(dest) == NULL ){ // global varibale found
											if(dest->getType()->isArrayTy()){
												std::vector<Value *> args;
												args.push_back(destPtr);
												ArrayRef<Value *> args_ref(args);
												destLen = Builder.CreateCall(strlenFunc, args_ref,"dest_len");
											}else{
												isAllow = 0;
											}
										}
										else if(!(dyn_cast<AllocaInst>(ins)->getAllocatedType() == Type::getInt128Ty(Ctx))){
											uint64_t len = dyn_cast<AllocaInst>(ins)->getAllocatedType()->getArrayNumElements();
											destLen = llvm::ConstantInt::get(Type::getInt64Ty(Ctx),len);

										}else{
											std::vector<Value *> args;
											args.push_back(destPtr);
											ArrayRef<Value *> args_ref(args);
											destLen = Builder.CreateCall(strlenFunc, args_ref,"dest_len");
										}
									}else{

										if(dyn_cast<GEPOperator>(dest)){
											GEPOperator *gep = dyn_cast<GEPOperator>(dest);
											uint64_t len =  gep->getSourceElementType()->getArrayNumElements();
											destLen = llvm::ConstantInt::get(Type::getInt64Ty(Ctx),len);
										}else{

											std::vector<Value *> args;
											args.push_back(dest);
											ArrayRef<Value *> args_ref(args);
											destLen = Builder.CreateCall(strlenFunc, args_ref,"dest_len");
										}
									}
									if(source->getType() == Type::getInt128Ty(Ctx)){
										tr_lo = new TruncInst(source, Type::getInt32Ty(Ctx),"fpr_low", op);
										sourcePtr = new IntToPtrInst(tr_lo,ptype,"ptrc",op);
										op->setOperand(1,sourcePtr);
										op->getOperand(1)->mutateType(ptype);

										std::vector<Value *> args;
										args.push_back(sourcePtr);
										ArrayRef<Value *> args_ref(args);
										sourceLen = Builder.CreateCall(strlenFunc, args_ref,"source_len");
									}else{
										std::vector<Value *> args;
										args.push_back(source);
										ArrayRef<Value *> args_ref(args);
										sourceLen = Builder.CreateCall(strlenFunc, args_ref,"source_len");
									}

									if(isAllow){


									//this is changed from ULT to ULE because string of length 10 can contain 
									// 9 characters and ends with \0 so one character reserved for EOC
									Value *res = Builder.CreateICmpULE (destLen, sourceLen,"check_len");
									Instruction *ter = SplitBlockAndInsertIfThen(res, I,true);

									Value *zero = llvm::ConstantInt::get(Type::getInt32Ty(Ctx),0);

									//creating function call prototype to exit(0)
									std::vector<Type*> exitParamTypes = {Type::getInt32Ty(Ctx)};
									Type *exitRetType = Type::getVoidTy(Ctx);
									FunctionType *exitFuncType = FunctionType::get(exitRetType, exitParamTypes, false);
									FunctionCallee exitF = F.getParent()->getOrInsertFunction("exit", exitFuncType);

									//creating a function call prototype to printf to print "Invalid Size"
									std::vector<Type*> printParamTypes = {Type::getInt8PtrTy(Ctx)};
									Type *printRetType = Type::getInt32Ty(Ctx);
									FunctionType *printFuncType = FunctionType::get(printRetType, printParamTypes, true);
									FunctionCallee printF = F.getParent()->getOrInsertFunction("printf", printFuncType);
									if(invalidStr == NULL)
										invalidStr = Builder.CreateGlobalStringPtr("Source Length greater than destination length\n");
									Builder.SetInsertPoint(ter);
									Builder.CreateCall(printF,invalidStr);
									Builder.CreateCall(exitF,zero);
									break;
									}
								}
								if(op->getCalledFunction()->isIntrinsic() && op->getCalledFunction()->getName().contains("memcpy")){
									Value *dest = op->getOperand(0);
									Value *src = op->getOperand(1);
									if(!(dest->getType() == Type::getInt8PtrTy(Ctx))){
									TruncInst *dest_lo = new TruncInst(dest, Type::getInt32Ty(Ctx),"fpr_low", op);
									IntToPtrInst *destPtr = new IntToPtrInst(dest_lo,op->getFunctionType()->getParamType(0),"ptrc",op);
									op->setOperand(0,destPtr);
									op->getOperand(0)->mutateType(op->getFunctionType()->getParamType(0));
									}

									if(!(src->getType() == Type::getInt8PtrTy(Ctx))){
									TruncInst *src_lo = new TruncInst(src, Type::getInt32Ty(Ctx),"fpr_low", op);
									IntToPtrInst *srcPtr = new IntToPtrInst(src_lo,op->getFunctionType()->getParamType(1),"ptrc",op);
									op->setOperand(1,srcPtr);
									op->getOperand(1)->mutateType(op->getFunctionType()->getParamType(1));
									}

									if(i == B.begin())
										continue;

									Value *zero64 = llvm::ConstantInt::get(Type::getInt64Ty(Ctx),0);
									Value *zero = llvm::ConstantInt::get(Type::getInt32Ty(Ctx),0);
									//creating function call prototype to exit(0)
									std::vector<Type*> exitParamTypes = {Type::getInt32Ty(Ctx)};
									Type *exitRetType = Type::getVoidTy(Ctx);
									FunctionType *exitFuncType = FunctionType::get(exitRetType, exitParamTypes, false);
									FunctionCallee exitF = F.getParent()->getOrInsertFunction("exit", exitFuncType);
									IRBuilder<> Builder(I);
									Builder.SetInsertPoint(I);
									Value *res = Builder.CreateICmpSLT(op->getOperand(2), zero64, "");
									Instruction *ter = SplitBlockAndInsertIfThen(res, I,true);

									//creating a function call prototype to printf to print "Invalid Size"
									std::vector<Type*> printParamTypes = {Type::getInt8PtrTy(Ctx)};
									Type *printRetType = Type::getInt32Ty(Ctx);
									FunctionType *printFuncType = FunctionType::get(printRetType, printParamTypes, true);
									FunctionCallee printF = F.getParent()->getOrInsertFunction("printf", printFuncType);
									if(chckStr == NULL)
										chckStr = Builder.CreateGlobalStringPtr("Size less than 0\n");
									Builder.SetInsertPoint(ter);
									Builder.CreateCall(printF,chckStr);
									Builder.CreateCall(exitF,zero);
									break;
								}
							}
							// errs()<<*op<<"\n";
							for(unsigned int i=0;i<op->getNumOperands()-1;i++)
							{
								//this means call parameters match function signature. else break it into required format.
								if(op->getOperand(i)->getType() == op->getFunctionType()->getParamType(i))
									continue;

								//if you are using a global pointer in printf scanf or other system calls then collapse that pointer to i8* or to the required pointer type before calling.
								if(op->getCalledFunction()!=NULL ) { //&& (!op->getCalledFunction()->isIntrinsic()) //&& op->getCalledFunction()->isDeclaration() -- not required as it will readh here only if its a declaration
										if(op->getOperand(i)->getType() == Type::getInt128Ty(Ctx)){
											errs() <<  "before : " << *op << "\n" ;
											//truncte to i8* and then pass to the function

											//validate the pointer 
											TruncInst *tr_lo = new TruncInst(op->getOperand(i), Type::getInt32Ty(Ctx),"fpr_low", op);
											/*Value* shamt = llvm::ConstantInt::get(Type::getInt128Ty(Ctx),64);
											BinaryOperator *shifted =  BinaryOperator::Create(Instruction::LShr, op->getOperand(i), shamt , "fpr_hi_big", op);
											TruncInst *tr_hi = new TruncInst(shifted, Type::getInt64Ty(Ctx),"fpr_hi", op);

											// Set up intrinsic arguments
											std::vector<Value *> args;

											args.push_back(tr_hi);
											args.push_back(tr_lo);
											ArrayRef<Value *> args_ref(args);

											// Create call to intrinsic
											IRBuilder<> Builder(I);
											Builder.SetInsertPoint(I);
											Builder.CreateCall(val, args_ref,"");
*/
											//validating the pointer done
											//type cast to i8* 
											Type *ptype = Type::getInt8PtrTy(Ctx);
											if(op->getCalledFunction() != NULL)
											{	errs()<<*(op->getCalledFunction()->getFunctionType())<<"\n";
												if(!op->getCalledFunction()->isVarArg())
												{
													ptype = op->getCalledFunction()->getFunctionType()->params()[i];
												}
												else if(i < op->getCalledFunction()->getFunctionType()->params().size())
												{
													ptype = op->getCalledFunction()->getFunctionType()->params()[i];
													errs()<<*(op->getCalledFunction()->getFunctionType())<<"\n";
												}
											}

											//Value* mask = llvm::ConstantInt::get(Type::getInt64Ty(Ctx),0xffffffff);
											//BinaryOperator *ptr32 =  BinaryOperator::Create(Instruction::And, tr_lo, mask , "ptr32_", op);

											//IntToPtrInst *ptr = new IntToPtrInst(ptr32,ptype,"ptrc",op);

											IntToPtrInst *ptr = new IntToPtrInst(tr_lo,ptype,"ptrc",op);
											op->setOperand(i,ptr);
											op->getOperand(i)->mutateType(ptype);
											continue;
											errs() <<  "after : " << *op << "\n" ;
										}
								}
								//if(op->getCalledFunction()->getName() == "fprintf")
								//errs()<<"op "<<i<<".\t"<<*op->getOperand(i)<<"\n";
								if(!op->getOperand(i)->getName().contains("arrayidx") && !op->getOperand(i)->getName().contains("fpr") && !op->getOperand(i)->getName().contains("fpld"))
								{
									continue;
								}

								TruncInst *tr_lo = new TruncInst(op->getOperand(i), Type::getInt64Ty(Ctx),"fpr_low", op);	// alloca stack cookie;
								Value* shamt = llvm::ConstantInt::get(Type::getInt128Ty(Ctx),64);
								BinaryOperator *shifted =  BinaryOperator::Create(Instruction::LShr, op->getOperand(i), shamt , "fpr_hi_big", op);
								TruncInst *tr_hi = new TruncInst(shifted, Type::getInt64Ty(Ctx),"fpr_hi", op);	// alloca stack cookie

								// Set up intrinsic arguments
								std::vector<Value *> args;

								args.push_back(tr_hi);
								args.push_back(tr_lo);
								ArrayRef<Value *> args_ref(args);

								// Create call to intrinsic
								IRBuilder<> Builder(I);
								Builder.SetInsertPoint(I);
								Builder.CreateCall(val, args_ref,"");

								errs()<<*op<<"\n";
								Type *ptype = Type::getInt8PtrTy(Ctx);;
								if(op->getCalledFunction() != NULL)
								{
									if(!op->getCalledFunction()->isVarArg())
									{
										ptype = op->getCalledFunction()->getFunctionType()->params()[i];
									}
									else if(i < op->getCalledFunction()->getFunctionType()->params().size())
									{
										ptype = op->getCalledFunction()->getFunctionType()->params()[i];
									}
								}else{

									if(!dyn_cast<FunctionType>(dyn_cast<PointerType>(op->getCalledOperand()->getType())->getElementType())->isVarArg()){
										//errs() << "Here ..... " ;
										ptype = dyn_cast<FunctionType>(dyn_cast<PointerType>(op->getCalledOperand()->getType())->getElementType())->params()[i] ;
									}
								}

								//errs()<<i<<".\t"<<ptype<<"\n";

								Value* mask = llvm::ConstantInt::get(Type::getInt64Ty(Ctx),0xffffffff);
								BinaryOperator *ptr32 =  BinaryOperator::Create(Instruction::And, tr_lo, mask , "ptr32_", op);

								IntToPtrInst *ptr = new IntToPtrInst(ptr32,ptype,"ptrc",op);

								op->setOperand(i,ptr);
								op->getOperand(i)->mutateType(ptype);
								// errs()<<*op<<"\n";
								// errs()<<*(op->getOperand(i)->getType())<<"\n";
							}
							if(op->getFunctionType()->getReturnType() == Type::getInt128Ty(Ctx))
							{
								op->mutateType(Type::getInt128Ty(Ctx));
							}
							// errs()<<*op<<"\n";
							// errs()<<"\n=************************************************\n";//*/
						}
						else if (auto *op = dyn_cast<ICmpInst>(I))
						{
							Value *o1 = op->getOperand(0);
							Value *o2 = op->getOperand(1);
							if(o1->getType() != o2->getType())
							{
								//errs()<<"TYPES: "<<*o1<<" "<<*o2<<"\n";
								if(dyn_cast<ConstantPointerNull>(o2))
								{

									//change this value to zero only if operand 0 is not a function pointer
									//else create a null valued function pointer
									if(dyn_cast<PointerType>(o1->getType())){
										if(dyn_cast<PointerType>(o1->getType())->getElementType()->isFunctionTy()){
											Constant *null_val = ConstantPointerNull::getNullValue(op->getOperand(0)->getType());
											op->setOperand(1,null_val);
											continue;
										}
									}
									op->setOperand(1,llvm::ConstantInt::get(Type::getInt128Ty(Ctx),0));
								}
								if(dyn_cast<ConstantPointerNull>(o1))
								{
									//change operand(0) to 0 if operand(1) is of type i128
									if(o2->getType() == Type::getInt128Ty(Ctx))
										op->setOperand(0,llvm::ConstantInt::get(Type::getInt128Ty(Ctx),0));
								}
								//if operand(1) is of type i8* and operand(0) of type i128
								else if(op->getOperand(1)->getType()->isPointerTy()){
									//errs() << "Here.....\n" ;
									//errs() << *op->getOperand(1) << "\n" ;
							 	   craftFatPointer(op,1,craftFunc,D,Ctx,ptr_to_st_cook,ptr_to_st_hash,rodata_cookie,ro_hash);
								}
								//if operand(0) is of type i8* and operand(1) of type i128
								else if(op->getOperand(0)->getType()->isPointerTy()){
									//errs() << "Here.....\n" ;
									//errs() << *op->getOperand(0) << "\n" ;
							 	   craftFatPointer(op,0,craftFunc,D,Ctx,ptr_to_st_cook,ptr_to_st_hash,rodata_cookie,ro_hash);
								}
							}
						}
						else if (auto *op = dyn_cast<PtrToIntInst>(I))
						{	
							// errs()<<"PtrToIntInst : "<<*op<<"\n";
							if(op->getOperand(0)->getType() == Type::getInt128Ty(Ctx))
							{
								Value* mask2 = llvm::ConstantInt::get(Type::getInt128Ty(Ctx),0x000000000000000000000000ffffffff);
								BinaryOperator *fpr_addr =  BinaryOperator::Create(Instruction::And, op->getOperand(0), mask2 , "fpr_addr_", op);
								TruncInst *ti_addr = new TruncInst(fpr_addr, op->getDestTy(),"fpr_ptrtoint_", op);
								op->replaceAllUsesWith(ti_addr);
								--i;
								op->dropAllReferences();
								op->removeFromParent();
							}
						}
						else if(auto *op = dyn_cast<PHINode>(I)){
							Value *op1 = op->getOperand(0);
							Value *op2 = op->getOperand(1);

							#ifdef debug_sms_pass_5
								errs()<<"PHINode : "<<*op<<" : "<<*(op->getType())<<" : "<<*(op1->getType())<<" : "<<*(op2->getType())<<"\n";
							#endif

							if((op1->getType()==op2->getType()) && (op2->getType() == Type::getInt128Ty(Ctx))){
								op->mutateType(Type::getInt128Ty(Ctx));
							}

							if(op1->getType()!=op2->getType()){
								if(op2->getType() == Type::getInt128Ty(Ctx)){
									//change type 0 to i128 and phi node type to i128 also.
									#ifdef debug_sms_pass_5
										errs()<<"Changing type 0\n";
									#endif
									craftFatPointer(op,0,craftFunc,D,Ctx,ptr_to_st_cook,ptr_to_st_hash,rodata_cookie,ro_hash);
								}

							}
							#ifdef debug_sms_pass_5
								errs()<<"PHINode : "<<*op<<" : "<<*(op->getType())<<" : "<<*(op1->getType())<<" : "<<*(op2->getType())<<"\n";
							#endif
						}
						//TODO: this is a temporary fix for functions that return pointers to global variables
						else if (auto *op = dyn_cast<ReturnInst>(I))
						{
							//errs()<<*op<<"\n"<<op->getReturnValue();
							if(op->getReturnValue() == NULL)
								continue;

							if(!op->getReturnValue()->getType()->isPointerTy())
								continue;

							//errs()<<"HERE1\n";
							if(op->getParent()->getParent()->getReturnType()->isPointerTy())
								continue;
							//errs()<<"HERE2\n";
							// return type is not pointer, but trying to return a pointer value
							craftFatPointer(op,0,craftFunc,D,Ctx,ptr_to_st_cook,ptr_to_st_hash,rodata_cookie,ro_hash);
						}
						//errs()<<*I;
						//errs()<<"\n--------\n";
					}

				}
				//errs()<<"\n*************************************************\n";
				//errs()<<F;
				//errs()<<"\n*************************************************\n";
			}
			#ifdef debug_spass
				errs()<<"Fifth pass done\n";
			#endif

			#ifdef debug_spass_dmodule
				errs()<<"\n--------------\n"<<M<<"\n----------------\n";
			#endif
			return modified;
		// }
		}
	};
}

Type* resolveFunctionPointers(FunctionType *func_type, LLVMContext &Ctx){
	bool fnHasPtr = false;
	bool isFnArr = 0;
	std::vector<Type*> fParamTypes;

	Type *func_ret_type = func_type->getReturnType();
	Type *fRetType;

	fnHasPtr = (func_type->getReturnType()->isPointerTy() ? true : false);

	if(dyn_cast<PointerType>(func_type->getReturnType())){
		isFnArr = dyn_cast<PointerType>(func_type->getReturnType())->getElementType()->isFunctionTy();
	}

	if(isFnArr){
		fRetType = resolveFunctionPointers(dyn_cast<FunctionType>(dyn_cast<PointerType>(func_ret_type)->getElementType()), Ctx);
	}
	else{
		fRetType = (func_type->getReturnType()->isPointerTy() && !(dyn_cast<PointerType>(func_ret_type)->getElementType()->isFunctionTy()) ? Type::getInt128Ty(Ctx) : func_ret_type);
	}	

	for(FunctionType::param_iterator k = func_type->param_begin(), endp = func_type->param_end(); k != endp; ++k){
		bool argIsFnArr = 0;
		if(dyn_cast<PointerType>(*k)){
			argIsFnArr = dyn_cast<PointerType>(*k)->getElementType()->isFunctionTy();
		}
		if((*k)->isPointerTy() && !argIsFnArr){
			fParamTypes.push_back(Type::getInt128Ty(Ctx));
		}
		else if(argIsFnArr){
			// Type *org_ty = dyn_cast<Type>(*k);
			FunctionType *org_func_type = dyn_cast<FunctionType>(dyn_cast<PointerType>(*k)->getElementType());
			Type *newSubType = resolveFunctionPointers(org_func_type, Ctx); 
			fParamTypes.push_back(newSubType);
		}
		else{
			fParamTypes.push_back(*k);
		}
	}
	FunctionType *newFuncType = FunctionType::get(fRetType,fParamTypes,func_type->isVarArg());
	//errs() << "new function type : " << *newFuncType->getPointerTo() << "\n" ;
	Type *newType = newFuncType->getPointerTo();
	return newType;
}

bool isLocal(Instruction *ins){

	//check if the variable is local or not 
	bool flag = false;


	while(dyn_cast<Instruction>(ins)){
		#ifdef debug_is_local
			errs() << "Inside isLocal() : "<<*ins<< "\n";
		#endif
		if(dyn_cast<AllocaInst>(ins))
			break;

		ins = dyn_cast<Instruction>(ins->getOperand(0)->stripPointerCasts());
	}

	if(dyn_cast<Instruction>(ins) == NULL ){ // global varibale found
		flag = false;
	}else{					//local variable found
		flag = true;
	}

	return flag;
}

void craftFatPointer(Instruction *ins, unsigned int i, FunctionCallee craftFunc,DataLayout *D,LLVMContext &Ctx,PtrToIntInst *ptr_to_st_cook,TruncInst *ptr_to_st_hash,GlobalVariable *rodata_cookie,unsigned long ro_hash){


	auto *op = dyn_cast<Instruction>(ins);
	auto *insertPoint = op;

	if(dyn_cast<PHINode>(op)){
		// BasicBlock *phiBlock = dyn_cast<PHINode>(op)->getIncomingBlock(0);
		// TerminatorInst *terInst = phiBlock->getTerminator();
		// insertPoint = terInst;
	}

	PtrToIntInst *trunc = new PtrToIntInst(op->getOperand(i), Type::getInt32Ty(Ctx),"pti1_",insertPoint);
	
	#ifdef debug_craft_fat_pointer
		errs() << "Inside carftFatPointer() : "<<*op->getOperand(i) << "\n";
	#endif

	std::vector<Value *> args;
	args.push_back(trunc);//ptr

	//check if the variable is local or not( local = 1 , global = 0 )
	bool isVarLocal = isLocal(dyn_cast<Instruction>( op->getOperand(i)));
	#ifdef debug_craft_fat_pointer
		errs() << "Inside carftFatPointer() isVarLocal: "<<isVarLocal<< "\n";
	#endif
	if(isVarLocal){
		args.push_back(ptr_to_st_cook);
	}else{
		PtrToIntInst *ptr32 = new PtrToIntInst(rodata_cookie, Type::getInt32Ty(Ctx),"ptr32_1_",insertPoint);
		args.push_back(ptr32);//base
	}

	Value *size;
	if(dyn_cast<GEPOperator>(op->getOperand(i))){
		GEPOperator *gep = dyn_cast<GEPOperator>(op->getOperand(i));
		size = resolveGEPOperator(gep,D,Ctx);
		#ifdef debug_craft_fat_pointer
			errs() << "Inside carftFatPointer() size : "<<size<< "\n";
		#endif
	}else{
		if( dyn_cast<PointerType>(op->getOperand(i)->getType())->getElementType() != Type::getInt16Ty(Ctx) )
			size =  llvm::ConstantInt::get(Type::getInt32Ty(Ctx),(D->getTypeAllocSize(dyn_cast<PointerType>(op->getOperand(i)->getType())->getElementType() ))); // need to check
		else
			size =  llvm::ConstantInt::get(Type::getInt32Ty(Ctx),(D->getTypeAllocSize(op->getOperand(i)->getType() ))); // need to check
	}
	BinaryOperator *bound = BinaryOperator::Create( Instruction::Add, trunc , size , "absolute_bnd", insertPoint); 
	args.push_back(bound);
	if(isVarLocal){
		args.push_back(ptr_to_st_hash);
	}else{
		args.push_back(ConstantInt::get(Type::getInt32Ty(Ctx),ro_hash));//hash
	}
	ArrayRef<Value *> args_ref(args);

	IRBuilder<> Builder(insertPoint);
	Builder.SetInsertPoint(insertPoint);
	Value *fpr = Builder.CreateCall(craftFunc, args_ref,op->getName()+"fprz");
	op->setOperand(i,fpr);

	if(dyn_cast<PHINode>(op)){
		op->mutateType(Type::getInt128Ty(Ctx));
	}
}
void staticLoadStore(GEPOperator* operand,Instruction *I,Function *F,std::string str,LLVMContext &Ctx){

	Value *errorStr=NULL;
	//errs() << "inside this function \n" << *F << "\n" ;
	Value *zero = llvm::ConstantInt::get(Type::getInt32Ty(Ctx),0);
	Value *val = llvm::ConstantInt::get(operand->getOperand(1)->getType(),0);
	IRBuilder<> Builder(I);
	Builder.SetInsertPoint(I);
	Value *res = Builder.CreateICmpUGT (operand->getOperand(1), val,"");
	Instruction *ter = SplitBlockAndInsertIfThen(res, I,true);
	//creating function call prototype to exit(0)
	std::vector<Type*> exitParamTypes = {Type::getInt32Ty(Ctx)};
	Type *exitRetType = Type::getVoidTy(Ctx);
	FunctionType *exitFuncType = FunctionType::get(exitRetType, exitParamTypes, false);
	FunctionCallee exitF = F->getParent()->getOrInsertFunction("exit", exitFuncType);

	//creating a function call prototype to printf to print "Invalid Size"
	std::vector<Type*> printParamTypes = {Type::getInt8PtrTy(Ctx)};
	Type *printRetType = Type::getInt32Ty(Ctx);
	FunctionType *printFuncType = FunctionType::get(printRetType, printParamTypes, true);
	FunctionCallee printF = F->getParent()->getOrInsertFunction("printf", printFuncType);
	if(errorStr == NULL)
		errorStr = Builder.CreateGlobalStringPtr(str);
	Builder.SetInsertPoint(ter);
	Builder.CreateCall(printF,errorStr);
	Builder.CreateCall(exitF,zero);

}

Value* resolveGEPOperator(GEPOperator *GI,DataLayout *D,LLVMContext &Context)
{
	int offset = 0;
	Value *Offset;
	int c = 0;
	//errs() << *GI << "\n" ;
	bool isNeg = false;
	//int noOfOperands = GI->getNumOperands();
	if(ConstantInt *CI = dyn_cast<ConstantInt>(GI->getOperand(GI->getNumOperands()-1))){// get the last operand of the getelementptr
		c = CI->getZExtValue ();
		if(c < 0){
			c = c * -1;
			isNeg = true;
		}
	}
	Type *type = GI->getSourceElementType(); //get the type of getelementptr
	if(StructType *t = dyn_cast<StructType>(type))
	{	//check for struct type
		const StructLayout *SL = D->getStructLayout(t);
		offset+=SL->getSizeInBytes();
	}
	else if(ArrayType *t = dyn_cast<ArrayType>(type))
	{
		offset+= D->getTypeAllocSize(t) - c*D->getTypeAllocSize(t->getElementType()); //D->getTypeAllocSize(t)/t->getArrayNumElements();
	}
	else
	{	//basic pointer increment or decrements

		offset+=c*D->getTypeAllocSize(type);
	}

	if(isNeg)
		offset = offset*-1;

	Offset = llvm::ConstantInt::get(Type::getInt32Ty(Context),offset);
	//errs() << offset << "\n";

	return Offset;
}


void resolveGetElementPtr(GetElementPtrInst *GI,DataLayout *D,LLVMContext &Context,std::map <StructType*, StructType*> rep_structs)
{

	int offset = 0;
	Value *Offset,*temp;
	int c = 0;
	bool isconstant = true;
	bool isNeg = false;
	int noOfOperands = GI->getNumOperands();
	if(ConstantInt *CI = dyn_cast<ConstantInt>(GI->getOperand(GI->getNumOperands()-1))){// get the last operand of the getelementptr
		c = CI->getZExtValue ();
		if(c < 0){
			c = c * -1;
			isNeg = true;
		}
	}
	else
	{
		//suppose the last index was not a constant then set 'c' to some special value and get the last operand.
		isconstant = false;
		// Instruction *I = dyn_cast<Instruction>(GI->getOperand(GI->getNumOperands()-1));
		// Offset = I->getOperand(0);
		Offset = GI->getOperand(GI->getNumOperands()-1);
	}
	Type *type = GI->getSourceElementType(); //get the type of getelementptr
	if(StructType *t = dyn_cast<StructType>(type))
	{	//check for struct type

		if(rep_structs.find(t) != rep_structs.end()){
			//errs() << "Here \n" ;
			t = rep_structs.at(t);
		}

		const StructLayout *SL = D->getStructLayout(t);

		if(!isconstant)
		{
			temp= llvm::ConstantInt::get(Type::getInt64Ty(Context), SL->getSizeInBytes());
			IRBuilder<> builder(GI);
			Offset = builder.CreateBinOp(Instruction::Mul,Offset, temp, "tmp");
		}
		else{
			if(!isNeg){
				//now the offset can be elements within structs or struct++. If struct++ then no of operand = 2 else 3
				if(noOfOperands == 2 )
					offset+=c*SL->getSizeInBytes();
				else
					offset+= SL->getElementOffset(c);
			}else
				offset+= c*SL->getSizeInBytes() ;
		}
	}
	else if(ArrayType *t = dyn_cast<ArrayType>(type))
	{
		ArrayType *rec = t;
		ArrayType *rec_old = t;
		//errs()<<0<<": "<<*rec<<"\n";
		int depth=1;
		std::stack <int> sizes;
		sizes.push(t->getArrayNumElements());
		while((rec = dyn_cast<ArrayType>(rec->getElementType())))
		{
			//errs()<<depth<<": "<<*rec<<"\n";
			sizes.push(rec->getArrayNumElements());
			rec_old = rec;
			depth++;
		}

		Type *baseTy = rec_old->getElementType();

		/*Type *gelType = Type::getInt128Ty(Context);
		while(depth)
		{
			int sz = sizes.top();
			sizes.pop();
			gelType = ArrayType::get(gelType,sz);
			depth--;
		}
		errs()<< "Depth : " << depth <<": "<<*gelType<<"\n";*/
		bool isFnArr = 0;
		if(dyn_cast<PointerType>(baseTy))
		{
			isFnArr = dyn_cast<PointerType>(baseTy)->getElementType()->isFunctionTy();
		}

		if(!isconstant)
		{
			//errs()<<"\n------\n"<<*GI<<"\n";
			if(noOfOperands == 2){
				temp = llvm::ConstantInt::get(Type::getInt64Ty(Context), D->getTypeAllocSize(t));
			}else{
			if(baseTy != Type::getInt8PtrTy(Context))
				temp= llvm::ConstantInt::get(Type::getInt64Ty(Context), D->getTypeAllocSize((baseTy->isPointerTy() && !isFnArr)?Type::getInt128Ty(Context):baseTy));
			else
				temp= llvm::ConstantInt::get(Type::getInt64Ty(Context), D->getTypeAllocSize(t->getElementType()));
			//errs() << "Hello : " <<*t->getElementType()<<"\n"<<D->getTypeAllocSize(t->getElementType())<<"\n"<< D->getTypeAllocSize(baseTy);
			}
			IRBuilder<> builder(GI);
			Offset = builder.CreateBinOp(Instruction::Mul,Offset, temp, "tmp");
		}
		else{
			if(noOfOperands == 2)
				offset+=c*D->getTypeAllocSize(t);
			else
				offset+=c*D->getTypeAllocSize( (t->getElementType()->isPointerTy() && !isFnArr) ? Type::getInt128Ty(Context):t->getElementType() ); //D->getTypeAllocSize(t)/t->getArrayNumElements();
		}
	}
	else
	{	//basic pointer increment or decrements

		if(!isconstant)
		{
			temp= llvm::ConstantInt::get(Type::getInt64Ty(Context), D->getTypeAllocSize(type));
			IRBuilder<> builder(GI);
			Offset = builder.CreateBinOp(Instruction::Mul,Offset, temp, "tmp");
		}
		else
			offset+=c*D->getTypeAllocSize(type);
	}

	if(isconstant)
		Offset = llvm::ConstantInt::get(Type::getInt32Ty(Context),offset);


	Instruction *op = dyn_cast<Instruction>(GI);
	BinaryOperator *binop;
	ZExtInst *zext_binop = new ZExtInst(Offset, Type::getInt128Ty(Context), "zextarrayidx", op);
	if(isNeg){
		//offset = offset*-1;
		binop =  BinaryOperator::Create(Instruction::Sub, GI->getOperand(0), zext_binop , "arrayidx", op);
	}else{
		binop =  BinaryOperator::Create(Instruction::Add, GI->getOperand(0), zext_binop , "arrayidx", op);
	}
	op->replaceAllUsesWith(binop);

}


char shaktiPass::ID = 0;
// static RegisterPass<shaktiPass> X("sms", "Shakti-T transforms");



// static RegisterStandardPasses Y(
//     PassManagerBuilder::EP_EnabledOnOptLevel0,
//     [](const PassManagerBuilder &Builder,
//        legacy::PassManagerBase &PM) { PM.add(new shaktiPass()); });

INITIALIZE_PASS_BEGIN(shaktiPass,
                      "sms",
                      "Shakti-T transforms", false, false)
INITIALIZE_PASS_END(shaktiPass,
                      "sms",
                      "Shakti-T transforms", false, false)

namespace llvm {
	ModulePass *createShaktiMSPass() {
  		return new shaktiPass();
	}
} // namespace llvm
