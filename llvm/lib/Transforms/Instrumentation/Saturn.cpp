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


using namespace llvm;

static cl::opt<bool>
    EnableBoundsCheck("enable-bounds-check",
                 cl::desc("Enable S/W bounds checking"), cl::init(false), cl::Hidden);

static cl::opt<bool>
    EnableStripAddressCompatibility("enable-strip-trusted-code",
                 cl::desc("Enable stripping even in trusted code for compatibility"), cl::init(false), cl::Hidden);



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

Value *stripCheckPointer(Instruction *I, Value *pointeroperand, Value *boundsTableAddr, LLVMContext &Ctx){
 	IRBuilder<> Builder(I);
	LLVM_DBG(dbgs() << "Strip with po " << *pointeroperand << "used in " << *I
                  << "\n");
	auto poType = pointeroperand->getType();

	/* Mask upper 32 bits, assuming 4GB memory space */
	/* TODO: Can be made configurable at compile time, increased in powers of 2. Tradeoff between memory space and number of objects. supported */
	llvm::Constant *stripUpperMask = llvm::ConstantInt::get(Int64Ty, 0x00000000FFFFFFFFULL, false);
	llvm::Constant *stripLowerMask = llvm::ConstantInt::get(Int64Ty, 0xFFFFFFFF00000000ULL, false);

	auto boundsTableIndex = Builder.CreateLShr(po,32,"boundsTableIndex")
	auto boundsTableOffset = Builder.CreateShl(index, 3, "boundsTableOffset")
	auto metadataAddrInt = Builder.CreateAdd(boundsTableAddr, index, "metadataAddrInt")
	auto metadataAddr = Builder.CreateIntToPtr(metadataAddrInt,Type::getInt32PtrTy(Ctx),"metadataAddr")
	auto metadata = Builder.CreateLoad(Int64Ty, metadataAddr,"metadata")

 	auto addressInt = Builder.CreatePtrToInt(pointeroperand, Int64Ty, "addressInt");
 	auto strippedAddress = Builder.CreateAnd(addressInt, StripMask, "strippedAddress");

	auto base = Builder.CreateAnd(metadata, stripUpperMask, "base");
	auto bound = Builder.CreateLShr(metadata,32,"bound");
	auto baseDiff = Builder.CreateSub(strippedAddress, base, "baseDiff");
	auto boundDiff = Builder.CreateSub(bound, strippedAddress, "boundDiff");
	auto resultDiff = Builder.CreateOr(baseDiff, boundDiff,"resultDiff");
	auto resultMask = Builder.CreateAnd(metadata, StripLowerMask, "resultMask");
	auto resultAddressInt = Builder.CreateOr(strippedAddress, resultMask, "resultPtrInt");

	auto resultAddress = Builder.CreateIntToPtr(resultAddressInt, poType, "resultAddr");


 	return resultAddress;
}


Value *stripCheckPointer(Instruction *I, Value *pointeroperand, LLVMContext &Ctx){
 	IRBuilder<> Builder(I);
	LLVM_DBG(dbgs() << "Strip with po " << *pointeroperand << "used in " << *I
                  << "\n");
	auto poType = pointeroperand->getType();

	/* Mask upper 32 bits, assuming 4GB memory space */
	/* TODO: Can be made configurable at compile time, increased in powers of 2. Tradeoff between memory space and number of objects. supported */
	llvm::Constant *stripUpperMask = llvm::ConstantInt::get(Int64Ty, 0x00000000FFFFFFFFULL, false);
	llvm::Constant *stripLowerMask = llvm::ConstantInt::get(Int64Ty, 0xFFFFFFFF00000000ULL, false);

 	auto addressInt = Builder.CreatePtrToInt(pointeroperand, Int64Ty, "addressInt");
 	auto strippedAddress = Builder.CreateAnd(addressInt, StripMask, "strippedAddress");
	auto resultAddress = Builder.CreateIntToPtr(strippedAddress, poType, "resultAddr");

 	return resultAddress;
}


namespace {
	struct SaturnPass : public ModulePass
	{
		static char ID;
		SaturnPass() : ModulePass(ID) {initializeSaturnPassPass(*PassRegistry::getPassRegistry());}

		std::map <StructType*, StructType*> rep_structs;

		virtual bool runOnModule(Module &M)
		{	

			bool moduleHasFunctions = false;

			// if(EnableShaktiMS == 1){
				/* before doing anything check whether pointer decrements are there or not in any function. */
			std::set<std::string> func_name;
			for (auto &F : M){
				if (!F.isDeclaration()) {
						
					moduleHasFunctions = true;
					break;
				}
			}

			bool modified=false;

			// Skipping Shakti-MS pass if the no functions present in the module
			if(moduleHasFunctions == false){
				return modified	;
			}

			if(EnableBoundsCheck){
				/* Replace allocator functions with safe variant */
				auto malloc_names = {"malloc", "_Znam", "_Znwm", "_ZnamRKSt9nothrow_t",
	                       "_ZnwmRKSt9nothrow_t"};
	 			auto free_names = {"free", "_ZdaPv", "_ZdlPv", "_ZdaPvRKSt9nothrow_t",
	                     "_ZdlPvRKSt9nothrow_t"};

	            SaturnMallocFn = M.getOrInsertFunction("__saturn_malloc", FunctionType::get(PtrTy, {Int64Ty}, false));
	            SaturnFreeFn = M.getOrInsertFunction("__saturn_free", FunctionType::get(VoidTy, {PtrTy}, false));

	            for (auto name : malloc_names) {
	    			M.getOrInsertFunction(name, FunctionType::get(PtrTy, {Int64Ty}, false)).getCallee()->replaceAllUsesWith(SaturnMallocFn.getCallee());
	    		}
	    		for (auto name : free_names) {
	    			M.getOrInsertFunction(name, FunctionType::get(VoidTy, {PtrTy}, false)).getCallee()->replaceAllUsesWith(SaturnFreeFn.getCallee());
	    		}
			}


    		/* TODO: Should do realloc, calloc any other allocator functions */


			/* Declare global variable which stores the bounds metadata table */
    		std::string boundsTableStr = "_saturn_bounds_table";
    		StringRef boundsTable = StringRef(boundsTableStr);
    		GlobalVariable* boundsTableGV = M.getOrInsertGlobal(boundsTable,arg0Type);

    		Value *boundsTableAddr = M.getOrInsertGlobal(startName, Type::getInt64Ty(Ctx));

    		//  I->getModule()->getNamedGlobal(Name);
    		// if (key) {
        	// 	LoadInst* load = Builder.CreateLoad(key);

        	// return load;
    		// }

			/* Replace load store instructions with bounds check */

    		for (auto &F : M){
    			for (auto &B : F)
				{
					// Iterate over Instrs in BB
					for (auto &I : B)
					{
						// If instruction is load instruction apply bounds check
						if (LoadInst *LI = dyn_cast<CallInst>(&I)){
							Value *po = LI->getPointerOperand();
							
							if(EnableBoundsCheck){
								Value *V = stripCheckPointer(LI, po, boundsTableAddr, Ctx);
								LI->setOperand(0, V);
							}
							if(!EnableBoundsCheck && EnableStripAddressCompatibility){
								Value *V = stripPointer(LI, po, Ctx);
								LI->setOperand(0, V);
							}
						}
						if (StoreInst *SI = dyn_cast<CallInst>(&I)){
							Value *po = SI->getPointerOperand();
							if(EnableBoundsCheck){
								Value *V = stripCheckPointer(SI, po, boundsTableAddr, Ctx);
								SI->setOperand(1, V);
							}
							if(!EnableBoundsCheck && EnableStripAddressCompatibility){
								Value *V = stripPointer(SI, po, Ctx);
								SI->setOperand(1, V);
							}	
						}
    				}
    			}
    		}	
    		
    		modified =  true
			return modified;
		}
	};
}

char SaturnPass::ID = 0;
// static RegisterPass<SaturnPass> X("saturn", "Shakti-T transforms");



// static RegisterStandardPasses Y(
//     PassManagerBuilder::EP_EnabledOnOptLevel0,
//     [](const PassManagerBuilder &Builder,
//        legacy::PassManagerBase &PM) { PM.add(new SaturnPass()); });

INITIALIZE_PASS_BEGIN(SaturnPass,
                      "saturn",
                      "Memory safety transforms", false, false)
INITIALIZE_PASS_END(SaturnPass,
                      "saturn",
                      "Memory safety transforms", false, false)

namespace llvm {
	ModulePass *createSaturnPass() {
  		return new SaturnPass();
	}
} // namespace llvm
