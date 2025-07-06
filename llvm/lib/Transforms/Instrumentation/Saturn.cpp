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



Value *stripPointer(Instruction *I, Value *pointeroperand, LLVMContext &Ctx){
 	IRBuilder<> Builder(I);
	// LLVM_DBG(dbgs() << "Strip with po " << *pointeroperand << "used in " << *I << "\n");
	auto poType = pointeroperand->getType();

	/* Mask upper 32 bits, assuming 4GB memory space */
	/* TODO: Can be made configurable at compile time, increased in powers of 2. Tradeoff between memory space and number of objects. supported */
	llvm::Constant *stripUpperMask = llvm::ConstantInt::get(Type::getInt64Ty(Ctx), 0x00000000FFFFFFFFULL, false);
	llvm::Constant *stripLowerMask = llvm::ConstantInt::get(Type::getInt64Ty(Ctx), 0xFFFFFFFF00000000ULL, false);

 	auto addressInt = Builder.CreatePtrToInt(pointeroperand, Type::getInt64Ty(Ctx), "addressInt");
 	auto strippedAddress = Builder.CreateAnd(addressInt, stripUpperMask, "strippedAddress");
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
		{	return 0;

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
