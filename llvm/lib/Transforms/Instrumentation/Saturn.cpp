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

static cl::opt<std::string> CapFilePath(
    "cap-file-path",
    cl::desc("Path where function-compartment mapping (.cap) file is present."),
    cl::Hidden);

static cl::opt<bool>
    EnableBoundsCheck("enable-bounds-check",
                 cl::desc("Enable S/W bounds checking"), cl::init(false), cl::Hidden);

static cl::opt<bool>
    EnableStripAddressCompatibility("enable-strip-trusted-code",
                 cl::desc("Enable stripping even in trusted code for compatibility"), cl::init(false), cl::Hidden);

static cl::opt<std::string> capFilePath(
    "cap-file-path",
    cl::desc("Path where function-compartment mapping (.cap) file is present."),
    cl::Hidden);

static cl::opt<int> defaultCompartment(
    "default-compartment-id",
    cl::desc("Default compartment id. Alternate way to set this, is \":<default_compartment_id>\" at the start of the .cap file."),
    cl::init(266), // currently 0-255 valid compartment range
    cl::Hidden);

static cl::opt<bool> allEntry(
    "all-entry",
    cl::desc("Instrument every function as valid entry point"),
    cl::init(false),
    cl::Hidden);

std::map <std::string, int> compartment_function_map;
std::map <std::string, int> checkcap_function_map;

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

void initialize_compartment_map(std::string source_filename_with_ext){
  if (!CapFilePath.empty()) {
    errs()<<CapFilePath<<"\n";
    std::string cap_filename(CapFilePath);
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
            defaultCompartment = std::stoi(myText.substr(myText.find_last_of(":")+1));
            
         }
         default_set = 1;
        }
        else{
          int checkcap_enable = std::stoi(myText.substr(myText.find_last_of(":")+1));
          std::string func_name_id_str = myText.substr(0, myText.find_last_of(":"));
          std::string function_name = func_name_id_str.substr(0, func_name_id_str.find_last_of(":"));
          int compartment_id = std::stoi(func_name_id_str.substr(func_name_id_str.find_last_of(":")+1));
          compartment_function_map.insert(std::pair<std::string, int>(function_name, compartment_id));
          if(checkcap_enable){
            checkcap_function_map.insert(std::pair<std::string, int>(function_name, 1));
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

Value *stripCheckPointer(Instruction *I, Value *pointeroperand, Value *boundsTableAddr, LLVMContext &Ctx){
 	IRBuilder<> Builder(I);
	// LLVM_DBG(dbgs() << "Strip with po " << *pointeroperand << "used in " << *I << "\n");
	auto poType = pointeroperand->getType();

	/* Mask upper 32 bits, assuming 4GB memory space */
	/* TODO: Can be made configurable at compile time, increased in powers of 2. Tradeoff between memory space and number of objects. supported */
	llvm::Constant *stripUpperMask = llvm::ConstantInt::get(Type::getInt64Ty(Ctx), 0x00000000FFFFFFFFULL, false);
	llvm::Constant *stripLowerMask = llvm::ConstantInt::get(Type::getInt64Ty(Ctx), 0xFFFFFFFF00000000ULL, false);

	Value* boundsTableIndex = Builder.CreateLShr(pointeroperand,32,"boundsTableIndex");
	auto boundsTableOffset = Builder.CreateShl(boundsTableIndex, 3, "boundsTableOffset");
	auto metadataAddrInt = Builder.CreateAdd(boundsTableAddr, boundsTableOffset, "metadataAddrInt");
	auto metadataAddr = Builder.CreateIntToPtr(metadataAddrInt,Type::getInt32PtrTy(Ctx),"metadataAddr");
	auto metadata = Builder.CreateLoad(Type::getInt64Ty(Ctx), metadataAddr,"metadata");

 	auto addressInt = Builder.CreatePtrToInt(pointeroperand, Type::getInt64Ty(Ctx), "addressInt");
 	auto strippedAddress = Builder.CreateAnd(addressInt, stripUpperMask, "strippedAddress");

	auto base = Builder.CreateAnd(metadata, stripUpperMask, "base");
	auto bound = Builder.CreateLShr(metadata,32,"bound");
	auto baseDiff = Builder.CreateSub(strippedAddress, base, "baseDiff");
	auto boundDiff = Builder.CreateSub(bound, strippedAddress, "boundDiff");
	auto resultDiff = Builder.CreateOr(baseDiff, boundDiff,"resultDiff");
	auto resultMask = Builder.CreateAnd(metadata, stripLowerMask, "resultMask");
	auto resultAddressInt = Builder.CreateOr(strippedAddress, resultMask, "resultPtrInt");

	auto resultAddress = Builder.CreateIntToPtr(resultAddressInt, poType, "resultAddr");


 	return resultAddress;
}


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
		SaturnPass() : ModulePass(ID) {initializeSaturnPass(*PassRegistry::getPassRegistry());}

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

	            auto SaturnMallocFn = M.getOrInsertFunction("__saturn_malloc", FunctionType::get(Type::getInt8PtrTy(Ctx), {Type::getInt64Ty(Ctx)}, false));
	            auto SaturnFreeFn = M.getOrInsertFunction("__saturn_free", FunctionType::get(Type::getVoidTy(Ctx), {Type::getInt8PtrTy(Ctx)}, false));

	            for (auto name : malloc_names) {
	    			M.getOrInsertFunction(name, FunctionType::get(Type::getInt8PtrTy(Ctx), {Type::getInt64Ty(Ctx)}, false)).getCallee()->replaceAllUsesWith(SaturnMallocFn.getCallee());
	    		}
	    		for (auto name : free_names) {
	    			M.getOrInsertFunction(name, FunctionType::get(Type::getVoidTy(Ctx), {Type::getInt8PtrTy(Ctx)}, false)).getCallee()->replaceAllUsesWith(SaturnFreeFn.getCallee());
	    		}
			}


    		/* TODO: Should do realloc, calloc any other allocator functions */


			/* Declare global variable which stores the bounds metadata table */
    		std::string boundsTableStr = "_saturn_bounds_table";
    		StringRef boundsTable = StringRef(boundsTableStr);
    		GlobalVariable* boundsTableGV = M.getOrInsertGlobal(boundsTable,Type::getInt64Ty(Ctx));

    		Value *boundsTableAddr = M.getOrInsertGlobal(boundsTable, Type::getInt64Ty(Ctx));

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
						if (LoadInst *LI = dyn_cast<LoadInst>(&I)){
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
						if (StoreInst *SI = dyn_cast<StoreInst>(&I)){
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



    		/* Setting code compartment metadata */
    		std::string source_filename_with_ext(M.getSourceFileName());
			std::string source_filename(M.getSourceFileName());
			initialize_compartment_map(sanitize(source_filename_with_ext, '/'));

			for (auto &F : M){
				int compartment_id = defaultCompartment;
			   	bool checkcap_insert = false;
			  	std::map <std::string, int>::iterator it;
			  	auto functionName = F.getName().str();
			  	it  = compartment_function_map.find(functionName);
			  	if(it != compartment_function_map.end()){
			    	compartment_id = compartment_function_map.at(functionName);
			  	}

	 			it  = checkcap_function_map.find(functionName);
			  	if(it != checkcap_function_map.end()){
			    	checkcap_insert = true;
			  	}
				std::string ts = ".text.c.";
			  	ts.append(std::to_string(compartment_id));
			  	F.setSection(StringRef(ts));
			 	
			  	if(checkcap_insert || allEntry){
			    	Constant* compartmentPrefix = ConstantInt::get(Type::getInt64Ty(Ctx), compartment_id, false);
			    	F.setPrefixData(compartmentPrefix);
			  	}
			}

    		// modified =  true
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
