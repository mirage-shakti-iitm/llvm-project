//===- Hello.cpp - Example code from "Writing an LLVM Pass" ---------------===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//
//
// This file implements two versions of the LLVM "Hello World" pass described
// in docs/WritingAnLLVMPass.html
//
//===----------------------------------------------------------------------===//

#include "llvm/ADT/Statistic.h"
#include "llvm/IR/Function.h"
#include "llvm/Pass.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/BasicBlock.h"
#include <fstream>
#include "llvm/ADT/StringRef.h"
#include "llvm/IR/LegacyPassManager.h"
#include "llvm/Transforms/IPO/PassManagerBuilder.h"

#include "llvm/IR/IRBuilder.h"

#include "llvm/IR/IntrinsicInst.h"
#include "llvm/IR/Intrinsics.h"
#include "llvm/IR/IntrinsicsAArch64.h"
#include "llvm/IR/IntrinsicsAMDGPU.h"
#include "llvm/IR/IntrinsicsARM.h"
#include "llvm/IR/IntrinsicsHexagon.h"
#include "llvm/IR/IntrinsicsNVPTX.h"
#include "llvm/IR/IntrinsicsPowerPC.h"
#include "llvm/IR/IntrinsicsX86.h"
#include "llvm/IR/IntrinsicsRISCV.h"


using namespace llvm;

#define DEBUG_TYPE "hello"

STATISTIC(HelloCounter, "Counts number of functions greeted");

static cl::opt<std::string> CapFilePath(
    "cap-file-path",
    cl::desc("Write to given path after running pass"),
    cl::Hidden);

static cl::opt<unsigned> DefaultCompartment(
    "default-compartment",
    cl::desc("Assign Default Compartment to all functions defined in this file"),
    cl::Hidden);

namespace {
  // Hello - The first implementation, without getAnalysisUsage.
  struct Hello : public ModulePass {
    static char ID; // Pass identification, replacement for typeid
    Hello() : ModulePass(ID) {}

    bool runOnModule(Module &M) override {
      bool modified = false;
      // if (!CapFilePath.empty()) {
      //   std::string cap_filename(CapFilePath);
      //   cap_filename.append("/");
      //   std::string source_filename_with_ext = M.getSourceFileName();
      //   std::string source_filename = source_filename_with_ext.substr(0, source_filename_with_ext.find_last_of("."));
      //   cap_filename.append(source_filename);
      //   cap_filename.append(".cap");
      //   std::ofstream CapFile(cap_filename);
      //   if(!(DefaultCompartment.getNumOccurrences() > 0)){
      //     DefaultCompartment = 290;
      //   }
      //   for(auto &F : M){
      //     if(!F.isDeclaration()) {
      //       auto func_name =  (F.getName().str());
      //       CapFile << func_name << ":" << DefaultCompartment << "\n";
      //     }
      //   }
      //   // CapFile << "Files can be tricky, but it is fun enough!";
      //   CapFile.close();
      // }
      
      for (auto &F : M)
			{
				LLVMContext &Ctx = F.getContext();
				Module *m = F.getParent();
				Function *checkcap = Intrinsic::getDeclaration(m, Intrinsic::riscv_checkcap);	// get hash intrinsic declaration
				for (auto &B : F)
				{
					if(&B == &((&F)->front()))
					{	// If BB is first
						Instruction *I = &((&B)->front());	// Get first instruction in function
            
						// Create call to intrinsic
						IRBuilder<> Builder(I);
						
            // Set up intrinsic arguments
						std::vector<Value *> args;
						args.push_back(Builder.getInt16(23));
						ArrayRef<Value *> args_ref(args);
            
            Builder.SetInsertPoint(I);
						Builder.CreateCall(checkcap, args_ref,"stack_chackcap");
					}
				}
			}

      // First pass adds stack cookie
			// for (auto &F : M)
			// {
			// 	LLVMContext &Ctx = F.getContext();
			// 	Module *m = F.getParent();
			// 	Function *hash = Intrinsic::getDeclaration(m, Intrinsic::riscv_hash);	// get hash intrinsic declaration
			// 	AllocaInst *st_cook;	// pointer to stack cookie
			// 	for (auto &B : F)
			// 	{
			// 		if(&B == &((&F)->front()))
			// 		{	// If BB is first
			// 			Instruction *I = &((&B)->front());	// Get first instruction in function
			// 			st_cook = new AllocaInst(Type::getInt64Ty(Ctx), 0,"stack_cookie", I);	// alloca stack cookie

			// 			// Set up intrinsic arguments
			// 			std::vector<Value *> args;
			// 			args.push_back(st_cook);
			// 			ArrayRef<Value *> args_ref(args);

			// 			// Create call to intrinsic
			// 			IRBuilder<> Builder(I);
			// 			Builder.SetInsertPoint(I);
			// 			Builder.CreateCall(hash, args_ref,"stack_hash");
			// 			modified = true;

			// 		}

			// 		for (auto &I : B)	// Iterate over instructions
			// 			if (dyn_cast<ReturnInst>(&I))
			// 			{	// If return instruction

			// 				// set up arguments
			// 				std::vector<Value *> args;
			// 				args.push_back(st_cook);
			// 				ArrayRef<Value *> args_ref(args);

			// 				// Call hash again to burn cookie
			// 				IRBuilder<> Builder(&I);
			// 				Builder.SetInsertPoint(&I);
			// 				Builder.CreateCall(hash, args_ref,"stack_cookie_burn");
			// 				modified = true;
			// 			}
			// 	}
			// }

      // for(auto &F : M){
      //   DataLayout *D = new DataLayout(&M);
      //   LLVMContext &Ctx = F.getContext();
      //   Module *m = F.getParent();
      //   Function *val_inst = Intrinsic::getDeclaration(&M, Intrinsic::riscv_validate);
      //   // bool modified=false;
      //   if(!F.isDeclaration()){
      //     for(auto &B : F){
      //       for(BasicBlock::iterator i = B.begin(), e = B.end(); i != e; ++i){
      //         Instruction *I = dyn_cast<Instruction>(i);
      //         if (auto *op = dyn_cast<LoadInst>(I))
      //         {
      //           errs() << "HEllo inside :" << *I << "\n\n";
      //           if(op->getOperand(0)->getType() != Type::getInt128Ty(Ctx))
      //             continue;
      //           modified = true;
      //           TruncInst *tr_lo = new TruncInst(op->getOperand(0), Type::getInt64Ty(Ctx),"fpr_low", op);	// alloca stack cookie
      //           Value* shamt = llvm::ConstantInt::get(Type::getInt128Ty(Ctx),64);
      //           BinaryOperator *shifted =  BinaryOperator::Create(Instruction::LShr, op->getOperand(0), shamt , "fpr_hi_big", op);
      //           TruncInst *tr_hi = new TruncInst(shifted, Type::getInt64Ty(Ctx),"fpr_hi", op);	// alloca stack cookie

      //           // Set up intrinsic arguments
      //           std::vector<Value *> args;

      //           args.push_back(tr_hi);
      //           args.push_back(tr_lo);
      //           ArrayRef<Value *> args_ref(args);

      //           // Create call to intrinsic
      //           IRBuilder<> Builder(I);
      //           Builder.SetInsertPoint(I);
      //           Builder.CreateCall(val_inst, args_ref,"");

      //           Type *loadtype = op->getType();
      //           Type *loadptrtype = loadtype->getPointerTo();

      //           IntToPtrInst *ptr = new IntToPtrInst(tr_lo,loadptrtype,"ptr",op);

      //           op->setOperand(0,ptr);

      //         }
      //       }
      //     }
          
      //   }
      // }
      errs() << "Finished";
      return false;
    }
  };
}

char Hello::ID = 0;
static RegisterPass<Hello> X("hello", "Hello World Pass");

// Automatically enable the pass.
// http://adriansampson.net/blog/clangpass.html
static void registerHello(const PassManagerBuilder &,
                         legacy::PassManagerBase &PM) {
  PM.add(new Hello());
}


static RegisterStandardPasses clangtoolLoader_Ox(PassManagerBuilder::EP_OptimizerLast, registerHello);
static RegisterStandardPasses clangtoolLoader_O0(PassManagerBuilder::EP_EnabledOnOptLevel0, registerHello);


namespace {
  // Hello2 - The second implementation with getAnalysisUsage implemented.
  struct Hello2 : public FunctionPass {
    static char ID; // Pass identification, replacement for typeid
    Hello2() : FunctionPass(ID) {}

    bool runOnFunction(Function &F) override {
      ++HelloCounter;
      errs() << "Hello: ";
      errs().write_escaped(F.getName()) << '\n';
      return false;
    }

    // We don't modify the program, so we preserve all analyses.
    void getAnalysisUsage(AnalysisUsage &AU) const override {
      AU.setPreservesAll();
    }
  };
}

char Hello2::ID = 0;
static RegisterPass<Hello2>
Y("hello2", "Hello World Pass (with getAnalysisUsage implemented)");
