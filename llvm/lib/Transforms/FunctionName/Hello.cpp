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
      if (!CapFilePath.empty()) {
        std::string cap_filename(CapFilePath);
        cap_filename.append("/");
        std::string source_filename_with_ext = M.getSourceFileName();
        std::string source_filename = source_filename_with_ext.substr(0, source_filename_with_ext.find_last_of("."));
        cap_filename.append(source_filename);
        cap_filename.append(".cap");
        std::ofstream CapFile(cap_filename);
        if(!(DefaultCompartment.getNumOccurrences() > 0)){
          DefaultCompartment = 290;
        }
        for(auto &F : M){
          if(!F.isDeclaration()) {
            auto func_name =  (F.getName().str());
            CapFile << func_name << ":" << DefaultCompartment << "\n";
          }
        }
        // CapFile << "Files can be tricky, but it is fun enough!";
        CapFile.close();
      }
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
