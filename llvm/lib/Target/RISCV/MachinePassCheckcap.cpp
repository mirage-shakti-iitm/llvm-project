//===-- MachinePassCheckcap.cpp - Insert Checkcap Instruction ---===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//
//
// This file tries to insert Checkcap instruction at the start of every function
// definition.
//===----------------------------------------------------------------------===//

#include "RISCV.h"
#include "RISCVInstrInfo.h"
#include "RISCVTargetMachine.h"
#include "llvm/CodeGen/LivePhysRegs.h"
#include "llvm/CodeGen/MachineFunctionPass.h"
#include "llvm/CodeGen/MachineInstrBuilder.h"
#include "llvm/CodeGen/MachineBasicBlock.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/IR/Module.h"
#include "llvm/ADT/StringRef.h"
#include <map>
#include <fstream>

using namespace llvm;

bool status  = 0;

std::map <std::string, uint8_t> compartment_function_map;
uint8_t default_compartment = 266; // currently 0-255 valid compartment range

static cl::opt<std::string> CapFilePath(
    "cap-file-path",
    cl::desc("Write to given path after running pass"),
    cl::Hidden);


#define RISCV_EXPAND_CHECKCAP_PSEUDO_NAME "RISCV pseudo instruction expansion pass"


namespace {

void initialize_compartment_map(std::string source_filename_with_ext){
  if (!CapFilePath.empty()) {
    errs()<<CapFilePath<<"\n";
    std::string cap_filename(CapFilePath);
    cap_filename.append("/");
    std::string source_filename = source_filename_with_ext.substr(0, source_filename_with_ext.find_last_of("."));
    cap_filename.append(source_filename);
    cap_filename.append(".cap");
    std::ifstream CapFile;
    CapFile.open(cap_filename);
    std::string myText;
    bool default_set = 0;
    // Use a while loop together with the getline() function to read the file line by line
    if(CapFile){
      while (getline (CapFile, myText)) {
        if(default_set == 0){
          std::size_t pos = myText.find_last_of(":");
          if(pos == std::string::npos){
            default_compartment = std::stoi(myText);
         }
         default_set = 1;
        }
        std::string function_name = myText.substr(0, myText.find_last_of(":"));
        uint8_t compartment_id = std::stoi(myText.substr(myText.find_last_of(":")+1));
        compartment_function_map.insert(std::pair<std::string, uint8_t>(function_name, compartment_id)); 
      }
    }
    CapFile.close();
  }
}

class RISCVExpandCheckcapPseudo : public MachineFunctionPass {
public:
  const RISCVInstrInfo *TII;
  static char ID;

  RISCVExpandCheckcapPseudo() : MachineFunctionPass(ID) {
    initializeRISCVExpandCheckcapPseudoPass(*PassRegistry::getPassRegistry());
  }

  bool runOnMachineFunction(MachineFunction &MF) override;

  StringRef getPassName() const override { return RISCV_EXPAND_CHECKCAP_PSEUDO_NAME; }

// private:


};

char RISCVExpandCheckcapPseudo::ID = 0;

bool RISCVExpandCheckcapPseudo::runOnMachineFunction(MachineFunction &MF) {
  unsigned num_instr = 0;
  TII = static_cast<const RISCVInstrInfo *>(MF.getSubtarget().getInstrInfo());
  MachineBasicBlock &FirstMBB = MF.front();
  MachineInstr &FirstMI = FirstMBB.front();
  DebugLoc DL = FirstMI.getDebugLoc();
  MachineBasicBlock::iterator FirstMBBI = FirstMBB.begin();
  // errs() << *FirstMBBI;

  if(status == 0){
    std::string source_filename((MF.getFunction()).getParent()->getSourceFileName());
    initialize_compartment_map(source_filename);
    status = 1;
  }

  std::string functionName = MF.getName().str();
  uint8_t compartment_id = default_compartment;
  std::map <std::string, uint8_t>::iterator it;
  it  = compartment_function_map.find(functionName);
  if(it != compartment_function_map.end()){
    compartment_id = compartment_function_map.at(functionName);
  }
  BuildMI(FirstMBB, FirstMBBI, DL, TII->get(RISCV::CHECKCAP))
    .addImm(compartment_id);

  // errs() << "\nFinished\n\n";
  // errs() << "\nmcount --- " << MF.getName() << " has " << num_instr << " instructions.\n";
  // errs() << InputFileName;
  // errs() << "\n" << (MF.getFunction()).getParent()->getSourceFileName();
  
  return false;
}

} // end of anonymous namespace

INITIALIZE_PASS(RISCVExpandCheckcapPseudo, "riscv-expand-checkcap",
                RISCV_EXPAND_CHECKCAP_PSEUDO_NAME, false, false)
namespace llvm {

FunctionPass *createRISCVExpandCheckcapPseudoPass() { return new RISCVExpandCheckcapPseudo(); }

} // end of namespace llvm
