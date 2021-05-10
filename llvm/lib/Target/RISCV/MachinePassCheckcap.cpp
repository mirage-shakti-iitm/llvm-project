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

using namespace llvm;

int glb = 20;
bool status  = 0;

#define RISCV_EXPAND_CHECKCAP_PSEUDO_NAME "RISCV pseudo instruction expansion pass"

static cl::opt<std::string>
    InputFileName("checkcap-file-name",
                 cl::desc("Print architectural register names rather than the "
                          "ABI names (such as x2 instead of sp)"), cl::Hidden);



namespace {

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

// inline MachineInstrBuilder BuildMI(MachineBasicBlock &BB,
//                                    MachineBasicBlock::iterator I,
//                                    const DebugLoc &DL,
//                                    const MCInstrDesc &MCID)

// FirstMBB = MF.front()
// FirstMI = FirstMBB.front()
// DL = FirstMI.getDebugLoc();
// auto FirstMBBI = FirstMBB.begin() 
// BuildMI(FirstMBB, FirstMBBI, DL, TII->get(RISCV::XORI), RISCV::X0)
// .addReg(RISCV::X0)
// .addImm(-1);

// BuildMI(LoopMBB, DL, TII->get(RISCV::AND))
//     .addReg(ScratchReg)
//     .addReg(RISCV::X0)
//     .addMBB(LoopMBB);


bool RISCVExpandCheckcapPseudo::runOnMachineFunction(MachineFunction &MF) {
  unsigned num_instr = 0;
  TII = static_cast<const RISCVInstrInfo *>(MF.getSubtarget().getInstrInfo());
  MachineBasicBlock &FirstMBB = MF.front();
  MachineInstr &FirstMI = FirstMBB.front();
  DebugLoc DL = FirstMI.getDebugLoc();
  MachineBasicBlock::iterator FirstMBBI = FirstMBB.begin();
  errs() << *FirstMBBI;
  BuildMI(FirstMBB, FirstMBBI, DL, TII->get(RISCV::CHECKCAP))
    .addImm(23);
  // BuildMI(FirstMBB, FirstMBBI, DL, TII->get(RISCV::ECALL));
    // .addReg(RISCV::X0)
    // .addImm(-1);
  
  auto I = MF.begin();
  auto E = MF.end();
  int bb = 0;
  for(; I != E; ++I){
    errs() << "BB: " << bb << "\n";
    errs() << I->front();
    bb++;   
    auto BBI = I->begin();
    auto BBE = I->end();
    for(; BBI != BBE; ++BBI){
      ++num_instr;
    }
  }
  errs() << "\n" << glb;
  if(status == 0){
    glb++;
    glb++;
    status = 1;
  }
  errs() << "\n" << glb;
  errs() << "\nFinished\n\n";
  errs() << "\nmcount --- " << MF.getName() << " has " << num_instr << " instructions.\n";
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
