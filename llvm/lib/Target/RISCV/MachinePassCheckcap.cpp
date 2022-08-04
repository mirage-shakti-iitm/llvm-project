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

#include <cstdlib>
#include <string>
#include "llvm/MC/MCSection.h"
// #include <unistd>

using namespace llvm;

bool status  = 0;

std::map <std::string, int> compartment_function_map;

static cl::opt<std::string> CapFilePath(
    "cap-file-path",
    cl::desc("Path where function-compartment mapping (.cap) file is present."),
    cl::Hidden);

static cl::opt<int> default_compartment(
    "default-compartment-id",
    cl::desc("Default compartment id. Alternate way to set this, is \":<default_compartment_id>\" at the start of the .cap file."),
    cl::init(266), // currently 0-255 valid compartment range
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
        
        int compartment_id = std::stoi(myText.substr(myText.find_last_of(":")+1));
        compartment_function_map.insert(std::pair<std::string, int>(function_name, compartment_id));

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


bool RISCVExpandCheckcapPseudo::runOnMachineFunction(MachineFunction &MF) {
  unsigned num_instr = 0;
  TII = static_cast<const RISCVInstrInfo *>(MF.getSubtarget().getInstrInfo());
  MachineBasicBlock &FirstMBB = MF.front();
  MachineInstr &FirstMI = FirstMBB.front();
  DebugLoc DL = FirstMI.getDebugLoc();
  MachineBasicBlock::iterator FirstMBBI = FirstMBB.begin();
  // errs() << *FirstMBBI;

  std::string source_filename_with_ext((MF.getFunction()).getParent()->getSourceFileName());
  if(status == 0){
    std::string source_filename((MF.getFunction()).getParent()->getSourceFileName());
    initialize_compartment_map(sanitize(source_filename_with_ext, '/'));  
    status = 1;
  }

  std::string functionName = MF.getName().str();
  int compartment_id = default_compartment;
  std::map <std::string, int>::iterator it;

  it  = compartment_function_map.find(functionName);
  if(it != compartment_function_map.end()){
    compartment_id = compartment_function_map.at(functionName);
  }
  BuildMI(FirstMBB, FirstMBBI, DL, TII->get(RISCV::CHECKCAP))
    .addImm(compartment_id);

// Generating .cap file where all function-compartmentId mappings would be present
  std::string linker_cap_file_path = getenv("LINKER_CAP_FILE_PATH");
  std::string source_filename = sanitize(source_filename_with_ext.substr(0, source_filename_with_ext.find_last_of(".")), '/');
  std::string linker_cap_file_name_with_ext (linker_cap_file_path);
  linker_cap_file_name_with_ext.append("/");
  linker_cap_file_name_with_ext.append(source_filename);
  linker_cap_file_name_with_ext.append(".cap");
  std::ofstream linker_cap_file;
  // std::string cmd("touch ");
  // cmd.append(linker_cap_file_name_with_ext);
  // int status = system(cmd.c_str());
  linker_cap_file.open(linker_cap_file_name_with_ext, std::ios::out | std::ios::app);
  errs()<<linker_cap_file_name_with_ext<<"\n";
  if(linker_cap_file.is_open()){ 
    errs()<<"Written"<<compartment_id<<"\n";
    linker_cap_file<<functionName<<":"<<compartment_id<<"\n";
    errs()<<functionName<<":"<<compartment_id<<"\n";
  }
  linker_cap_file.close();  

  // if(functionName.compare("__gmp_randclear") == 0){
    // errs() << "\nSource Filename: " <<source_filename<<"\nLinkerCap Filename: "<<linker_cap_file_name_with_ext;    
  // }

  // errs() << "\nFinished Section : " << (MF.getSection())->getName()<<"\n\n";

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
