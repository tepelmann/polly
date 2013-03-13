//===- DebugLocationHelper.cpp - Some Helper Functions   ------------------===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
//
// Functions that help getting source code location information.
//
//===----------------------------------------------------------------------===//

#include "polly/Support/DebugLocationHelper.h"
#define DEBUG_TYPE "polly-debuglocation-helper"

#include "llvm/Analysis/RegionInfo.h"
#include <llvm/Analysis/ScalarEvolution.h>
#include "llvm/Analysis/LoopInfo.h"
#include "llvm/ADT/STLExtras.h"

#include "llvm/Support/Debug.h"
#include <llvm/DebugInfo.h>
#include <llvm/IR/Function.h>
#include <llvm/IR/IntrinsicInst.h>
#include <llvm/IR/Metadata.h>
#include <llvm/IR/Module.h>
#include "llvm/Assembly/Writer.h"

using namespace llvm;
using namespace polly;

void polly::getDebugLocation(const Region *R, CodePos& location) {
  location.LineBegin = 0;
  location.ColBegin = 0;
  location.LineEnd = 0;
  location.ColEnd = 0;

  for (Region::const_block_iterator RI = R->block_begin(), RE = R->block_end();
       RI != RE; ++RI)
    for (BasicBlock::iterator BI = (*RI)->begin(), BE = (*RI)->end(); BI != BE;
         ++BI) {
      DebugLoc DL = BI->getDebugLoc();
      if (DL.isUnknown())
        continue;

      DIScope Scope(DL.getScope(BI->getContext()));

      location.File = Scope.getFilename();
      location.Dir = Scope.getDirectory();

      unsigned NewLine = DL.getLine();

      location.LineBegin = std::min(location.LineBegin, NewLine);
      location.LineEnd = std::max(location.LineEnd, NewLine);
      break;
    }
}

void polly::getDebugLocation(BasicBlock *BB, CodePos& location) {
  location.LineBegin = 0;
  location.ColBegin = 0;
  location.LineEnd = 0;
  location.ColEnd = 0;

  for (BasicBlock::iterator BI = BB->begin(), BE = BB->end(); BI != BE; ++BI){
    DebugLoc DL = BI->getDebugLoc();
    if (DL.isUnknown())
      continue;

    DIScope Scope(DL.getScope(BI->getContext()));

    location.File = Scope.getFilename();
    location.Dir = Scope.getDirectory();

    unsigned NewLine = DL.getLine();

    location.LineBegin = std::min(location.LineBegin, NewLine);
    location.LineEnd = std::max(location.LineEnd, NewLine);
  }
}

void polly::getDebugLocation(Instruction *instruction, CodePos& location) {
  location.LineBegin = 0;
  location.ColBegin = 0;
  location.LineEnd = 0;
  location.ColEnd = 0;

  DebugLoc DL, DLNext;
  DL = instruction->getDebugLoc();
  Instruction *nextInstr = instruction->getNextNode();
  if (nextInstr != NULL)
    DLNext = nextInstr->getDebugLoc();

  if (DL.isUnknown())
    return;

  DIScope Scope(DL.getScope(instruction->getContext()));

  location.File = Scope.getFilename();
  location.Dir = Scope.getDirectory();

  location.LineBegin = DL.getLine();
  location.ColBegin = DL.getCol();
  location.LineEnd = location.LineBegin;

  if (nextInstr != NULL) {
    if (DLNext.getLine() > location.LineBegin)
      location.LineEnd = DLNext.getLine();
    else
      location.ColEnd = DLNext.getCol() - 1;
  }
}

void polly::getDebugLocation(Function *func, CodePos& location) {
  location.LineBegin = 0;
  location.ColBegin = 0;
  location.LineEnd = 0;
  location.ColEnd = 0;

  const Module *M = func->getParent();
  NamedMDNode *NMD = M->getNamedMetadata("llvm.dbg.cu");
  if (!NMD)
    return;

  for (unsigned i = 0, e = NMD->getNumOperands(); i != e; i++) {
    DIDescriptor CompileUnit(cast<MDNode>(NMD->getOperand(i)));
    unsigned subProgPos = CompileUnit->getNumOperands()-3;
    DIDescriptor SubProgs(cast<MDNode>(CompileUnit->getOperand(subProgPos)));
    for (unsigned s = 0; s < SubProgs->getNumOperands(); s++) {
      Value* VV = cast<Value>(SubProgs->getOperand(s));
      if (isa<MDNode>(VV)) {
        DIDescriptor DescSubProg(cast<MDNode>(VV));
        DISubprogram SubProg(DescSubProg);
        if (SubProg.getFunction() == func) {
          location.LineBegin = SubProg.getLineNumber();
          location.File = SubProg.getFilename();
          location.Dir = SubProg.getDirectory();
          location.Name = SubProg.getDisplayName();
          return;
        }
      }
    }
  }
}
