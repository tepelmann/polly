//===------ Support/DebugLocationHelper.h -- Some Helper Functions --------===//
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

#ifndef POLLY_SUPPORT_DEBUGLOC_H
#define POLLY_SUPPORT_DEBUGLOC_H

#include <string>
#include "llvm/Support/raw_ostream.h"
#include "llvm/Analysis/ScalarEvolution.h"
#include "llvm/Analysis/ScalarEvolutionExpressions.h"

namespace llvm {
  class Instruction;
  class Region;
  class BasicBlock;
}

namespace polly {
  
  struct CodePos {
    unsigned LineBegin;
    unsigned ColBegin;
    unsigned LineEnd;
    unsigned ColEnd;
    // can be variable or function name etc.
    std::string Name;
    std::string File;
    std::string Dir;
  };
  
  /// @brief Get the location of a region from the debug info.
  ///
  /// @param R The region to get debug info for.
  /// @param CodePos Describes the extent of the region.
  void getDebugLocation(const llvm::Region *R, CodePos& location);
  
  void getDebugLocation(llvm::BasicBlock *BB, CodePos& location);
  
  void getDebugLocation(llvm::Instruction *instruction, CodePos& location);
  
  void getDebugLocation(llvm::Function *func, CodePos& location);
  
  llvm::raw_string_ostream& evPrint(
                               const llvm::SCEV& accessFunction,
                                     llvm::raw_string_ostream& OS);
}
#endif
