//===----- ScopDetection.cpp  - Detect Scops --------------------*- C++ -*-===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
//
// Detect the maximal Scops of a function.
//
// A static control part (Scop) is a subgraph of the control flow graph (CFG)
// that only has statically known control flow and can therefore be described
// within the polyhedral model.
//
// Every Scop fullfills these restrictions:
//
// * It is a single entry single exit region
//
// * Only affine linear bounds in the loops
//
// Every natural loop in a Scop must have a number of loop iterations that can
// be described as an affine linear function in surrounding loop iterators or
// parameters. (A parameter is a scalar that does not change its value during
// execution of the Scop).
//
// * Only comparisons of affine linear expressions in conditions
//
// * All loops and conditions perfectly nested
//
// The control flow needs to be structured such that it could be written using
// just 'for' and 'if' statements, without the need for any 'goto', 'break' or
// 'continue'.
//
// * Side effect free functions call
//
// Only function calls and intrinsics that do not have side effects are allowed
// (readnone).
//
// The Scop detection finds the largest Scops by checking if the largest
// region is a Scop. If this is not the case, its canonical subregions are
// checked until a region is a Scop. It is now tried to extend this Scop by
// creating a larger non canonical region.
//
//===----------------------------------------------------------------------===//

#include "polly/ScopDetection.h"

#include "polly/LinkAllPasses.h"
#include "polly/Support/ScopHelper.h"
#include "polly/Support/SCEVValidator.h"

#include "llvm/IR/LLVMContext.h"
#include "llvm/ADT/Statistic.h"
#include "llvm/Analysis/AliasAnalysis.h"
#include "llvm/Analysis/LoopInfo.h"
#include "llvm/Analysis/RegionIterator.h"
#include "llvm/Analysis/ScalarEvolution.h"
#include "llvm/Analysis/ScalarEvolutionExpressions.h"
#include "llvm/DebugInfo.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Assembly/Writer.h"

#define DEBUG_TYPE "polly-detect"
#include "llvm/Support/Debug.h"

#include <set>

using namespace llvm;
using namespace polly;

static cl::opt<std::string>
OnlyFunction("polly-detect-only", cl::desc("Only detect scops in function"),
             cl::Hidden, cl::value_desc("The function name to detect scops in"),
             cl::ValueRequired, cl::init(""));

static cl::opt<bool>
IgnoreAliasing("polly-ignore-aliasing",
               cl::desc("Ignore possible aliasing of the array bases"),
               cl::Hidden, cl::init(false));

static cl::opt<bool>
ReportLevel("polly-report", cl::desc("Print information about Polly"),
            cl::Hidden, cl::init(false));

static cl::opt<bool>
AllowNonAffine("polly-allow-nonaffine",
               cl::desc("Allow non affine access functions in arrays"),
               cl::Hidden, cl::init(false));

static cl::opt<bool>
VerboseScopErrors("polly-verbose-scop-errors",
    cl::desc("More helpful error messeges why a scop could not be recognized"),
    cl::Hidden, cl::init(false));

//===----------------------------------------------------------------------===//
// Statistics.

STATISTIC(ValidRegion, "Number of regions that a valid part of Scop");

#define logging_printStream(token) { std::stringstream o; o << token; logging::print(o.str().c_str()); }

#define BADSCOP_STAT(NAME, DESC)                                               \
  STATISTIC(Bad##NAME##ForScop, "Number of bad regions for Scop: " DESC)

#define INVALID_NORETURN(NAME, MESSAGE, LOCATION)                              \
       _INVALID(NAME, MESSAGE, LOCATION, ;)
  
#define INVALID(NAME, MESSAGE, LOCATION)                                       \
       _INVALID(NAME, MESSAGE, LOCATION, return false;)
  
#define _INVALID(NAME, MESSAGE, LOCATION, RET)                                 \
  do {                                                                         \
    std::string Buf;                                                           \
    raw_string_ostream fmt(Buf);                                               \
    fmt << MESSAGE;                                                            \
    fmt.flush();                                                               \
    LastFailure = Buf;                                                         \
    DEBUG(dbgs() << MESSAGE);                                                  \
    DEBUG(dbgs() << "\n");                                                     \
    assert(!Context.Verifying && #NAME);                                       \
    if (!Context.Verifying)                                                    \
      ++Bad##NAME##ForScop;                                                    \
    if (VerboseScopErrors)                                                     \
      badScop(NAME, Buf, LOCATION);                                            \
    RET                                                                        \
  } while (0);

#define INVALID_NORETURN_NOVERIFY(NAME, MESSAGE, LOCATION)                     \
       _INVALID_NOVERIFY(NAME, MESSAGE, LOCATION, ;)
  
#define INVALID_NOVERIFY(NAME, MESSAGE, LOCATION)                              \
       _INVALID_NOVERIFY(NAME, MESSAGE, LOCATION, return false;)
  
#define _INVALID_NOVERIFY(NAME, MESSAGE, LOCATION, RET)                        \
  do {                                                                         \
    std::string Buf;                                                           \
    raw_string_ostream fmt(Buf);                                               \
    fmt << MESSAGE;                                                            \
    fmt.flush();                                                               \
    LastFailure = Buf;                                                         \
    DEBUG(dbgs() << MESSAGE);                                                  \
    DEBUG(dbgs() << "\n");                                                     \
    /* DISABLED: assert(!Context.Verifying && #NAME); */                       \
    if (!Context.Verifying)                                                    \
      ++Bad##NAME##ForScop;                                                    \
    if (VerboseScopErrors)                                                     \
      badScop(NAME, Buf, LOCATION);                                            \
    RET                                                                        \
  } while (0);

BADSCOP_STAT(CFG, "CFG too complex");
BADSCOP_STAT(IndVar, "Non canonical induction variable in loop");
BADSCOP_STAT(LoopBound, "Loop bounds can not be computed");
BADSCOP_STAT(FuncCall, "Function call with side effects appeared");
BADSCOP_STAT(AffFunc, "Expression not affine");
BADSCOP_STAT(Scalar, "Found scalar dependency");
BADSCOP_STAT(Alias, "Found base address alias");
BADSCOP_STAT(SimpleRegion, "Region not simple");
BADSCOP_STAT(Other, "Others");

//===----------------------------------------------------------------------===//
// ScopDetection.
bool ScopDetection::isMaxRegionInScop(const Region &R) const {
  // The Region is valid only if it could be found in the set.
  return ValidRegions.count(&R);
}

std::string ScopDetection::regionIsInvalidBecause(const Region *R) const {
  if (!InvalidRegions.count(R))
    return "";
  
  std::string Buf;
  raw_string_ostream fmt(Buf);
  if (VerboseScopErrors && InvalidRegionsErrors.find(R)->second.size() > 0) {
    fmt << InvalidRegionsErrors.find(R)->second[0].Message;
    if (InvalidRegionsErrors.find(R)->second.size() > 1)
      fmt << " -- " << InvalidRegionsErrors.find(R)->second.size() 
          << " more problems...";
  }
  else
    fmt << InvalidRegions.find(R)->second;
  return fmt.str();
}

bool ScopDetection::isValidCFG(BasicBlock &BB,
                               DetectionContext &Context) const {
  Region &RefRegion = Context.CurRegion;
  TerminatorInst *TI = BB.getTerminator();

  // Return instructions are only valid if the region is the top level region.
  if (isa<ReturnInst>(TI) && !RefRegion.getExit() && TI->getNumOperands() == 0)
    return true;

  BranchInst *Br = dyn_cast<BranchInst>(TI);

  if (!Br)
    INVALID(CFG, "Non branch instruction terminates BB: " + BB.getName(), *Br);

  if (Br->isUnconditional())
    return true;

  Value *Condition = Br->getCondition();

  // UndefValue is not allowed as condition.
  if (isa<UndefValue>(Condition)) {
    INVALID(AffFunc, "Condition based on 'undef' value in BB: " + 
                      BB.getName(), *Br);
    return false;
  }

  // Only Constant and ICmpInst are allowed as condition.
  if (!(isa<Constant>(Condition) || isa<ICmpInst>(Condition)))
    INVALID(AffFunc, "Condition in BB '" + BB.getName() + "' neither "
                     "constant nor an icmp instruction", *Br);

  // Allow perfectly nested conditions.
  assert(Br->getNumSuccessors() == 2 && "Unexpected number of successors");

  if (ICmpInst *ICmp = dyn_cast<ICmpInst>(Condition)) {
    // Unsigned comparisons are not allowed. They trigger overflow problems
    // in the code generation.
    //
    // TODO: This is not sufficient and just hides bugs. However it does pretty
    // well.
    if (ICmp->isUnsigned())
      return false;

    // Are both operands of the ICmp affine?
    if (isa<UndefValue>(ICmp->getOperand(0)) ||
        isa<UndefValue>(ICmp->getOperand(1)))
      INVALID(AffFunc, "undef operand in branch at BB: " + BB.getName(), *ICmp);

    const SCEV *LHS = SE->getSCEV(ICmp->getOperand(0));
    const SCEV *RHS = SE->getSCEV(ICmp->getOperand(1));

    if (!isAffineExpr(&Context.CurRegion, LHS, *SE) ||
        !isAffineExpr(&Context.CurRegion, RHS, *SE))
      INVALID(AffFunc, "Non affine branch in BB '" << BB.getName() <<
                       "' with LHS: " << *LHS << " and RHS: " << *RHS, 
                      *ICmp);

  }

  // Allow loop exit conditions.
  Loop *L = LI->getLoopFor(&BB);
  if (L && L->getExitingBlock() == &BB)
    return true;

  // Allow perfectly nested conditions.
  Region *R = RI->getRegionFor(&BB);
  if (R->getEntry() != &BB)
    INVALID(CFG, "Not well structured condition at BB: " + BB.getName(), BB);

  return true;
}

bool ScopDetection::isValidCallInst(CallInst &CI) {
  if (CI.mayHaveSideEffects() || CI.doesNotReturn())
    return false;

  if (CI.doesNotAccessMemory())
    return true;

  Function *CalledFunction = CI.getCalledFunction();

  // Indirect calls are not supported.
  if (CalledFunction == 0)
    return false;

  // TODO: Intrinsics.
  return false;
}

bool ScopDetection::isValidMemoryAccess(Instruction &Inst,
                                        DetectionContext &Context) const {
  Value *Ptr = getPointerOperand(Inst);
  const SCEV *AccessFunction = SE->getSCEV(Ptr);
  const SCEVUnknown *BasePointer;
  Value *BaseValue;

  BasePointer = dyn_cast<SCEVUnknown>(SE->getPointerBase(AccessFunction));

  if (!BasePointer)
    INVALID(AffFunc, "No base pointer", Inst);

  BaseValue = BasePointer->getValue();

  if (isa<UndefValue>(BaseValue))
    INVALID(AffFunc, "Undefined base pointer", Inst);

  AccessFunction = SE->getMinusSCEV(AccessFunction, BasePointer);

  if (!isAffineExpr(&Context.CurRegion, AccessFunction, *SE, BaseValue) &&
      !AllowNonAffine) {
    std::string Buf;
    raw_string_ostream OS(Buf);
    //polly::evPrint(*AccessFunction, OS);
    //INVALID(AffFunc, "Non affine access function: " << OS.str(), Inst);
  INVALID(AffFunc, "Non affine access function: " << *AccessFunction, Inst);
  }

  // FIXME: Alias Analysis thinks IntToPtrInst aliases with alloca instructions
  // created by IndependentBlocks Pass.
  if (isa<IntToPtrInst>(BaseValue))
    INVALID(Other, "Find bad intToptr prt: " << *BaseValue, Inst);

  // Check if the base pointer of the memory access does alias with
  // any other pointer. This cannot be handled at the moment.
  AliasSet &AS =
      Context.AST.getAliasSetForPointer(BaseValue, AliasAnalysis::UnknownSize,
                                        Inst.getMetadata(LLVMContext::MD_tbaa));

  // INVALID triggers an assertion in verifying mode, if it detects that a SCoP
  // was detected by SCoP detection and that this SCoP was invalidated by a pass
  // that stated it would preserve the SCoPs.
  // We disable this check as the independent blocks pass may create memory
  // references which seem to alias, if -basicaa is not available. They actually
  // do not, but as we can not proof this without -basicaa we would fail. We
  // disable this check to not cause irrelevant verification failures.
  if (!AS.isMustAlias() && !IgnoreAliasing) {
    std::string Message;
    raw_string_ostream OS(Message);

    OS << "Possible aliasing: ";

    std::vector<Value *> Pointers;

    for (AliasSet::iterator AI = AS.begin(), AE = AS.end(); AI != AE; ++AI)
      Pointers.push_back(AI.getPointer());

    std::sort(Pointers.begin(), Pointers.end());

    unsigned foundArgumentAliasings = 0;
    unsigned functionLine = 0;
    std::vector<CodePos>* aliasingPositions = new std::vector<CodePos>();
    for (std::vector<Value *>::iterator PI = Pointers.begin(),
                                        PE = Pointers.end();
         ;) {
      CodePos codePos;
      Value *V = *PI;
      
      std::string Name;
      raw_string_ostream NOS(Name);
      if (V->getName().size() == 0) {
        OS  << "\"" << *V << "\"";
        NOS << *V;
      } else {
        OS << "\"" << V->getName() << "\"";
        NOS << V->getName();
      }
    
      if (Argument *arg = dyn_cast<Argument>(V)) {
        getDebugLocation(arg->getParent(), codePos);
        if (codePos.LineBegin != 0) {
          functionLine = codePos.LineBegin;
        }
        foundArgumentAliasings++;
        codePos.Name = NOS.str();
        aliasingPositions->push_back(codePos);
      }
      
      if (Instruction *inst = dyn_cast<Instruction>(V)) {
        getDebugLocation(inst, codePos);
        if (codePos.LineBegin != 0) {
          OS << " [" << codePos.File << ":" << codePos.LineBegin << "]";
        }
        codePos.Name = NOS.str();
        aliasingPositions->push_back(codePos);
      }
      
      ++PI;

      if (PI != PE)
        OS << ", ";
      else
        break;
    }
    
    INVALID_NORETURN_NOVERIFY(Alias, OS.str(), Inst)
    if (VerboseScopErrors) {
      if (foundArgumentAliasings > 1) {
        OS  << "\t(Function Argument aliasing, see line " << functionLine << ") \n"
            << "\tHint: Try to add \"restrict\" keyword" 
            << " to the arguments if possible.\n";
        LastScopError->Message = OS.str();
      }
      if (LastScopError->ErrorPositions)
        delete (LastScopError->ErrorPositions);
      LastScopError->ErrorPositions = aliasingPositions;
      ScopErrors.pop_back();
      ScopErrors.push_back(*LastScopError);
    }
    return false;
    
  }

  return true;
}

bool ScopDetection::hasScalarDependency(Instruction &Inst,
                                        Region &RefRegion) const {
  for (Instruction::use_iterator UI = Inst.use_begin(), UE = Inst.use_end();
       UI != UE; ++UI)
    if (Instruction *Use = dyn_cast<Instruction>(*UI))
      if (!RefRegion.contains(Use->getParent())) {
        // DirtyHack 1: PHINode user outside the Scop is not allow, if this
        // PHINode is induction variable, the scalar to array transform may
        // break it and introduce a non-indvar PHINode, which is not allow in
        // Scop.
        // This can be fix by:
        // Introduce a IndependentBlockPrepare pass, which translate all
        // PHINodes not in Scop to array.
        // The IndependentBlockPrepare pass can also split the entry block of
        // the function to hold the alloca instruction created by scalar to
        // array.  and split the exit block of the Scop so the new create load
        // instruction for escape users will not break other Scops.
        if (isa<PHINode>(Use))
          return true;
      }

  return false;
}

bool ScopDetection::isValidInstruction(Instruction &Inst,
                                       DetectionContext &Context) const {
  bool isValid = true;
                                         
  // Only canonical IVs are allowed.
  if (PHINode *PN = dyn_cast<PHINode>(&Inst))
    if (!isIndVar(PN, LI)) {
      INVALID_NORETURN(IndVar, "Non canonical PHI node: " << Inst, Context.CurRegion);
      isValid = false;
    }

  // Scalar dependencies are not allowed.
  if (hasScalarDependency(Inst, Context.CurRegion)) {
    INVALID_NORETURN(Scalar, "Scalar dependency found: " << Inst, Inst);
    isValid = false;
  }

  // We only check the call instruction but not invoke instruction.
  if (CallInst *CI = dyn_cast<CallInst>(&Inst)) {
    if (isValidCallInst(*CI))
      return true;

    INVALID_NORETURN(FuncCall, "Call instruction: " << Inst, Inst);
    isValid = false;
  }

  if (!Inst.mayWriteToMemory() && !Inst.mayReadFromMemory()) {
    if (isa<AllocaInst>(Inst)) {
      INVALID_NORETURN(Other, "Alloca instruction: " << Inst, Inst);
      isValid = false;
    }

    return isValid;
  }

  // Check the access function.
  if (isa<LoadInst>(Inst) || isa<StoreInst>(Inst))
    return isValidMemoryAccess(Inst, Context);

  // We do not know this instruction, therefore we assume it is invalid.
  INVALID(Other, "Unknown instruction: " << Inst, Inst);
}

bool ScopDetection::isValidBasicBlock(BasicBlock &BB,
                                      DetectionContext &Context) const {
  bool isValid = true;
  isValid = isValidCFG(BB, Context);

  // Check all instructions, except the terminator instruction.
  for (BasicBlock::iterator I = BB.begin(), E = --BB.end(); I != E; ++I)
    isValid = isValid && isValidInstruction(*I, Context);

  Loop *L = LI->getLoopFor(&BB);
  isValid = isValid && !(L && L->getHeader() == &BB && !isValidLoop(L, Context));

  return isValid;
}

bool ScopDetection::isValidLoop(Loop *L, DetectionContext &Context) const {
  PHINode *InductionVar = L->getCanonicalInductionVariable();
  // No canonical induction variable.
  if (!InductionVar)
    INVALID(IndVar, "No canonical IV at loop header: "
                    << L->getHeader()->getName(), *L->getHeader());

  // Is the loop count affine?
  const SCEV *LoopCount = SE->getBackedgeTakenCount(L);
  if (!isAffineExpr(&Context.CurRegion, LoopCount, *SE))
    INVALID(LoopBound, "Non affine loop bound '" << *LoopCount << "' in loop: "
                       << L->getHeader()->getName(), *L->getHeader());

  return true;
}

Region *ScopDetection::expandRegion(Region &R) {
  // Initial no valid region was found (greater than R)
  Region *LastValidRegion = NULL;
  Region *ExpandedRegion = R.getExpandedRegion();

  DEBUG(dbgs() << "\tExpanding " << R.getNameStr() << "\n");

  while (ExpandedRegion) {
    DetectionContext Context(*ExpandedRegion, *AA, false /* verifying */);
    DEBUG(dbgs() << "\t\tTrying " << ExpandedRegion->getNameStr() << "\n");

    // Check the exit first (cheap)
    if (isValidExit(Context)) {
      // If the exit is valid check all blocks
      //  - if true, a valid region was found => store it + keep expanding
      //  - if false, .tbd. => stop  (should this really end the loop?)
      if (!allBlocksValid(Context))
        break;

      // Delete unnecessary regions (allocated by getExpandedRegion)
      if (LastValidRegion)
        delete LastValidRegion;

      // Store this region, because it is the greatest valid (encountered so far)
      LastValidRegion = ExpandedRegion;

      // Create and test the next greater region (if any)
      ExpandedRegion = ExpandedRegion->getExpandedRegion();

    } else {
      // Create and test the next greater region (if any)
      Region *TmpRegion = ExpandedRegion->getExpandedRegion();

      // Delete unnecessary regions (allocated by getExpandedRegion)
      delete ExpandedRegion;

      ExpandedRegion = TmpRegion;
    }
  }

  DEBUG(
  if (LastValidRegion)
    dbgs() << "\tto " << LastValidRegion->getNameStr() << "\n";
  else
    dbgs() << "\tExpanding " << R.getNameStr() << " failed\n";
  );

  return LastValidRegion;
}

void ScopDetection::findScops(Region &R) {
  DetectionContext Context(R, *AA, false /*verifying*/);

  LastFailure = "";
  ScopErrors.clear();

  if (isValidRegion(Context)) {
    ++ValidRegion;
    ValidRegions.insert(&R);
    return;
  }

  InvalidRegions[&R] = LastFailure;
  InvalidRegionsErrors[&R] = ScopErrors;

  for (Region::iterator I = R.begin(), E = R.end(); I != E; ++I)
    findScops(**I);

  // Try to expand regions.
  //
  // As the region tree normally only contains canonical regions, non canonical
  // regions that form a Scop are not found. Therefore, those non canonical
  // regions are checked by expanding the canonical ones.

  std::vector<Region *> ToExpand;

  for (Region::iterator I = R.begin(), E = R.end(); I != E; ++I)
    ToExpand.push_back(*I);

  for (std::vector<Region *>::iterator RI = ToExpand.begin(),
                                       RE = ToExpand.end();
       RI != RE; ++RI) {
    Region *CurrentRegion = *RI;

    // Skip invalid regions. Regions may become invalid, if they are element of
    // an already expanded region.
    if (ValidRegions.find(CurrentRegion) == ValidRegions.end())
      continue;

    Region *ExpandedR = expandRegion(*CurrentRegion);

    if (!ExpandedR)
      continue;

    R.addSubRegion(ExpandedR, true);
    ValidRegions.insert(ExpandedR);
    ValidRegions.erase(CurrentRegion);

    for (Region::iterator I = ExpandedR->begin(), E = ExpandedR->end(); I != E;
         ++I)
      ValidRegions.erase(*I);
  }
}

bool ScopDetection::allBlocksValid(DetectionContext &Context) const {
  Region &R = Context.CurRegion;
  
  bool isValid = true;
  for (Region::block_iterator I = R.block_begin(), E = R.block_end(); I != E;
       ++I)
    isValid = isValid && isValidBasicBlock(**I, Context);

  return isValid;
}

bool ScopDetection::isValidExit(DetectionContext &Context) const {
  Region &R = Context.CurRegion;

  // PHI nodes are not allowed in the exit basic block.
  if (BasicBlock *Exit = R.getExit()) {
    BasicBlock::iterator I = Exit->begin();
    if (I != Exit->end() && isa<PHINode>(*I))
      INVALID(Other, "PHI node in exit BB", *Exit);
  }

  return true;
}

bool ScopDetection::isValidRegion(DetectionContext &Context) const {
  Region &R = Context.CurRegion;

  bool isValid = true;
  CodePos regionPos;
  getDebugLocation(&R, regionPos);
  DEBUG(dbgs() << "Checking region: " << R.getNameStr() << "["
               << regionPos.File      << ":" 
               << regionPos.LineBegin << ":"
               << regionPos.LineEnd   << "]\n\t");

  // The toplevel region is no valid region.
  if (!R.getParent()) {
    if (VerboseScopErrors)
    {
      std::string Buf;
      raw_string_ostream fmt(Buf);
      fmt << "Top level region is invalid:";
      fmt.flush();
      badScop(TopLevelInvalid, Buf, R);
    }
    else
    {
      DEBUG(dbgs() << "Top level region is invalid";
          dbgs() << "\n");
    }
    return false;
  }

  // SCoP cannot contain the entry block of the function, because we need
  // to insert alloca instruction there when translate scalar to array.
  if (R.getEntry() == &(R.getEntry()->getParent()->getEntryBlock()))
    INVALID(Other, "Region containing entry block of function is invalid!", R);

  // Only a simple region is allowed.
  if (!R.isSimple())
    INVALID_NORETURN(SimpleRegion, "Region not simple: " << R.getNameStr(), R);

  isValid = isValid && isValidExit(Context);

  isValid = isValid && allBlocksValid(Context);

  DEBUG(dbgs() << "OK\n");
  return isValid;
}

bool ScopDetection::isValidFunction(llvm::Function &F) {
  return !InvalidFunctions.count(&F);
}

void ScopDetection::printLocations(llvm::Function &F) {
  for (iterator RI = begin(), RE = end(); RI != RE; ++RI) {
    CodePos codePos;

    getDebugLocation(*RI, codePos);

    if (codePos.File.empty()) {
      outs() << "Scop detected at unknown location. Compile with debug info "
                "(-g) to get more precise information. \n";
      return;
    }

    outs() << "Found Scop!\n";
    outs() << codePos.Dir << codePos.File << ":" 
           << codePos.LineBegin << ":" << codePos.LineEnd << "\n";
  }
  if (VerboseScopErrors){
    outs() << "------ Problems in function '" << F.getName() << "' ( " 
           << InvalidRegionsErrors.size() << " Regions) ------\n";
    typedef std::map<const Region*, std::vector<ScopError> >::iterator it_type;
    for (it_type it = InvalidRegionsErrors.begin();
                 it != InvalidRegionsErrors.end(); it++) {
      outs() << "--- Region " << it->first->getNameStr() << " ---\n";
      std::vector<ScopError> errors = it->second;
      for (std::size_t i = 0; i < errors.size(); i++){
        ScopError err = errors[i];
        outs() << "Error --- " << err.Message << "\n";
        for (std::size_t p = 0; p < err.ErrorPositions->size(); p++) {
          CodePos pos = err.ErrorPositions->operator[](p);
          outs() << "\t - " << pos.Name << " " << pos.File 
                << ":" << pos.LineBegin << ":" << pos.LineEnd << "\n";
        }
        outs() << "\n";
      }
    } 
  } 
}

#define PRINT_SCOP_PROBLEM                                                     \
  do {                                                                         \
    CodePos codePos;                                                           \
    getDebugLocation(&location, codePos);                                      \
    std::vector<CodePos>* errPos = new std::vector<CodePos>;                   \
    errPos->push_back(codePos);                                                \
    LastScopError = new ScopError(reason, message, errPos);                    \
    ScopErrors.push_back(*LastScopError);                                      \
    if (codePos.LineBegin == 0)                                                \
      DEBUG(outs() << " - Could not find scop problem location. Compile with " \
                " debug info (-g) to get more precise information. \n");       \
    else                                                                       \
      DEBUG(outs() << " in " << codePos.File << ":" << codePos.LineBegin << ":"\
                                              << codePos.LineEnd    << "\n");  \
  } while(0);                                                                  \

void ScopDetection::badScop(BadScopReason reason, std::string &message, 
                            Region &location) const {
  PRINT_SCOP_PROBLEM
}
  
void ScopDetection::badScop(BadScopReason reason, std::string &message, 
                            BasicBlock &location) const {
  PRINT_SCOP_PROBLEM
}

void ScopDetection::badScop(BadScopReason reason, std::string &message,
                            Instruction &location) const {
  PRINT_SCOP_PROBLEM
}

bool ScopDetection::runOnFunction(llvm::Function &F) {
  AA = &getAnalysis<AliasAnalysis>();
  SE = &getAnalysis<ScalarEvolution>();
  LI = &getAnalysis<LoopInfo>();
  RI = &getAnalysis<RegionInfo>();
  Region *TopRegion = RI->getTopLevelRegion();

  releaseMemory();

  if (OnlyFunction != "" && F.getName() != OnlyFunction)
    return false;

  if (!isValidFunction(F))
    return false;
  
  findScops(*TopRegion);

  if (ReportLevel >= 1 || VerboseScopErrors)
    printLocations(F);

  return false;
}

void polly::ScopDetection::verifyRegion(const Region &R) const {
  assert(isMaxRegionInScop(R) && "Expect R is a valid region.");
  DetectionContext Context(const_cast<Region &>(R), *AA, true /*verifying*/);
  isValidRegion(Context);
}

void polly::ScopDetection::verifyAnalysis() const {
  for (RegionSet::const_iterator I = ValidRegions.begin(),
                                 E = ValidRegions.end();
       I != E; ++I)
    verifyRegion(**I);
}

void ScopDetection::getAnalysisUsage(AnalysisUsage &AU) const {
  AU.addRequired<DominatorTree>();
  AU.addRequired<PostDominatorTree>();
  AU.addRequired<LoopInfo>();
  AU.addRequired<ScalarEvolution>();
  // We also need AA and RegionInfo when we are verifying analysis.
  AU.addRequiredTransitive<AliasAnalysis>();
  AU.addRequiredTransitive<RegionInfo>();
  AU.setPreservesAll();
}

void ScopDetection::print(raw_ostream &OS, const Module *)const {
  for (RegionSet::const_iterator I = ValidRegions.begin(),
                                 E = ValidRegions.end();
       I != E; ++I)
    OS << "Valid Region for Scop: " << (*I)->getNameStr() << '\n';

  OS << "\n";
}

void ScopDetection::releaseMemory() {
  ValidRegions.clear();
  InvalidRegions.clear();
  InvalidRegionsErrors.clear();
  // Do not clear the invalid function set.
}

char ScopDetection::ID = 0;

INITIALIZE_PASS_BEGIN(ScopDetection, "polly-detect",
                      "Polly - Detect static control parts (SCoPs)", false,
                      false)
INITIALIZE_AG_DEPENDENCY(AliasAnalysis)
INITIALIZE_PASS_DEPENDENCY(DominatorTree)
INITIALIZE_PASS_DEPENDENCY(LoopInfo)
INITIALIZE_PASS_DEPENDENCY(PostDominatorTree)
INITIALIZE_PASS_DEPENDENCY(RegionInfo)
INITIALIZE_PASS_DEPENDENCY(ScalarEvolution)
INITIALIZE_PASS_END(ScopDetection, "polly-detect",
                    "Polly - Detect static control parts (SCoPs)", false, false)

Pass *polly::createScopDetectionPass() {
  return new ScopDetection();
}
