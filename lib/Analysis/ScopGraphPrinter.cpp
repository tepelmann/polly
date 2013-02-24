//===- GraphPrinter.cpp - Create a DOT output describing the Scop. --------===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
//
// Create a DOT output describing the Scop.
//
// For each function a dot file is created that shows the control flow graph of
// the function and highlights the detected Scops.
//
//===----------------------------------------------------------------------===//

#include "polly/LinkAllPasses.h"
#include "polly/ScopDetection.h"

#include <iostream>
#include <fstream>
#include <string>
#include <sstream>
#include "llvm/DebugInfo.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/raw_ostream.h"

#include "llvm/Analysis/DOTGraphTraitsPass.h"
#include "llvm/Analysis/RegionInfo.h"
#include "llvm/Analysis/RegionIterator.h"

using namespace polly;
using namespace llvm;

static cl::opt<bool>
ScopsShowSource("dot-scops-source",
            cl::desc("Print source code inside the nodes of the scop graph"),
            cl::Hidden, cl::init(false));

static cl::opt<std::string>
ScopsShowProfilingData("dot-scops-profiling-data",
                       cl::desc("Print the profiling data in the file inside the nodes of the scop graph"),
                       cl::Hidden, cl::init(""));

namespace llvm {
  template <> struct GraphTraits<ScopDetection*>
    : public GraphTraits<RegionInfo*> {

    static NodeType *getEntryNode(ScopDetection *SD) {
      return GraphTraits<RegionInfo*>::getEntryNode(SD->getRI());
    }
    static nodes_iterator nodes_begin(ScopDetection *SD) {
      return nodes_iterator::begin(getEntryNode(SD));
    }
    static nodes_iterator nodes_end(ScopDetection *SD) {
      return nodes_iterator::end(getEntryNode(SD));
    }
  };

template<>
struct DOTGraphTraits<RegionNode*> : public DefaultDOTGraphTraits {

  DOTGraphTraits (bool isSimple=false)
    : DefaultDOTGraphTraits(isSimple) {}

  std::string getNodeLabel(RegionNode *Node, RegionNode *Graph) {

    if (!Node->isSubRegion()) {
      BasicBlock *BB = Node->getNodeAs<BasicBlock>();

      if (isSimple())
        return DOTGraphTraits<const Function*>
          ::getSimpleNodeLabel(BB, BB->getParent());
      else
        return DOTGraphTraits<const Function*>
          ::getCompleteNodeLabel(BB, BB->getParent());
    }

    return "Not implemented";
  }
};

template<>
struct DOTGraphTraits<ScopDetection*> : public DOTGraphTraits<RegionNode*> {
  DOTGraphTraits (bool isSimple=false)
    : DOTGraphTraits<RegionNode*>(isSimple) {}
  static std::string getGraphName(ScopDetection *SD) {
    return "Scop Graph";
  }

  std::string getEdgeAttributes(RegionNode *srcNode,
    GraphTraits<RegionInfo*>::ChildIteratorType CI, ScopDetection *SD) {

    RegionNode *destNode = *CI;

    if (srcNode->isSubRegion() || destNode->isSubRegion())
      return "";

    // In case of a backedge, do not use it to define the layout of the nodes.
    BasicBlock *srcBB = srcNode->getNodeAs<BasicBlock>();
    BasicBlock *destBB = destNode->getNodeAs<BasicBlock>();

    RegionInfo *RI = SD->getRI();
    Region *R = RI->getRegionFor(destBB);

    while (R && R->getParent())
      if (R->getParent()->getEntry() == destBB)
        R = R->getParent();
      else
        break;

    if (R->getEntry() == destBB && R->contains(srcBB))
      return "constraint=false";

    return "";
  }

  // Gets the start and endline of the basic block in the original source file.
  static void getDebugLocation(BasicBlock *BB, unsigned &LineBegin, unsigned &LineEnd, std::string &FileName, std::string &Dir) {
    LineBegin = -1;
    LineEnd = 0;
    for (BasicBlock::iterator BI = BB->begin(), BE = BB->end(); BI != BE; ++BI) {
      DebugLoc DL = BI->getDebugLoc();
      if (DL.isUnknown())
        continue;

      DIScope Scope(DL.getScope(BI->getContext()));

      FileName = Scope.getFilename();
      Dir = Scope.getDirectory();

      unsigned NewLine = DL.getLine();

      LineBegin = std::min(LineBegin, NewLine);
      LineEnd = std::max(LineEnd, NewLine);
    }
  }

  static void gotoFileLine(std::ifstream& stream, unsigned lineNumber) {
    std::string s;
    long length;

    stream.seekg (0, std::ios::beg); // go to the first line

    for (int i=1; (i<lineNumber && stream.good()); i++) // loop till the desired line
        getline(stream, s);

    length = stream.tellg(); // tell the first position at the line
    stream.seekg(length);
  }
  
  // Get the percentage of profiling samples that hit the basic block.
  // The file with the profiling data looks like this:
  // Percentage | FileName | LineNumber
  // 23.42 main.cc 123
  static float getNodeProfilingPercentage(std::string& filePathProfilingData, std::string& fileName, int bbBegin, int bbEnd) {
    std::ifstream ProfilingData(filePathProfilingData.c_str());
    if (ProfilingData.is_open())
    {
        float percentBasicBlock = 0.0;
        for (int nr = bbBegin; nr <= bbEnd; nr++)
        {
            std::stringstream searchPattern;
            searchPattern << fileName << " " << nr;
            std::string line;
            size_t foundIdx = std::string::npos;
            getline(ProfilingData, line);
            do
            {
                foundIdx = line.find(searchPattern.str());
            }while(foundIdx == std::string::npos && getline(ProfilingData, line));
            if (foundIdx != std::string::npos)
            {
                float percentCodeLine;
                std::stringstream ssLine(line);
                ssLine >> percentCodeLine;
                percentBasicBlock += percentCodeLine;
            }
            ProfilingData.clear();
            ProfilingData.seekg(0);
        }
        return percentBasicBlock;
    }
    return 0.0;
  }

  std::string getNodeLabel(RegionNode *Node, ScopDetection *SD) {
    std::stringstream label;
    bool Profiling = ScopsShowProfilingData.hasArgStr();
    if (ScopsShowSource)
    {
        std::string fileName, dir;
        unsigned begin, end;
        std::stringstream filePathSrc, filePathProfilingData;
        getDebugLocation(Node->getEntry(), begin, end, fileName, dir);

        if (Profiling)
        {
            //filePathProfilingData << ScopsShowProfilingData; // "/home/jan/Dropbox/diplomarbeit/algo1-isaft/Implementierung/perfAnnotatedSummery.txt";
            if (begin != -1)
            {
                float percentage = getNodeProfilingPercentage(ScopsShowProfilingData, fileName, begin, end);
                if (percentage > 0) {
                    label << percentage;
                    label << "\\|";
                }
            }
        }

        if (ScopsShowSource)
        {
            filePathSrc << dir << "/" << fileName;
            if (begin == -1) label << "source file not found! \n";
            std::ifstream SourceFile(filePathSrc.str().c_str());
            if (SourceFile.is_open()) {
                gotoFileLine(SourceFile, begin);
                for (int i=begin; i<=end; i++){
                    std::string line;
                    getline(SourceFile, line);
                    label << (line) << "\\\l";
                }
                SourceFile.close();
            }else{
                label << "could not open source file '" << filePathSrc.str().c_str() << "'";
            }

            // place a horizontal line between the original source code and the llvm-ir
            label << "\\|";
        }
    }
    label << DOTGraphTraits<RegionNode*>::getNodeLabel(Node, SD->getRI()->getTopLevelRegion());
    return label.str();
  }

  static std::string getNodeAttributes(RegionNode *Node, ScopDetection *SD){
    std::stringstream attr;
    bool Profiling = ScopsShowProfilingData.hasArgStr();
    if (Profiling)
    {
        std::string fileName, dir;
        unsigned begin, end;
        std::stringstream filePathProfilingData;
        getDebugLocation(Node->getEntry(), begin, end, fileName, dir);
        //filePathProfilingData << ScopsShowProfilingData;//"/home/jan/Dropbox/diplomarbeit/algo1-isaft/Implementierung/perfAnnotatedSummery.txt";
        if (begin != -1)
        {
            float percentage = getNodeProfilingPercentage(ScopsShowProfilingData, fileName, begin, end);
            attr << "fillcolor=\"" << "0 " << (percentage / 100) << " 1\"";
            return attr.str();
        }
    }
    return "fillcolor=white";
  }

  static std::string escapeString(std::string String) {
    std::string Escaped;

    for (std::string::iterator SI = String.begin(), SE = String.end();
         SI != SE; ++SI) {

      if (*SI == '"')
        Escaped += '\\';

      Escaped += *SI;
    }
    return Escaped;
  }

  // Print the cluster of the subregions. This groups the single basic blocks
  // and adds a different background color for each group.
  static void printRegionCluster(const ScopDetection *SD, const Region *R,
                                 raw_ostream &O, unsigned depth = 0) {
    O.indent(2 * depth) << "subgraph cluster_" << static_cast<const void*>(R)
      << " {\n";
    std::string ErrorMessage = SD->regionIsInvalidBecause(R);
    ErrorMessage = escapeString(ErrorMessage);
    O.indent(2 * (depth + 1)) << "label = \"" << ErrorMessage << "\";\n";

    if (SD->isMaxRegionInScop(*R)) {
      O.indent(2 * (depth + 1)) << "style = filled;\n";

      // Set color to green.
      O.indent(2 * (depth + 1)) << "color = 3";
    } else {
      O.indent(2 * (depth + 1)) << "style = solid;\n";

      int color = (R->getDepth() * 2 % 12) + 1;

      // We do not want green again.
      if (color == 3)
        color = 6;

      O.indent(2 * (depth + 1)) << "color = "
      << color << "\n";
    }

    for (Region::const_iterator RI = R->begin(), RE = R->end(); RI != RE; ++RI)
      printRegionCluster(SD, *RI, O, depth + 1);

    RegionInfo *RI = R->getRegionInfo();

    for (Region::const_block_iterator BI = R->block_begin(),
         BE = R->block_end(); BI != BE; ++BI)
      if (RI->getRegionFor(*BI) == R)
        O.indent(2 * (depth + 1)) << "Node"
          << static_cast<const void*>(RI->getTopLevelRegion()->getBBNode(*BI))
          << ";\n";

    O.indent(2 * depth) << "}\n";
  }
  static void addCustomGraphFeatures(const ScopDetection *SD,
                                     GraphWriter<ScopDetection*> &GW) {
    raw_ostream &O = GW.getOStream();
    O << "\tcolorscheme = \"paired12\"\n";
    printRegionCluster(SD, SD->getRI()->getTopLevelRegion(), O, 4);
  }
};

}  //end namespace llvm

struct ScopViewer
  : public DOTGraphTraitsViewer<ScopDetection, false> {
  static char ID;
  ScopViewer() : DOTGraphTraitsViewer<ScopDetection, false>("scops", ID){}
};
char ScopViewer::ID = 0;

struct ScopOnlyViewer
  : public DOTGraphTraitsViewer<ScopDetection, true> {
  static char ID;
  ScopOnlyViewer()
    : DOTGraphTraitsViewer<ScopDetection, true>("scopsonly", ID){}
};
char ScopOnlyViewer::ID = 0;

struct ScopPrinter
  : public DOTGraphTraitsPrinter<ScopDetection, false> {
  static char ID;
  ScopPrinter() :
    DOTGraphTraitsPrinter<ScopDetection, false>("scops", ID) {}
};
char ScopPrinter::ID = 0;

struct ScopOnlyPrinter
  : public DOTGraphTraitsPrinter<ScopDetection, true> {
  static char ID;
  ScopOnlyPrinter() :
    DOTGraphTraitsPrinter<ScopDetection, true>("scopsonly", ID) {}
};
char ScopOnlyPrinter::ID = 0;

static RegisterPass<ScopViewer>
X("view-scops","Polly - View Scops of function");

static RegisterPass<ScopOnlyViewer>
Y("view-scops-only",
  "Polly - View Scops of function (with no function bodies)");

static RegisterPass<ScopPrinter>
M("dot-scops", "Polly - Print Scops of function");

static RegisterPass<ScopOnlyPrinter>
N("dot-scops-only",
  "Polly - Print Scops of function (with no function bodies)");

Pass *polly::createDOTViewerPass() {
  return new ScopViewer();
}

Pass *polly::createDOTOnlyViewerPass() {
  return new ScopOnlyViewer();
}

Pass *polly::createDOTPrinterPass() {
  return new ScopPrinter();
}

Pass *polly::createDOTOnlyPrinterPass() {
  return new ScopOnlyPrinter();
}
