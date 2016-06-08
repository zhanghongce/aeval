#include "llvm/IR/Instructions.h"
#include "llvm/IR/Dominators.h"
#include "llvm/Analysis/LoopPass.h"
#include "llvm/Analysis/LoopInfo.h"
#include "llvm/Analysis/LoopIterator.h"
//#include "llvm/Analysis/AssumptionCache.h"
//#include "llvm/Transforms/Utils/UnrollLoop.h"
#include "llvm/Transforms/Scalar.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/ADT/Statistic.h"

#include "llvm/Transforms/Utils/BasicBlockUtils.h"
#include "llvm/Transforms/Utils/Cloning.h"

#include "boost/range.hpp"
#include "avy/AvyDebug.h"

using namespace llvm;

#define DEBUG_TYPE "unfold-loop-for-dsa"

namespace seahorn {

  /* 
     Unfold the first iteration of a loop if it is useful for DSA.
     TODO: can be generalized to unfold N iterations.
   */
  class UnfoldLoopForDsa : public LoopPass 
  {

    bool ShouldLoopBeUnfolded (Loop* L);
    bool isSafeToUnfold (Loop* L);
    void RemapInstruction(Instruction *I, ValueToValueMapTy &VMap);
    bool OneUnfoldLoop (Loop* L);

    LoopInfo *LI;
    
   public:

    static char ID;
    
    UnfoldLoopForDsa (): LoopPass (ID), LI (nullptr) { }

    bool runOnLoop (Loop *L, LPPassManager &LPM) override
    {
      LI = &getAnalysis<LoopInfo>();      
      if (ShouldLoopBeUnfolded (L)) {
        return OneUnfoldLoop (L);
      }
      return false;
    }

    /// This transformation requires natural loop information &
    /// requires that loop preheaders be inserted into the CFG...
    /// It also requires LCSSA.
    void getAnalysisUsage (AnalysisUsage &AU) const override {
      //AU.addRequired<AssumptionCacheTracker>();
      //AU.addPreserved<DominatorTreeWrapperPass>();

      // XXX: I believe LoopInfo and LoopSimplify is preserved since
      // we do not add/remove loops and although we modify a bit the
      // loops they are kept in natural form after the unfolding.
      AU.addRequired<LoopInfo>();
      AU.addPreserved<LoopInfo>();
      AU.addRequiredID(LoopSimplifyID);
      AU.addPreservedID(LoopSimplifyID);
      AU.addRequiredID(LCSSAID);
      // XXX: FIXME I think LCSSA is not preserved
      //AU.addPreservedID(LCSSAID);
    }
    
    virtual const char *getPassName () const 
    {return "Unfold first iteration of loops if useful for DSA";}
    
  };

  // This is just an heuristic to decide whether the first iteration
  // of a loop should be unfolded or not.
  bool UnfoldLoopForDsa::ShouldLoopBeUnfolded (Loop* TheLoop) {
    // For each block in the loop.
    for (Loop::block_iterator bb = TheLoop->block_begin(),
             be = TheLoop->block_end(); bb != be; ++bb) {
      BasicBlock *BB = *bb;
      // Scan the instructions in the block
      for (auto &I: *BB) {
        if (PHINode *Phi = dyn_cast<PHINode>(&I)) {
          // Scan all the incoming values of the PHI node
          GetElementPtrInst *GEP = nullptr;
          for (unsigned i=0, e = Phi->getNumIncomingValues(); i!=e; ++i) {
            // Heuristics: if a PHI node has two or more *different*
            // incoming GEP instructions then we pick the loop for
            // unrolling
            Value *V = Phi->getIncomingValue(i);
            if (V->getType()->isPointerTy()) {
              V = V->stripPointerCasts();
              if (GetElementPtrInst* GEPV = dyn_cast<GetElementPtrInst>(V)) {
                if (!GEP)  {
                  GEP = GEPV;
                  continue;
                  } else if (GEP == GEPV) {
                  continue;
                } else {
                  LOG ("unfold-loop-for-dsa", 
                       errs () << *Phi 
                       << " has two incoming values from different GEPs\n");
                  return true;
                }
              }
            }
          }
        }
      }
    }
    return false;
  }

  void UnfoldLoopForDsa::RemapInstruction(Instruction *I, ValueToValueMapTy &VMap) {
    for (unsigned op = 0, E = I->getNumOperands(); op != E; ++op) {
      Value *Op = I->getOperand(op);
      ValueToValueMapTy::iterator It = VMap.find(Op);
      if (It != VMap.end())
          I->setOperand(op, It->second);
    }
    if (PHINode *PN = dyn_cast<PHINode>(I)) {
      for (unsigned i = 0, e = PN->getNumIncomingValues(); i != e; ++i) {
        ValueToValueMapTy::iterator It = VMap.find(PN->getIncomingBlock(i));
        if (It != VMap.end())
          PN->setIncomingBlock(i, cast<BasicBlock>(It->second));
      }
    }
  }

  bool UnfoldLoopForDsa::isSafeToUnfold (Loop* L){
    if (!(L->getLoopPreheader())) {
      LOG("unfold-loop-for-dsa", 
          errs() << "  Can't unroll; loop preheader-insertion failed.\n");
      return false;
    }
    
    BasicBlock *LatchBlock = L->getLoopLatch();
    if (!LatchBlock) {
      LOG("unfold-loop-for-dsa", 
          errs() << "  Can't unroll; loop exit-block-insertion failed.\n");
      return false;
    }
    
    // Loops with indirectbr cannot be cloned.
    if (!L->isSafeToClone()) {
      LOG("unfold-loop-for-dsa", 
          errs() << "  Can't unroll; Loop body cannot be cloned.\n");
      return false;
    }
    
    BasicBlock *Header = L->getHeader();
    BranchInst *BI = dyn_cast<BranchInst>(LatchBlock->getTerminator());
    
    if (!BI || BI->isUnconditional()) {
      LOG("unfold-loop-for-dsa", errs() <<
          "  Can't unroll; loop not terminated by a conditional branch.\n");
      return false;
    }

    if (Header->hasAddressTaken()) {
      LOG("unfold-loop-for-dsa", errs() <<
          "  Won't unroll loop: address of header block is taken.\n");
      return false;
    }      
    return true;
  }

  /*
    A loop of this form:
    
    do { 
      B
    } while (C);
    
    is transformed into
    
    B;
    if (C) {
      do { 
       B
      } while (C);
    }
    
  */
    
  bool UnfoldLoopForDsa::OneUnfoldLoop (Loop* L) {
    
    if (!isSafeToUnfold(L)) return false;
    
    BasicBlock* Preheader = L->getLoopPreheader();      
    BasicBlock *Header = L->getHeader();
    BasicBlock *LatchBlock = L->getLoopLatch();      
    
    assert(Preheader);
    assert(Header);
    assert(LatchBlock);
    
    BranchInst *BI = dyn_cast<BranchInst>(LatchBlock->getTerminator());
    
    std::vector<PHINode*> OrigPHINode;
    for (BasicBlock::iterator I = Header->begin(); isa<PHINode>(I); ++I) {
      OrigPHINode.push_back(cast<PHINode>(I));
    }
    
    // The current on-the-fly SSA update requires blocks to be processed in
    // reverse postorder so that LastValueMap contains the correct value at each exit.
    LoopBlocksDFS DFS(L);
    DFS.perform(LI);
    
    // Stash the DFS iterators before adding blocks to the loop.
    LoopBlocksDFS::RPOIterator BlockBegin = DFS.beginRPO();
    LoopBlocksDFS::RPOIterator BlockEnd = DFS.endRPO();
    
    BasicBlock* UnfoldedHeader = nullptr;
    BasicBlock* UnfoldedLatchBlock = nullptr;
    
    std::vector<BasicBlock*> NewBlocks;
    ValueToValueMapTy VMap;
    Function *F = Header->getParent();
    for (LoopBlocksDFS::RPOIterator BB = BlockBegin; BB != BlockEnd; ++BB) {
      BasicBlock *New = CloneBasicBlock(*BB, VMap, ".1");
      VMap[*BB] = New;
      F->getBasicBlockList().push_back(New);
      if (*BB == Header) UnfoldedHeader = New;
      if (*BB == LatchBlock) UnfoldedLatchBlock = New;
      NewBlocks.push_back(New);        
    } 
    
    assert (UnfoldedHeader);
    assert (UnfoldedLatchBlock);
    
    // Remap all instructions with new map
    for (unsigned i = 0; i < NewBlocks.size(); ++i)
      for (BasicBlock::iterator I = NewBlocks[i]->begin(),
               E = NewBlocks[i]->end(); I != E; ++I)
        RemapInstruction(I, VMap);
    
    // remove phi nodes in the new header
    for (unsigned i = 0, e = OrigPHINode.size(); i != e; ++i) {
      PHINode *PN = OrigPHINode[i];
      PHINode *NewPHI = cast<PHINode>(VMap[PN]);
      Value* IncVal = PN->getIncomingValueForBlock(Preheader);
      NewPHI->replaceAllUsesWith(IncVal);
      PN->removeIncomingValue(Preheader);
      
      // connect phi node of the original header with incoming value
      // from the new latch block.
      PN->addIncoming(NewPHI->getIncomingValueForBlock(UnfoldedLatchBlock), 
                      UnfoldedLatchBlock);
      UnfoldedHeader->getInstList().erase(NewPHI);
    }
    
    // connect preheader with new header
    BranchInst *Term = cast<BranchInst>(Preheader->getTerminator());
    assert(Term->isUnconditional ());
    Term->setSuccessor(0, UnfoldedHeader);
    
    BranchInst *UnfoldedBI = dyn_cast<BranchInst>(UnfoldedLatchBlock->getTerminator());
    // finish the connection between new latch block and the
    // original header
    if (L->contains(BI->getSuccessor(0))) {
      UnfoldedBI->setSuccessor(0, BI->getSuccessor(0));
    } else if (L->contains(BI->getSuccessor(1))) {
      UnfoldedBI->setSuccessor(1, BI->getSuccessor(1));
    }
    return true;
  }

  char UnfoldLoopForDsa::ID = 0;

  Pass *createUnfoldLoopForDsaPass () 
  {return new UnfoldLoopForDsa ();} 


} // end namespace seahorn

static llvm::RegisterPass<seahorn::UnfoldLoopForDsa> 
X ("unfold-loop-dsa", 
   "Unfold a loop iteration if useful for DSA", false, false);
