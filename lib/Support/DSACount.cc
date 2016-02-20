#include "seahorn/Support/DSACount.hh"

#include "llvm/IR/IntrinsicInst.h"
#include "llvm/IR/InstIterator.h"
#include "llvm/Support/CommandLine.h"

static llvm::cl::opt<unsigned int>
DSNodeThreshold("dsa-count-threshold",
    llvm::cl::desc ("Only show DSA node stats if its memory accesses exceed the threshold"),
    llvm::cl::init (0),
    llvm::cl::Hidden);

#ifdef HAVE_DSA
#include "boost/range.hpp"
#include "avy/AvyDebug.h"

namespace seahorn
{
  using namespace llvm;

  
  DSACount::DSACount () : 
      llvm::ModulePass (ID), 
      m_dsa (nullptr), m_gDsg (nullptr), m_id (1) { }

    
  unsigned DSACount::getId (const DSNode* n) const {
     auto it = m_nodes.find (n);
     assert (it != m_nodes.end ());
     return it->second.m_id;
  }

  bool DSACount::isAccessed (const DSNode* n) const {
     auto it = m_nodes.find (n);
     assert (it != m_nodes.end ());
     return it->second.m_accesses > 0;
  }

  // Print statistics 
  void DSACount::write (llvm::raw_ostream& o) {
    
      std::vector<WrapperDSNode> nodes_vector;
      nodes_vector.reserve (m_nodes.size ());
      for (auto &kv: m_nodes) { nodes_vector.push_back (kv.second); }
      std::sort (nodes_vector.begin (), nodes_vector.end ());

      errs () << " ========== DSACount  ==========\n";

      unsigned num_accessed_nodes = 0;
      for (auto &n: nodes_vector) {
        if (n.m_accesses > 0)
          num_accessed_nodes++;
      }
      errs () << nodes_vector.size () << " Total number of DS nodes\n";     
      errs () << num_accessed_nodes   << " Total number of read/written DS nodes\n";     
      
      for (auto &n: nodes_vector) {
        if (n.m_accesses > DSNodeThreshold) {
          errs () << "  Node " << n.m_id << ": "  
                  << n.m_accesses << " memory accesses\n";
          LOG("dsa-count", n.m_n->dump ();); 
        }
        // if (n.m_n->getNumReferrers() > DSNodeThreshold) {
        //   if (!has_referrers (n.m_n)) continue;
        //   const ValueSet& referrers = get_referrers (n.m_n);
        //   LOG("dsa-count",
        //         errs () << "Node " << n.m_id << ": "  
        //                 << referrers.size () << " referrers\n";);
        //   LOG("dsa-count", n.m_n->dump (); 
        //        errs () << "\tReferrers={";
        //          for (auto const& r : referrers) {
        //             if (r->hasName ())
        //               errs () << r->getName ();
        //             else 
        //               errs () << *r; 
        //             errs () << ";";
        //          }
        //          errs () << "}\n";);
        // }
      }
  }        


  bool DSACount::runOnModule (llvm::Module &M) {  

      m_dsa = &getAnalysis<SteensgaardDataStructures> ();
      m_gDsg = m_dsa->getGlobalsGraph ();

      // Assign a numeric id to each DSNode and gather the number of
      // referrers

      DSScalarMap &SM = m_gDsg->getScalarMap ();
      for (const Value*v : boost::make_iterator_range (SM.global_begin (), 
                                                       SM.global_end ())){
        const DSNodeHandle lN = SM[v];
        const DSNode* n = lN.getNode ();
        if (n) {
          add_node (n);
          insert_referrers_map  (n, v);
        }
      }

      for (auto &F: M) { 
        if (F.isDeclaration ()) continue;

        DSGraph* dsg = m_dsa->getDSGraph (F);
        if (!dsg) continue;
        
        DSScalarMap &SM = dsg->getScalarMap ();
        for (auto const &kv : boost::make_iterator_range (SM.begin (), 
                                                          SM.end ())){
          const Value* v = kv.first;
          const DSNode* n = kv.second.getNode ();
          if (n) {
            add_node (n);
            insert_referrers_map  (n, v);
          }
        }     
      }

      // Count number of accesses to each DSNode
      for (Function &F : M) {
        if (F.isDeclaration ()) continue;

        DSGraph* dsg = m_dsa->getDSGraph (F);
        if (!dsg) continue;
        DSGraph* gDsg = dsg->getGlobalsGraph (); 
             
        for (inst_iterator i = inst_begin(F), e = inst_end(F); i != e; ++i)  {
          Instruction *I = &*i;
          if (LoadInst *LI = dyn_cast<LoadInst>(I)) {
            Value* ptr = LI->getPointerOperand ();
            const DSNode* n = dsg->getNodeForValue (ptr).getNode ();
            if (!n) n = gDsg->getNodeForValue (ptr).getNode ();
            if (n) {
              auto it = m_nodes.find (n);
              if (it != m_nodes.end ())
                it->second.m_accesses++;
            }            
          }
          else if (StoreInst *SI = dyn_cast<StoreInst>(I)) {
            Value* ptr = SI->getPointerOperand ();
            const DSNode* n = dsg->getNodeForValue (ptr).getNode ();
            if (!n) n = gDsg->getNodeForValue (ptr).getNode ();
            if (n) {
              auto it = m_nodes.find (n);
              if (it != m_nodes.end ())
                it->second.m_accesses++;
            }            
          }
          else if (MemTransferInst *MTI = dyn_cast<MemTransferInst>(I)) {
            Value* ptr = MTI->getDest ();
            // Assume both dest and src should be in the same alias class
            // so we just check for one.
            const DSNode* n = dsg->getNodeForValue (ptr).getNode ();
            if (!n) n = gDsg->getNodeForValue (ptr).getNode ();
            if (n) {
              auto it = m_nodes.find (n);
              if (it != m_nodes.end ())
                it->second.m_accesses+=2;
            }            
          } else if (MemSetInst *MSI = dyn_cast<MemSetInst>(I)) {
            Value* ptr = MSI->getDest ();
            const DSNode* n = dsg->getNodeForValue (ptr).getNode ();
            if (!n) n = gDsg->getNodeForValue (ptr).getNode ();
            if (n) {
              auto it = m_nodes.find (n);
              if (it != m_nodes.end ())
                it->second.m_accesses++;
            }            
          }   
        }
      }
      
      return false;
  }

  void DSACount::getAnalysisUsage (llvm::AnalysisUsage &AU) const {
    AU.setPreservesAll ();
    AU.addRequiredTransitive<llvm::SteensgaardDataStructures> ();
  }

} // end namespace
#endif

namespace seahorn{
 
  char DSACount::ID = 0;

  llvm::Pass* createDSACountPass () { return new DSACount (); }

  static llvm::RegisterPass<DSACount> 
  X ("dsa-count", "Count DSA Nodes");

} 

