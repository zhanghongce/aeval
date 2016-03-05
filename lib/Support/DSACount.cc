#include "seahorn/Support/DSACount.hh"

#include "llvm/IR/IntrinsicInst.h"
#include "llvm/IR/InstIterator.h"
#include "llvm/Target/TargetLibraryInfo.h"
#include "llvm/Analysis/MemoryBuiltins.h"
#include "llvm/Support/CommandLine.h"

static llvm::cl::opt<unsigned int>
DSNodeThreshold("dsa-count-threshold",
    llvm::cl::desc ("Only show DSA node stats if its memory accesses exceed the threshold"),
    llvm::cl::init (0),
    llvm::cl::Hidden);

static llvm::cl::opt<bool>
OnlyArrayAlloca("dsa-count-only-array-alloca",
    llvm::cl::desc ("Only show alloca sites of array type"),
    llvm::cl::init (false),
    llvm::cl::Hidden);

static llvm::cl::opt<bool>
DSACountPrint("dsa-count-print-stats",
    llvm::cl::desc ("Print all DSA and allocation information"),
    llvm::cl::init (false),
    llvm::cl::Hidden);

#ifdef HAVE_DSA
#include "boost/range.hpp"
#include "avy/AvyDebug.h"

namespace seahorn
{
  using namespace llvm;

  
  DSACount::DSACount () : 
      llvm::ModulePass (ID), 
      m_dsa (nullptr), m_gDsg (nullptr) { }

    
  unsigned int DSACount::getDSNodeID (const DSNode* n) const {
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
  void DSACount::write_dsa_info (llvm::raw_ostream& o) {

      o << " ========== DSACount  ==========\n";
    
      std::vector<WrapperDSNode> nodes_vector;
      nodes_vector.reserve (m_nodes.size ());
      for (auto &kv: m_nodes) { 
        if (kv.second.m_accesses > 0)
          nodes_vector.push_back (kv.second); 
      }
      
      o << nodes_vector.size ()  
        << " Total number of read/written DS nodes\n";     

      std::sort (nodes_vector.begin (), nodes_vector.end (),
                 [](WrapperDSNode n1, WrapperDSNode n2){
                   return (n1.m_id < n2.m_id);
                 });
      
      for (auto &n: nodes_vector) {
        if (n.m_accesses > DSNodeThreshold) {
          if (!has_referrers (n.m_n)) continue;
          const ValueSet& referrers = get_referrers (n.m_n);
          o << "  [Node Id " << n.m_id  << "] ";

          if (n.m_rep_name != "") {
            if (n.m_n->getUniqueScalar ()) {
              o << " singleton={" << n.m_rep_name << "}";
            } else {
              o << " non-singleton={" << n.m_rep_name << ",...}";
            }
          }

          o << "  with " << n.m_accesses << " memory accesses \n";

          LOG("dsa-count", /*n.m_n->dump ();*/ 
              o << "\tReferrers={";
              for (auto const& r : referrers) {
                if (r->hasName ())
                  o << r->getName ();
                else 
                  o << *r; 
                o << ";";
              }
              o << "}\n";);
        }
      }
  }        

  // horribly expensive
  unsigned int DSACount::findDSNodeForValue (const Value* v) {
    for (auto &p: m_referrers_map) {
      for (auto &s: p.second) {
        if (v == s) {
          return getDSNodeID (p.first);
        }
      }
    }
    return 0;
  }

  void DSACount::write_alloca_info (llvm::raw_ostream& o) {
    o << " ========== Allocation sites  ==========\n";
    o << m_alloc_sites.right.size ()  
      << " Total number of allocation sites\n";     
    
    for (auto p: m_alloc_sites.right) {
      unsigned NodeId = findDSNodeForValue (p.second);
      o << "  [Alloc site Id " << p.first << " DSNode Id "; 
      if (NodeId == 0) o << " NOT FOUND";
      else o << NodeId;
      o <<  "]  " << *p.second  << "\n";
    }
  }

  bool DSACount::runOnModule (llvm::Module &M) {  

      m_dsa = &getAnalysis<SteensgaardDataStructures> ();
      m_gDsg = m_dsa->getGlobalsGraph ();

      // Collect all referrers per DSNode
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

      // figure out deterministically a representative name for each
      // DSNode
      for (auto &p: m_nodes) {
        WrapperDSNode& n = p.second;
        if (!has_referrers (n.m_n) || n.m_accesses == 0) continue;

        // we collect all referrers and sort by their names in order
        // to make sure that the representative is always
        // chosen deterministically.
        const ValueSet& referrers = get_referrers (n.m_n);
        std::vector<std::string> named_referrers;
        named_referrers.reserve (referrers.size ());
        for (auto &r: referrers) {
          if (r->hasName ()) {
            named_referrers.push_back (r->getName().str());
          } 
        }

        // if no named value we create a name from the unnamed values.
        if (named_referrers.empty ()) {
          std::string str("");
          raw_string_ostream str_os (str);
          for (auto &r: referrers) {
            if (!r->hasName ()) {
              // build a name from the unnamed value
              r->print (str_os); 
              std::string inst_name (str_os.str ());
              named_referrers.push_back (inst_name);
            }
          }
        }

        std::sort (named_referrers.begin (), named_referrers.end (),
                   [](std::string s1, std::string s2){
                     return (s1 < s2);
                   });

        if (!named_referrers.empty ()) // should not be empty
          n.m_rep_name = named_referrers [0];
        
      }

      // Try to assign deterministically a numeric id to each node
      std::vector<WrapperDSNode*> nodes_vector;
      nodes_vector.reserve (m_nodes.size ());
      for (auto &kv: m_nodes) { 
        if (kv.second.m_accesses > 0)
          nodes_vector.push_back (&(kv.second)); 
      }
      std::sort (nodes_vector.begin (), nodes_vector.end (),
                 [](WrapperDSNode* n1, WrapperDSNode* n2){
                   return ((n1->m_rep_name < n2->m_rep_name) ||
                           ((n1->m_rep_name == n2->m_rep_name) &&
                            (n1->m_accesses < n2->m_accesses)));
                 });
      unsigned id = 1;
      for (auto n: nodes_vector) n->m_id = id++;

      // Identify allocation sites and assign an identifier to each one

      const TargetLibraryInfo * tli = &getAnalysis<TargetLibraryInfo>();
      for (auto &F: M) {
        for (inst_iterator i = inst_begin(F), e = inst_end(F); i != e; ++i) {      
          Instruction* I = &*i;
          /// XXX: Global variables???
          if (AllocaInst* AI = dyn_cast<AllocaInst> (I)) {
            if (AI->getAllocatedType ()->isIntegerTy ())
              continue;
            if (AI->getAllocatedType ()->isFloatingPointTy ())
              continue;
            if (OnlyArrayAlloca && !AI->getAllocatedType ()->isArrayTy ())
              continue;
            
            unsigned int alloc_site_id; 
            add_alloc_site (AI, alloc_site_id);
          } else if (isAllocationFn (I, tli, true)) {
            Value *V = I;
            V = V->stripPointerCasts();
            unsigned int alloc_site_id; 
            add_alloc_site (V, alloc_site_id);
          }
        }
      }

      if (DSACountPrint) {
        write_dsa_info (errs ());
        write_alloca_info (errs ());
      }

      return false;
  }

  void DSACount::getAnalysisUsage (llvm::AnalysisUsage &AU) const {
    AU.setPreservesAll ();
    AU.addRequiredTransitive<llvm::SteensgaardDataStructures> ();
    AU.addRequired<llvm::TargetLibraryInfo>();
  }

} // end namespace
#endif

namespace seahorn{
 
  char DSACount::ID = 0;

  llvm::Pass* createDSACountPass () { return new DSACount (); }

  static llvm::RegisterPass<DSACount> 
  X ("dsa-count", "Count DSA Nodes");

} 

