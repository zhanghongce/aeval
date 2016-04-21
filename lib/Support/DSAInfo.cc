#include "seahorn/Support/DSAInfo.hh"
#include "llvm/Support/CommandLine.h"

static llvm::cl::opt<bool>
DSAInfoPrint("dsa-info",
    llvm::cl::desc ("Print all DSA and allocation information"),
    llvm::cl::init (false),
    llvm::cl::Hidden);

#ifdef HAVE_DSA
#include "llvm/IR/IntrinsicInst.h"
#include "llvm/IR/InstIterator.h"
#include "llvm/Target/TargetLibraryInfo.h"
#include "llvm/Analysis/MemoryBuiltins.h"

#include "boost/range.hpp"
#include "avy/AvyDebug.h"

namespace seahorn
{
  using namespace llvm;

  inline bool IsStaticallyKnown (const DataLayout* dl, 
                                 const TargetLibraryInfo* tli,
                                 const Value* V) {
    uint64_t Size;
    if (getObjectSize (V, Size, dl, tli, true))
      return (Size > 0);
    
    return false; 
  }
   
  inline void countAccesses (const DataLayout* dl,
                             const TargetLibraryInfo* tli,
                             DSGraph* dsg, DSGraph* gDsg,
                             DenseMap<const DSNode*, DSAInfo::WrapperDSNode>& nodes,
                             Value* V) {    
    const DSNode* n = dsg->getNodeForValue (V).getNode ();
    if (!n) n = gDsg->getNodeForValue (V).getNode ();
    if (!n) return;

    auto It = nodes.find (n);
    if (It != nodes.end () && !IsStaticallyKnown (dl, tli, V))
      It->second.m_accesses++;
  }        

  DSAInfo::DSAInfo () : 
      llvm::ModulePass (ID), 
      m_dsa (nullptr), m_gDsg (nullptr) { }

    
  unsigned int DSAInfo::getDSNodeID (const DSNode* n) const {
     auto it = m_nodes.find (n);
     assert (it != m_nodes.end ());
     return it->second.m_id;
  }

  bool DSAInfo::isAccessed (const DSNode* n) const {
     auto it = m_nodes.find (n);
     assert (it != m_nodes.end ());
     return it->second.m_accesses > 0;
  }

  // Print statistics 
  void DSAInfo::WriteDSInfo (llvm::raw_ostream& o) {

      o << " ========== DSAInfo  ==========\n";
    
      std::vector<WrapperDSNode> nodes_vector;
      nodes_vector.reserve (m_nodes.size ());
      for (auto &kv: m_nodes) { 
        if (kv.second.m_accesses > 0)
          nodes_vector.push_back (kv.second); 
      }

      //o << m_nodes.size () 
      //  << " Total number of DS nodes.\n";     

      // -- Some DSNodes are never read or written because after they
      //    are created they are only passed to external calls.
      o << nodes_vector.size ()  
        << " Total number of accessed (read/written) DS nodes.\n";     

      unsigned int total_accesses = 0;
      for (auto &n: nodes_vector) 
        total_accesses += n.m_accesses;

      o << total_accesses
        << " Total number of accessed DS nodes.\n";     

      {  //  Print a summary of accesses
        unsigned int sum_size = 5;
        o << "Summary of the " << sum_size  << " most accessed DS nodes:\n";
        std::vector<WrapperDSNode> tmp_nodes_vector (nodes_vector);
        std::sort (tmp_nodes_vector.begin (), tmp_nodes_vector.end (),
                   [](WrapperDSNode n1, WrapperDSNode n2){
                     return (n1.m_accesses > n2.m_accesses);
                   });
        if (total_accesses > 0) {
          for (auto &n: tmp_nodes_vector) {
          if (sum_size <= 0) break;
          sum_size--;
          if (n.m_accesses == 0) break;
          o << "  [Node Id " << n.m_id  << "] " 
            << (int) (n.m_accesses * 100 / total_accesses) 
            << "% of total memory accesses\n" ;
          }
          o << "  ...\n";
        }
      }

      if (!DSAInfoPrint) return;

      o << "Detailed information about all DS nodes\n";
      std::sort (nodes_vector.begin (), nodes_vector.end (),
                 [](WrapperDSNode n1, WrapperDSNode n2){
                   return (n1.m_id < n2.m_id);
                 });
      
      for (auto &n: nodes_vector) {
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

        // --- print type information
        DSNode * nn = const_cast<DSNode*> (n.m_n);
        LOG("dsa-info", errs () << "     ";  nn->dump ());
        if (nn->hasNoType ())
          o << "  Types={untyped";
        else {
          o << "  Types={";
          DSNode::type_iterator ii = nn->type_begin(), ie = nn->type_end();
          DSNode::type_iterator jj = ii;
          if (++jj == ie) {
            auto ty_set_ptr = ii->second;
            if (ty_set_ptr->size () == 1) {
              o << **(ty_set_ptr->begin ());
            } else {
              svset<Type*>::const_iterator ki = (*ty_set_ptr).begin (), ke = (*ty_set_ptr).end ();
              o << "[";
              for (; ki != ke; ) { 
                o << **ki;
                ++ki;
                if (ki != ke) o << " | ";
              }
              o << "]";
            }
          }
          else {
            o << "struct {";
            while (ii != ie) {
              o << ii->first << ":";
              if (!ii->second) { 
                o << "untyped";
              } else {
                auto ty_set_ptr = ii->second;
                if (ty_set_ptr->size () == 1) {
                  o << **(ty_set_ptr->begin ());
                } else {
                  svset<Type*>::const_iterator ki = ty_set_ptr->begin (), ke = ty_set_ptr->end ();
                  o << "[";
                  for (; ki != ke; ) { 
                    o << **ki;
                    ++ki;
                    if (ki != ke) o << " | ";
                  }
                  o << "]";
                }
              }
              ++ii;
              if (ii != ie)
                o << ",";   
            }
            o << "}*";
          }
        }
        // --- print llvm values referring to the DSNodes
        o << "}\n";
        LOG("dsa-info", 
            o << "  Referrers={\n";
            for (auto const& r : referrers) {
              if (r->hasName ()) o << "    " << r->getName ();
              else o << "  " << *r;  
              o << "\n";
            }
            o << "  }\n");
      }
  }        

  void DSAInfo::findDSNodeForValue (const Value* v, std::set<unsigned int>& nodes) {
    for (auto &p: m_referrers_map) {
      const ValueSet& referrers = p.second;
      if (referrers.count (v) > 0)
        if (getDSNodeID (p.first) > 0)
          nodes.insert( getDSNodeID (p.first));
    }
  }

  void DSAInfo::WriteAllocaInfo (llvm::raw_ostream& o) {
    o << " ========== Allocation sites  ==========\n";

    // -- total number of allocations in the program
    // o << m_alloc_sites.right.size ()  
    //   << " Total number of allocation sites.\n";     

    unsigned actual_alloc_sites = 0;
    for (auto p: m_alloc_sites.right) {
      std::set<unsigned int> nodes;
      findDSNodeForValue (p.second, nodes);
      if (nodes.empty ()) continue;
      actual_alloc_sites++;
    }      

    // -- total number of allocations that belong to a DSNode that is
    //    ever read or written. Some DSNodes are never read or written
    //    because after they are created they are only passed to
    //    external calls.
    o << actual_alloc_sites
      << " Total number of allocation sites from an accessed DSNode.\n";     
    
    if (!DSAInfoPrint) return;

    std::set <unsigned int> seen;
    for (auto p: m_alloc_sites.right) {
      std::set<unsigned int> nodes;
      findDSNodeForValue (p.second, nodes);
      // if not DSNode found then the alloca belongs to a DSNode to
      // which nobody reads/write from/to.
      if (nodes.empty ()) continue;

      // -- Sanity check: an alloca site belongs only to one DSNode
      if (nodes.size () > 1) {
        errs () << "DSAInfo: alloca site " << p.first 
                << " belongs to multiple DSNodes {";
        for (auto NodeId: nodes) o << NodeId << ","; 
        errs () << "}\n";
        continue;
      }

      o << "  [Alloc site Id " << p.first << " DSNode Id " << *(nodes.begin ())
        << "]  " << *p.second  << "\n";
      seen.insert (*(nodes.begin ()));
    }

    // -- Sanity check: each DSNode has an allocation site
    for (auto& kv: m_nodes) {
      unsigned int NodeID = kv.second.m_id;
      if (seen.count (NodeID) > 0) continue;
      // An ID can be 0 (undefined) if the node did not have any
      // access
      if (NodeID > 0) {
        errs () << "DSAInfo: DSNode ID " << NodeID << " has no allocation site\n";
        LOG ("dsa-info", 
             const ValueSet& referrers = get_referrers (kv.second.m_n);
             for (auto const& r : referrers) {
               if (r->hasName ())
                 o << "\t  " << r->getName ();
               else 
                 o << "\t" << *r; 
               o << "\n";
             });
        
      }
    }
  }

  bool DSAInfo::runOnModule (llvm::Module &M) {  


      m_dsa = &getAnalysis<SteensgaardDataStructures> ();
      m_gDsg = m_dsa->getGlobalsGraph ();

      //errs () << M << "\n";

      // Collect all referrers per DSNode
      DSScalarMap &SM = m_gDsg->getScalarMap ();
      for (const Value*v : boost::make_iterator_range (SM.global_begin (), 
                                                       SM.global_end ())){
        const DSNodeHandle lN = SM[v];
        if (lN.isForwarding ()) continue;

        if (const DSNode* n = lN.getNode ()) {
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
          DSNodeHandle lN = kv.second;
          if (lN.isForwarding ()) continue;

          if (const DSNode* n = lN.getNode ()) {
            add_node (n);
            insert_referrers_map  (n, v);
          }
        }     
      }

      const TargetLibraryInfo * tli = &getAnalysis<TargetLibraryInfo>();
      const DataLayout* dl = &getAnalysis<DataLayoutPass>().getDataLayout ();

      // Count number of reads and writes to each DSNode
      for (Function &F : M) {
        if (F.isDeclaration ()) continue;

        DSGraph* dsg = m_dsa->getDSGraph (F);
        if (!dsg) continue;
        DSGraph* gDsg = dsg->getGlobalsGraph (); 
             
        for (inst_iterator i = inst_begin(F), e = inst_end(F); i != e; ++i)  {
          Instruction *I = &*i;
          if (LoadInst *LI = dyn_cast<LoadInst>(I)) {
            countAccesses (dl, tli, dsg, gDsg, m_nodes, LI->getPointerOperand ());
          } else if (StoreInst *SI = dyn_cast<StoreInst>(I)) {
            countAccesses (dl, tli, dsg, gDsg, m_nodes, SI->getPointerOperand ());
          } else if (MemTransferInst *MTI = dyn_cast<MemTransferInst>(I)) {
            countAccesses (dl, tli, dsg, gDsg, m_nodes, MTI->getDest ());
            countAccesses (dl, tli, dsg, gDsg, m_nodes, MTI->getSource ());
          } else if (MemSetInst *MSI = dyn_cast<MemSetInst>(I)) {
            countAccesses (dl, tli, dsg, gDsg, m_nodes, MSI->getDest ());
          }   
        }
      }

      // figure out deterministically a representative name for each DSNode
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

      // Identify allocation sites and assign a numeric id to each one
      for (auto &GV: M.globals ()) {
        Type *Ty = cast<PointerType>(GV.getType())->getElementType();
        if (!Ty->isSized()) continue;
        if (!GV.hasInitializer()) continue;
        if (GV.hasSection()) {
          StringRef Section(GV.getSection());
          // Globals from llvm.metadata aren't emitted, do not instrument them.
          if (Section == "llvm.metadata") continue;
        }
        unsigned int alloc_site_id; 
        add_alloc_site (&GV, alloc_site_id);
      }
      
      for (auto &F: M) {
        for (inst_iterator i = inst_begin(F), e = inst_end(F); i != e; ++i) {      
          Instruction* I = &*i;
          if (AllocaInst* AI = dyn_cast<AllocaInst> (I)) {
            Type *Ty = AI->getAllocatedType();
            if (!Ty->isSized() || dl->getTypeAllocSize(Ty) <= 0) {
              errs () << "DSAInfo " << *AI 
                      << " will be ignored because it is not sized\n";
              continue;
            }
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


      WriteDSInfo (errs ());
      WriteAllocaInfo (errs ());

      return false;
  }

  void DSAInfo::getAnalysisUsage (llvm::AnalysisUsage &AU) const {
    AU.setPreservesAll ();
    AU.addRequiredTransitive<llvm::SteensgaardDataStructures> ();
    AU.addRequired<llvm::DataLayoutPass>();
    AU.addRequired<llvm::TargetLibraryInfo>();
  }

} // end namespace
#endif

namespace seahorn{
 
  char DSAInfo::ID = 0;

  llvm::Pass* createDSAInfoPass () { return new DSAInfo (); }

  static llvm::RegisterPass<DSAInfo> 
  X ("dsa-info", "Show information about DSA Nodes");

} 

