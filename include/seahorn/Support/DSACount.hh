#ifndef __DSA_COUNT__HH__
#define __DSA_COUNT__HH__

#include "llvm/Pass.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Function.h"

#include "seahorn/config.h"

#ifndef HAVE_DSA
namespace seahorn
{
  using namespace llvm;

  class DSACount : public llvm::ModulePass {
   public:
    static char ID;
    DSACount () : llvm::ModulePass (ID){ }
    virtual bool runOnModule (llvm::Module &M) { return false;}
    virtual bool runOnFunction (Function &F) { return false; }
    virtual void getAnalysisUsage (llvm::AnalysisUsage &AU) const{ AU.setPreservesAll ();}
    virtual const char* getPassName () const {return "DSACount";}
    void write (llvm::raw_ostream& o);
  };
}
#else
// Real implementation starts there
#include "dsa/Steensgaard.hh"
#include "dsa/DataStructure.h"
#include "dsa/DSGraph.h"
#include "dsa/DSNode.h"
#include "llvm/ADT/DenseMap.h"
#include "llvm/Support/Debug.h"

namespace seahorn
{
  using namespace llvm;
  
  class DSACount : public llvm::ModulePass
  {
    typedef std::set <const Value*> ValueSet;

    struct WrapperDSNode {
      unsigned m_id;
      const DSNode* m_n;
      unsigned m_accesses;

      WrapperDSNode (unsigned id, const DSNode* n): 
          m_id (id), m_n (n), m_accesses (0) { }

      bool operator==(const WrapperDSNode& o) const {
         return m_n == o.m_n;
      }

      // Sort by id!
      bool operator<(const WrapperDSNode& o) const {
        return m_id < o.m_id;
      }
    };

    DataStructures *m_dsa;
    DSGraph* m_gDsg;
    DenseMap<const DSNode*, WrapperDSNode> m_nodes;
    DenseMap<const DSNode*, ValueSet> m_referrers_map;
    unsigned m_id;

    unsigned add_node (const DSNode* n) {
      auto it = m_nodes.find (n);
      if (it == m_nodes.end ()) {
        unsigned id = m_id++;
        m_nodes.insert (std::make_pair(n, WrapperDSNode (id, n)));
        return id;
      }
      else 
        return it->second.m_id;
    }

    void insert_referrers_map (const DSNode* n, const Value* v) {
      auto it = m_referrers_map.find (n);
      if (it != m_referrers_map.end ())
        it->second.insert (v);
      else {
        ValueSet s;
        s.insert (v);
        m_referrers_map.insert (std::make_pair (n, s));
      }
    }

    bool has_referrers (const DSNode* n) const {
      return m_referrers_map.find (n) != m_referrers_map.end ();
    }

    const ValueSet& get_referrers (const DSNode* n) const {
      auto it = m_referrers_map.find (n);
      assert (has_referrers (n));
      return it->second;
    }

  public:
 
    static char ID;
    
    DSACount ();
    unsigned getId (const DSNode* n) const;
    DataStructures * getDSA () { return m_dsa; }
    virtual bool runOnModule (llvm::Module &M);
    virtual void getAnalysisUsage (llvm::AnalysisUsage &AU) const;
    virtual const char* getPassName () const {return "DSACount";}
    void write (llvm::raw_ostream& o);

  };
}
#endif 
#endif
