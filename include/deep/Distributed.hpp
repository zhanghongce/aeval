#ifndef DISTRIBUTED_HPP__
#define DISTRIBUTED_HPP__

#include <boost/serialization/utility.hpp>
#include <boost/serialization/vector.hpp>
#include <boost/serialization/shared_ptr.hpp>
#include <boost/serialization/unique_ptr.hpp>
#include <boost/mpi.hpp>
#include "LinCom.hpp"

using namespace ufo;
using namespace std;

#define MSG_TAG_NORMAL 1

enum WorkerResultKind: int {
  WorkerResultKindGarbage,
  WorkerResultKindFailure,
  WorkerResultKindLemma,
  WorkerResultKindDone,
  WorkerResultKindFoundInvariants
};

struct StartIterMsg {
  bool shouldStop;
  unsigned int globalIter;
  unsigned long newLemmaCnt;
};

struct WorkerResult {
  WorkerResultKind kind;
  unsigned declIdx;  // index of `disj` home LAfactory
  std::unique_ptr<LAdisj> disj;
};

template<class Archive>
void serialize(Archive& ar, StartIterMsg& sj, const unsigned int version)
{
  ar & sj.shouldStop;
  ar & sj.globalIter;
  ar & sj.newLemmaCnt;
}

template<class Archive>
void serialize(Archive& ar, WorkerResult& pr, const unsigned int version)
{
  ar & pr.kind;
  ar & pr.declIdx;
  ar & pr.disj;
}


// point-to-point MPI send to all other workers; blocks for send completions
template<typename T>
void sendToOthers(boost::mpi::communicator world, int tag, const T &t)
{
  vector<boost::mpi::request> completionReqs(world.size() - 1);
  for (size_t i = 0; i < world.size(); i++) {
    if (i != world.rank()) {
      boost::mpi::request r = world.isend(i, tag, t);
      completionReqs.push_back(r);
    }
  }
  boost::mpi::wait_all(completionReqs.begin(), completionReqs.end());
}

// everything the worker needs to pop a job
struct ReceivedWorkerJob {
  unsigned globalIter;
  vector<std::pair<unsigned, LAdisj>> newLemmas;
  vector<LAdisj> curCandDisjs;
  ReceivedWorkerJob(unsigned i) : globalIter(i), newLemmas(), curCandDisjs() {}
  bool shouldStop() { return curCandDisjs.size() == 0; }
};

ReceivedWorkerJob recvWorkerJob(boost::mpi::communicator world, unsigned invNum) {
  // Receive either a job start or stop message
  StartIterMsg startMsg;
  world.recv(0, MSG_TAG_NORMAL, startMsg);
  if (startMsg.shouldStop)
    return ReceivedWorkerJob(startMsg.globalIter);

  // Recv new lemmas, if any
  ReceivedWorkerJob ret(startMsg.globalIter);
  for (size_t i = 0; i < startMsg.newLemmaCnt; i++) {
    std::unique_ptr<WorkerResult> lemmaResult;
    world.recv(0, MSG_TAG_NORMAL, lemmaResult);
    assert(lemmaResult->kind == WorkerResultKindLemma);
    ret.newLemmas.emplace_back(lemmaResult->declIdx, *lemmaResult->disj);
  }

  // Recv candidates, filling curCandidates÷
  for (size_t i = 0; i < invNum; i++) {
    ret.curCandDisjs.emplace_back();
    LAdisj& disj = ret.curCandDisjs.back();
    world.recv(0, MSG_TAG_NORMAL, disj);
  }
  return ret;
}

#endif
