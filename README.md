FreqHorn
========

Parallel satisfiability solver for constrained Horn clauses (CHC) based on the Expression library of <a href="http://seahorn.github.io/">SeaHorn</a> and the <a href="https://github.com/Z3Prover/z3">Z3</a> SMT solver. It combines probabilistic and syntax-guided methods to sample candidate invariants and checks their inductiveness / safety. Find more details at the FMCAD'17 <a href="http://www.cs.princeton.edu/~grigoryf/freqhorn.pdf">paper</a> and <a href="http://www.cs.princeton.edu/~grigoryf/freqhorn_slides.pdf">slides</a>.

Installation
============

Assumes preinstalled MPI, Gmp and Boost (system, mpi, and serialization) packages.

* `cd aeval ; mkdir build ; cd build`
* `cmake ../`
* `make` to build dependencies (Z3 and LLVM)
* `make deephorn` to build FreqHorn

The binary of FreqHorn can be found at `build/tools/deep/`.
Run `./tools/deep/deephorn --help` for the usage info.

Benchmarks
==========

Collection of the SMT-LIB2 translations of the satisfiable CHC system can be found at `bench_horn`. FreqHorn is expected to eventually discover solutions for the systems.

Sequential Solver
=================

Original version of FreqHorn (compiled without MPI) can be found at the <a href="https://github.com/grigoryfedyukovich/aeval/tree/rnd">rnd</a> branch.

