#!/usr/bin/env python

def seaAbc(args, extra):
    print "Hello world\n"

# /home/jorge/SeaHorn/bin/sea pp  --kill-vaarg=true  --inline-constructors --inline-allocators --strip-extern=false --promote-arrays --simplify-pointer-loops --unfold-loops-for-dsa --lower-invoke --devirt-functions --externalize-addr-taken-funcs --abc=2 --abc-dsa-node=0 --abc-alloc-site=0 --abc-instrument-underflow=false --abc-instrument-mem-intrinsics=false --abc-escape-ptr --abc-use-deref --externalize-function=.... CASS_DDSim.o3.g.bc -o CASS_DDSim.o3.g.pp.bc
# /home/jorge/SeaHorn/bin/seapp -o CASS_DDSim.o3.g.pp.ms.bc --horn-mixed-sem --ms-reduce-main --horn-symbolize-loops CASS_DDSim.o3.g.pp.bc
# /home/jorge/SeaHorn/bin/seaopt -f -funit-at-a-time -o /tmp/user/1000/sea-Zf8bbs/CASS_DDSim.o3.g.pp.ms.o.bc -O3 --enable-indvar=false --enable-loop-idiom=false --enable-nondet-init=false --unroll-threshold=150 /tmp/user/1000/sea-Zf8bbs/CASS_DDSim.o3.g.pp.ms.bc
# /home/jorge/SeaHorn/bin/seahorn --keep-shadows=true --horn-solve --horn-answer -horn-inter-proc -horn-sem-lvl=mem --horn-step=large CASS_DDSim.o3.g.pp.ms.o.bc --horn-singleton-aliases=true --horn-global-constraints=true --horn-stats --horn-skip-constraints=true --horn-make-undef-warning-error=false --horn-child-order=false --horn-reduce-constraints --horn-extra-cps=h2 --horn-use-write

