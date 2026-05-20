   __  __                 _             _
  |  \/  | ___  _ __ __ _| |_ __ _ _ __ | |_
  | |\/| |/ _ \| '__/ _` | __/ _` | '_ \| __|
  | |  | | (_) | | | (_| | || (_| | | | | |_
  |_|  |_|\___/|_|  \__,_|\__\__,_|_| |_|\__|

 seccomp-bpf policy compiler that compiles a declarative syscall policy into
BPF (cBPF) programs installable through the linux seccomp interface. 
it is written in C11 and carries a formally specified compiler model in Agda.
 it doesnt  wrap libseccomp classic BPF only, not eBPF.

<==============================================================================>

   policy.mdt
       |
       v
   [ parser ] --> [ typed IR ] --> [ lower ] --> [ branch ]
                                                      |
                                                      v
                                               [ validate ]
                                                      |
                                                      v
                                               [ sock_filter[] ]
                                                      |
                                                      v
                                               [ linux seccomp ]

<==============================================================================>
target

   linux x86-64, little endian, native syscall ABI
   rejects x32 syscall numbers (the 0x40000000 bit)
   emits an AUDIT_ARCH_X86_64 (0xc000003e) guard before syscall dispatch
   architecture mismatch and x32 numbers fail closed (kill_process)

<==============================================================================>
policy language

```
arch x86_64

default errno 1

allow read
allow write
allow close
allow exit
allow exit_group

allow mmap if arg2 & 0x4 == 0

allow mprotect if arg2 & 0x4 == 0

allow ioctl if arg1 == 0x5401
```

<==============================================================================>
seccomp actions

   allow      SECCOMP_RET_ALLOW          0x7fff0000
   errno N    SECCOMP_RET_ERRNO | N      0x00050000 | N
   kill       SECCOMP_RET_KILL_PROCESS   0x80000000

   errno N must be in 1..65535.

<==============================================================================>
filter format

   16-byte little-endian header:
     magic    u32   0x3146444d  ('MDF1')
     version  u32   1
     arch     u32   audit arch
     count    u32   instruction count

   then `count` records of 8 bytes:
     code  u16
     jt    u8
     jf    u8
     k     u32

   portable across processes on the target platform and not a raw in-memory
   sock_fprog

<==============================================================================>
usage

```
mordant check policy.mdt
mordant compile policy.mdt -o filter.bin
mordant dump filter.bin
mordant eval policy.mdt --syscall mmap --arg2 0x4
mordant verify filter.bin
```

   exit codes:
     0   ok
     1   usage or io error
     2   policy or validation error
     3   compile or limit error
     4   runtime error

<==============================================================================>
build

```
make              builds mordant and mordant-load
make test         runs the C unit tests
make test-kernel  builds and runs the seccomp kernel integration tests (linux)
make agda         typechecks the Agda development
make diff         generates random policies and contexts and runs the C compiled
                  filter interpreter and the Agda specification then compares actions
```

<==============================================================================>
loader

   tools/loader (mordant-load) installs a compiled filter into its own process.
   it validates the filter +  calls prctl(PR_SET_NO_NEW_PRIVS, 1, 0, 0, 0), then
   seccomp(SECCOMP_SET_MODE_FILTER, 0, &prog). it never executes an external
   command unless --exec is given explicitly as well as  not install filters into
   other processes

<==============================================================================>
verification

   the Agda development defines as total data types and functions the policy
   syntax and its 64-bit evaluation along with the BPF instruction set and its
   execution, predicate lowering, symbolic to relative branch layout, and a
   structural validity predicate over programs

   also contains a total compiler from policies to BPF and a
   BPF interpreter. the differential runner executes that compiler that
   interpreter and the policy evaluator on generated fixtures and checks that
   the compiled program reproduces the decision the policy prescribes

   3 specific kinds, not interchangeable:
     (a) the Agda properties listed above
     (b) differential evidence: the C compiler and the Agda specification agree
         on generated random policies and syscall contexts (make diff)
     (c) kernel validated behavior: the seccomp integration tests install
         compiled filters and observe the kernel honor their decisions

   the C executable is a separate implementation. the Agda proofs dont
   transfer to it without a refinement proof or a verified extraction path

<==============================================================================>
compiler

   rejects programs exceeding the kernel limit of 4096 instructions at compile
   time. 64-bit comparisons lower to lexicographic unsigned comparison of the
   high and low halves. bitmask predicates check both halves and  branch layout
   resolves symbolic labels to encoded offsets with trampolines when an 8-bit
   conditional offset would overflow while all jumps are forward

<==============================================================================>
filter stacking

   the kernel combines multiple installed seccomp filters by seccomp action
   precedence. mordant guarantees the behavior of its own compiled filter, not
   the final kernel action when other filters are stacked.


<==============================================================================>
references

   seccomp(2)        https://man7.org/linux/man-pages/man2/seccomp.2.html
   linux/filter.h    https://git.kernel.org/pub/scm/linux/kernel/git/torvalds/linux.git/tree/include/uapi/linux/filter.h
   linux/seccomp.h   https://git.kernel.org/pub/scm/linux/kernel/git/torvalds/linux.git/tree/include/uapi/linux/seccomp.h
