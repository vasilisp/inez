Inez - A Constraint Solver
==========================

Introduction
------------

Inez is a constraint solver.

Inez implements the *ILP Modulo Theories* scheme, as described in a
[CAV paper][cav2013]. Simply put, we combine a Mathematical
Programming solver with background solvers.

Inez is OCaml-centric. The preferred mode of interacting with the
solver is via scripts written in a Camlp4-powered [superset of
OCaml][langintro].

Inez is a research prototype, and may contain serious bugs. You should
not use it in production.

Dependencies
------------

### Unix

Inez is known to work on x86_64 GNU/Linux and Mac OS X. Other modern
Unixen should work, as long as all dependencies are satisfied.

Inez does not work on Windows. We depend quite heavily on
[Jane Street Core][jsgithub], which is Unix-only.

### SCIP

Inez depends on the [SCIP optimization suite][scip], version
3.1.x. The SCIP optimization suite is available without charge for
academic and non-commercial purposes. For other purposes, a license
agreement is required.

Once you obtain the "optimization suite" distribution, the following
recipe suffices (applied to the toplevel directory):

    make scipoptlib \
        SHARED=true \
        READLINE=false \
        ZLIB=false \
        GMP=false \
        ZIMPL=false

The `.so` is under `lib/`. Create a symbolic link to it as follows:

    ln -s libscipopt-3.1.0.linux.x86_64.gnu.opt.so libscipopt.so

### C and C++ Libraries and Tools

Building Inez requires GCC (C++ frontend included). We also depend on
Boost. Fetch and untar a [fresh tarball][boost].

### OCaml Libraries and Tools

Inez requires OCaml 4.02 or newer. Additionally, you will need recent
versions of the following packages:

- `async`
- `camlidl`
- `camlp4`
- `comparelib`
- `core`
- `herelib`
- `ocamlfind`
- `ocaml_plugin`
- `omake`
- `sexplib`

The best way to obtain the above is via [OPAM][opam].

Installation
------------

Once all dependencies are satisfied, you have to:

- Copy `OMakefile.config.sample` to `OMakefile.config`.
- Adapt `OMakefile.config` for your setup.
- Type `omake frontend/inez.opt` to build Inez.

`inez.opt` is dynamically linked against `libscipopt.so`.  Modify
`LD_LIBRARY_PATH` so that the dynamic linker can find this shared
library. On OS X, you should set `DYLD_FALLBACK_LIBRARY_PATH` in place
of `LD_LIBRARY_PATH`.

`inez.opt` accepts a single argument for the input program. Some
examples can be found under `frontend/examples`.

[jsgithub]: http://janestreet.github.io/
[scip]: http://scip.zib.de/download.shtml
[boost]: http://www.boost.org/users/download/
[opam]: http://opam.ocamlpro.com/
[cav2013]: http://www.ccs.neu.edu/home/vpap/pub/cav-2013.pdf
[langintro]: https://github.com/vasilisp/inez/wiki/Inez-Language