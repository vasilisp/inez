Inez - A Constraint Solver
==========================

Introduction
------------

Inez is a constraint solver.

Inez implements the *ILP Modulo Theories* scheme, as described in a
[CAV paper][cav2013]. Simply put, we combine a Mathematical
Programming solver with background solvers.

Inez is OCaml-centric. The preferred mode of interacting with the
solver is via scripts written in a Camlp4-powered superset of OCaml.

Inez is a research prototype, and may contain serious bugs. You should
not use it in production.

Dependencies
------------

### GNU/Linux

We develop and test Inez on Debian x86_64. In principle, other modern
Unixen should work, as long as you can satisfy all dependencies.

Inez will not work on Windows any time soon. We depend quite heavily
on [Jane Street Core][jsgithub], which is Unix-only.

### SCIP

Inez depends on the [SCIP optimization suite][scip], which is
available without charge for academic and non-commercial purposes. For
other purposes, you will need a license agreement.

Once you obtain the "optimization suite" distribution, the following
recipe suffices (applied to the toplevel directory):

    make scipoptlib \
        SHARED=true \
        READLINE=false \
        ZLIB=false \
        ZIMPL=false

The `.so` is under `lib/`. Rename it to `libscipopt.so`.

### C and C++ Libraries and Tools

Building Inez requires GCC (C++ frontend included). We also depend on
Boost. Fetch and untar a [fresh tarball][boost].

### OCaml Libraries and Tools

Inez requires OCaml 4.00 or newer. Older OCaml will not work; the
reason is GADTs.

Additionally, you will need recent versions of the following packages:

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
- Type `omake target*` to build the executables you need.

The interesting targets are:

- `frontend/inez-smt.opt`: SMT-LIB v2.0 frontend.
- `frontend/inez.opt`: The main Inez executable. It runs scripts in
  our OCaml superset.
- `frontend/inez.top`: OCaml toplevel preloaded with Inez libraries
  and syntax.
  
All of the executables above are dynamically linked against
`libscipopt.so`. Copy the latter to a standard location ( *e.g.,*
`/usr/local/lib` ), or modify `LD_LIBRARY_PATH` accordingly.

Running Inez
------------

Some examples can be found under `frontend/examples`.

[jsgithub]: http://janestreet.github.io/
[scip]: http://scip.zib.de/
[boost]: http://www.boost.org/users/download/
[opam]: http://opam.ocamlpro.com/
[cav2013]: http://www.ccs.neu.edu/home/vpap/pub/cav-2013.pdf
