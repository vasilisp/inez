# Inez - A Constraint Solver

## Introduction

Inez is a constraint solver.

Inez implements the *ILP Modulo Theories* scheme, as described in a
[CAV paper][cav2013]. Simply put, we combine a Mathematical
Programming solver with other decision procedures.

Inez is OCaml-centric. The preferred mode of interacting with the
solver is via scripts written in a Camlp4-powered superset of OCaml.

## Dependencies

### GNU/Linux

We develop and test Inez on Debian x86_64. In principle, other modern
Unixen should work, as long as you can satisfy all dependencies.

Windows will not work any time soon. We depend quite heavily on
[Jane Street Core][jsgithub], which is Unix-only.

### SCIP

Inez depends on SCIP >= 3.0.0 . We need the
[SCIP optimization suite][scip] in shared library form (`.so`).  The
following recipe should suffice (applied to the SCIP optimization
suite toplevel directory):

    make scipoptlib \
        SHARED=true \
        READLINE=false \
        ZLIB=false \
        ZIMPL=false

The `.so` is under `lib/`. Rename it to `libscipopt.so`.

### C and C++ Libraries and Tools

Building Inez requires GCC (C++ frontend included). We also depend on
Boost. Fetch a [fresh tarball][boost], untar it, and note the path.

### OCaml Libraries and Tools

Inez requires OCaml 4.00 or newer. Older OCaml will not work,
because we use GADTs.

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

## Installation

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
`libscipopt.so`. Copy the latter to a standard location (*e.g.,*
`/usr/share/lib`), or modify `LD_LIBRARY_PATH` accordingly.

[jsgithub]: http://janestreet.github.io/
[scip]: http://scip.zib.de/download.shtml
[boost]: http://www.boost.org/users/download/
[opam]: http://opam.ocamlpro.com/
[cav2013]: http://www.ccs.neu.edu/home/vpap/pub/cav-2013.pdf

## Running Inez

Some examples can be found under `frontend/examples`.
