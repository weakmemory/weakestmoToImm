For the development, one needs to have `coq-imm` project being installed.
To get it, one has to execute following instructions:
```bash
opam repo add coq-released https://coq.inria.fr/opam/released
opam remote add coq-weakmemory-local -k git https://github.com/weakmemory/local-coq-opam-archive
opam install coq-imm
```