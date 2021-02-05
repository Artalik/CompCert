# ITP

This is code presented inside the ITP paper.

Examples about relabel are inside `relabels`.

You will find inside the `CompCert` folder, the CompCert compiler to which
we have added the modified files we are talking about in the paper.

## Dependencies

CompCert :

* Ocaml 4.05 or later
* Coq.8.13.0
* Menhir
* Iris

relabels :

* Coq.8.13.0 or later
* Iris

## Installation

Via opam :

Ocaml : create a new switch

Coq : ```opam install coq.8.13.0```

Menhir : ```opam install menhir```

Iris :

```opam repo add iris-dev https://gitlab.mpi-sws.org/iris/opam.git```

```opam install coq-iris.dev.2021-02-01.1.4c96a504```
