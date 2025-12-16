#!/bin/sh

dune build narya.opam
opam install . --deps-only
dune build @install
dune test
dune install
