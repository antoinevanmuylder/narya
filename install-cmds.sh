#!/bin/sh

dune build narya.opam # generates the narya.opam metadata file from dune-project
opam install . --deps-only # fetches from web and compile deps, add them to opam switch
dune build @install # build project
dune test
dune install # move compiled files to opam switch
