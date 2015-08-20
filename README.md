# A Witness Building Algorithm  #

[![Build Status](https://travis-ci.org/sylvarant/moduleml-witness-algorithm.svg?branch=master)](https://travis-ci.org/sylvarant/moduleml-witness-algorithm)

### What is this repository for? ###

Ocaml implementation of the module distinction algorithm mentioned in an APLAS 2015 paper.
The algorithm takes in 2 MiniML files and 2 .traces files that are produced by these files,
it reuses the parser, type checker and static modules compiler of the secure compiler.


### Setup ###
$ make setup
$ make now
$ make test


### Repository Structure ###
* src/ : algorithm source code
* tests/ : a series of differing MiniML programs that the algorithm can build a witness for


