# A Witness Building Algorithm  #

[![Build Status](https://travis-ci.org/sylvarant/moduleml-witness-algorithm.svg?branch=master)](https://travis-ci.org/sylvarant/moduleml-witness-algorithm)[![Coverage Status](https://coveralls.io/repos/sylvarant/moduleml-witness-algorithm/badge.svg?branch=master&service=github)](https://coveralls.io/github/sylvarant/moduleml-witness-algorithm?branch=master)

### What is this repository for? ###

Ocaml implementation of the module distinction algorithm mentioned in the
APLAS 2015 paper:`A Secure Compiler for ML Modules`.
The algorithm takes in 2 MiniML source files and 2 .traces files that are produced by these files.
The implementation of the algorithm reuses the parser, type checker and static modules compiler of the secure compiler.

### Setup ###
Set up the environment:
```bash
make setup
```
Compile the algorithm:
```bash
make now
```
Compile and run the tests:
```bash
make test
```


### Repository Structure ###
* src/ : algorithm source code
* tests/ : a series of differing MiniML programs that the algorithm can build a witness for

## License

[Artistic License 2.0](http://www.perlfoundation.org/artistic_license_2_0)
