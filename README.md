This directory contains the executable semantics accompanying the [paper](https://arxiv.org/abs/2209.01179).

It does not contain any proofs.

## Installing the Dependencies

The development is known to compile with Coq 8.12.0.
Furthermore the coq-record-update library is needed.
```
opam install coq-record-update
```

## Building the project
Generate the Makefile from the _CoqProject file
using 
```
coq_makefile -f _CoqProject -o CoqMakefile
```
and then
```
make -f CoqMakefile
```

To generate the HTML output of examples.v use [alectryon](https://github.com/cpitclaudel/alectryon) with the follwing command:
```
alectryon theories/examples.v -R theories/ spec
```
# Organization

We describe the contents of each file
| File | Description |
|------|:-----------:|
|Maps.v| Helper file to define a map from A -> B. |
|Lang.v| Contains the syntax of muasm and the non-speculative semantics. |
|semantics.v| Contains the speculative semantics. The semantics is structured in a base case (everything not related to speculation) and the speculation case. Each semantics just instantiates on what is speculated on (i.e. by specifying a list of instructions and the corresponding speculation function). |
|notations.v| Defines the notation used for the syntax |
|programs.v| Definition of the programs used in the paper. |
|examples.v| Uses the programs in programs.v and defines suitable configurations to execute these programs. This file generates the traces and can be used as base to create new programs and configurations.|
