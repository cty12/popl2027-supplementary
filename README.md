# Supplementary Material for *Taming Scope Extrusion in Gradual Imperative Metaprogramming*
[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.23226491.svg)](https://doi.org/10.5281/zenodo.23226491)

The supplementary material consists of three parts: the Appendix, the Agda proof
scripts, a prototype implementation of LambdaAlphaRefStar and its static sister
language. We also provide example programs of LambdaAlphaRefStar and its static
sister.

For artifact evaluation, we provide a pre-built Docker image for evaluating the
mechanized proofs and running the prototype on all examples. Please refer to the
"POPL 2027 Artifact Evaluation" below. Thank you.

## Repository Structure

This repository is organized as follows.

### The Appendix

The Appendix that supplements the main text of the paper is `Appendix.pdf`. It
includes a table (Table 2) that maps the on-paper lemmas and theorems to their
Agda counterparts.

### The mechanized proofs of LambdaAlphaRefStar

The LambdaAlphaRefStar Agda proofs are in the `Theories/` directory. More
information can be found in the `README.md ` file in that directory.

### Prototype implementation and examples

The prototype Racket implementations of LambdaAlphaRefStar and the
LambdaAlphaRef sister language, and their example programs are in the
`Interpreter/` directory. To run the interpreter on those examples, please
follow the instructions in `Interpreter/readme.md`.

## POPL 2027 Artifact Evaluation

Everything is checked inside a Docker image that pins the toolchain this
artifact was developed against: Agda 2.8.0 with standard library v2.3, and
Racket v9.2 [cs]. Docker is the only prerequisite.

### Option 1: use the prebuilt image (Fast and Recommended)

Download the image from the [latest release][latest], load it, and run it:

```
curl -fLO https://github.com/cty12/popl2027-supplementary/releases/latest/download/lambdaalpharefstar-amd64.tar.gz
docker load -i lambdaalpharefstar-amd64.tar.gz
docker run --rm lambdaalpharefstar
```

[latest]: https://github.com/cty12/popl2027-supplementary/releases/latest

### Option 2: build the image from this repository

```
docker build -t lambdaalpharefstar .
docker run --rm lambdaalpharefstar
```

Building from scratch takes a much longer time than option 1. Most of the time
is spent type checking the proofs, installing Racket packages, and finally
downloading Agda, the Agda standard library, and Racket. It needs network
access, so a slow connection will take longer.


### What the run does

`docker run` executes the two Makefiles described above:

- `make -C Theories` type checks the Agda proofs, starting from
  `MainTheorems`, which reaches every result listed in `Theories/README.md`.
- `make -C Interpreter` runs the prototype over every example program in
  `Interpreter/examples/` and `Interpreter/sister-language/examples/`.

These Makefiles finish running in under a minute, because the image is built
with the proofs already checked once. Here is what the output should look like:

```
make: Entering directory '/artifact/Theories'
Checking all proofs ...
/usr/bin/env agda src/LambdaAlphaRefStar/Theories/MainTheorems.agda
make: Leaving directory '/artifact/Theories'
make: Entering directory '/artifact/Interpreter'
Running all examples ...
/usr/bin/env racket test-examples.rkt
52/52 tests succeeded (enable debug to see details)
make: Leaving directory '/artifact/Interpreter'
```

while exiting with status 0. A failure in either half makes the command exit
with a non-zero code.

To run just one Makefile, run either one of these:

```
docker run --rm lambdaalpharefstar make -C Theories
docker run --rm lambdaalpharefstar make -C Interpreter
```

### Caveats

- **Mac Users.** The released image is `linux/amd64`. On an Apple Silicon machine, add
`--platform linux/amd64` to the `docker run** command to use emulation.

- **Checking the proofs and running the prototype manually.** To check the
proofs or run the interpreter without Docker, follow `Theories/README.md` and
`Interpreter/readme.md`, which list the toolchain versions each one needs.
