# Supplementary Materials for LambdaAlphaRefStar
[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.23226492.svg)](https://doi.org/10.5281/zenodo.23226492)

The supplementary material consists of four parts: the Appendix, the Agda proof
scripts, a prototype implementation of LambdaAlphaRefStar (and its static
sister), and example programs of LambdaAlphaRefStar (and its static sister). We
show where to find each of them below.

## The Appendix

The Appendix that supplements the main text of the paper is `Appendix.pdf`.

## The mechanized proofs of LambdaAlphaRefStar

The LambdaAlphaRefStar Agda proofs are in the `Theories/` directory. More
information can be found in the `README.md ` file in that directory.

## Prototype implementation and examples

The prototype Racket implementations of LambdaAlphaRefStar and the
LambdaAlphaRef sister language, and their example programs are in the
`Interpreter/` directory. To run the interpreter on those examples, please
follow the instructions in `Interpreter/readme.md`.

# POPL 2027 Artifact Evaluation

Everything is checked inside a Docker image that pins the toolchain this
artifact was developed against: Agda 2.8.0 with standard library v2.3, and
Racket v9.2 [cs]. Docker is the only prerequisite.

## Option 1: use the prebuilt image (Fast and Recommended)

Download the image from the [latest release][latest], load it, and run it:

```
curl -fLO https://github.com/cty12/popl2027-supplementary/releases/latest/download/lambdaalpharefstar-amd64.tar.gz
gunzip -c lambdaalpharefstar-amd64.tar.gz | docker load
docker run --rm lambdaalpharefstar
```

[latest]: https://github.com/cty12/popl2027-supplementary/releases/latest

## Option 2: build the image from this repository

```
docker build -t lambdaalpharefstar .
docker run --rm lambdaalpharefstar
```

Building from scratch takes a much longer time than option 1. Most of the time
is spent type checking the proofs, installing Racket packages, and finally
downloading Agda, the Agda standard library, and Racket. It needs network
access, so a slow connection will take longer.

## What the run does

`docker run` executes the two Makefiles described above:

- `make -C Theories` type checks the Agda proofs, starting from
  `MainTheorems`, which reaches every result listed in `Theories/README.md`.
- `make -C Interpreter` runs the prototype over every example program in
  `Interpreter/examples/` and `Interpreter/sister-language/examples/`.

These Makefiles finish running in under a minute, because the image is built
with the proofs already checked once, and ends with:

```
52/52 tests succeeded (enable debug to see details)
```

exiting with status 0. A failure in either half makes the command exit
with a non-zero code.

To run just one Makefile, run either one of these:

```
docker run --rm lambdaalpharefstar make -C Theories
docker run --rm lambdaalpharefstar make -C Interpreter
```

## Notes

The released image is `linux/amd64`. On an Apple Silicon machine, add
`--platform linux/amd64` to the `docker run` command to use emulation.

To check the proofs or run the interpreter without Docker, follow
`Theories/README.md` and `Interpreter/readme.md`, which list the toolchain
versions each one needs.

