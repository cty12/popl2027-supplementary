# Prototype Implementation of LambdaAlphaRefStar 

This repository contains the prototype implementation of LambdaAlphaRefStar and
its sister language LambdaAlphaRef. It also contains examples.

The `examples/` subdirectory contains files with the `.lar` extension, 
which are example programs in LambdaAlphaRefStar. The `sister-language/examples/` 
subdirectory contains statically typed LambdaAlphaRef examples.

Note that the examples write EC bounded polymorphism as `∀ e₁ <: α <: e₂. Â`,
which elaboration compiles into `∀ α. e₁ <: e₂ ⇒ Â` in the cast calculus. The
two forms mean the same thing; the result of the elaboration uses the syntax
mentioned in the research paper.

# Requirements

Racket v9.2 [cs], and the packages declared in `info.rkt`: `base`,
`rackunit-lib` and `graph-lib`. To install those packages, run the following
from this directory:

```
make deps
```

That wraps `raco pkg install --auto --no-docs`, which resolves the
dependencies without prompting and skips building their documentation.

# Running the Examples

```
make
```

This runs `test-examples.rkt`, which checks every example in `examples/` and
`sister-language/examples/`. It ends with

```
52/52 tests succeeded (enable debug to see details)
```

and exits non-zero if any example fails.

`make clean` removes the generated `compiled/` directories. Run it if you
switch Racket versions: Racket rejects bytecode built by a different version
rather than recompiling it, so a stale `compiled/` makes the tests fail with a
version mismatch.

To run everything in a pinned container instead, see the artifact evaluation
section of the top-level `README.md`.
