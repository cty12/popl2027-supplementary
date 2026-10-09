# Prototype Implementation of LambdaAlphaRefStar 

(TODO: update this once I sync this repo with the new version of the prototype)

This repository contains the prototype implementation of LambdaAlphaRefStar and
its sister language LambdaAlphaRef. It also contains examples.

The `examples/` subdirectory contains files with the `.lar` extension, 
which are example programs in LambdaAlphaRefStar. The `sister-language/examples/` 
subdirectory contains LambdaAlphaRef examples (so they are statically-typed).

To download the Racket dependencies run the following command in the
`Interpreter/` directory:
```
raco pkg install --auto
```

The `test-examples.rkt` file tests the examples in both `examples/` and
`sister-language/examples/`. To run all those examples, simply run

```
racket test-examples.rkt
```

from the `Interpreter/` directory. It was tested on Racket v9.2 [cs].




Implementation note: the EC bounded polymorphism `∀ e₁ <: α <: e₂. Â` gets
compiled into `∀ α. e₁ <: e₂ ⇒ Â` during elaboration into the cast calculus.
