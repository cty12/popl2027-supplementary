# Prototype Implementation of LambdaAlphaRefStar 

This repository contains the prototype implementation of LambdaAlphaRefStar and
its sister language LambdaAlphaRef. It also contains examples.

The `examples/` subdirectory contains files with the `.lar` extension, 
which are example programs in LambdaAlphaRefStar. The `sister-language/examples/` 
subdirectory contains LambdaAlphaRef examples (so they are statically-typed).

The `test-examples.rkt` file tests the examples in both `examples/` and
`sister-language/examples/`. To run all those examples, simply run

```
racket test-examples.rkt
```

from the `stepper/` directory. It was tested on Racket v9.0 [cs].




Implementation note: the EC bounded polymorphism `∀ e₁ <: α <: e₂. Â` gets
compiled into `∀ α. e₁ <: e₂ ⇒ Â` during elaboration into the cast calculus.
