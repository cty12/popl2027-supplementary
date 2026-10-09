This directory contains the Agda mechanization of the proofs in our paper.

# Building Instructions

Requirements: Agda 2.8.0 and the Agda standard library v2.3. 

To check every proof, run the following from this directory:

```
make
```

This type checks `MainTheorems`, which names the three headline results: scope
safety (Theorem 7.7), the static sister language's corollary (Corollary 7.8) and
space consumption (Theorem 8.1). This type check therefore transitively
reaches every result listed under "Proof Contents" below.

`make clean` removes the generated `_build/` directory.

# Paper-to-Proof Correspondence

The lists in the next subsections are a list version of Table 2 of the Appendix.
File names link to their source under `src/LambdaAlphaRefStar/Theories/`.

## Section 7: Type and scope safety

- Preservation for CCAlphaRefStar (Lemma 7.1)
    `preserveᵒ`, `preserveᵐ` in [`CCAlphaRefStarPreservation.agda`](src/LambdaAlphaRefStar/Theories/CCAlphaRefStarPreservation.agda)

- Progress for CCAlphaRefStar (Lemma 7.2)
    `progressᵒ`, `progressᵐ` in [`CCAlphaRefStarProgress.agda`](src/LambdaAlphaRefStar/Theories/CCAlphaRefStarProgress.agda)

- Elaboration preserves types (Lemma 7.3)
    `code-synth-preserves`, `code-check-preserves`, `meta-elab-preserves` in [`ElaborationPreserves.agda`](src/LambdaAlphaRefStar/Theories/ElaborationPreserves.agda)

- Reification preserves types (Lemma 7.4)
    `reify-preserves-types` in [`ReifyPreserves.agda`](src/LambdaAlphaRefStar/Theories/ReifyPreserves.agda)

- Reification is total for code values (Lemma 7.5)
    `scope-safety-val` in [`ScopeSafetyValue.agda`](src/LambdaAlphaRefStar/Theories/ScopeSafetyValue.agda)

- Observation for code-typed values (Lemma 7.6)
    `obs-code` in [`CanonicalForms.agda`](src/LambdaAlphaRefStar/Theories/CanonicalForms.agda)

- Scope safety for LambdaAlphaRefStar (Theorem 7.7)
    `scope-safety` in [`ScopeSafety.agda`](src/LambdaAlphaRefStar/Theories/ScopeSafety.agda)

- Scope safety for LambdaAlphaRef (Corollary 7.8)
    `static-scope-safety` in [`StaticScopeSafety.agda`](src/LambdaAlphaRefStar/Theories/StaticScopeSafety.agda)

## Section 8: Space efficiency

- Space consumption (Theorem 8.1)
    `space-consumption-elab` in [`SpaceEfficiency/SpaceEfficient.agda`](src/LambdaAlphaRefStar/Theories/SpaceEfficiency/SpaceEfficient.agda)

- Elaboration efficient (Lemma 8.2)
    `elab-efficient`, `elab-efficientᵒ⇒`, `elab-efficientᵒ⇐` in
    [`SpaceEfficiency/Proofs/ElaborationEfficient.agda`](src/LambdaAlphaRefStar/Theories/SpaceEfficiency/Proofs/ElaborationEfficient.agda)

- Preserve adjacent casts (Lemma 8.3)
    `preserve-okᵐ`, `preserve-okᵒ` in [`SpaceEfficiency/Proofs/PreserveOK.agda`](src/LambdaAlphaRefStar/Theories/SpaceEfficiency/Proofs/PreserveOK.agda)

- Preserve adjacent casts in heaps (Lemma 8.4)
    `preserve-heap-values-okᵐ`, `preserve-heap-values-okᵒ` in [`SpaceEfficiency/Proofs/PreserveOK.agda`](src/LambdaAlphaRefStar/Theories/SpaceEfficiency/Proofs/PreserveOK.agda)

- Composition height (Lemma 8.5)
    `compose-height-code`, `compose-height-code-middle`, `compose-height-meta`, `compose-height-meta-middle`
    in [`SpaceEfficiency/Proofs/HypercoercionCompositionBounded.agda`](src/LambdaAlphaRefStar/Theories/SpaceEfficiency/Proofs/HypercoercionCompositionBounded.agda)

- Preserve height (Lemma 8.6)
    `preserve-heightᵐ`, `preserve-heightᵒ` in [`SpaceEfficiency/Proofs/PreserveHeight.agda`](src/LambdaAlphaRefStar/Theories/SpaceEfficiency/Proofs/PreserveHeight.agda)

- Size bounded by number of terms  (Lemma 8.7)
    `real-size-tsizeᵐ`, `real-size-tsizeᵒ` in [`SpaceEfficiency/Proofs/RealSizeTermAndHeapSize.agda`](src/LambdaAlphaRefStar/Theories/SpaceEfficiency/Proofs/RealSizeTermAndHeapSize.agda)

- Number of terms bounded by ideal size  (Lemma 8.8)
    `size-OK`, `sizeᵒ-OK` in [`SpaceEfficiency/Proofs/SizeOK.agda`](src/LambdaAlphaRefStar/Theories/SpaceEfficiency/Proofs/SizeOK.agda)
