#########################################################
##    Supplementary Material of LambdaAlphaRefStar     ##
#########################################################

I. The Appendix that supplements the main text of the paper is `Appendix.pdf`.

II. The mechanized proofs of LambdaAlphaRefStar are in the `Theories/`
    directory.

- The list below is a list version of Table 2 of the Appendix. File paths are
    relative to `Theories/`.

- To verify scope safety, please run `agda Theories/ScopeSafety.agda` from the
  root.

- To verify space efficiency, please run `agda
  Theories/SpaceEfficiency/SpaceEfficient.agda` from the root.

- The proofs were checked on Agda 2.8.0 and Agda standard library v2.3.

Section 7: Type and scope safety

- Preservation for CCAlphaRefStar (Lemma 7.1)
    preserve^o, preserve^m in CCAlphaRefStarPreservation.agda

- Progress for CCAlphaRefStar (Lemma 7.2)
    progress^o, progress^m in CCAlphaRefStarProgress.agda

- Elaboration preserves types (Lemma 7.3)
    code-synth-preserves, code-check-preserves, meta-elab-preserves in ElaborationPreserves.agda

- Reification preserves types (Lemma 7.4)
    reify-preserves-types in ReifyPreserves.agda

- Scope safety for code values (Lemma 7.5)
    scope-safety-val in ScopeSafetyValue.agda

- Observation for code-typed values (Lemma 7.6)
    obs-code in CanonicalForms.agda

- Scope safety for LambdaAlphaRefStar (Theorem 7.7)
    scope-safety in ScopeSafety.agda

- Scope safety for LambdaAlphaRef (Corollary 7.8)
    static-scope-safety in StaticScopeSafety.agda

Section 8: Space efficiency

- Space consumption (Theorem 8.1)
    space-consumption-elab in SpaceEfficiency/SpaceEfficient.agda

- Elaboration efficient (Lemma 8.2)
    elab-efficient, elab-efficient^o=>, elab-efficient^o<= in SpaceEfficiency/Proofs/ElaborationEfficient.agda

- Preserve adjacent casts (Lemma 8.3)
    preserve-ok^m, preserve-ok^o in SpaceEfficiency/Proofs/PreserveOK.agda

- Preserve adjacent casts in heaps (Lemma 8.4)
    preserve-heap-values-ok^m, preserve-heap-values-ok^o in SpaceEfficiency/Proofs/PreserveOK.agda

- Composition height (Lemma 8.5)
    compose-height-code, compose-height-code-middle, compose-height-meta, compose-height-meta-middle
    in SpaceEfficiency/Proofs/HypercoercionCompositionBounded.agda

- Preserve height (Lemma 8.6)
    preserve-height^m, preserve-height^o in SpaceEfficiency/Proofs/PreserveHeight.agda

- Real size bounded by size (Lemma 8.7)
    real-size-tsize^m, real-size-tsize^o in SpaceEfficiency/Proofs/RealSizeTermAndHeapSize.agda

- Size bounded by ideal size (Lemma 8.8)
    size-OK, size^o-OK in SpaceEfficiency/Proofs/SizeOK.agda

III. The prototype Racket implementations of LambdaAlphaRefStar and the
     LambdaAlphaRef sister language are in the `Interpreter/` directory.

IV. The example programs of LambdaAlphaRefStar and its static sister
    LambdaAlphaRef are also in `Interpreter/`. To run the interpreter on those
    examples, please follow the instructions in `Interpreter/readme.md`.
