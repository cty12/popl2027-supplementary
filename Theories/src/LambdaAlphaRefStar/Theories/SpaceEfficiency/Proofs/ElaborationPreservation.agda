module LambdaAlphaRefStar.Theories.SpaceEfficiency.Proofs.ElaborationPreservation where

open import LambdaAlphaRefStar.Theories.SpaceEfficiency.CCAlphaRefStarSyntaxAndTypeSystem
open import LambdaAlphaRefStar.Theories.SpaceEfficiency.Elaboration


mutual

  synthᵒ-type : ∀ {Δ Θ Γᵐ Γᵒ e M M′ T}
    → Δ ; Θ ; Γᵐ ; Γᵒ ; e ⊢ M ↝ M′ ⭆ T
      -------------------------------------------------
    → Δ ; elab-ctx Θ Γᵐ Γᵒ ; e ⊢ᵒ M′ ⦂ T
  synthᵒ-type code-const = ⊢constᵒ _
  synthᵒ-type (code-var lookup sub) = ⊢varᵒ lookup sub
  synthᵒ-type (code-abs elab) = ⊢lamᵒ (synthᵒ-type elab)
  synthᵒ-type (code-app elabL elabM) = ⊢appᵒ (synthᵒ-type elabL) (checkᵒ-type elabM)

  checkᵒ-type : ∀ {Δ Θ Γᵐ Γᵒ e M M′ T}
    → Δ ; Θ ; Γᵐ ; Γᵒ ; e ⊢ M ↝ M′ ⭅ T
      -------------------------------------------------
    → Δ ; elab-ctx Θ Γᵐ Γᵒ ; e ⊢ᵒ M′ ⦂ T
  checkᵒ-type (splice elabM A≲T) =
    ⊢splice (⊢cast (synthᵐ-type elabM) (typedᵐ (coerce A≲T _))) ⌈ _ ⌉ᵒ-↪
  checkᵒ-type (check elabM) = synthᵒ-type elabM

  synthᵐ-type : ∀ {Δ Θ Γᵐ Γᵒ M M′ A}
    → Δ ; Θ ; Γᵐ ; Γᵒ ⊢ M ↝ M′ ⦂ A
      ---------------------------------------------
    → Δ ; elab-ctx Θ Γᵐ Γᵒ ⊢ᵐ M′ ⦂ A
  synthᵐ-type meta-const = ⊢constᵐ _
  synthᵐ-type (meta-var lookup) = ⊢varᵐ lookup
  synthᵐ-type (meta-abs ⊢A elabM) = ⊢lamᵐ ⊢A (synthᵐ-type elabM)
  synthᵐ-type (meta-app elabL elabM B≲A₁) =
    ⊢appᵐ (synthᵐ-type elabL) (⊢cast (synthᵐ-type elabM) (typedᵐ (coerce B≲A₁ _)))
  synthᵐ-type (meta-app⋆ {A = A} {ℓ = ℓ} elabL elabM) =
    ⊢appᵐ
      (⊢cast (synthᵐ-type elabL) (typedᵐ (coerce {Δ = _} {Θ = _} (csub-⋆-left {A = ⋆ ⇒ ⋆}) ℓ)))
      (⊢cast (synthᵐ-type elabM) (typedᵐ (coerce {Δ = _} {Θ = _} (csub-⋆-right {A = A}) ℓ)))
  synthᵐ-type (meta-ecabs elabM) = ⊢eclam (synthᵐ-type elabM)
  synthᵐ-type (meta-ecapp ⊢e elabM) = ⊢ecapp (synthᵐ-type elabM) ⊢e
  synthᵐ-type (meta-ecapp⋆ {ℓ = ℓ} ⊢e elabM) =
    ⊢ecapp (⊢cast (synthᵐ-type elabM) (typedᵐ (coerce {Δ = _} {Θ = _} (csub-⋆-left {A = ∀̇ ⋆}) ℓ))) ⊢e
  synthᵐ-type (meta-subintro ⊢e₁ ⊢e₂ elabM) = ⊢subintro ⊢e₁ ⊢e₂ (synthᵐ-type elabM)
  synthᵐ-type (meta-subelim sub elabM) = ⊢subelim (synthᵐ-type elabM) sub
  synthᵐ-type (meta-subelim⋆ {ℓ = ℓ} elabM) = ⊢subelim⋆ (synthᵐ-type elabM) ℓ
  synthᵐ-type (meta-quote ⊢e elabM) = ⊢quote (synthᵒ-type elabM) ⊢e ⌈ _ ⌉ᵒ-↪
  synthᵐ-type (meta-ref elabM) = ⊢ref (synthᵐ-type elabM)
  synthᵐ-type (meta-assign elabL elabM B≲A) =
    ⊢assign (synthᵐ-type elabL) (⊢cast (synthᵐ-type elabM) (typedᵐ (coerce B≲A _)))
  synthᵐ-type (meta-assign⋆ {A = A} {ℓ = ℓ} elabL elabM) =
    ⊢assign
      (⊢cast (synthᵐ-type elabL) (typedᵐ (coerce {Δ = _} {Θ = _} (csub-⋆-left {A = Ref ⋆}) ℓ)))
      (⊢cast (synthᵐ-type elabM) (typedᵐ (coerce {Δ = _} {Θ = _} (csub-⋆-right {A = A}) ℓ)))
  synthᵐ-type (meta-deref elabM) = ⊢deref (synthᵐ-type elabM)
  synthᵐ-type (meta-deref⋆ {ℓ = ℓ} elabM) =
    ⊢deref (⊢cast (synthᵐ-type elabM) (typedᵐ (coerce {Δ = _} {Θ = _} (csub-⋆-left {A = Ref ⋆}) ℓ)))
