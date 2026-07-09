module LambdaAlphaRefStar.Theories.CoercionSequences.Code.Preservation where

open import Data.List using (_++_)

open import LambdaAlphaRefStar.Theories.CoercionSequences.Code.Definition


++-preserve : ∀ {c̅ᵒ d̅ᵒ C₁ C₂ C₃}
  → ⊢ᵒ̅ c̅ᵒ ⦂ C₁ ⇒ C₂
  → ⊢ᵒ̅ d̅ᵒ ⦂ C₂ ⇒ C₃
    ------------------------------
  → ⊢ᵒ̅ c̅ᵒ ++ d̅ᵒ ⦂ C₁ ⇒ C₃
++-preserve ⊢[] ⊢d̅ᵒ = ⊢d̅ᵒ
++-preserve (⊢; ⊢cᵒ ⊢c̅ᵒ) ⊢d̅ᵒ =
  ⊢; ⊢cᵒ (++-preserve ⊢c̅ᵒ ⊢d̅ᵒ)


private

  preserve-pair : ∀ {cᵒ₁ cᵒ₂ d̅ᵒ C₁ C₂ C₃}
    → ⊢ᵒ cᵒ₁ ; cᵒ₂ ⟶ d̅ᵒ
    → ⊢ᵒ cᵒ₁ ⦂ C₁ ⇒ C₂
    → ⊢ᵒ cᵒ₂ ⦂ C₂ ⇒ C₃
      ------------------------------
    → ⊢ᵒ̅ d̅ᵒ ⦂ C₁ ⇒ C₃
  preserve-pair collapse (⊢! g) (⊢? ℓ h) =
    ⊢[]
  preserve-pair (collide Gᵒ≢Hᵒ) (⊢! g) (⊢? ℓ h) =
    ⊢; (⊢⊥ _ _ ℓ) ⊢[]
  preserve-pair seq-fun (⊢fun ⊢c̅ᵒ₁ ⊢c̅ᵒ₂) (⊢fun ⊢d̅ᵒ₁ ⊢d̅ᵒ₂) =
    ⊢; (⊢fun (++-preserve ⊢d̅ᵒ₁ ⊢c̅ᵒ₁) (++-preserve ⊢c̅ᵒ₂ ⊢d̅ᵒ₂)) ⊢[]
  preserve-pair ⊥-left (⊢⊥ C₁ C₂ ℓ) ⊢cᵒ₂ =
    ⊢; (⊢⊥ C₁ _ ℓ) ⊢[]
  preserve-pair ⊥-right-! (⊢! g) (⊢⊥ .⋆ C₃ ℓ) =
    ⊢; (⊢⊥ _ C₃ ℓ) ⊢[]
  preserve-pair ⊥-right-fun (⊢fun ⊢c̅ᵒ₁ ⊢c̅ᵒ₂) (⊢⊥ _ C₃ ℓ) =
    ⊢; (⊢⊥ _ C₃ ℓ) ⊢[]


mutual

  preserveᵒ : ∀ {cᵒ d̅ᵒ C₁ C₂}
    → ⊢ᵒ cᵒ —→ d̅ᵒ
    → ⊢ᵒ cᵒ ⦂ C₁ ⇒ C₂
      -----------------------
    → ⊢ᵒ̅ d̅ᵒ ⦂ C₁ ⇒ C₂
  preserveᵒ id-fun (⊢fun ⊢[] ⊢[]) =
    ⊢[]
  preserveᵒ (ξ-fun-dom c̅ᵒ₁—→d̅ᵒ₁) (⊢fun ⊢c̅ᵒ₁ ⊢c̅ᵒ₂) =
    ⊢; (⊢fun (preserve c̅ᵒ₁—→d̅ᵒ₁ ⊢c̅ᵒ₁) ⊢c̅ᵒ₂) ⊢[]
  preserveᵒ (ξ-fun-cod nf not-blame c̅ᵒ₂—→d̅ᵒ₂) (⊢fun ⊢c̅ᵒ₁ ⊢c̅ᵒ₂) =
    ⊢; (⊢fun ⊢c̅ᵒ₁ (preserve c̅ᵒ₂—→d̅ᵒ₂ ⊢c̅ᵒ₂)) ⊢[]
  preserveᵒ ξ-⊥-fun-dom (⊢fun (⊢; (⊢⊥ C₃ C₁ ℓ) ⊢[]) ⊢c̅ᵒ₂) =
    ⊢; (⊢⊥ _ _ ℓ) ⊢[]
  preserveᵒ (ξ-⊥-fun-cod nf not-blame) (⊢fun ⊢c̅ᵒ₁ (⊢; (⊢⊥ C₂ C₄ ℓ) ⊢[])) =
    ⊢; (⊢⊥ _ _ ℓ) ⊢[]

  preserve : ∀ {c̅ᵒ d̅ᵒ C₁ C₂}
    → ⊢ᵒ̅ c̅ᵒ —→ d̅ᵒ
    → ⊢ᵒ̅ c̅ᵒ ⦂ C₁ ⇒ C₂
      ------------------------
    → ⊢ᵒ̅ d̅ᵒ ⦂ C₁ ⇒ C₂
  preserve (reduce-head cᵒ—→d̅ᵒ) (⊢; ⊢cᵒ ⊢c̅ᵒ) =
    ++-preserve (preserveᵒ cᵒ—→d̅ᵒ ⊢cᵒ) ⊢c̅ᵒ
  preserve (reduce-neighbors nf cᵒ₁;cᵒ₂⟶d̅ᵒ) (⊢; ⊢cᵒ₁ (⊢; ⊢cᵒ₂ ⊢c̅ᵒ)) =
    ++-preserve (preserve-pair cᵒ₁;cᵒ₂⟶d̅ᵒ ⊢cᵒ₁ ⊢cᵒ₂) ⊢c̅ᵒ
  preserve (reduce-tail nf irred cᵒ₂;c̅ᵒ—→d̅ᵒ) (⊢; ⊢cᵒ₁ ⊢cᵒ₂;c̅ᵒ) =
    ⊢; ⊢cᵒ₁ (preserve cᵒ₂;c̅ᵒ—→d̅ᵒ ⊢cᵒ₂;c̅ᵒ)
