module LambdaAlphaRefStar.Theories.CoercionSequences.EC.Preservation where

open import Data.List using (_++_)

open import LambdaAlphaRefStar.Theories.CoercionSequences.EC.Definition


wf-domᵉ : ∀ {Δ Θ cᵉ ê₁ ê₂}
  → Δ ; Θ ⊢ᵉ cᵉ ⦂ ê₁ ⇒ ê₂
    ------------------------------
  → Δ ⊢ᵉ⋆ ê₁
wf-domᵉ (⊢! e ⊢e) = wf-ec ⊢e
wf-domᵉ (⊢? e ⊢e ℓ) = wf-⋆
wf-domᵉ (⊢↑ ⊢ê₁ ⊢ê₂ ê₁<:ê₂) = ⊢ê₁
wf-domᵉ (⊢⊥ ⊢ê₁ ⊢ê₂ ℓ) = ⊢ê₁

wf-codᵉ : ∀ {Δ Θ cᵉ ê₁ ê₂}
  → Δ ; Θ ⊢ᵉ cᵉ ⦂ ê₁ ⇒ ê₂
    ------------------------------
  → Δ ⊢ᵉ⋆ ê₂
wf-codᵉ (⊢! e ⊢e) = wf-⋆
wf-codᵉ (⊢? e ⊢e ℓ) = wf-ec ⊢e
wf-codᵉ (⊢↑ ⊢ê₁ ⊢ê₂ ê₁<:ê₂) = ⊢ê₂
wf-codᵉ (⊢⊥ ⊢ê₁ ⊢ê₂ ℓ) = ⊢ê₂

wf-domᵉ̅ : ∀ {Δ Θ c̅ᵉ ê₁ ê₂}
  → Δ ; Θ ⊢ᵉ̅ c̅ᵉ ⦂ ê₁ ⇒ ê₂
    --------------------------------
  → Δ ⊢ᵉ⋆ ê₁
wf-domᵉ̅ (⊢[] ⊢ê) = ⊢ê
wf-domᵉ̅ (⊢; ⊢cᵉ ⊢c̅ᵉ) = wf-domᵉ ⊢cᵉ

wf-codᵉ̅ : ∀ {Δ Θ c̅ᵉ ê₁ ê₂}
  → Δ ; Θ ⊢ᵉ̅ c̅ᵉ ⦂ ê₁ ⇒ ê₂
    --------------------------------
  → Δ ⊢ᵉ⋆ ê₂
wf-codᵉ̅ (⊢[] ⊢ê) = ⊢ê
wf-codᵉ̅ (⊢; ⊢cᵉ ⊢c̅ᵉ) = wf-codᵉ̅ ⊢c̅ᵉ


++ᵉ-preserve : ∀ {Δ Θ c̅ᵉ d̅ᵉ ê₁ ê₂ ê₃}
  → Δ ; Θ ⊢ᵉ̅ c̅ᵉ ⦂ ê₁ ⇒ ê₂
  → Δ ; Θ ⊢ᵉ̅ d̅ᵉ ⦂ ê₂ ⇒ ê₃
    --------------------------------------
  → Δ ; Θ ⊢ᵉ̅ c̅ᵉ ++ d̅ᵉ ⦂ ê₁ ⇒ ê₃
++ᵉ-preserve (⊢[] _) ⊢d̅ᵉ = ⊢d̅ᵉ
++ᵉ-preserve (⊢; ⊢cᵉ ⊢c̅ᵉ) ⊢d̅ᵉ =
  ⊢; ⊢cᵉ (++ᵉ-preserve ⊢c̅ᵉ ⊢d̅ᵉ)


private

  preserveᵉ : ∀ {Δ Θ cᵉ d̅ᵉ ê₁ ê₂}
    → Θ ⊢ᵉ cᵉ —→ d̅ᵉ
    → Δ ; Θ ⊢ᵉ cᵉ ⦂ ê₁ ⇒ ê₂
      ----------------------------------
    → Δ ; Θ ⊢ᵉ̅ d̅ᵉ ⦂ ê₁ ⇒ ê₂
  preserveᵉ ↑-id (⊢↑ ⊢ê _ _) =
    ⊢[] ⊢ê

  preserve-pair : ∀ {Δ Θ cᵉ₁ cᵉ₂ d̅ᵉ ê₁ ê₂ ê₃}
    → Θ ⊢ᵉ cᵉ₁ ; cᵉ₂ ⟶ d̅ᵉ
    → Δ ; Θ ⊢ᵉ cᵉ₁ ⦂ ê₁ ⇒ ê₂
    → Δ ; Θ ⊢ᵉ cᵉ₂ ⦂ ê₂ ⇒ ê₃
      ----------------------------------
    → Δ ; Θ ⊢ᵉ̅ d̅ᵉ ⦂ ê₁ ⇒ ê₃
  preserve-pair (collapse e₁<:e₂) (⊢! e₁ ⊢e₁) (⊢? e₂ ⊢e₂ ℓ) =
    ⊢; (⊢↑ (wf-ec ⊢e₁) (wf-ec ⊢e₂) (<:-ec e₁<:e₂)) (⊢[] (wf-ec ⊢e₂))
  preserve-pair (collide _) (⊢! e₁ ⊢e₁) (⊢? e₂ ⊢e₂ ℓ) =
    ⊢; (⊢⊥ (wf-ec ⊢e₁) (wf-ec ⊢e₂) ℓ) (⊢[] (wf-ec ⊢e₂))
  preserve-pair ↑-collapse (⊢↑ ⊢ê₁ ⊢ê₂ ê₁<:ê₂) (⊢↑ _ ⊢ê₃ ê₂<:ê₃) =
    ⊢; (⊢↑ ⊢ê₁ ⊢ê₃ (<:⋆-trans ê₁<:ê₂ ê₂<:ê₃)) (⊢[] ⊢ê₃)
  preserve-pair ⊥-left (⊢⊥ ⊢ê₁ ⊢ê₂ ℓ) ⊢cᵉ₂ =
    ⊢; (⊢⊥ ⊢ê₁ (wf-codᵉ ⊢cᵉ₂) ℓ) (⊢[] (wf-codᵉ ⊢cᵉ₂))
  preserve-pair (⊥-right not-blame) ⊢cᵉ₁ (⊢⊥ ⊢ê₂ ⊢ê₃ ℓ) =
    ⊢; (⊢⊥ (wf-domᵉ ⊢cᵉ₁) ⊢ê₃ ℓ) (⊢[] ⊢ê₃)


preserve : ∀ {Δ Θ c̅ᵉ d̅ᵉ ê₁ ê₂}
  → Θ ⊢ᵉ̅ c̅ᵉ —→ d̅ᵉ
  → Δ ; Θ ⊢ᵉ̅ c̅ᵉ ⦂ ê₁ ⇒ ê₂
    ---------------------------------
  → Δ ; Θ ⊢ᵉ̅ d̅ᵉ ⦂ ê₁ ⇒ ê₂
preserve (reduce-head cᵉ—→d̅ᵉ) (⊢; ⊢cᵉ ⊢c̅ᵉ) =
  ++ᵉ-preserve (preserveᵉ cᵉ—→d̅ᵉ ⊢cᵉ) ⊢c̅ᵉ
preserve (reduce-neighbors _ cᵉ₁;cᵉ₂⟶dᵉ) (⊢; ⊢cᵉ₁ (⊢; ⊢cᵉ₂ ⊢c̅ᵉ)) =
  ++ᵉ-preserve (preserve-pair cᵉ₁;cᵉ₂⟶dᵉ ⊢cᵉ₁ ⊢cᵉ₂) ⊢c̅ᵉ
preserve (reduce-tail snf irred cᵉ₂;c̅ᵉ—→d̅ᵉ) (⊢; ⊢cᵉ₁ ⊢cᵉ₂;c̅ᵉ) =
  ⊢; ⊢cᵉ₁ (preserve cᵉ₂;c̅ᵉ—→d̅ᵉ ⊢cᵉ₂;c̅ᵉ)
