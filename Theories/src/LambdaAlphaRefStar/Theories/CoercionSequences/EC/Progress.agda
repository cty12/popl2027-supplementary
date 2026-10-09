module LambdaAlphaRefStar.Theories.CoercionSequences.EC.Progress where

open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (refl)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Nullary.Negation using (contradiction)

open import LambdaAlphaRefStar.Theories.CoercionSequences.EC.Definition
open import LambdaAlphaRefStar.Theories.ECSubtypeDecidable using (ec-<:?)


data Progressᵉ (Θ : SubCtx) (cᵉ : ECSingleCoercion) : Set where

  stepᵉ : ∀ {d̅ᵉ}
    → Θ ⊢ᵉ cᵉ —→ d̅ᵉ
      ----------------------
    → Progressᵉ Θ cᵉ

  doneᵉ
    : SingleNF cᵉ
      ----------------------
    → Progressᵉ Θ cᵉ


data PairProgress (Θ : SubCtx) (cᵉ₁ cᵉ₂ : ECSingleCoercion) : Set where

  pair-step : ∀ {d̅ᵉ}
    → Θ ⊢ᵉ cᵉ₁ ; cᵉ₂ ⟶ d̅ᵉ
      ------------------------------
    → PairProgress Θ cᵉ₁ cᵉ₂

  pair-done
    : IrredPair cᵉ₁ cᵉ₂
      ------------------------------
    → PairProgress Θ cᵉ₁ cᵉ₂


data Progress (Θ : SubCtx) (c̅ᵉ : ECCoercionSeq) : Set where

  step : ∀ {d̅ᵉ}
    → Θ ⊢ᵉ̅ c̅ᵉ —→ d̅ᵉ
      ------------------
    → Progress Θ c̅ᵉ

  done :
    NF c̅ᵉ
      ------------------
    → Progress Θ c̅ᵉ


progressᵉ : ∀ {Δ Θ cᵉ ê₁ ê₂}
  → Δ ; Θ ⊢ᵉ cᵉ ⦂ ê₁ ⇒ ê₂
    ------------------------------
  → Progressᵉ Θ cᵉ
progressᵉ (⊢! e ⊢e) = doneᵉ nf-!
progressᵉ (⊢? e ⊢e ℓ) = doneᵉ nf-?
progressᵉ (⊢⊥ _ _ ℓ) = doneᵉ nf-⊥
progressᵉ (⊢↑ {ê₁ = ê₁} {ê₂ = ê₂} ⊢ê₁ ⊢ê₂ ê₁<:ê₂) with ê₁ ≡?ᵉ⋆ ê₂
... | yes refl = stepᵉ ↑-id
... | no ê₁≢ê₂ = doneᵉ (nf-↑ ê₁≢ê₂)


pair-progress : ∀ {Δ Θ cᵉ₁ cᵉ₂ ê₁ ê₂ ê₃}
  → SingleNF cᵉ₁
  → Δ ; Θ ⊢ᵉ cᵉ₁ ⦂ ê₁ ⇒ ê₂
  → Δ ; Θ ⊢ᵉ cᵉ₂ ⦂ ê₂ ⇒ ê₃
    ------------------------------
  → PairProgress Θ cᵉ₁ cᵉ₂
pair-progress nf-! (⊢! e ⊢e) (⊢? e′ ⊢e′ ℓ) with ec-<:? _ e e′
... | yes e<:e′ = pair-step (collapse e<:e′)
... | no e≮:e′ = pair-step (collide e≮:e′)
pair-progress nf-! (⊢! e ⊢e) (⊢↑ wf-⋆ wf-⋆ <:-⋆) =
  pair-done irred-!↑⋆
pair-progress nf-! (⊢! e ⊢e) (⊢⊥ _ _ ℓ) =
  pair-step (⊥-right (λ ()))
pair-progress nf-? (⊢? e ⊢e ℓ) (⊢! .e ⊢e′) =
  pair-done irred-?!
pair-progress nf-? (⊢? e ⊢e ℓ) (⊢↑ {ê₂ = ec e′} (wf-ec ⊢e′) (wf-ec ⊢e″) (<:-ec e′<:e″))
  with e ≡?ᵉ e′
... | yes refl = pair-done irred-?↑
... | no e≢e′ = pair-done irred-?↑
pair-progress nf-? (⊢? e ⊢e ℓ) (⊢⊥ _ _ ℓ′) =
  pair-step (⊥-right (λ ()))
pair-progress (nf-↑ ê≢ê′) (⊢↑ {ê₁ = ec e′} (wf-ec ⊢e′) (wf-ec ⊢e) (<:-ec e′<:e)) (⊢! e ⊢e″)
  with e′ ≡?ᵉ e
... | yes refl = contradiction refl ê≢ê′
... | no e′≢e = pair-done (irred-↑! e′≢e)
pair-progress (nf-↑ ê≢ê′) (⊢↑ wf-⋆ wf-⋆ <:-⋆) (⊢? e ⊢e ℓ) =
  contradiction refl ê≢ê′
pair-progress (nf-↑ ê≢ê′) (⊢↑ ⊢ê₁ ⊢ê₂ ê₁<:ê₂) (⊢↑ _ ⊢ê₃ ê₂<:ê₃) =
  pair-step ↑-collapse
pair-progress (nf-↑ ê≢ê′) (⊢↑ ⊢ê₁ ⊢ê₂ ê₁<:ê₂) (⊢⊥ _ _ ℓ) =
  pair-step (⊥-right (λ ()))
pair-progress nf-⊥ (⊢⊥ ⊢ê₁ ⊢ê₂ ℓ) ⊢cᵉ₂ =
  pair-step ⊥-left


progress : ∀ {Δ Θ c̅ᵉ ê₁ ê₂}
  → Δ ; Θ ⊢ᵉ̅ c̅ᵉ ⦂ ê₁ ⇒ ê₂
    ------------------------------
  → Progress Θ c̅ᵉ
progress (⊢[] _) =
  done nf-empty
progress (⊢; ⊢cᵉ (⊢[] _)) with progressᵉ ⊢cᵉ
... | stepᵉ cᵉ—→d̅ᵉ = step (reduce-head cᵉ—→d̅ᵉ)
... | doneᵉ snf = done (nf-singleton snf)
progress (⊢; ⊢cᵉ₁ (⊢; ⊢cᵉ₂ ⊢c̅ᵉ)) with progressᵉ ⊢cᵉ₁ | progress (⊢; ⊢cᵉ₂ ⊢c̅ᵉ)
... | stepᵉ cᵉ₁—→d̅ᵉ | _ = step (reduce-head cᵉ₁—→d̅ᵉ)
... | doneᵉ snf₁ | tail-progress with pair-progress snf₁ ⊢cᵉ₁ ⊢cᵉ₂
...   | pair-step cᵉ₁;cᵉ₂⟶d̅ᵉ = step (reduce-neighbors snf₁ cᵉ₁;cᵉ₂⟶d̅ᵉ)
...   | pair-done irred with tail-progress
...     | step cᵉ₂;c̅ᵉ—→d̅ᵉ = step (reduce-tail snf₁ irred cᵉ₂;c̅ᵉ—→d̅ᵉ)
...     | done nf-tail = done (nf-step snf₁ irred nf-tail)
