module LambdaAlphaRefStar.Theories.CoercionSequences.EC.Determinism where

open import Data.Empty using (⊥-elim)
open import Data.List using (_++_)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import Relation.Nullary using (¬_)

open import LambdaAlphaRefStar.Theories.CoercionSequences.EC.Definition


private

  single-deterministic : ∀ {Θ cᵉ d̅ᵉ₁ d̅ᵉ₂}
    → Θ ⊢ᵉ cᵉ —→ d̅ᵉ₁
    → Θ ⊢ᵉ cᵉ —→ d̅ᵉ₂
      ------------------
    → d̅ᵉ₁ ≡ d̅ᵉ₂
  single-deterministic ↑-id ↑-id = refl

  single-nf-no-step : ∀ {Θ cᵉ d̅ᵉ}
    → SingleNF cᵉ
      -------------------------
    → ¬ (Θ ⊢ᵉ cᵉ —→ d̅ᵉ)
  single-nf-no-step nf-! ()
  single-nf-no-step nf-? ()
  single-nf-no-step (nf-↑ ê₁≢ê₂) ↑-id = ê₁≢ê₂ refl
  single-nf-no-step nf-⊥ ()

  pair-deterministic : ∀ {Θ cᵉ₁ cᵉ₂ d̅ᵉ₁ d̅ᵉ₂}
    → Θ ⊢ᵉ cᵉ₁ ; cᵉ₂ ⟶ d̅ᵉ₁
    → Θ ⊢ᵉ cᵉ₁ ; cᵉ₂ ⟶ d̅ᵉ₂
      --------------------------
    → d̅ᵉ₁ ≡ d̅ᵉ₂
  pair-deterministic (collapse e₁<:e₂) (collapse e₁<:e₂′) = refl
  pair-deterministic (collapse e₁<:e₂) (collide e₁≮:e₂) =
    ⊥-elim (e₁≮:e₂ e₁<:e₂)
  pair-deterministic (collide e₁≮:e₂) (collapse e₁<:e₂) =
    ⊥-elim (e₁≮:e₂ e₁<:e₂)
  pair-deterministic (collide e₁≮:e₂) (collide e₁≮:e₂′) = refl
  pair-deterministic ↑-collapse ↑-collapse = refl
  pair-deterministic ⊥-left ⊥-left = refl
  pair-deterministic ⊥-left (⊥-right not-blame) =
    ⊥-elim (not-blame (_ , refl))
  pair-deterministic (⊥-right not-blame) ⊥-left =
    ⊥-elim (not-blame (_ , refl))
  pair-deterministic (⊥-right not-blame) (⊥-right not-blame′) = refl

  irred-no-pair-step : ∀ {Θ cᵉ₁ cᵉ₂ d̅ᵉ}
    → IrredPair cᵉ₁ cᵉ₂
      ------------------------------
    → ¬ (Θ ⊢ᵉ cᵉ₁ ; cᵉ₂ ⟶ d̅ᵉ)
  irred-no-pair-step irred-?! ()
  irred-no-pair-step (irred-↑! e′≢e) ()
  irred-no-pair-step irred-!↑⋆ ()
  irred-no-pair-step irred-?↑ ()

  nf-no-step : ∀ {Θ c̅ᵉ d̅ᵉ}
    → NF c̅ᵉ
      --------------------------
    → ¬ (Θ ⊢ᵉ̅ c̅ᵉ —→ d̅ᵉ)
  nf-no-step nf-empty ()
  nf-no-step (nf-singleton snf) (reduce-head cᵉ—→d̅ᵉ) =
    single-nf-no-step snf cᵉ—→d̅ᵉ
  nf-no-step (nf-step snf irred nf-tail) (reduce-head cᵉ—→d̅ᵉ) =
    single-nf-no-step snf cᵉ—→d̅ᵉ
  nf-no-step (nf-step snf irred nf-tail) (reduce-neighbors _ cᵉ₁;cᵉ₂⟶dᵉ) =
    irred-no-pair-step irred cᵉ₁;cᵉ₂⟶dᵉ
  nf-no-step (nf-step snf irred nf-tail) (reduce-tail _ _ cᵉ₂;c̅ᵉ—→d̅ᵉ) =
    nf-no-step nf-tail cᵉ₂;c̅ᵉ—→d̅ᵉ


deterministic : ∀ {Θ c̅ᵉ d̅ᵉ₁ d̅ᵉ₂}
  → Θ ⊢ᵉ̅ c̅ᵉ —→ d̅ᵉ₁
  → Θ ⊢ᵉ̅ c̅ᵉ —→ d̅ᵉ₂
    ------------------
  → d̅ᵉ₁ ≡ d̅ᵉ₂
deterministic (reduce-head cᵉ—→d̅ᵉ₁) (reduce-head cᵉ—→d̅ᵉ₂) =
  cong (λ d̅ᵉ → d̅ᵉ ++ _) (single-deterministic cᵉ—→d̅ᵉ₁ cᵉ—→d̅ᵉ₂)
deterministic (reduce-head cᵉ—→d̅ᵉ) (reduce-neighbors snf cᵉ₁;cᵉ₂⟶d̅ᵉ) =
  ⊥-elim (single-nf-no-step snf cᵉ—→d̅ᵉ)
deterministic (reduce-head cᵉ—→d̅ᵉ) (reduce-tail snf irred cᵉ₂;c̅ᵉ—→d̅ᵉ) =
  ⊥-elim (single-nf-no-step snf cᵉ—→d̅ᵉ)
deterministic (reduce-neighbors snf cᵉ₁;cᵉ₂⟶d̅ᵉ) (reduce-head cᵉ—→d̅ᵉ) =
  ⊥-elim (single-nf-no-step snf cᵉ—→d̅ᵉ)
deterministic (reduce-neighbors snf cᵉ₁;cᵉ₂⟶d̅ᵉ₁) (reduce-neighbors snf′ cᵉ₁;cᵉ₂⟶d̅ᵉ₂) =
  cong (λ d̅ᵉ → d̅ᵉ ++ _) (pair-deterministic cᵉ₁;cᵉ₂⟶d̅ᵉ₁ cᵉ₁;cᵉ₂⟶d̅ᵉ₂)
deterministic (reduce-neighbors snf cᵉ₁;cᵉ₂⟶d̅ᵉ) (reduce-tail snf′ irred cᵉ₂;c̅ᵉ—→d̅ᵉ) =
  ⊥-elim (irred-no-pair-step irred cᵉ₁;cᵉ₂⟶d̅ᵉ)
deterministic (reduce-tail snf irred cᵉ₂;c̅ᵉ—→d̅ᵉ) (reduce-head cᵉ—→d̅ᵉ) =
  ⊥-elim (single-nf-no-step snf cᵉ—→d̅ᵉ)
deterministic (reduce-tail snf irred cᵉ₂;c̅ᵉ—→d̅ᵉ) (reduce-neighbors snf′ cᵉ₁;cᵉ₂⟶d̅ᵉ) =
  ⊥-elim (irred-no-pair-step irred cᵉ₁;cᵉ₂⟶d̅ᵉ)
deterministic (reduce-tail snf irred cᵉ₂;c̅ᵉ—→d̅ᵉ₁) (reduce-tail snf′ irred′ cᵉ₂;c̅ᵉ—→d̅ᵉ₂) =
  cong (λ d̅ᵉ → _ ; d̅ᵉ) (deterministic cᵉ₂;c̅ᵉ—→d̅ᵉ₁ cᵉ₂;c̅ᵉ—→d̅ᵉ₂)
