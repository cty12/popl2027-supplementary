module LambdaAlphaRefStar.Theories.CoercionSequences.Code.Determinism where

open import Data.Empty using (⊥-elim)
open import Data.List using (_++_; [_])
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import Relation.Nullary using (¬_)

open import LambdaAlphaRefStar.Theories.CoercionSequences.Code.Definition


private

  pair-deterministic : ∀ {cᵒ₁ cᵒ₂ d̅ᵒ₁ d̅ᵒ₂}
    → ⊢ᵒ cᵒ₁ ; cᵒ₂ ⟶ d̅ᵒ₁
    → ⊢ᵒ cᵒ₁ ; cᵒ₂ ⟶ d̅ᵒ₂
      -----------------------
    → d̅ᵒ₁ ≡ d̅ᵒ₂
  pair-deterministic collapse collapse = refl
  pair-deterministic collapse (collide Gᵒ≢Gᵒ) = ⊥-elim (Gᵒ≢Gᵒ refl)
  pair-deterministic (collide Gᵒ≢Gᵒ) collapse = ⊥-elim (Gᵒ≢Gᵒ refl)
  pair-deterministic (collide Gᵒ≢Hᵒ) (collide Gᵒ≢Hᵒ′) = refl
  pair-deterministic seq-fun seq-fun = refl
  pair-deterministic ⊥-left ⊥-left = refl
  pair-deterministic ⊥-right-! ⊥-right-! = refl
  pair-deterministic ⊥-right-fun ⊥-right-fun = refl

  irred-no-pair-step : ∀ {cᵒ₁ cᵒ₂ dᵒ}
    → IrredPair cᵒ₁ cᵒ₂
      --------------------------
    → ¬ (⊢ᵒ cᵒ₁ ; cᵒ₂ ⟶ dᵒ)
  irred-no-pair-step irred-?! ()
  irred-no-pair-step irred-?fun ()
  irred-no-pair-step irred-fun! ()
  irred-no-pair-step irred-?⊥ ()

  mutual

    single-nf-no-step : ∀ {cᵒ d̅ᵒ}
      → SingleNF cᵒ
        ----------------
      → ¬ (⊢ᵒ cᵒ —→ d̅ᵒ)
    single-nf-no-step nf-! ()
    single-nf-no-step nf-? ()
    single-nf-no-step nf-⊥ ()
    single-nf-no-step (nf-fun nf₁ nf₂ not-both-id not-blame₁ not-blame₂) id-fun =
      not-both-id (refl , refl)
    single-nf-no-step (nf-fun nf₁ nf₂ _ _ _) (ξ-fun-dom c̅ᵒ₁—→d̅ᵒ₁) =
      nf-no-step nf₁ c̅ᵒ₁—→d̅ᵒ₁
    single-nf-no-step (nf-fun nf₁ nf₂ _ _ _) (ξ-fun-cod _ _ c̅ᵒ₂—→d̅ᵒ₂) =
      nf-no-step nf₂ c̅ᵒ₂—→d̅ᵒ₂
    single-nf-no-step (nf-fun _ _ _ not-blame _) ξ-⊥-fun-dom =
      not-blame (_ , refl)
    single-nf-no-step (nf-fun _ _ _ _ not-blame) (ξ-⊥-fun-cod _ _) =
      not-blame (_ , refl)

    nf-no-step : ∀ {c̅ᵒ d̅ᵒ}
      → NF c̅ᵒ
        -----------------
      → ¬ (⊢ᵒ̅ c̅ᵒ —→ d̅ᵒ)
    nf-no-step nf-empty ()
    nf-no-step (nf-singleton snf) (reduce-head cᵒ—→dᵒ) =
      single-nf-no-step snf cᵒ—→dᵒ
    nf-no-step (nf-step snf irred nf-tail) (reduce-head cᵒ—→dᵒ) =
      single-nf-no-step snf cᵒ—→dᵒ
    nf-no-step (nf-step snf irred nf-tail) (reduce-neighbors nf cᵒ₁;cᵒ₂⟶dᵒ) =
      irred-no-pair-step irred cᵒ₁;cᵒ₂⟶dᵒ
    nf-no-step (nf-step snf irred nf-tail) (reduce-tail _ _ cᵒ₂;c̅ᵒ—→d̅ᵒ) =
      nf-no-step nf-tail cᵒ₂;c̅ᵒ—→d̅ᵒ


mutual

  deterministicᵒ : ∀ {cᵒ d̅ᵒ₁ d̅ᵒ₂}
    → ⊢ᵒ cᵒ —→ d̅ᵒ₁
    → ⊢ᵒ cᵒ —→ d̅ᵒ₂
      ----------------
    → d̅ᵒ₁ ≡ d̅ᵒ₂
  deterministicᵒ id-fun id-fun = refl
  deterministicᵒ id-fun (ξ-fun-dom c̅ᵒ₁—→d̅ᵒ₁) =
    ⊥-elim (nf-no-step nf-empty c̅ᵒ₁—→d̅ᵒ₁)
  deterministicᵒ id-fun (ξ-fun-cod nf not-blame c̅ᵒ₂—→d̅ᵒ₂) =
    ⊥-elim (nf-no-step nf-empty c̅ᵒ₂—→d̅ᵒ₂)
  deterministicᵒ (ξ-fun-dom c̅ᵒ₁—→d̅ᵒ₁) id-fun =
    ⊥-elim (nf-no-step nf-empty c̅ᵒ₁—→d̅ᵒ₁)
  deterministicᵒ (ξ-fun-dom c̅ᵒ₁—→d̅ᵒ₁) (ξ-fun-dom c̅ᵒ₁—→d̅ᵒ₂) =
    cong (λ d̅ᵒ → [ d̅ᵒ ⇒ _ ]) (deterministic c̅ᵒ₁—→d̅ᵒ₁ c̅ᵒ₁—→d̅ᵒ₂)
  deterministicᵒ (ξ-fun-dom c̅ᵒ₁—→d̅ᵒ₁) (ξ-fun-cod nf not-blame c̅ᵒ₂—→d̅ᵒ₂) =
    ⊥-elim (nf-no-step nf c̅ᵒ₁—→d̅ᵒ₁)
  deterministicᵒ (ξ-fun-dom c̅ᵒ₁—→d̅ᵒ₁) ξ-⊥-fun-dom =
    ⊥-elim (nf-no-step (nf-singleton nf-⊥) c̅ᵒ₁—→d̅ᵒ₁)
  deterministicᵒ (ξ-fun-dom c̅ᵒ₁—→d̅ᵒ₁) (ξ-⊥-fun-cod nf not-blame) =
    ⊥-elim (nf-no-step nf c̅ᵒ₁—→d̅ᵒ₁)
  deterministicᵒ (ξ-fun-cod nf not-blame c̅ᵒ₂—→d̅ᵒ₁) id-fun =
    ⊥-elim (nf-no-step nf-empty c̅ᵒ₂—→d̅ᵒ₁)
  deterministicᵒ (ξ-fun-cod nf not-blame c̅ᵒ₂—→d̅ᵒ₁) (ξ-fun-dom c̅ᵒ₁—→d̅ᵒ₂) =
    ⊥-elim (nf-no-step nf c̅ᵒ₁—→d̅ᵒ₂)
  deterministicᵒ (ξ-fun-cod nf not-blame c̅ᵒ₂—→d̅ᵒ₁) (ξ-fun-cod nf′ not-blame′ c̅ᵒ₂—→d̅ᵒ₂) =
    cong (λ d̅ᵒ → [ _ ⇒ d̅ᵒ ]) (deterministic c̅ᵒ₂—→d̅ᵒ₁ c̅ᵒ₂—→d̅ᵒ₂)
  deterministicᵒ (ξ-fun-cod nf not-blame c̅ᵒ₂—→d̅ᵒ₁) ξ-⊥-fun-dom =
    ⊥-elim (not-blame (_ , refl))
  deterministicᵒ (ξ-fun-cod nf not-blame c̅ᵒ₂—→d̅ᵒ₁) (ξ-⊥-fun-cod nf′ not-blame′) =
    ⊥-elim (nf-no-step (nf-singleton nf-⊥) c̅ᵒ₂—→d̅ᵒ₁)
  deterministicᵒ ξ-⊥-fun-dom (ξ-fun-dom c̅ᵒ₁—→d̅ᵒ₂) =
    ⊥-elim (nf-no-step (nf-singleton nf-⊥) c̅ᵒ₁—→d̅ᵒ₂)
  deterministicᵒ ξ-⊥-fun-dom (ξ-fun-cod nf not-blame c̅ᵒ₂—→d̅ᵒ₂) =
    ⊥-elim (not-blame (_ , refl))
  deterministicᵒ ξ-⊥-fun-dom ξ-⊥-fun-dom = refl
  deterministicᵒ ξ-⊥-fun-dom (ξ-⊥-fun-cod nf not-blame) =
    ⊥-elim (not-blame (_ , refl))
  deterministicᵒ (ξ-⊥-fun-cod nf not-blame) (ξ-fun-dom c̅ᵒ₁—→d̅ᵒ₂) =
    ⊥-elim (nf-no-step nf c̅ᵒ₁—→d̅ᵒ₂)
  deterministicᵒ (ξ-⊥-fun-cod nf not-blame) (ξ-fun-cod nf′ not-blame′ c̅ᵒ₂—→d̅ᵒ₂) =
    ⊥-elim (nf-no-step (nf-singleton nf-⊥) c̅ᵒ₂—→d̅ᵒ₂)
  deterministicᵒ (ξ-⊥-fun-cod nf not-blame) ξ-⊥-fun-dom =
    ⊥-elim (not-blame (_ , refl))
  deterministicᵒ (ξ-⊥-fun-cod nf not-blame) (ξ-⊥-fun-cod nf′ not-blame′) = refl

  deterministic : ∀ {c̅ᵒ d̅ᵒ₁ d̅ᵒ₂}
    → ⊢ᵒ̅ c̅ᵒ —→ d̅ᵒ₁
    → ⊢ᵒ̅ c̅ᵒ —→ d̅ᵒ₂
      -----------------
    → d̅ᵒ₁ ≡ d̅ᵒ₂
  deterministic (reduce-head cᵒ—→dᵒ₁) (reduce-head cᵒ—→dᵒ₂) =
    cong (λ d̅ᵒ → d̅ᵒ ++ _) (deterministicᵒ cᵒ—→dᵒ₁ cᵒ—→dᵒ₂)
  deterministic (reduce-head cᵒ—→dᵒ) (reduce-neighbors nf cᵒ₁;cᵒ₂⟶dᵒ) =
    ⊥-elim (single-nf-no-step nf cᵒ—→dᵒ)
  deterministic (reduce-head cᵒ—→dᵒ) (reduce-tail nf irred cᵒ₂;c̅ᵒ—→d̅ᵒ) =
    ⊥-elim (single-nf-no-step nf cᵒ—→dᵒ)
  deterministic (reduce-neighbors nf cᵒ₁;cᵒ₂⟶dᵒ) (reduce-head cᵒ—→dᵒ) =
    ⊥-elim (single-nf-no-step nf cᵒ—→dᵒ)
  deterministic (reduce-neighbors nf cᵒ₁;cᵒ₂⟶dᵒ₁) (reduce-neighbors nf′ cᵒ₁;cᵒ₂⟶dᵒ₂) =
    cong (λ d̅ᵒ → d̅ᵒ ++ _) (pair-deterministic cᵒ₁;cᵒ₂⟶dᵒ₁ cᵒ₁;cᵒ₂⟶dᵒ₂)
  deterministic (reduce-neighbors nf cᵒ₁;cᵒ₂⟶dᵒ) (reduce-tail nf′ irred cᵒ₂;c̅ᵒ—→d̅ᵒ) =
    ⊥-elim (irred-no-pair-step irred cᵒ₁;cᵒ₂⟶dᵒ)
  deterministic (reduce-tail nf irred cᵒ₂;c̅ᵒ—→d̅ᵒ) (reduce-head cᵒ—→dᵒ) =
    ⊥-elim (single-nf-no-step nf cᵒ—→dᵒ)
  deterministic (reduce-tail nf irred cᵒ₂;c̅ᵒ—→d̅ᵒ) (reduce-neighbors nf′ cᵒ₁;cᵒ₂⟶dᵒ) =
    ⊥-elim (irred-no-pair-step irred cᵒ₁;cᵒ₂⟶dᵒ)
  deterministic (reduce-tail nf irred cᵒ₂;c̅ᵒ—→d̅ᵒ₁) (reduce-tail nf′ irred′ cᵒ₂;c̅ᵒ—→d̅ᵒ₂) =
    cong (λ d̅ᵒ → _ ; d̅ᵒ) (deterministic cᵒ₂;c̅ᵒ—→d̅ᵒ₁ cᵒ₂;c̅ᵒ—→d̅ᵒ₂)
