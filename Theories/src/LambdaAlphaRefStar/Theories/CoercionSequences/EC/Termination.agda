module LambdaAlphaRefStar.Theories.CoercionSequences.EC.Termination where

open import Data.List using ([]; _∷_; _++_)
open import Data.Nat using (ℕ; zero; suc; _+_; _<_; z≤n; s≤s)
open import Data.Nat.Induction using (<-wellFounded)
open import Data.Nat.Properties using (n<1+n; +-monoˡ-<)
open import Data.Product using (_×_; ∃-syntax) renaming (_,_ to ⟨_,_⟩)
open import Induction.WellFounded using (Acc; acc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import LambdaAlphaRefStar.Theories.CoercionSequences.EC.Definition
open import LambdaAlphaRefStar.Theories.CoercionSequences.EC.Progress
  using (Progress; progress)
open import LambdaAlphaRefStar.Theories.CoercionSequences.EC.Preservation
  using (preserve)


seqSize : ECCoercionSeq → ℕ
seqSize [] = zero
seqSize (cᵉ ; c̅ᵉ) = suc (seqSize c̅ᵉ)

seqSize-++ : ∀ c̅ᵉ d̅ᵉ → seqSize (c̅ᵉ ++ d̅ᵉ) ≡ seqSize c̅ᵉ + seqSize d̅ᵉ
seqSize-++ [] d̅ᵉ = refl
seqSize-++ (cᵉ ; c̅ᵉ) d̅ᵉ rewrite seqSize-++ c̅ᵉ d̅ᵉ = refl


single-step-decreases : ∀ {Θ cᵉ d̅ᵉ}
  → Θ ⊢ᵉ cᵉ —→ d̅ᵉ
    --------------------------
  → seqSize d̅ᵉ < suc zero
single-step-decreases ↑-id = s≤s z≤n

pair-step-decreases : ∀ {Θ cᵉ₁ cᵉ₂ d̅ᵉ}
  → Θ ⊢ᵉ cᵉ₁ ; cᵉ₂ ⟶ d̅ᵉ
    --------------------------
  → seqSize d̅ᵉ < suc (suc zero)
pair-step-decreases (collapse e₁<:e₂) = n<1+n 1
pair-step-decreases (collide e₁≮:e₂) = n<1+n 1
pair-step-decreases ↑-collapse = n<1+n 1
pair-step-decreases ⊥-left = n<1+n 1
pair-step-decreases (⊥-right not-blame) = n<1+n 1

seq-step-decreases : ∀ {Θ c̅ᵉ d̅ᵉ}
  → Θ ⊢ᵉ̅ c̅ᵉ —→ d̅ᵉ
    ------------------------------
  → seqSize d̅ᵉ < seqSize c̅ᵉ
seq-step-decreases (reduce-head {d̅ᵉ = d̅ᵉ} {c̅ᵉ = c̅ᵉ} cᵉ—→d̅ᵉ)
  rewrite seqSize-++ d̅ᵉ c̅ᵉ =
  +-monoˡ-< (seqSize c̅ᵉ) (single-step-decreases cᵉ—→d̅ᵉ)
seq-step-decreases (reduce-neighbors {d̅ᵉ = d̅ᵉ} {c̅ᵉ = c̅ᵉ} _ cᵉ₁;cᵉ₂⟶dᵉ)
  rewrite seqSize-++ d̅ᵉ c̅ᵉ =
  +-monoˡ-< (seqSize c̅ᵉ) (pair-step-decreases cᵉ₁;cᵉ₂⟶dᵉ)
seq-step-decreases (reduce-tail {cᵉ₁ = cᵉ₁} _ irred cᵉ₂;c̅ᵉ—→d̅ᵉ) =
  s≤s (seq-step-decreases cᵉ₂;c̅ᵉ—→d̅ᵉ)


private

  -- | Well-founded induction on seqSize. Each reduction step uses
  -- | seq-step-decreases to justify the recursive call at a smaller measure.
  normalize-acc : ∀ {Δ Θ c̅ᵉ ê₁ ê₂}
    → Acc _<_ (seqSize c̅ᵉ)
    → Δ ; Θ ⊢ᵉ̅ c̅ᵉ ⦂ ê₁ ⇒ ê₂
      ---------------------------------------
    → ∃[ d̅ᵉ ] Θ ⊢ᵉ̅ c̅ᵉ —↠ d̅ᵉ × (NF d̅ᵉ)
  normalize-acc (acc rec) ⊢c̅ᵉ with progress ⊢c̅ᵉ
  ... | Progress.done nf =
    ⟨ _ , ⟨ ↠-refl , nf ⟩ ⟩
  ... | Progress.step c̅ᵉ—→d̅ᵉ
      with normalize-acc (rec (seq-step-decreases c̅ᵉ—→d̅ᵉ)) (preserve c̅ᵉ—→d̅ᵉ ⊢c̅ᵉ)
  ...   | ⟨ e̅ᵉ , ⟨ d̅ᵉ—↠e̅ᵉ , nf ⟩ ⟩ =
    ⟨ e̅ᵉ , ⟨ ↠-step c̅ᵉ—→d̅ᵉ d̅ᵉ—↠e̅ᵉ , nf ⟩ ⟩


terminates : ∀ {Δ Θ c̅ᵉ ê₁ ê₂}
  → Δ ; Θ ⊢ᵉ̅ c̅ᵉ ⦂ ê₁ ⇒ ê₂
    -------------------------
  → ∃[ d̅ᵉ ] Θ ⊢ᵉ̅ c̅ᵉ —↠ d̅ᵉ × (NF d̅ᵉ)
terminates {c̅ᵉ = c̅ᵉ} ⊢c̅ᵉ = normalize-acc (<-wellFounded (seqSize c̅ᵉ)) ⊢c̅ᵉ
