module Theories.CoercionSequences.Code.Termination where

open import Data.List using ([]; _++_)
open import Data.Nat using (ℕ; zero; suc; _+_; _<_; z≤n; s≤s)
open import Data.Nat.Induction using (<-wellFounded)
open import Data.Nat.Properties using
  (0<1+n; n<1+n; m<m+n; +-assoc; +-comm; +-identityʳ; +-monoˡ-<; +-monoʳ-<)
open import Data.Nat.Solver using (module +-*-Solver)
open import Data.Product using (_×_; ∃-syntax) renaming (_,_ to ⟨_,_⟩)
open import Induction.WellFounded using (Acc; acc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)

open import Theories.CoercionSequences.Code.Definition
open import Theories.CoercionSequences.Code.Progress
  using (Progress; progress)
open import Theories.CoercionSequences.Code.Preservation
  using (preserve)


mutual

  -- | Syntactically, a coercion sequence is a list of higher-order coercions
  -- | (trees). The measure below counts the total number of coercion nodes in
  -- | that forest. For example, a function coercion contributes one node plus
  -- | the sizes of its two children.
  singleSize : OSingleCoercion → ℕ
  singleSize ((Gᵒ ！) g) = 1
  singleSize ((Gᵒ ？ ℓ) g) = 1
  singleSize (c̅ᵒ₁ ⇒ c̅ᵒ₂) = 1 + (seqSize c̅ᵒ₁ + seqSize c̅ᵒ₂)
  singleSize (⊥ ℓ) = 1

  seqSize : OCoercionSeq → ℕ
  seqSize [] = 0
  seqSize (cᵒ ; c̅ᵒ) = singleSize cᵒ + seqSize c̅ᵒ


private

  singleSize-positive : ∀ cᵒ → 0 < singleSize cᵒ
  singleSize-positive ((Gᵒ ！) g) = 0<1+n
  singleSize-positive ((Gᵒ ？ ℓ) g) = 0<1+n
  singleSize-positive (c̅ᵒ₁ ⇒ c̅ᵒ₂) = 0<1+n
  singleSize-positive (⊥ ℓ) = 0<1+n

  seqSize-++ : ∀ c̅ᵒ d̅ᵒ → seqSize (c̅ᵒ ++ d̅ᵒ) ≡ seqSize c̅ᵒ + seqSize d̅ᵒ
  seqSize-++ [] d̅ᵒ = refl
  seqSize-++ (cᵒ ; c̅ᵒ) d̅ᵒ
    rewrite seqSize-++ c̅ᵒ d̅ᵒ
          | sym (+-assoc (singleSize cᵒ) (seqSize c̅ᵒ) (seqSize d̅ᵒ)) =
    refl

  seq-fun-size : ∀ c̅ᵒ₁ c̅ᵒ₂ d̅ᵒ₁ d̅ᵒ₂
    → 1 + singleSize ((d̅ᵒ₁ ++ c̅ᵒ₁) ⇒ (c̅ᵒ₂ ++ d̅ᵒ₂))
        ≡ singleSize (c̅ᵒ₁ ⇒ c̅ᵒ₂) + singleSize (d̅ᵒ₁ ⇒ d̅ᵒ₂)
  seq-fun-size c̅ᵒ₁ c̅ᵒ₂ d̅ᵒ₁ d̅ᵒ₂
    rewrite seqSize-++ d̅ᵒ₁ c̅ᵒ₁
          | seqSize-++ c̅ᵒ₂ d̅ᵒ₂ =
    solve 4
      (λ a b c d →
        con 1 :+ (con 1 :+ ((c :+ a) :+ (b :+ d)))
          :=ᵉ (con 1 :+ (a :+ b)) :+ (con 1 :+ (c :+ d)))
      refl
      (seqSize c̅ᵒ₁)
      (seqSize c̅ᵒ₂)
      (seqSize d̅ᵒ₁)
      (seqSize d̅ᵒ₂)
    where
    open +-*-Solver using (solve; _:+_; con) renaming (_:=_ to _:=ᵉ_)

  pair-step-decreases : ∀ {cᵒ₁ cᵒ₂ d̅ᵒ}
    → ⊢ᵒ cᵒ₁ ; cᵒ₂ ⟶ d̅ᵒ
      ------------------------------
    → seqSize d̅ᵒ < singleSize cᵒ₁ + singleSize cᵒ₂
  pair-step-decreases collapse = s≤s z≤n
  pair-step-decreases (collide Gᵒ≢Hᵒ) = n<1+n 1
  pair-step-decreases {cᵒ₁ = c̅ᵒ₁ ⇒ c̅ᵒ₂} {cᵒ₂ = d̅ᵒ₁ ⇒ d̅ᵒ₂} seq-fun
    rewrite +-identityʳ (singleSize ((d̅ᵒ₁ ++ c̅ᵒ₁) ⇒ (c̅ᵒ₂ ++ d̅ᵒ₂))) =
    subst
      (singleSize ((d̅ᵒ₁ ++ c̅ᵒ₁) ⇒ (c̅ᵒ₂ ++ d̅ᵒ₂)) <_)
      (seq-fun-size c̅ᵒ₁ c̅ᵒ₂ d̅ᵒ₁ d̅ᵒ₂)
      (n<1+n _)
  pair-step-decreases {cᵒ₂ = cᵒ} ⊥-left = s≤s (singleSize-positive cᵒ)
  pair-step-decreases ⊥-right-! = n<1+n 1
  pair-step-decreases {cᵒ₁ = c̅ᵒ₁ ⇒ c̅ᵒ₂} {cᵒ₂ = ⊥ ℓ} ⊥-right-fun
    rewrite +-comm (seqSize c̅ᵒ₁ + seqSize c̅ᵒ₂) 1 =
    s≤s (s≤s z≤n)

mutual

  co-step-decreases : ∀ {cᵒ d̅ᵒ}
    → ⊢ᵒ cᵒ —→ d̅ᵒ
      --------------------
    → seqSize d̅ᵒ < singleSize cᵒ
  co-step-decreases id-fun = s≤s z≤n
  co-step-decreases {cᵒ = c̅ᵒ₁ ⇒ c̅ᵒ₂} (ξ-fun-dom {d̅ᵒ₁ = d̅ᵒ₁} c̅ᵒ₁—→d̅ᵒ₁)
    rewrite +-identityʳ (singleSize (d̅ᵒ₁ ⇒ c̅ᵒ₂)) =
    s≤s (+-monoˡ-< _ (seq-step-decreases c̅ᵒ₁—→d̅ᵒ₁))
  co-step-decreases {cᵒ = c̅ᵒ₁ ⇒ c̅ᵒ₂} (ξ-fun-cod {d̅ᵒ₂ = d̅ᵒ₂} nf not-blame c̅ᵒ₂—→d̅ᵒ₂)
    rewrite +-identityʳ (singleSize (c̅ᵒ₁ ⇒ d̅ᵒ₂)) =
    s≤s (+-monoʳ-< _ (seq-step-decreases c̅ᵒ₂—→d̅ᵒ₂))
  co-step-decreases ξ-⊥-fun-dom rewrite +-identityʳ 1 = s≤s (s≤s z≤n)
  co-step-decreases (ξ-⊥-fun-cod {c̅ᵒ = c̅ᵒ} nf not-blame)
    rewrite +-identityʳ 1
          | +-comm (seqSize c̅ᵒ) 1 =
    s≤s (s≤s z≤n)

  seq-step-decreases : ∀ {c̅ᵒ d̅ᵒ}
    → ⊢ᵒ̅ c̅ᵒ —→ d̅ᵒ
      ----------------------
    → seqSize d̅ᵒ < seqSize c̅ᵒ
  seq-step-decreases (reduce-head {d̅ᵒ = d̅ᵒ} {c̅ᵒ = c̅ᵒ} cᵒ—→dᵒ)
    rewrite seqSize-++ d̅ᵒ c̅ᵒ =
    +-monoˡ-< (seqSize c̅ᵒ) (co-step-decreases cᵒ—→dᵒ)
  seq-step-decreases (reduce-neighbors {cᵒ₁ = cᵒ₁} {cᵒ₂ = cᵒ₂} {d̅ᵒ = d̅ᵒ} {c̅ᵒ = c̅ᵒ} cᵒ₁-nf cᵒ₁;cᵒ₂⟶dᵒ)
    rewrite seqSize-++ d̅ᵒ c̅ᵒ =
    subst
      (seqSize d̅ᵒ + seqSize c̅ᵒ <_)
      (+-assoc (singleSize cᵒ₁) (singleSize cᵒ₂) (seqSize c̅ᵒ))
      (+-monoˡ-< (seqSize c̅ᵒ) (pair-step-decreases cᵒ₁;cᵒ₂⟶dᵒ))
  seq-step-decreases (reduce-tail {cᵒ₁ = cᵒ₁} cᵒ₁-nf irred cᵒ₂;c̅ᵒ—→d̅ᵒ) =
    +-monoʳ-< (singleSize cᵒ₁) (seq-step-decreases cᵒ₂;c̅ᵒ—→d̅ᵒ)


private

  -- | Well-founded induction on the nested coercion size.  The seq-fun
  -- | rule decreases because it replaces two function coercion nodes by one.
  normalize-acc : ∀ {c̅ᵒ C₁ C₂}
    → Acc _<_ (seqSize c̅ᵒ)
    → ⊢ᵒ̅ c̅ᵒ ⦂ C₁ ⇒ C₂
      --------------------------------
    → ∃[ d̅ᵒ ] ⊢ᵒ̅ c̅ᵒ —↠ d̅ᵒ × NF d̅ᵒ
  normalize-acc (acc rec) ⊢c̅ᵒ with progress ⊢c̅ᵒ
  ... | Progress.done nf =
    ⟨ _ , ⟨ ↠-refl , nf ⟩ ⟩
  ... | Progress.step c̅ᵒ—→d̅ᵒ
      with normalize-acc (rec (seq-step-decreases c̅ᵒ—→d̅ᵒ)) (preserve c̅ᵒ—→d̅ᵒ ⊢c̅ᵒ)
  ...   | ⟨ e̅ᵒ , ⟨ d̅ᵒ—↠e̅ᵒ , nf ⟩ ⟩ =
    ⟨ e̅ᵒ , ⟨ ↠-step c̅ᵒ—→d̅ᵒ d̅ᵒ—↠e̅ᵒ , nf ⟩ ⟩


terminates : ∀ {c̅ᵒ C₁ C₂}
  → ⊢ᵒ̅ c̅ᵒ ⦂ C₁ ⇒ C₂
    ------------------------------------
  → ∃[ d̅ᵒ ] ⊢ᵒ̅ c̅ᵒ —↠ d̅ᵒ × NF d̅ᵒ
terminates {c̅ᵒ = c̅ᵒ} ⊢c̅ᵒ = normalize-acc (<-wellFounded (seqSize c̅ᵒ)) ⊢c̅ᵒ
