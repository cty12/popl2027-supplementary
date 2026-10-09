module LambdaAlphaRefStar.Theories.CoercionSequences.Meta.Termination where

open import Data.List using ([]; _∷_; _++_)
open import Data.Nat using (ℕ; zero; suc; _+_; _≤_; _<_; z≤n; s≤s)
open import Data.Nat.Induction using (<-wellFounded)
open import Data.Nat.Properties using
  ( 0<1+n; n<1+n; m<m+n; m≤m+n; ≤-refl
  ; +-assoc; +-comm; +-identityʳ; +-suc; +-monoˡ-<; +-monoʳ-<; +-monoʳ-≤; ≤-<-trans
  )
open import Data.Nat.Solver using (module +-*-Solver)
open import Data.Product using (_×_; ∃-syntax) renaming (_,_ to ⟨_,_⟩)
open import Induction.WellFounded using (Acc; acc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)

import LambdaAlphaRefStar.Theories.CoercionSequences.Code.Definition as OC
import LambdaAlphaRefStar.Theories.CoercionSequences.Code.Termination as OCT
import LambdaAlphaRefStar.Theories.CoercionSequences.EC.Definition as ECS
import LambdaAlphaRefStar.Theories.CoercionSequences.EC.Termination as ECT
open import LambdaAlphaRefStar.Theories.CoercionSequences.Meta.Definition
open import LambdaAlphaRefStar.Theories.CoercionSequences.Meta.Progress
  using (Progress; progress)
open import LambdaAlphaRefStar.Theories.CoercionSequences.Meta.Preservation
  using (preserve)


mutual

  -- | A meta coercion sequence is a list of coercion trees.  The measure counts
  -- | meta coercion nodes plus the embedded code/EC sequence sizes.  The code
  -- | wrapper has cost 2 so propagation from an embedded EC blame strictly
  -- | decreases even when the embedded code sequence is empty.
  singleSize : MSingleCoercion → ℕ
  singleSize ((G ！) g) = 1
  singleSize ((G ？ ℓ) g) = 1
  singleSize (c̅ᵐ₁ ⇒ c̅ᵐ₂) = 1 + (seqSize c̅ᵐ₁ + seqSize c̅ᵐ₂)
  singleSize (‶ c̅ᵒ ″ c̅ᵉ) = 2 + (OCT.seqSize c̅ᵒ + ECT.seqSize c̅ᵉ)
  singleSize (Ref c̅ᵐ₁ , c̅ᵐ₂) = 1 + (seqSize c̅ᵐ₁ + seqSize c̅ᵐ₂)
  singleSize (∀̇ c̅ᵐ) = 1 + seqSize c̅ᵐ
  singleSize (e₁ <: e₂ => c̅ᵐ) = 1 + seqSize c̅ᵐ
  singleSize (⊥ ℓ) = 1

  seqSize : MCoercionSeq → ℕ
  seqSize [] = 0
  seqSize (cᵐ ; c̅ᵐ) = singleSize cᵐ + seqSize c̅ᵐ


private

  singleSize-positive : ∀ cᵐ → 0 < singleSize cᵐ
  singleSize-positive ((G ！) g) = 0<1+n
  singleSize-positive ((G ？ ℓ) g) = 0<1+n
  singleSize-positive (c̅ᵐ₁ ⇒ c̅ᵐ₂) = 0<1+n
  singleSize-positive (‶ c̅ᵒ ″ c̅ᵉ) = 0<1+n
  singleSize-positive (Ref c̅ᵐ₁ , c̅ᵐ₂) = 0<1+n
  singleSize-positive (∀̇ c̅ᵐ) = 0<1+n
  singleSize-positive (e₁ <: e₂ => c̅ᵐ) = 0<1+n
  singleSize-positive (⊥ ℓ) = 0<1+n

  seqSize-++ : ∀ c̅ᵐ d̅ᵐ → seqSize (c̅ᵐ ++ d̅ᵐ) ≡ seqSize c̅ᵐ + seqSize d̅ᵐ
  seqSize-++ [] d̅ᵐ = refl
  seqSize-++ (cᵐ ; c̅ᵐ) d̅ᵐ
    rewrite seqSize-++ c̅ᵐ d̅ᵐ
          | sym (+-assoc (singleSize cᵐ) (seqSize c̅ᵐ) (seqSize d̅ᵐ)) =
    refl

  code-seqSize-++ : ∀ c̅ᵒ d̅ᵒ → OCT.seqSize (c̅ᵒ ++ d̅ᵒ) ≡ OCT.seqSize c̅ᵒ + OCT.seqSize d̅ᵒ
  code-seqSize-++ [] d̅ᵒ = refl
  code-seqSize-++ (cᵒ ∷ c̅ᵒ) d̅ᵒ
    rewrite code-seqSize-++ c̅ᵒ d̅ᵒ
          | sym (+-assoc (OCT.singleSize cᵒ) (OCT.seqSize c̅ᵒ) (OCT.seqSize d̅ᵒ)) =
    refl

  seq-binary-size : ∀ c̅ᵐ₁ c̅ᵐ₂ d̅ᵐ₁ d̅ᵐ₂
    → 1 + singleSize ((d̅ᵐ₁ ++ c̅ᵐ₁) ⇒ (c̅ᵐ₂ ++ d̅ᵐ₂))
        ≡ singleSize (c̅ᵐ₁ ⇒ c̅ᵐ₂) + singleSize (d̅ᵐ₁ ⇒ d̅ᵐ₂)
  seq-binary-size c̅ᵐ₁ c̅ᵐ₂ d̅ᵐ₁ d̅ᵐ₂
    rewrite seqSize-++ d̅ᵐ₁ c̅ᵐ₁
          | seqSize-++ c̅ᵐ₂ d̅ᵐ₂ =
    solve 4
      (λ a b c d →
        con 1 :+ (con 1 :+ ((c :+ a) :+ (b :+ d)))
          :=ᵉ (con 1 :+ (a :+ b)) :+ (con 1 :+ (c :+ d)))
      refl
      (seqSize c̅ᵐ₁)
      (seqSize c̅ᵐ₂)
      (seqSize d̅ᵐ₁)
      (seqSize d̅ᵐ₂)
    where
    open +-*-Solver using (solve; _:+_; con) renaming (_:=_ to _:=ᵉ_)

  seq-unary-size : ∀ c̅ᵐ d̅ᵐ
    → 1 + (1 + seqSize (c̅ᵐ ++ d̅ᵐ)) ≡ (1 + seqSize c̅ᵐ) + (1 + seqSize d̅ᵐ)
  seq-unary-size c̅ᵐ d̅ᵐ
    rewrite seqSize-++ c̅ᵐ d̅ᵐ =
    solve 2
      (λ a b → con 1 :+ (con 1 :+ (a :+ b)) :=ᵉ (con 1 :+ a) :+ (con 1 :+ b))
      refl
      (seqSize c̅ᵐ)
      (seqSize d̅ᵐ)
    where
    open +-*-Solver using (solve; _:+_; con) renaming (_:=_ to _:=ᵉ_)

  seq-code-rhs : ∀ a b c d
    → (2 + ((a + c) + (b + d))) + 2 ≡ (2 + (a + b)) + (2 + (c + d))
  seq-code-rhs =
    solve 4
      (λ a b c d →
        ((con 2 :+ ((a :+ c) :+ (b :+ d))) :+ con 2)
          :=ᵉ (con 2 :+ (a :+ b)) :+ (con 2 :+ (c :+ d)))
      refl
    where
    open +-*-Solver using (solve; _:+_; con) renaming (_:=_ to _:=ᵉ_)

  seq-code-size-bound : ∀ a b c d k
    → k ≤ b + d
      -------------------------------------------------------
    → 2 + ((a + c) + k) < (2 + (a + b)) + (2 + (c + d))
  seq-code-size-bound a b c d k k≤ =
    ≤-<-trans
      (s≤s (s≤s (+-monoʳ-≤ (a + c) k≤)))
      (subst (2 + ((a + c) + (b + d)) <_)
        (seq-code-rhs a b c d)
        (m<m+n (2 + ((a + c) + (b + d))) (s≤s z≤n)))

  pair-step-decreases : ∀ {Θ cᵐ₁ cᵐ₂ d̅ᵐ}
    → Θ ⊢ᵐ cᵐ₁ ; cᵐ₂ ⟶ d̅ᵐ
      ------------------------------
    → seqSize d̅ᵐ < singleSize cᵐ₁ + singleSize cᵐ₂
  pair-step-decreases collapse = s≤s z≤n
  pair-step-decreases (collide G≢H) = n<1+n 1
  pair-step-decreases {cᵐ₁ = c̅ᵐ₁ ⇒ c̅ᵐ₂} {cᵐ₂ = d̅ᵐ₁ ⇒ d̅ᵐ₂} seq-fun
    rewrite +-identityʳ (singleSize ((d̅ᵐ₁ ++ c̅ᵐ₁) ⇒ (c̅ᵐ₂ ++ d̅ᵐ₂))) =
    subst
      (singleSize ((d̅ᵐ₁ ++ c̅ᵐ₁) ⇒ (c̅ᵐ₂ ++ d̅ᵐ₂)) <_)
      (seq-binary-size c̅ᵐ₁ c̅ᵐ₂ d̅ᵐ₁ d̅ᵐ₂)
      (n<1+n _)
  pair-step-decreases {cᵐ₁ = Ref c̅ᵐ₁ , c̅ᵐ₂} {cᵐ₂ = Ref d̅ᵐ₁ , d̅ᵐ₂} seq-ref
    rewrite +-identityʳ (singleSize (Ref (d̅ᵐ₁ ++ c̅ᵐ₁) , (c̅ᵐ₂ ++ d̅ᵐ₂))) =
    subst
      (singleSize (Ref (d̅ᵐ₁ ++ c̅ᵐ₁) , (c̅ᵐ₂ ++ d̅ᵐ₂)) <_)
      (seq-binary-size c̅ᵐ₁ c̅ᵐ₂ d̅ᵐ₁ d̅ᵐ₂)
      (n<1+n _)
  pair-step-decreases {cᵐ₁ = ‶ c̅ᵒ ″ c̅ᵉ} {cᵐ₂ = ‶ d̅ᵒ ″ d̅ᵉ} seq-code
    rewrite +-identityʳ (singleSize (‶ c̅ᵒ ++ d̅ᵒ ″ (c̅ᵉ ++ d̅ᵉ)))
          | code-seqSize-++ c̅ᵒ d̅ᵒ
          | ECT.seqSize-++ c̅ᵉ d̅ᵉ =
    seq-code-size-bound
      (OCT.seqSize c̅ᵒ)
      (ECT.seqSize c̅ᵉ)
      (OCT.seqSize d̅ᵒ)
      (ECT.seqSize d̅ᵉ)
      (ECT.seqSize c̅ᵉ + ECT.seqSize d̅ᵉ)
      ≤-refl
  pair-step-decreases {cᵐ₁ = ∀̇ c̅ᵐ} {cᵐ₂ = ∀̇ d̅ᵐ} seq-forall
    rewrite +-identityʳ (singleSize (∀̇ (c̅ᵐ ++ d̅ᵐ))) =
    subst
      (singleSize (∀̇ (c̅ᵐ ++ d̅ᵐ)) <_)
      (seq-unary-size c̅ᵐ d̅ᵐ)
      (n<1+n _)
  pair-step-decreases {cᵐ₁ = e₁ <: e₂ => c̅ᵐ} {cᵐ₂ = .e₁ <: .e₂ => d̅ᵐ} seq-sub
    rewrite +-identityʳ (singleSize (e₁ <: e₂ => (c̅ᵐ ++ d̅ᵐ))) =
    subst
      (singleSize (e₁ <: e₂ => (c̅ᵐ ++ d̅ᵐ)) <_)
      (seq-unary-size c̅ᵐ d̅ᵐ)
      (n<1+n _)
  pair-step-decreases {cᵐ₂ = cᵐ} ⊥-left
    rewrite +-identityʳ 1 =
    s≤s (singleSize-positive cᵐ)
  pair-step-decreases {cᵐ₁ = cᵐ} (⊥-right not-blame not-proj)
    rewrite +-identityʳ 1
          | +-comm (singleSize cᵐ) 1 =
    s≤s (singleSize-positive cᵐ)

  mutual

    co-step-decreases : ∀ {Θ cᵐ d̅ᵐ}
      → Θ ⊢ᵐ cᵐ —→ d̅ᵐ
        --------------------
      → seqSize d̅ᵐ < singleSize cᵐ
    co-step-decreases id-fun = s≤s z≤n
    co-step-decreases id-code = s≤s z≤n
    co-step-decreases id-ref = s≤s z≤n
    co-step-decreases id-forall = s≤s z≤n
    co-step-decreases id-sub = s≤s z≤n
    co-step-decreases {cᵐ = c̅ᵐ₁ ⇒ c̅ᵐ₂} (ξ-fun-dom {d̅ᵐ₁ = d̅ᵐ₁} c̅ᵐ₁—→d̅ᵐ₁)
      rewrite +-identityʳ (singleSize (d̅ᵐ₁ ⇒ c̅ᵐ₂)) =
      s≤s (+-monoˡ-< _ (seq-step-decreases c̅ᵐ₁—→d̅ᵐ₁))
    co-step-decreases {cᵐ = c̅ᵐ₁ ⇒ c̅ᵐ₂} (ξ-fun-cod {d̅ᵐ₂ = d̅ᵐ₂} nf c̅ᵐ₂—→d̅ᵐ₂)
      rewrite +-identityʳ (singleSize (c̅ᵐ₁ ⇒ d̅ᵐ₂)) =
      s≤s (+-monoʳ-< _ (seq-step-decreases c̅ᵐ₂—→d̅ᵐ₂))
    co-step-decreases {cᵐ = Ref c̅ᵐ₁ , c̅ᵐ₂} (ξ-ref-in {d̅ᵐ₁ = d̅ᵐ₁} c̅ᵐ₁—→d̅ᵐ₁)
      rewrite +-identityʳ (singleSize (Ref d̅ᵐ₁ , c̅ᵐ₂)) =
      s≤s (+-monoˡ-< _ (seq-step-decreases c̅ᵐ₁—→d̅ᵐ₁))
    co-step-decreases {cᵐ = Ref c̅ᵐ₁ , c̅ᵐ₂} (ξ-ref-out {d̅ᵐ₂ = d̅ᵐ₂} nf c̅ᵐ₂—→d̅ᵐ₂)
      rewrite +-identityʳ (singleSize (Ref c̅ᵐ₁ , d̅ᵐ₂)) =
      s≤s (+-monoʳ-< _ (seq-step-decreases c̅ᵐ₂—→d̅ᵐ₂))
    co-step-decreases {cᵐ = ∀̇ c̅ᵐ} (ξ-forall {d̅ᵐ = d̅ᵐ} c̅ᵐ—→d̅ᵐ)
      rewrite +-identityʳ (singleSize (∀̇ d̅ᵐ)) =
      s≤s (seq-step-decreases c̅ᵐ—→d̅ᵐ)
    co-step-decreases {cᵐ = e₁ <: e₂ => c̅ᵐ} (ξ-sub {d̅ᵐ = d̅ᵐ} c̅ᵐ—→d̅ᵐ)
      rewrite +-identityʳ (singleSize (e₁ <: e₂ => d̅ᵐ)) =
      s≤s (seq-step-decreases c̅ᵐ—→d̅ᵐ)
    co-step-decreases {cᵐ = ‶ c̅ᵒ ″ c̅ᵉ} (ξ-code {d̅ᵒ = d̅ᵒ} c̅ᵒ—→d̅ᵒ)
      rewrite +-identityʳ (singleSize (‶ d̅ᵒ ″ c̅ᵉ)) =
      s≤s (s≤s (+-monoˡ-< _ (OCT.seq-step-decreases c̅ᵒ—→d̅ᵒ)))
    co-step-decreases {cᵐ = ‶ c̅ᵒ ″ c̅ᵉ} (ξ-code-ec {d̅ᵉ = d̅ᵉ} nfᵒ not-blameᵒ c̅ᵉ—→d̅ᵉ)
      rewrite +-identityʳ (singleSize (‶ c̅ᵒ ″ d̅ᵉ)) =
      s≤s (s≤s (+-monoʳ-< _ (ECT.seq-step-decreases c̅ᵉ—→d̅ᵉ)))
    co-step-decreases ξ-code-⊥ rewrite +-identityʳ 1 = s≤s (s≤s z≤n)
    co-step-decreases (ξ-code-ec-⊥ nfᵒ not-blameᵒ) rewrite +-identityʳ 1 = s≤s (s≤s z≤n)

    seq-step-decreases : ∀ {Θ c̅ᵐ d̅ᵐ}
      → Θ ⊢ᵐ̅ c̅ᵐ —→ d̅ᵐ
        ----------------------
      → seqSize d̅ᵐ < seqSize c̅ᵐ
    seq-step-decreases (reduce-head {d̅ᵐ = d̅ᵐ} {c̅ᵐ = c̅ᵐ} cᵐ—→dᵐ)
      rewrite seqSize-++ d̅ᵐ c̅ᵐ =
      +-monoˡ-< (seqSize c̅ᵐ) (co-step-decreases cᵐ—→dᵐ)
    seq-step-decreases (reduce-neighbors {cᵐ₁ = cᵐ₁} {cᵐ₂ = cᵐ₂} {d̅ᵐ = d̅ᵐ} {c̅ᵐ = c̅ᵐ} cᵐ₁-nf cᵐ₁;cᵐ₂⟶dᵐ)
      rewrite seqSize-++ d̅ᵐ c̅ᵐ =
      subst
        (seqSize d̅ᵐ + seqSize c̅ᵐ <_)
        (+-assoc (singleSize cᵐ₁) (singleSize cᵐ₂) (seqSize c̅ᵐ))
        (+-monoˡ-< (seqSize c̅ᵐ) (pair-step-decreases cᵐ₁;cᵐ₂⟶dᵐ))
    seq-step-decreases (reduce-tail {cᵐ₁ = cᵐ₁} cᵐ₁-nf irred cᵐ₂;c̅ᵐ—→d̅ᵐ) =
      +-monoʳ-< (singleSize cᵐ₁) (seq-step-decreases cᵐ₂;c̅ᵐ—→d̅ᵐ)

  -- | Well-founded induction on the nested coercion size.  The measure also
  -- | counts embedded code and EC coercion sequences, so congruence steps under
  -- | code casts are strictly decreasing.
  normalize-acc : ∀ {Δ Θ c̅ᵐ A B}
    → Acc _<_ (seqSize c̅ᵐ)
    → Δ ; Θ ⊢ᵐ̅ c̅ᵐ ⦂ A ⇒ B
      --------------------------------
    → ∃[ d̅ᵐ ] Θ ⊢ᵐ̅ c̅ᵐ —↠ d̅ᵐ × NF d̅ᵐ
  normalize-acc (acc rec) ⊢c̅ᵐ with progress ⊢c̅ᵐ
  ... | Progress.done nf =
    ⟨ _ , ⟨ ↠-refl , nf ⟩ ⟩
  ... | Progress.step c̅ᵐ—→d̅ᵐ
      with normalize-acc (rec (seq-step-decreases c̅ᵐ—→d̅ᵐ)) (preserve c̅ᵐ—→d̅ᵐ ⊢c̅ᵐ)
  ...   | ⟨ e̅ᵐ , ⟨ d̅ᵐ—↠e̅ᵐ , nf ⟩ ⟩ =
    ⟨ e̅ᵐ , ⟨ ↠-step c̅ᵐ—→d̅ᵐ d̅ᵐ—↠e̅ᵐ , nf ⟩ ⟩


terminates : ∀ {Δ Θ c̅ᵐ A B}
  → Δ ; Θ ⊢ᵐ̅ c̅ᵐ ⦂ A ⇒ B
    ---------------------------------------
  → ∃[ d̅ᵐ ] Θ ⊢ᵐ̅ c̅ᵐ —↠ d̅ᵐ × NF d̅ᵐ
terminates {c̅ᵐ = c̅ᵐ} ⊢c̅ᵐ = normalize-acc (<-wellFounded (seqSize c̅ᵐ)) ⊢c̅ᵐ
