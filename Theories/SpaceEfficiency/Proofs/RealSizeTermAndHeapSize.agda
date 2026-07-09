module LambdaAlphaRefStar.Theories.SpaceEfficiency.Proofs.RealSizeTermAndHeapSize where

open import Data.List using ([]; _∷_)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _≤_; _⊔_; z≤n; s≤s)
open import Data.Nat.Properties using
  (≤-refl; ≤-trans; ≤-reflexive; +-comm; +-mono-≤; *-distribˡ-+; *-mono-≤; *-monoʳ-≤; *-suc;
   m≤m+n; m≤n+m; m≤m⊔n; m≤n⊔m)
open import Relation.Binary.PropositionalEquality using (sym)

open Data.Nat.Properties.≤-Reasoning

open import LambdaAlphaRefStar.Theories.SpaceEfficiency.CCAlphaRefStarSyntaxAndTypeSystem hiding (size)
open import LambdaAlphaRefStar.Theories.SpaceEfficiency.CCAlphaRefStarSizeAndHeight
open import LambdaAlphaRefStar.Theories.SpaceEfficiency.Proofs.SizeHeightBounded


nine-pow2-positive : ∀ h → 1 ≤ 9 * pow2 h
nine-pow2-positive h = ≤-trans (m≤m+n 1 4) (five≤nine-pow2 h)

base-real-size-tsize : ∀ h → 1 ≤ (9 * pow2 h) * 1
base-real-size-tsize h = *-mono-≤ (nine-pow2-positive h) ≤-refl

real-size-tsize-one : ∀ {r s h}
  → r ≤ (9 * pow2 h) * s
  → suc r ≤ (9 * pow2 h) * suc s
real-size-tsize-one {r} {s} {h} IH =
  begin
    suc r
  ≤⟨ s≤s IH ⟩
    suc ((9 * pow2 h) * s)
  ≤⟨ +-mono-≤ {x = 1} {y = 9 * pow2 h} (nine-pow2-positive h) ≤-refl ⟩
    9 * pow2 h + (9 * pow2 h) * s
  ≤⟨ ≤-reflexive (sym (*-suc (9 * pow2 h) s)) ⟩
    (9 * pow2 h) * suc s
  ∎

real-size-tsize-two : ∀ {r₁ r₂ s₁ s₂ h₁ h₂}
  → r₁ ≤ (9 * pow2 h₁) * s₁
  → r₂ ≤ (9 * pow2 h₂) * s₂
  → suc (r₁ + r₂) ≤ (9 * pow2 (h₁ ⊔ h₂)) * suc (s₁ + s₂)
real-size-tsize-two {r₁} {r₂} {s₁} {s₂} {h₁} {h₂} IH₁ IH₂ =
  begin
    suc (r₁ + r₂)
  ≤⟨ s≤s (+-mono-≤ IH₁ IH₂) ⟩
    suc (((9 * pow2 h₁) * s₁) + ((9 * pow2 h₂) * s₂))
  ≤⟨ s≤s (+-mono-≤
       (*-mono-≤
         {x = 9 * pow2 h₁} {y = 9 * pow2 (h₁ ⊔ h₂)}
         {u = s₁} {v = s₁}
         (*-mono-≤
           {x = 9} {y = 9}
           {u = pow2 h₁} {v = pow2 (h₁ ⊔ h₂)}
           ≤-refl (pow2-mono (m≤m⊔n h₁ h₂)))
         ≤-refl)
       (*-mono-≤
         {x = 9 * pow2 h₂} {y = 9 * pow2 (h₁ ⊔ h₂)}
         {u = s₂} {v = s₂}
         (*-mono-≤
           {x = 9} {y = 9}
           {u = pow2 h₂} {v = pow2 (h₁ ⊔ h₂)}
           ≤-refl (pow2-mono (m≤n⊔m h₁ h₂)))
         ≤-refl)) ⟩
    suc (((9 * pow2 (h₁ ⊔ h₂)) * s₁) + ((9 * pow2 (h₁ ⊔ h₂)) * s₂))
  ≤⟨ s≤s (≤-reflexive (sym (*-distribˡ-+ (9 * pow2 (h₁ ⊔ h₂)) s₁ s₂))) ⟩
    suc ((9 * pow2 (h₁ ⊔ h₂)) * (s₁ + s₂))
  ≤⟨ +-mono-≤ {x = 1} {y = 9 * pow2 (h₁ ⊔ h₂)}
       (nine-pow2-positive (h₁ ⊔ h₂)) ≤-refl ⟩
    9 * pow2 (h₁ ⊔ h₂) + (9 * pow2 (h₁ ⊔ h₂)) * (s₁ + s₂)
  ≤⟨ ≤-reflexive (sym (*-suc (9 * pow2 (h₁ ⊔ h₂)) (s₁ + s₂))) ⟩
    (9 * pow2 (h₁ ⊔ h₂)) * suc (s₁ + s₂)
  ∎

meta-hc-size≤height : ∀ c → meta-hc-size c ≤ 9 * pow2 (meta-hc-height c)
meta-hc-size≤height c =
  ≤-trans (m≤n+m (meta-hc-size c) 5) (size-height c)

real-size-tsize-cast : ∀ {r s h c}
  → r ≤ (9 * pow2 h) * s
  → r + meta-hc-size c ≤ (9 * pow2 (h ⊔ meta-hc-height c)) * suc s
real-size-tsize-cast {r} {s} {h} {c} IH =
  begin
    r + meta-hc-size c
  ≤⟨ +-mono-≤
       (≤-trans IH
         (*-mono-≤
           {x = 9 * pow2 h} {y = 9 * pow2 (h ⊔ meta-hc-height c)}
           {u = s} {v = s}
           (*-mono-≤
             {x = 9} {y = 9}
             {u = pow2 h} {v = pow2 (h ⊔ meta-hc-height c)}
             ≤-refl (pow2-mono (m≤m⊔n h (meta-hc-height c))))
           ≤-refl))
       (≤-trans (meta-hc-size≤height c)
         (*-monoʳ-≤ 9 (pow2-mono (m≤n⊔m h (meta-hc-height c))))) ⟩
    (9 * pow2 (h ⊔ meta-hc-height c)) * s + 9 * pow2 (h ⊔ meta-hc-height c)
  ≤⟨ ≤-reflexive
       (+-comm ((9 * pow2 (h ⊔ meta-hc-height c)) * s)
               (9 * pow2 (h ⊔ meta-hc-height c))) ⟩
    9 * pow2 (h ⊔ meta-hc-height c) + (9 * pow2 (h ⊔ meta-hc-height c)) * s
  ≤⟨ ≤-reflexive (sym (*-suc (9 * pow2 (h ⊔ meta-hc-height c)) s)) ⟩
    (9 * pow2 (h ⊔ meta-hc-height c)) * suc s
  ∎

mutual

  real-size-tsizeᵒ : (M : CodeTerm)
    → real-sizeᵒ M ≤ (9 * pow2 (c-heightᵒ M)) * sizeᵒ M
  real-size-tsizeᵒ ($ k) = base-real-size-tsize 0
  real-size-tsizeᵒ (` x) = base-real-size-tsize 0
  real-size-tsizeᵒ (ƛ T ˙ N) =
    real-size-tsize-one {r = real-sizeᵒ N} {s = sizeᵒ N} {h = c-heightᵒ N} (real-size-tsizeᵒ N)
  real-size-tsizeᵒ (ƛ̅ e ˙ N) =
    real-size-tsize-one {r = real-sizeᵒ N} {s = sizeᵒ N} {h = c-heightᵒ N} (real-size-tsizeᵒ N)
  real-size-tsizeᵒ (L · M) =
    real-size-tsize-two
      {r₁ = real-sizeᵒ L} {r₂ = real-sizeᵒ M}
      {s₁ = sizeᵒ L} {s₂ = sizeᵒ M}
      {h₁ = c-heightᵒ L} {h₂ = c-heightᵒ M}
      (real-size-tsizeᵒ L) (real-size-tsizeᵒ M)
  real-size-tsizeᵒ (~ M) =
    real-size-tsize-one {r = real-size M} {s = size M} {h = c-height M} (real-size-tsizeᵐ M)
  real-size-tsizeᵒ (blameᵒ ℓ) = base-real-size-tsize 0

  real-size-tsizeᵐ : (M : MetaTerm)
    → real-size M ≤ (9 * pow2 (c-height M)) * size M
  real-size-tsizeᵐ ($ k) = base-real-size-tsize 0
  real-size-tsizeᵐ (` x) = base-real-size-tsize 0
  real-size-tsizeᵐ (addr a) = base-real-size-tsize 0
  real-size-tsizeᵐ (ƛ N) =
    real-size-tsize-one {r = real-size N} {s = size N} {h = c-height N} (real-size-tsizeᵐ N)
  real-size-tsizeᵐ (L · M) =
    real-size-tsize-two
      {r₁ = real-size L} {r₂ = real-size M}
      {s₁ = size L} {s₂ = size M}
      {h₁ = c-height L} {h₂ = c-height M}
      (real-size-tsizeᵐ L) (real-size-tsizeᵐ M)
  real-size-tsizeᵐ (Λ N) =
    real-size-tsize-one {r = real-size N} {s = size N} {h = c-height N} (real-size-tsizeᵐ N)
  real-size-tsizeᵐ (M ·[ e ]) =
    real-size-tsize-one {r = real-size M} {s = size M} {h = c-height M} (real-size-tsizeᵐ M)
  real-size-tsizeᵐ (e₁ <: e₂ => N) =
    real-size-tsize-one {r = real-size N} {s = size N} {h = c-height N} (real-size-tsizeᵐ N)
  real-size-tsizeᵐ (M ●) =
    real-size-tsize-one {r = real-size M} {s = size M} {h = c-height M} (real-size-tsizeᵐ M)
  real-size-tsizeᵐ (M ★ ℓ) =
    real-size-tsize-one {r = real-size M} {s = size M} {h = c-height M} (real-size-tsizeᵐ M)
  real-size-tsizeᵐ (‶ M ″ e) =
    real-size-tsize-one {r = real-sizeᵒ M} {s = sizeᵒ M} {h = c-heightᵒ M} (real-size-tsizeᵒ M)
  real-size-tsizeᵐ (ref M) =
    real-size-tsize-one {r = real-size M} {s = size M} {h = c-height M} (real-size-tsizeᵐ M)
  real-size-tsizeᵐ (L := M) =
    real-size-tsize-two
      {r₁ = real-size L} {r₂ = real-size M}
      {s₁ = size L} {s₂ = size M}
      {h₁ = c-height L} {h₂ = c-height M}
      (real-size-tsizeᵐ L) (real-size-tsizeᵐ M)
  real-size-tsizeᵐ (! M) =
    real-size-tsize-one {r = real-size M} {s = size M} {h = c-height M} (real-size-tsizeᵐ M)
  real-size-tsizeᵐ (M ⟨ c ⟩) =
    real-size-tsize-cast {r = real-size M} {s = size M} {h = c-height M} {c = c} (real-size-tsizeᵐ M)
  real-size-tsizeᵐ (blame ℓ) = base-real-size-tsize 0

real-size-tsizeᵐ-height : ∀ {M h}
  → c-height M ≤ h
    ---------------------------------------------
  → real-size M ≤ (9 * pow2 h) * size M
real-size-tsizeᵐ-height {M = M} M≤h =
  ≤-trans
    (real-size-tsizeᵐ M)
    (*-mono-≤
      (*-monoʳ-≤ 9 (pow2-mono M≤h))
      ≤-refl)

heap-real-size-tsize-height : ∀ {h} μ
  → heap-c-height μ ≤ h
    ---------------------------------------------------
  → heap-real-size μ ≤ (9 * pow2 h) * heap-size μ
heap-real-size-tsize-height [] μ≤h = z≤n
heap-real-size-tsize-height {h = h} (V ∷ μ) μ≤h =
  begin
    real-size V + heap-real-size μ
  ≤⟨ +-mono-≤
       (real-size-tsizeᵐ-height
         (≤-trans (m≤m⊔n (c-height V) (heap-c-height μ)) μ≤h))
       (heap-real-size-tsize-height μ
         (≤-trans (m≤n⊔m (c-height V) (heap-c-height μ)) μ≤h)) ⟩
    (9 * pow2 h) * size V + (9 * pow2 h) * heap-size μ
  ≤⟨ ≤-reflexive (sym (*-distribˡ-+ (9 * pow2 h) (size V) (heap-size μ))) ⟩
    (9 * pow2 h) * (size V + heap-size μ)
  ∎
