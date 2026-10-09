module LambdaAlphaRefStar.Theories.SpaceEfficiency.Proofs.SizeHeightBounded where

open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _≤_; _⊔_; z≤n; s≤s)
open import Data.Nat.Properties using
  (≤-refl; ≤-trans; +-mono-≤; *-distribˡ-+; *-monoʳ-≤;
   m≤m+n; m≤m⊔n; m≤n⊔m)
open import Data.Nat.Solver using (module +-*-Solver)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym)

open Data.Nat.Properties.≤-Reasoning

open import LambdaAlphaRefStar.Theories.SpaceEfficiency.CCAlphaRefStarSizeAndHeight
open import LambdaAlphaRefStar.Theories.SpaceEfficiency.ECHypercoercions
open import LambdaAlphaRefStar.Theories.SpaceEfficiency.ObjectHypercoercions
open import LambdaAlphaRefStar.Theories.SpaceEfficiency.MetaHypercoercions


pow2-positive : ∀ n → 1 ≤ pow2 n
pow2-positive zero = ≤-refl
pow2-positive (suc n) = ≤-trans (pow2-positive n) (m≤m+n (pow2 n) (pow2 n))

pow2-mono : ∀ {m n} → m ≤ n → pow2 m ≤ pow2 n
pow2-mono {zero} {n} z≤n = pow2-positive n
pow2-mono {suc m} {suc n} (s≤s m≤n) =
  +-mono-≤ (pow2-mono m≤n) (pow2-mono m≤n)

five≤nine-pow2 : ∀ n → 5 ≤ 9 * pow2 n
five≤nine-pow2 n =
  begin
    5
  ≤⟨ m≤m+n 5 4 ⟩
    9
  ≤⟨ *-monoʳ-≤ 9 (pow2-positive n) ⟩
    9 * pow2 n
  ∎

double-nine-pow2 : ∀ n → 9 * pow2 n + 9 * pow2 n ≡ 9 * pow2 (suc n)
double-nine-pow2 n = sym (*-distribˡ-+ 9 (pow2 n) (pow2 n))

binary-middle-shape : ∀ a b → 9 + suc (a + b) ≡ (5 + a) + (5 + b)
binary-middle-shape a b =
  solve 2
    (λ x y → con 9 :+ (con 1 :+ (x :+ y)) :=ᵉ (con 5 :+ x) :+ (con 5 :+ y))
    refl
    a
    b
  where
  open +-*-Solver renaming (_:=_ to _:=ᵉ_) using (solve; _:+_; con)

binary-size-height-step : ∀ {a b h₁ h₂}
  → a ≤ 9 * pow2 h₁
  → b ≤ 9 * pow2 h₂
  → a + b ≤ 9 * pow2 (suc (h₁ ⊔ h₂))
binary-size-height-step {a} {b} {h₁} {h₂} a≤ b≤ =
  begin
    a + b
  ≤⟨ +-mono-≤ a≤ b≤ ⟩
    9 * pow2 h₁ + 9 * pow2 h₂
  ≤⟨ +-mono-≤
       (*-monoʳ-≤ 9 (pow2-mono (m≤m⊔n h₁ h₂)))
       (*-monoʳ-≤ 9 (pow2-mono (m≤n⊔m h₁ h₂))) ⟩
    9 * pow2 (h₁ ⊔ h₂) + 9 * pow2 (h₁ ⊔ h₂)
  ≡⟨ double-nine-pow2 (h₁ ⊔ h₂) ⟩
    9 * pow2 (suc (h₁ ⊔ h₂))
  ∎

unary-size-height-step : ∀ {a h}
  → a ≤ 9 * pow2 h
  → 5 + a ≤ 9 * pow2 (suc h)
unary-size-height-step {a} {h} a≤ =
  begin
    5 + a
  ≤⟨ +-mono-≤ (five≤nine-pow2 h) a≤ ⟩
    9 * pow2 h + 9 * pow2 h
  ≡⟨ double-nine-pow2 h ⟩
    9 * pow2 (suc h)
  ∎

ec-size-height : (c : ECHypercoercion)
  → 5 + ec-hc-size c ≤ 9 * pow2 (ec-hc-height c)
ec-size-height c = m≤m+n 10 8

mutual

  size-height-code-middle : (m : OMiddle)
    → 9 + code-middle-size m ≤ 9 * pow2 (code-middle-height m)
  size-height-code-middle (c₁ ⇒ c₂)
    rewrite binary-middle-shape (code-hc-size c₁) (code-hc-size c₂) =
    binary-size-height-step
      {h₁ = code-hc-height c₁} {h₂ = code-hc-height c₂}
      (size-height-code c₁) (size-height-code c₂)
  size-height-code-middle (err ℓ) = m≤m+n 10 8
  size-height-code-middle id⋆ = m≤m+n 10 8
  size-height-code-middle (idι ι) = m≤m+n 10 8

  size-height-code : (c : OHypercoercion)
    → 5 + code-hc-size c ≤ 9 * pow2 (code-hc-height c)
  size-height-code (h ⨾ m ⨾ t) = size-height-code-middle m

mutual

  size-height-meta-middle : (m : MMiddle)
    → 9 + meta-middle-size m ≤ 9 * pow2 (meta-middle-height m)
  size-height-meta-middle (c₁ ⇒ c₂)
    rewrite binary-middle-shape (meta-hc-size c₁) (meta-hc-size c₂) =
    binary-size-height-step
      {h₁ = meta-hc-height c₁} {h₂ = meta-hc-height c₂}
      (size-height c₁) (size-height c₂)
  size-height-meta-middle (‶ cᵒ ″ cᵉ)
    rewrite binary-middle-shape (code-hc-size cᵒ) (ec-hc-size cᵉ) =
    binary-size-height-step
      {h₁ = code-hc-height cᵒ} {h₂ = ec-hc-height cᵉ}
      (size-height-code cᵒ) (ec-size-height cᵉ)
  size-height-meta-middle (ref c₁ c₂)
    rewrite binary-middle-shape (meta-hc-size c₁) (meta-hc-size c₂) =
    binary-size-height-step
      {h₁ = meta-hc-height c₁} {h₂ = meta-hc-height c₂}
      (size-height c₁) (size-height c₂)
  size-height-meta-middle (∀̇ c) =
    unary-size-height-step {a = 5 + meta-hc-size c} {h = meta-hc-height c} (size-height c)
  size-height-meta-middle (e₁ <: e₂ => c) =
    unary-size-height-step {a = 5 + meta-hc-size c} {h = meta-hc-height c} (size-height c)
  size-height-meta-middle (err ℓ) = m≤m+n 10 8
  size-height-meta-middle id⋆ = m≤m+n 10 8
  size-height-meta-middle (idι ι) = m≤m+n 10 8

  size-height : (c : MHypercoercion)
    → 5 + meta-hc-size c ≤ 9 * pow2 (meta-hc-height c)
  size-height (h ⨾ m ⨾ t) = size-height-meta-middle m
