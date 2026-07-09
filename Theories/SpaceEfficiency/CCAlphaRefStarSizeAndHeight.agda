module Theories.SpaceEfficiency.CCAlphaRefStarSizeAndHeight where

open import Data.List using ([]; _∷_)
open import Data.Nat using (ℕ; zero; suc; _+_; _≤_; _⊔_; z≤n; s≤s)
open import Data.Nat.Properties using (≤-refl)

open import Theories.SpaceEfficiency.CCAlphaRefStarSyntaxAndTypeSystem hiding (size)
open import Theories.SpaceEfficiency.Configuration
open import Theories.SpaceEfficiency.ECHypercoercions
open import Theories.SpaceEfficiency.ObjectHypercoercions
open import Theories.SpaceEfficiency.MetaHypercoercions


ec-hc-height : ECHypercoercion → ℕ
ec-hc-height cᵉ = 1


mutual

  code-middle-height : OMiddle → ℕ
  code-middle-height (c₁ ⇒ c₂) = suc (code-hc-height c₁ ⊔ code-hc-height c₂)
  code-middle-height (err ℓ) = 1
  code-middle-height id⋆ = 1
  code-middle-height (idι ι) = 1

  code-hc-height : OHypercoercion → ℕ
  code-hc-height (h ⨾ m ⨾ t) = code-middle-height m


mutual

  meta-middle-height : MMiddle → ℕ
  meta-middle-height (c₁ ⇒ c₂) = suc (meta-hc-height c₁ ⊔ meta-hc-height c₂)
  meta-middle-height (‶ cᵒ ″ cᵉ) = suc (code-hc-height cᵒ ⊔ ec-hc-height cᵉ)
  meta-middle-height (ref c₁ c₂) = suc (meta-hc-height c₁ ⊔ meta-hc-height c₂)
  meta-middle-height (∀̇ c) = suc (meta-hc-height c)
  meta-middle-height (e₁ <: e₂ => c) = suc (meta-hc-height c)
  meta-middle-height (err ℓ) = 1
  meta-middle-height id⋆ = 1
  meta-middle-height (idι ι) = 1

  meta-hc-height : MHypercoercion → ℕ
  meta-hc-height (h ⨾ m ⨾ t) = meta-middle-height m


-- EC hypercoercions have constant size 5:
-- 2 for the two composition operators `_⨾_⨾_`,
-- 1 for the head, 1 for the middle, and 1 for the tail.
ec-hc-size : ECHypercoercion → ℕ
ec-hc-size cᵉ = 2 + 1 + 1 + 1

mutual

  code-middle-size : OMiddle → ℕ
  code-middle-size (c₁ ⇒ c₂) = suc (code-hc-size c₁ + code-hc-size c₂)
  code-middle-size (err ℓ) = 1
  code-middle-size id⋆ = 1
  code-middle-size (idι ι) = 1

  -- The constant numbers used are:
  -- 2 for the two composition operators `_⨾_⨾_`,
  -- 1 for the head size,
  -- and 1 for the tail size.
  -- So a code hypercoercion size is `4 + size(middle)`.
  code-hc-size : OHypercoercion → ℕ
  code-hc-size (h ⨾ m ⨾ t) = 2 + 1 + 1 + code-middle-size m

mutual

  meta-middle-size : MMiddle → ℕ
  meta-middle-size (c₁ ⇒ c₂) = suc (meta-hc-size c₁ + meta-hc-size c₂)
  meta-middle-size (‶ cᵒ ″ cᵉ) = suc (code-hc-size cᵒ + ec-hc-size cᵉ)
  meta-middle-size (ref c₁ c₂) = suc (meta-hc-size c₁ + meta-hc-size c₂)
  meta-middle-size (∀̇ c) = suc (meta-hc-size c)
  meta-middle-size (e₁ <: e₂ => c) = suc (meta-hc-size c)
  meta-middle-size (err ℓ) = 1
  meta-middle-size id⋆ = 1
  meta-middle-size (idι ι) = 1

  -- The constant numbers used are:
  -- 2 for the two composition operators `_⨾_⨾_`,
  -- 1 for the head size,
  -- and 1 for the tail size.
  -- So a meta hypercoercion size is `4 + size(middle)`.
  meta-hc-size : MHypercoercion → ℕ
  meta-hc-size (h ⨾ m ⨾ t) = 2 + 1 + 1 + meta-middle-size m


pow2 : ℕ → ℕ
pow2 zero = 1
pow2 (suc n) = pow2 n + pow2 n

mutual

  sizeᵒ : CodeTerm → ℕ
  sizeᵒ ($ k) = 1
  sizeᵒ (` x) = 1
  sizeᵒ (ƛ T ˙ N) = suc (sizeᵒ N)
  sizeᵒ (ƛ̅ e ˙ N) = suc (sizeᵒ N)
  sizeᵒ (L · M) = suc (sizeᵒ L + sizeᵒ M)
  sizeᵒ (~ M) = suc (size M)
  sizeᵒ (blameᵒ ℓ) = 1

  size : MetaTerm → ℕ
  size ($ k) = 1
  size (` x) = 1
  size (addr a) = 1
  size (ƛ N) = suc (size N)
  size (L · M) = suc (size L + size M)
  size (Λ N) = suc (size N)
  size (M ·[ e ]) = suc (size M)
  size (e₁ <: e₂ => N) = suc (size N)
  size (M ●) = suc (size M)
  size (M ★ ℓ) = suc (size M)
  size (‶ M ″ e) = suc (sizeᵒ M)
  size (ref M) = suc (size M)
  size (L := M) = suc (size L + size M)
  size (! M) = suc (size M)
  size (M ⟨ c ⟩) = suc (size M)
  size (blame ℓ) = 1

mutual

  ideal-sizeᵒ : CodeTerm → ℕ
  ideal-sizeᵒ ($ k) = 1
  ideal-sizeᵒ (` x) = 1
  ideal-sizeᵒ (ƛ T ˙ N) = suc (ideal-sizeᵒ N)
  ideal-sizeᵒ (ƛ̅ e ˙ N) = suc (ideal-sizeᵒ N)
  ideal-sizeᵒ (L · M) = suc (ideal-sizeᵒ L + ideal-sizeᵒ M)
  ideal-sizeᵒ (~ M) = suc (ideal-size M)
  ideal-sizeᵒ (blameᵒ ℓ) = 1

  ideal-size : MetaTerm → ℕ
  ideal-size ($ k) = 1
  ideal-size (` x) = 1
  ideal-size (addr a) = 1
  ideal-size (ƛ N) = suc (ideal-size N)
  ideal-size (L · M) = suc (ideal-size L + ideal-size M)
  ideal-size (Λ N) = suc (ideal-size N)
  ideal-size (M ·[ e ]) = suc (ideal-size M)
  ideal-size (e₁ <: e₂ => N) = suc (ideal-size N)
  ideal-size (M ●) = suc (ideal-size M)
  ideal-size (M ★ ℓ) = suc (ideal-size M)
  ideal-size (‶ M ″ e) = suc (ideal-sizeᵒ M)
  ideal-size (ref M) = suc (ideal-size M)
  ideal-size (L := M) = suc (ideal-size L + ideal-size M)
  ideal-size (! M) = suc (ideal-size M)
  ideal-size (M ⟨ c ⟩) = ideal-size M
  ideal-size (blame ℓ) = 1

ideal-sizeᵒ-positive : (M : CodeTerm) → 1 ≤ ideal-sizeᵒ M
ideal-sizeᵒ-positive ($ k) = ≤-refl
ideal-sizeᵒ-positive (` x) = ≤-refl
ideal-sizeᵒ-positive (ƛ T ˙ N) = s≤s z≤n
ideal-sizeᵒ-positive (ƛ̅ e ˙ N) = s≤s z≤n
ideal-sizeᵒ-positive (L · M) = s≤s z≤n
ideal-sizeᵒ-positive (~ M) = s≤s z≤n
ideal-sizeᵒ-positive (blameᵒ ℓ) = ≤-refl

mutual

  real-sizeᵒ : CodeTerm → ℕ
  real-sizeᵒ ($ k) = 1
  real-sizeᵒ (` x) = 1
  real-sizeᵒ (ƛ T ˙ N) = suc (real-sizeᵒ N)
  real-sizeᵒ (ƛ̅ e ˙ N) = suc (real-sizeᵒ N)
  real-sizeᵒ (L · M) = suc (real-sizeᵒ L + real-sizeᵒ M)
  real-sizeᵒ (~ M) = suc (real-size M)
  real-sizeᵒ (blameᵒ ℓ) = 1

  real-size : MetaTerm → ℕ
  real-size ($ k) = 1
  real-size (` x) = 1
  real-size (addr a) = 1
  real-size (ƛ N) = suc (real-size N)
  real-size (L · M) = suc (real-size L + real-size M)
  real-size (Λ N) = suc (real-size N)
  real-size (M ·[ e ]) = suc (real-size M)
  real-size (e₁ <: e₂ => N) = suc (real-size N)
  real-size (M ●) = suc (real-size M)
  real-size (M ★ ℓ) = suc (real-size M)
  real-size (‶ M ″ e) = suc (real-sizeᵒ M)
  real-size (ref M) = suc (real-size M)
  real-size (L := M) = suc (real-size L + real-size M)
  real-size (! M) = suc (real-size M)
  real-size (M ⟨ c ⟩) = real-size M + meta-hc-size c
  real-size (blame ℓ) = 1

mutual

  c-heightᵒ : CodeTerm → ℕ
  c-heightᵒ ($ k) = 0
  c-heightᵒ (` x) = 0
  c-heightᵒ (ƛ T ˙ N) = c-heightᵒ N
  c-heightᵒ (ƛ̅ e ˙ N) = c-heightᵒ N
  c-heightᵒ (L · M) = c-heightᵒ L ⊔ c-heightᵒ M
  c-heightᵒ (~ M) = c-height M
  c-heightᵒ (blameᵒ ℓ) = 0

  c-height : MetaTerm → ℕ
  c-height ($ k) = 0
  c-height (` x) = 0
  c-height (addr a) = 0
  c-height (ƛ N) = c-height N
  c-height (L · M) = c-height L ⊔ c-height M
  c-height (Λ N) = c-height N
  c-height (M ·[ e ]) = c-height M
  c-height (e₁ <: e₂ => N) = c-height N
  c-height (M ●) = c-height M
  c-height (M ★ ℓ) = c-height M
  c-height (‶ M ″ e) = c-heightᵒ M
  c-height (ref M) = c-height M
  c-height (L := M) = c-height L ⊔ c-height M
  c-height (! M) = c-height M
  c-height (M ⟨ c ⟩) = c-height M ⊔ meta-hc-height c
  c-height (blame ℓ) = 0


heap-c-height : Heap → ℕ
heap-c-height [] = 0
heap-c-height (V ∷ μ) = c-height V ⊔ heap-c-height μ

heap-size : Heap → ℕ
heap-size [] = 0
heap-size (V ∷ μ) = size V + heap-size μ

heap-real-size : Heap → ℕ
heap-real-size [] = 0
heap-real-size (V ∷ μ) = real-size V + heap-real-size μ

heap-ideal-size : Heap → ℕ
heap-ideal-size [] = 0
heap-ideal-size (V ∷ μ) = ideal-size V + heap-ideal-size μ

code-config-height : Config CodeTerm → ℕ
code-config-height C = heap-c-height (C .μ) ⊔ c-heightᵒ (C .M)

meta-config-height : Config MetaTerm → ℕ
meta-config-height C = heap-c-height (C .μ) ⊔ c-height (C .M)

code-config-real-size : Config CodeTerm → ℕ
code-config-real-size C = heap-real-size (C .μ) + real-sizeᵒ (C .M)

meta-config-real-size : Config MetaTerm → ℕ
meta-config-real-size C = heap-real-size (C .μ) + real-size (C .M)

code-config-ideal-size : Config CodeTerm → ℕ
code-config-ideal-size C = heap-ideal-size (C .μ) + ideal-sizeᵒ (C .M)

meta-config-ideal-size : Config MetaTerm → ℕ
meta-config-ideal-size C = heap-ideal-size (C .μ) + ideal-size (C .M)
