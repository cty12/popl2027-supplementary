module LambdaAlphaRefStar.Theories.SpaceEfficiency.Proofs.SizeOK where

open import Data.Bool using (Bool)
open import Data.List using ([]; _∷_)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _≤_; z≤n; s≤s)
open import Data.Nat.Properties using
  (≤-refl; ≤-reflexive; +-mono-≤; +-monoʳ-≤; *-distribˡ-+; *-distribʳ-+; *-mono-≤;
   m≤n⇒m≤1+n)
open import Data.Nat.Solver using (module +-*-Solver)
open import Relation.Binary.PropositionalEquality using (refl; sym)

open Data.Nat.Properties.≤-Reasoning

open import LambdaAlphaRefStar.Theories.SpaceEfficiency.CCAlphaRefStarSyntaxAndTypeSystem hiding (size)
open import LambdaAlphaRefStar.Theories.SpaceEfficiency.CCAlphaRefStarSizeAndHeight
open import LambdaAlphaRefStar.Theories.SpaceEfficiency.Proofs.PreserveOK


adj-casts-≤3 : ∀ {M n delayed}
  → n ∣ delayed ⊢ᵐ M ok
  → n ≤ 3
adj-casts-≤3 (castdelayedOK Mok n≤1) = s≤s (m≤n⇒m≤1+n n≤1)
adj-casts-≤3 (castOK Mok n≤2) = s≤s n≤2
adj-casts-≤3 constᵐOK = z≤n
adj-casts-≤3 varᵐOK = s≤s z≤n
adj-casts-≤3 addrOK = z≤n
adj-casts-≤3 (absᵐOK Mok) = z≤n
adj-casts-≤3 (appᵐOK Lok Mok) = z≤n
adj-casts-≤3 (ecAbsOK Mok) = z≤n
adj-casts-≤3 (ecAppOK Mok) = z≤n
adj-casts-≤3 (subIntroOK Mok) = z≤n
adj-casts-≤3 (subElimOK Mok) = z≤n
adj-casts-≤3 (subElimDynOK Mok) = z≤n
adj-casts-≤3 (quoteOK Mok) = z≤n
adj-casts-≤3 (refOK Mok) = z≤n
adj-casts-≤3 (assignOK Lok Mok) = z≤n
adj-casts-≤3 (derefOK Mok) = z≤n
adj-casts-≤3 blameOK = z≤n

lt-1-10 : 1 ≤ 10
lt-1-10 = s≤s z≤n

lt-4-10 : 4 ≤ 10
lt-4-10 = s≤s (s≤s (s≤s (s≤s z≤n)))

lt-7-10 : 7 ≤ 10
lt-7-10 = s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))))

size-OK-1 : ∀ {delayed} (M : MetaTerm) (n : ℕ)
  → n ∣ delayed ⊢ᵐ M ok
  → size M ≤ n + 10 * ideal-size M
  → 1 + size M ≤ 10 * (1 + ideal-size M)
size-OK-1 M n Mok IH =
  begin
    1 + size M
  ≤⟨ s≤s IH ⟩
    1 + (n + 10 * ideal-size M)
  ≤⟨ s≤s (+-mono-≤ (adj-casts-≤3 Mok) ≤-refl) ⟩
    4 + 10 * ideal-size M
  ≤⟨ +-mono-≤ lt-4-10 ≤-refl ⟩
    10 + 10 * ideal-size M
  ≤⟨ ≤-reflexive (sym (*-distribˡ-+ 10 1 (ideal-size M))) ⟩
    10 * (1 + ideal-size M)
  ∎

sizeᵒ-OK-1 : (M : CodeTerm)
  → sizeᵒ M ≤ 10 * ideal-sizeᵒ M
  → 1 + sizeᵒ M ≤ 10 * (1 + ideal-sizeᵒ M)
sizeᵒ-OK-1 M IH =
  begin
    1 + sizeᵒ M
  ≤⟨ s≤s IH ⟩
    1 + 10 * ideal-sizeᵒ M
  ≤⟨ +-mono-≤ lt-1-10 ≤-refl ⟩
    10 + 10 * ideal-sizeᵒ M
  ≤⟨ ≤-reflexive (sym (*-distribˡ-+ 10 1 (ideal-sizeᵒ M))) ⟩
    10 * (1 + ideal-sizeᵒ M)
  ∎

sizeᵒ-binary : ∀ {L M : CodeTerm}
  → sizeᵒ L ≤ 10 * ideal-sizeᵒ L
  → sizeᵒ M ≤ 10 * ideal-sizeᵒ M
  → 1 + sizeᵒ L + sizeᵒ M ≤ 10 * (1 + ideal-sizeᵒ L + ideal-sizeᵒ M)
sizeᵒ-binary {L = L} {M = M} LIH MIH =
  begin
    1 + sizeᵒ L + sizeᵒ M
  ≤⟨ s≤s (+-mono-≤ LIH MIH) ⟩
    1 + 10 * ideal-sizeᵒ L + 10 * ideal-sizeᵒ M
  ≤⟨ +-mono-≤ lt-1-10 ≤-refl ⟩
    10 + 10 * ideal-sizeᵒ L + 10 * ideal-sizeᵒ M
  ≤⟨ +-monoʳ-≤ 10 (≤-reflexive (sym (*-distribˡ-+ 10 (ideal-sizeᵒ L) (ideal-sizeᵒ M)))) ⟩
    10 + 10 * (ideal-sizeᵒ L + ideal-sizeᵒ M)
  ≤⟨ ≤-reflexive (sym (*-distribˡ-+ 10 1 (ideal-sizeᵒ L + ideal-sizeᵒ M))) ⟩
    10 * (1 + ideal-sizeᵒ L + ideal-sizeᵒ M)
  ∎

size-binary : ∀ {L M : MetaTerm} {delayed}
  → (n m : ℕ)
  → n ∣ delayed ⊢ᵐ L ok
  → m ∣ delayed ⊢ᵐ M ok
  → size L ≤ n + 10 * ideal-size L
  → size M ≤ m + 10 * ideal-size M
  → 1 + size L + size M ≤ 10 * (1 + ideal-size L + ideal-size M)
size-binary {L = L} {M = M} n m Lok Mok LIH MIH =
  begin
    1 + size L + size M
  ≤⟨ s≤s (+-mono-≤ LIH MIH) ⟩
    1 + (n + 10 * ideal-size L) + (m + 10 * ideal-size M)
  ≤⟨ s≤s (+-mono-≤ (+-mono-≤ (adj-casts-≤3 Lok) ≤-refl) (+-mono-≤ (adj-casts-≤3 Mok) ≤-refl)) ⟩
    1 + (3 + 10 * ideal-size L) + (3 + 10 * ideal-size M)
  ≤⟨ ≤-reflexive (solve 2
       (λ x y → con 1 :+ (con 3 :+ con 10 :* x) :+ (con 3 :+ con 10 :* y) :=ᵉ con 7 :+ (con 10 :* x) :+ (con 10 :* y))
       refl (ideal-size L) (ideal-size M)) ⟩
    7 + 10 * ideal-size L + 10 * ideal-size M
  ≤⟨ +-mono-≤ lt-7-10 ≤-refl ⟩
    10 + 10 * ideal-size L + 10 * ideal-size M
  ≤⟨ +-monoʳ-≤ 10 (≤-reflexive (sym (*-distribˡ-+ 10 (ideal-size L) (ideal-size M)))) ⟩
    10 + 10 * (ideal-size L + ideal-size M)
  ≤⟨ ≤-reflexive (sym (*-distribˡ-+ 10 1 (ideal-size L + ideal-size M))) ⟩
    10 * (1 + ideal-size L + ideal-size M)
  ∎
  where
  open +-*-Solver renaming (_:=_ to _:=ᵉ_) using (solve; _:+_; _:*_; con)

mutual

  sizeᵒ-OK : ∀ {d M}
    → d ⊢ᵒ M ok
    → sizeᵒ M ≤ 10 * ideal-sizeᵒ M
  sizeᵒ-OK (spliceOK {M = M} Mok) = size-OK-1 M _ Mok (size-OK M _ Mok)
  sizeᵒ-OK constᵒOK = s≤s z≤n
  sizeᵒ-OK varᵒOK = s≤s z≤n
  sizeᵒ-OK (absᵒOK {N = N} Nok) = sizeᵒ-OK-1 N (sizeᵒ-OK Nok)
  sizeᵒ-OK (absValᵒOK {N = N} Nok) = sizeᵒ-OK-1 N (sizeᵒ-OK Nok)
  sizeᵒ-OK (appᵒOK Lok Mok) = sizeᵒ-binary (sizeᵒ-OK Lok) (sizeᵒ-OK Mok)
  sizeᵒ-OK blameᵒOK = s≤s z≤n

  size-OK : (M : MetaTerm) (n : ℕ) {delayed : Bool}
    → n ∣ delayed ⊢ᵐ M ok
    → size M ≤ n + 10 * ideal-size M
  size-OK (M ⟨ c ⟩) (suc n) (castdelayedOK Mok n≤1) =
    begin
      1 + size M
    ≤⟨ s≤s (size-OK M n Mok) ⟩
      1 + (n + 10 * ideal-size M)
    ≤⟨ ≤-refl ⟩
      suc n + 10 * ideal-size M
    ∎
  size-OK (M ⟨ c ⟩) (suc n) (castOK Mok n≤2) =
    begin
      1 + size M
    ≤⟨ s≤s (size-OK M n Mok) ⟩
      1 + (n + 10 * ideal-size M)
    ≤⟨ ≤-refl ⟩
      suc n + 10 * ideal-size M
    ∎
  size-OK ($ k) zero constᵐOK = s≤s z≤n
  size-OK (` x) (suc zero) varᵐOK = s≤s z≤n
  size-OK (addr a) zero addrOK = s≤s z≤n
  size-OK (ƛ N) zero (absᵐOK Nok) = size-OK-1 N _ Nok (size-OK N _ Nok)
  size-OK (L · M) zero (appᵐOK {n = n} {m = m} Lok Mok) =
    size-binary n m Lok Mok (size-OK L n Lok) (size-OK M m Mok)
  size-OK (Λ N) zero (ecAbsOK Nok) = size-OK-1 N _ Nok (size-OK N _ Nok)
  size-OK (M ·[ e ]) zero (ecAppOK Mok) = size-OK-1 M _ Mok (size-OK M _ Mok)
  size-OK (e₁ <: e₂ => N) zero (subIntroOK Nok) = size-OK-1 N _ Nok (size-OK N _ Nok)
  size-OK (M ●) zero (subElimOK Mok) = size-OK-1 M _ Mok (size-OK M _ Mok)
  size-OK (M ★ ℓ) zero (subElimDynOK Mok) = size-OK-1 M _ Mok (size-OK M _ Mok)
  size-OK (‶ M ″ e) zero (quoteOK Mok) = sizeᵒ-OK-1 M (sizeᵒ-OK Mok)
  size-OK (ref M) zero (refOK Mok) = size-OK-1 M _ Mok (size-OK M _ Mok)
  size-OK (L := M) zero (assignOK {n = n} {m = m} Lok Mok) =
    size-binary n m Lok Mok (size-OK L n Lok) (size-OK M m Mok)
  size-OK (! M) zero (derefOK Mok) = size-OK-1 M _ Mok (size-OK M _ Mok)
  size-OK (blame ℓ) zero blameOK = s≤s z≤n

ideal-size-positive : (M : MetaTerm) → 1 ≤ ideal-size M
ideal-size-positive ($ k) = ≤-refl
ideal-size-positive (` x) = ≤-refl
ideal-size-positive (addr a) = ≤-refl
ideal-size-positive (ƛ N) = s≤s z≤n
ideal-size-positive (L · M) = s≤s z≤n
ideal-size-positive (Λ N) = s≤s z≤n
ideal-size-positive (M ·[ e ]) = s≤s z≤n
ideal-size-positive (e₁ <: e₂ => N) = s≤s z≤n
ideal-size-positive (M ●) = s≤s z≤n
ideal-size-positive (M ★ ℓ) = s≤s z≤n
ideal-size-positive (‶ M ″ e) = s≤s z≤n
ideal-size-positive (ref M) = s≤s z≤n
ideal-size-positive (L := M) = s≤s z≤n
ideal-size-positive (! M) = s≤s z≤n
ideal-size-positive (M ⟨ c ⟩) = ideal-size-positive M
ideal-size-positive (blame ℓ) = ≤-refl

three≤three* : ∀ {n}
  → 1 ≤ n
    -------
  → 3 ≤ 3 * n
three≤three* {n = n} 1≤n =
  *-mono-≤ {x = 3} {y = 3} {u = 1} {v = n} ≤-refl 1≤n

size-OK≤13ideal : ∀ {M n delayed}
  → n ∣ delayed ⊢ᵐ M ok
    ----------------------------
  → size M ≤ 13 * ideal-size M
size-OK≤13ideal {M = M} {n = n} Mok =
  begin
    size M
  ≤⟨ size-OK M n Mok ⟩
    n + 10 * ideal-size M
  ≤⟨ +-mono-≤ (adj-casts-≤3 Mok) ≤-refl ⟩
    3 + 10 * ideal-size M
  ≤⟨ +-mono-≤ (three≤three* (ideal-size-positive M)) ≤-refl ⟩
    3 * ideal-size M + 10 * ideal-size M
  ≤⟨ ≤-reflexive (sym (*-distribʳ-+ (ideal-size M) 3 10)) ⟩
    13 * ideal-size M
  ∎

heap-size-OK≤13ideal : ∀ {μ}
  → ⊢ μ ok
    ------------------------------------
  → heap-size μ ≤ 13 * heap-ideal-size μ
heap-size-OK≤13ideal μok-[] = z≤n
heap-size-OK≤13ideal (μok-∷ {μ = μ} {V = V} value Vok μok) =
  begin
    size V + heap-size μ
  ≤⟨ +-mono-≤ (size-OK≤13ideal Vok) (heap-size-OK≤13ideal μok) ⟩
    13 * ideal-size V + 13 * heap-ideal-size μ
  ≤⟨ ≤-reflexive (sym (*-distribˡ-+ 13 (ideal-size V) (heap-ideal-size μ))) ⟩
    13 * (ideal-size V + heap-ideal-size μ)
  ∎
