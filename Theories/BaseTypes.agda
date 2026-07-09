module LambdaAlphaRefStar.Theories.BaseTypes where

  open import Data.Nat     using (ℕ; zero; suc)
  open import Data.Bool    using (Bool) renaming (_≟_ to _=?_)
  open import Data.Integer using (ℤ) renaming (_≟_ to _=int_)
  open import Data.Unit    using (⊤; tt)
  open import Relation.Nullary using (¬_; ¬?; Dec; yes; no)
  open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym)

  -- | Base Types
  data Base : Set where
      Nat   : Base
      Int   : Base
      𝔹     : Base
      Unit  : Base

  -- | Maps base types to their Agda types
  base-rep : Base → Set
  base-rep Nat  = ℕ
  base-rep Int  = ℤ
  base-rep 𝔹    = Bool
  base-rep Unit = ⊤

  -- | Equality
  base-eq? : ∀ (ι₁ ι₂ : Base) → Dec (ι₁ ≡ ι₂)
  base-eq? Nat Nat = yes refl
  base-eq? Nat Int = no λ ()
  base-eq? Nat 𝔹 = no λ ()
  base-eq? Nat Unit = no λ ()
  base-eq? Int Nat = no λ ()
  base-eq? Int Int = yes refl
  base-eq? Int 𝔹 = no λ ()
  base-eq? Int Unit = no λ ()
  base-eq? 𝔹 Nat = no λ ()
  base-eq? 𝔹 Int = no λ ()
  base-eq? 𝔹 𝔹 = yes refl
  base-eq? 𝔹 Unit = no λ ()
  base-eq? Unit Nat = no λ ()
  base-eq? Unit Int = no λ ()
  base-eq? Unit 𝔹 = no λ ()
  base-eq? Unit Unit = yes refl
