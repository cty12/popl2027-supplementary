module Theories.STLC where

open import Data.List using (List; _∷_)
open import Data.Nat using (ℕ)

open import Theories.Utils using (_∋_⦂_)
open import Theories.BaseTypes using (base-rep)
open import Theories.CodeTypes using (OType; `_ ; _⇒_)


-- | Ordinary STLC terms.
infix 8 $_
infix 8 `_
infix 8 ƛ_˙_
infixl 7 _·_

data STLCTerm : Set where
  $_    : ∀ {ι} → base-rep ι → STLCTerm
  `_    : ℕ → STLCTerm
  ƛ_˙_  : OType → STLCTerm → STLCTerm
  _·_   : STLCTerm → STLCTerm → STLCTerm


STLCCtx : Set
STLCCtx = List OType


-- | STLC typing.
infix 3 _⊢_⦂_

data _⊢_⦂_ : STLCCtx → STLCTerm → OType → Set where

  ⊢const : ∀ {Γ ι}
    → (r : base-rep ι)
      ---------------------
    → Γ ⊢ $ r ⦂ ` ι

  ⊢var : ∀ {Γ x T}
    → Γ ∋ x ⦂ T
      ------------------
    → Γ ⊢ ` x ⦂ T

  ⊢lam : ∀ {Γ M T₁ T₂}
    → T₁ ∷ Γ ⊢ M ⦂ T₂
      -------------------------------
    → Γ ⊢ ƛ T₁ ˙ M ⦂ T₁ ⇒ T₂

  ⊢app : ∀ {Γ L M T₁ T₂}
    → Γ ⊢ L ⦂ T₁ ⇒ T₂
    → Γ ⊢ M ⦂ T₁
      -------------------
    → Γ ⊢ L · M ⦂ T₂
