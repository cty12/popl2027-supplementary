module LambdaAlphaRefStar.Theories.SpaceEfficiency.AdjacentCastOK where

open import Data.Bool using (Bool; true; false)
open import Data.Nat using (ℕ; zero; suc; _≤_)

open import LambdaAlphaRefStar.Theories.BaseTypes
open import LambdaAlphaRefStar.Theories.SpaceEfficiency.CCAlphaRefStarSyntaxAndTypeSystem


infix 3 _⊢ᵒ_ok
infix 3 _∣_⊢ᵐ_ok

data _⊢ᵒ_ok (d : Bool) : CodeTerm → Set
data _∣_⊢ᵐ_ok : ℕ → Bool → MetaTerm → Set

data _⊢ᵒ_ok d where

  spliceOK : ∀ {n M}
    → n ∣ d ⊢ᵐ M ok
      ------------------
    → d ⊢ᵒ ~ M ok

  constᵒOK : ∀ {ι} {k : base-rep ι}
      ----------------
    → d ⊢ᵒ $ k ok

  varᵒOK : ∀ {x}
      ----------------
    → d ⊢ᵒ ` x ok

  absᵒOK : ∀ {T N}
    → d ⊢ᵒ N ok
      ----------------------
    → d ⊢ᵒ ƛ T ˙ N ok

  absValᵒOK : ∀ {e N}
    → d ⊢ᵒ N ok
      ----------------------
    → d ⊢ᵒ ƛ̅ e ˙ N ok

  appᵒOK : ∀ {L M}
    → d ⊢ᵒ L ok
    → d ⊢ᵒ M ok
      ------------------
    → d ⊢ᵒ L · M ok

  blameᵒOK : ∀ {ℓ}
      ----------------------
    → d ⊢ᵒ blameᵒ ℓ ok

data _∣_⊢ᵐ_ok where

  castdelayedOK : ∀ {M c n}
    → n ∣ true ⊢ᵐ M ok
    → n ≤ 1
      ----------------------------
    → suc n ∣ true ⊢ᵐ M ⟨ c ⟩ ok

  castOK : ∀ {M c n}
    → n ∣ false ⊢ᵐ M ok
    → n ≤ 2
      -----------------------------
    → suc n ∣ false ⊢ᵐ M ⟨ c ⟩ ok

  constᵐOK : ∀ {ι delayed} {k : base-rep ι}
      -----------------------
    → 0 ∣ delayed ⊢ᵐ $ k ok

  varᵐOK : ∀ {x delayed}
      -----------------------
    → 1 ∣ delayed ⊢ᵐ ` x ok

  addrOK : ∀ {a delayed}
      ----------------------------
    → 0 ∣ delayed ⊢ᵐ addr a ok

  absᵐOK : ∀ {N n delayed}
    → n ∣ true ⊢ᵐ N ok
      ----------------------
    → 0 ∣ delayed ⊢ᵐ ƛ N ok

  appᵐOK : ∀ {L M delayed n m}
    → n ∣ delayed ⊢ᵐ L ok
    → m ∣ delayed ⊢ᵐ M ok
      -----------------------
    → 0 ∣ delayed ⊢ᵐ L · M ok

  ecAbsOK : ∀ {N delayed n}
    → n ∣ true ⊢ᵐ N ok
      ----------------------
    → 0 ∣ delayed ⊢ᵐ Λ N ok

  ecAppOK : ∀ {M e delayed n}
    → n ∣ delayed ⊢ᵐ M ok
      ----------------------------
    → 0 ∣ delayed ⊢ᵐ M ·[ e ] ok

  subIntroOK : ∀ {e₁ e₂ N delayed n}
    → n ∣ true ⊢ᵐ N ok
      -----------------------------------
    → 0 ∣ delayed ⊢ᵐ e₁ <: e₂ => N ok

  subElimOK : ∀ {M delayed n}
    → n ∣ delayed ⊢ᵐ M ok
      -----------------------
    → 0 ∣ delayed ⊢ᵐ M ● ok

  subElimDynOK : ∀ {M delayed n ℓ}
    → n ∣ delayed ⊢ᵐ M ok
      -------------------------
    → 0 ∣ delayed ⊢ᵐ M ★ ℓ ok

  quoteOK : ∀ {M e delayed}
    → delayed ⊢ᵒ M ok
      --------------------------
    → 0 ∣ delayed ⊢ᵐ ‶ M ″ e ok

  refOK : ∀ {M delayed n}
    → n ∣ delayed ⊢ᵐ M ok
      -------------------------
    → 0 ∣ delayed ⊢ᵐ ref M ok

  assignOK : ∀ {L M delayed n m}
    → n ∣ delayed ⊢ᵐ L ok
    → m ∣ delayed ⊢ᵐ M ok
      --------------------------
    → 0 ∣ delayed ⊢ᵐ L := M ok

  derefOK : ∀ {M delayed n}
    → n ∣ delayed ⊢ᵐ M ok
      -----------------------
    → 0 ∣ delayed ⊢ᵐ ! M ok

  blameOK : ∀ {ℓ delayed}
      --------------------------
    → 0 ∣ delayed ⊢ᵐ blame ℓ ok
