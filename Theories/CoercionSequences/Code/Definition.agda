module Theories.CoercionSequences.Code.Definition where

open import Data.List using (List; []; _∷_; _++_; [_])
open import Data.Product using (∃-syntax; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_)
open import Relation.Nullary using (¬_)

open import Theories.CodeTypes public
open import Theories.BlameLabels public


infix 9 _！
infix 9 _？_
infixr 6 _⇒_
infix 8 ⊥_
infixr 7 _;_


-- | Single code coercions (cᵒ, dᵒ).
data OSingleCoercion : Set where
  _！ : (Gᵒ : OType⋆) → OGround Gᵒ → OSingleCoercion
  _？_ : (Gᵒ : OType⋆) → BlameLabel → OGround Gᵒ → OSingleCoercion
  _⇒_ : List OSingleCoercion → List OSingleCoercion → OSingleCoercion
  ⊥_ : BlameLabel → OSingleCoercion


-- | Code coercion sequences (c̅ᵒ, d̅ᵒ).
OCoercionSeq = List OSingleCoercion

-- | Coercion sequences are ordinary lists.  We use semicolon for cons to
--   match the paper notation, and Data.List.[_] for singleton sequences.
pattern _;_ cᵒ c̅ᵒ = cᵒ ∷ c̅ᵒ


-- | Singleton identity sequence.
IdSeq : OCoercionSeq → Set
IdSeq c̅ᵒ = c̅ᵒ ≡ []

-- | Singleton blame sequences.
BlameSeq : OCoercionSeq → Set
BlameSeq c̅ᵒ = ∃[ ℓ ] c̅ᵒ ≡ [ ⊥ ℓ ]


-- | Code coercion typing.
infix 4 ⊢ᵒ_⦂_⇒_
infix 4 ⊢ᵒ̅_⦂_⇒_

mutual

  data ⊢ᵒ_⦂_⇒_ : OSingleCoercion → OType⋆ → OType⋆ → Set where

    ⊢! : ∀ {Gᵒ}
      → (g : OGround Gᵒ)
        ---------------------------
      → ⊢ᵒ (Gᵒ ！) g ⦂ Gᵒ ⇒ ⋆

    ⊢? : ∀ {Gᵒ}
      → (ℓ : BlameLabel)
      → (g : OGround Gᵒ)
        ---------------------------
      → ⊢ᵒ (Gᵒ ？ ℓ) g ⦂ ⋆ ⇒ Gᵒ

    ⊢fun : ∀ {C₁ C₂ C₃ C₄ c̅ᵒ d̅ᵒ}
      → ⊢ᵒ̅ c̅ᵒ ⦂ C₃ ⇒ C₁
      → ⊢ᵒ̅ d̅ᵒ ⦂ C₂ ⇒ C₄
        ---------------------------------------------
      → ⊢ᵒ (c̅ᵒ ⇒ d̅ᵒ) ⦂ (C₁ ⇒ C₂) ⇒ (C₃ ⇒ C₄)

    ⊢⊥ : ∀ C₁ C₂ ℓ
        ------------------------
      → ⊢ᵒ (⊥ ℓ) ⦂ C₁ ⇒ C₂

  data ⊢ᵒ̅_⦂_⇒_ : OCoercionSeq → OType⋆ → OType⋆ → Set where

    ⊢[] : ∀ {C}
        ------------------
      → ⊢ᵒ̅ [] ⦂ C ⇒ C

    ⊢; : ∀ {C₁ C₂ C₃ cᵒ c̅ᵒ}
      → ⊢ᵒ cᵒ ⦂ C₁ ⇒ C₂
      → ⊢ᵒ̅ c̅ᵒ ⦂ C₂ ⇒ C₃
        ---------------------------
      → ⊢ᵒ̅ (cᵒ ; c̅ᵒ) ⦂ C₁ ⇒ C₃


-- | Irreducible adjacent pairs of single coercions.
data IrredPair : OSingleCoercion → OSingleCoercion → Set where

  irred-?! : ∀ {Gᵒ ℓ} {g h : OGround Gᵒ}
      ---------------------------------------
    → IrredPair ((Gᵒ ？ ℓ) g) ((Gᵒ ！) h)

  irred-?⊥ : ∀ {Gᵒ ℓ₁ ℓ₂} {g : OGround Gᵒ}
      ---------------------------------------
    → IrredPair ((Gᵒ ？ ℓ₁) g) (⊥ ℓ₂)

  irred-?fun : ∀ {ℓ c̅ᵒ₁ c̅ᵒ₂}
      ---------------------------------------------------
    → IrredPair (((⋆ ⇒ ⋆) ？ ℓ) gfun) (c̅ᵒ₁ ⇒ c̅ᵒ₂)

  irred-fun! : ∀ {c̅ᵒ₁ c̅ᵒ₂}
      ------------------------------------------------
    → IrredPair (c̅ᵒ₁ ⇒ c̅ᵒ₂) (((⋆ ⇒ ⋆) ！) gfun)


-- | Normal forms for single coercions and sequences.
mutual

  data SingleNF : OSingleCoercion → Set where

    nf-! : ∀ {Gᵒ} {g : OGround Gᵒ}
        ------------------------------
      → SingleNF ((Gᵒ ！) g)

    nf-? : ∀ {Gᵒ ℓ} {g : OGround Gᵒ}
        ---------------------------------
      → SingleNF ((Gᵒ ？ ℓ) g)

    nf-⊥ : ∀ {ℓ}
        ------------------
      → SingleNF (⊥ ℓ)

    nf-fun : ∀ {c̅ᵒ₁ c̅ᵒ₂}
      → NF c̅ᵒ₁
      → NF c̅ᵒ₂
      → ¬ (IdSeq c̅ᵒ₁ × IdSeq c̅ᵒ₂)
      → ¬ (BlameSeq c̅ᵒ₁)
      → ¬ (BlameSeq c̅ᵒ₂)
        ------------------------------
      → SingleNF (c̅ᵒ₁ ⇒ c̅ᵒ₂)

  data NF : OCoercionSeq → Set where

    nf-empty :
        ---------
        NF []

    nf-singleton : ∀ {cᵒ}
      → SingleNF cᵒ
        ---------------
      → NF [ cᵒ ]

    nf-step : ∀ {cᵒ₁ cᵒ₂ c̅ᵒ}
      → SingleNF cᵒ₁
      → IrredPair cᵒ₁ cᵒ₂
      → NF (cᵒ₂ ; c̅ᵒ)
        ------------------------
      → NF (cᵒ₁ ; cᵒ₂ ; c̅ᵒ)


-- | Adjacent-pair reduction for single code coercions.
infix 3 ⊢ᵒ_;_⟶_

data ⊢ᵒ_;_⟶_ : OSingleCoercion → OSingleCoercion → OCoercionSeq → Set where

  collapse : ∀ {Gᵒ ℓ} {g h : OGround Gᵒ}
      ------------------------------------------
    → ⊢ᵒ ((Gᵒ ！) g) ; ((Gᵒ ？ ℓ) h) ⟶ []

  collide : ∀ {Gᵒ Hᵒ ℓ} {g : OGround Gᵒ} {h : OGround Hᵒ}
    → Gᵒ ≢ Hᵒ
      ------------------------------------------
    → ⊢ᵒ ((Gᵒ ！) g) ; ((Hᵒ ？ ℓ) h) ⟶ [ ⊥ ℓ ]

  seq-fun : ∀ {c̅ᵒ₁ c̅ᵒ₂ d̅ᵒ₁ d̅ᵒ₂}
      ---------------------------------------------------------------------
    → ⊢ᵒ (c̅ᵒ₁ ⇒ c̅ᵒ₂) ; (d̅ᵒ₁ ⇒ d̅ᵒ₂) ⟶ [ (d̅ᵒ₁ ++ c̅ᵒ₁) ⇒ (c̅ᵒ₂ ++ d̅ᵒ₂) ]

  ⊥-left : ∀ {ℓ cᵒ}
      ------------------------
    → ⊢ᵒ ⊥ ℓ ; cᵒ ⟶ [ ⊥ ℓ ]

  ⊥-right-! : ∀ {Gᵒ ℓ} {g : OGround Gᵒ}
      ---------------------------------
    → ⊢ᵒ ((Gᵒ ！) g) ; ⊥ ℓ ⟶ [ ⊥ ℓ ]

  -- NOTE: new rule
  ⊥-right-fun : ∀ {c̅ᵒ₁ c̅ᵒ₂ ℓ}
      ---------------------------------
    → ⊢ᵒ (c̅ᵒ₁ ⇒ c̅ᵒ₂) ; ⊥ ℓ ⟶ [ ⊥ ℓ ]


-- | Reduction for single code coercions and code coercion sequences.
infix 3 ⊢ᵒ_—→_
infix 3 ⊢ᵒ̅_—→_

mutual

  data ⊢ᵒ_—→_ : OSingleCoercion → OCoercionSeq → Set where

    id-fun :
        ---------------------------------
        ⊢ᵒ ([] ⇒ []) —→ []

    ξ-fun-dom : ∀ {c̅ᵒ₁ c̅ᵒ₂ d̅ᵒ₁}
      → ⊢ᵒ̅ c̅ᵒ₁ —→ d̅ᵒ₁
        ---------------------------------------
      → ⊢ᵒ (c̅ᵒ₁ ⇒ c̅ᵒ₂) —→ [ d̅ᵒ₁ ⇒ c̅ᵒ₂ ]

    ξ-fun-cod : ∀ {c̅ᵒ₁ c̅ᵒ₂ d̅ᵒ₂}
      → NF c̅ᵒ₁
      → ¬ (BlameSeq c̅ᵒ₁)
      → ⊢ᵒ̅ c̅ᵒ₂ —→ d̅ᵒ₂
        ---------------------------------------
      → ⊢ᵒ (c̅ᵒ₁ ⇒ c̅ᵒ₂) —→ [ c̅ᵒ₁ ⇒ d̅ᵒ₂ ]

    ξ-⊥-fun-dom : ∀ {ℓ c̅ᵒ}
        -------------------------------
      → ⊢ᵒ ([ ⊥ ℓ ] ⇒ c̅ᵒ) —→ [ ⊥ ℓ ]

    ξ-⊥-fun-cod : ∀ {c̅ᵒ ℓ}
      → NF c̅ᵒ
      → ¬ (BlameSeq c̅ᵒ)
        -------------------------------
      → ⊢ᵒ (c̅ᵒ ⇒ [ ⊥ ℓ ]) —→ [ ⊥ ℓ ]

  data ⊢ᵒ̅_—→_ : OCoercionSeq → OCoercionSeq → Set where

    reduce-head : ∀ {cᵒ d̅ᵒ c̅ᵒ}
      → ⊢ᵒ cᵒ —→ d̅ᵒ
        ---------------------------------
      → ⊢ᵒ̅ (cᵒ ; c̅ᵒ) —→ (d̅ᵒ ++ c̅ᵒ)

    reduce-neighbors : ∀ {cᵒ₁ cᵒ₂ d̅ᵒ c̅ᵒ}
      → SingleNF cᵒ₁
      → ⊢ᵒ cᵒ₁ ; cᵒ₂ ⟶ d̅ᵒ
        ---------------------------------------
      → ⊢ᵒ̅ (cᵒ₁ ; cᵒ₂ ; c̅ᵒ) —→ (d̅ᵒ ++ c̅ᵒ)

    reduce-tail : ∀ {cᵒ₁ cᵒ₂ c̅ᵒ d̅ᵒ}
      → SingleNF cᵒ₁
      → IrredPair cᵒ₁ cᵒ₂
      → ⊢ᵒ̅ (cᵒ₂ ; c̅ᵒ) —→ d̅ᵒ
        ---------------------------------------
      → ⊢ᵒ̅ (cᵒ₁ ; cᵒ₂ ; c̅ᵒ) —→ (cᵒ₁ ; d̅ᵒ)


-- | Multi-step reduction for code coercion sequences.
infix 3 ⊢ᵒ̅_—↠_

data ⊢ᵒ̅_—↠_ : OCoercionSeq → OCoercionSeq → Set where

  ↠-refl : ∀ {c̅ᵒ}
      ------------------
    → ⊢ᵒ̅ c̅ᵒ —↠ c̅ᵒ

  ↠-step : ∀ {c̅ᵒ d̅ᵒ e̅ᵒ}
    → ⊢ᵒ̅ c̅ᵒ —→ d̅ᵒ
    → ⊢ᵒ̅ d̅ᵒ —↠ e̅ᵒ
      ------------------
    → ⊢ᵒ̅ c̅ᵒ —↠ e̅ᵒ
