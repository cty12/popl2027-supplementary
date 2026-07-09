module Theories.CoercionSequences.EC.Definition where

open import Data.List using (List; []; _∷_; _++_; [_])
open import Data.Product using (∃-syntax)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_)
open import Relation.Nullary using (¬_)

open import Theories.EnvClassifiers public
open import Theories.BlameLabels     public


infix 9 _！
infix 9 _？_
infix 8 _↑_
infix 8 ⊥_
infixr 7 _;_


-- | Single EC coercions (cᵉ, dᵉ).
data ECSingleCoercion : Set where
  _！  : EC → ECSingleCoercion
  _？_ : EC → BlameLabel → ECSingleCoercion
  _↑_ : EC⋆ → EC⋆ → ECSingleCoercion
  ⊥_  : BlameLabel → ECSingleCoercion

-- | EC coercion sequences (c̅ᵉ, d̅ᵉ).
ECCoercionSeq = List ECSingleCoercion

-- | Coercion sequences are ordinary lists.  We use semicolon for cons to
--   match the paper notation, and Data.List.[_] for singleton sequences.
pattern _;_ cᵉ c̅ᵉ = cᵉ ∷ c̅ᵉ


-- | Singleton blame coercions.
Blame : ECSingleCoercion → Set
Blame cᵉ = ∃[ ℓ ] cᵉ ≡ ⊥ ℓ

-- | Singleton blame EC coercion sequences.
BlameSeq : ECCoercionSeq → Set
BlameSeq c̅ᵉ = ∃[ ℓ ] c̅ᵉ ≡ [ ⊥ ℓ ]

-- | Identity EC coercion sequences.
IdSeq : ECCoercionSeq → Set
IdSeq c̅ᵉ = c̅ᵉ ≡ []

-- | Single EC coercion typing.
infix 4 _;_⊢ᵉ_⦂_⇒_

data _;_⊢ᵉ_⦂_⇒_ : ECCtx → SubCtx → ECSingleCoercion → EC⋆ → EC⋆ → Set where

  ⊢! : ∀ {Δ Θ}
    → (e : EC)
    → Δ ⊢ᵉ e
      ------------------------------
    → Δ ; Θ ⊢ᵉ e ！ ⦂ ec e ⇒ ⋆

  ⊢? : ∀ {Δ Θ}
    → (e : EC)
    → Δ ⊢ᵉ e
    → (ℓ : BlameLabel)
      ---------------------------------
    → Δ ; Θ ⊢ᵉ e ？ ℓ ⦂ ⋆ ⇒ ec e

  ⊢↑ : ∀ {Δ Θ ê₁ ê₂}
    → Δ ⊢ᵉ⋆ ê₁
    → Δ ⊢ᵉ⋆ ê₂
    → Θ ⊢ᵉ ê₁ <:⋆ ê₂
      ---------------------------------
    → Δ ; Θ ⊢ᵉ ê₁ ↑ ê₂ ⦂ ê₁ ⇒ ê₂

  ⊢⊥ : ∀ {Δ Θ ê₁ ê₂}
    → Δ ⊢ᵉ⋆ ê₁
    → Δ ⊢ᵉ⋆ ê₂
    → (ℓ : BlameLabel)
      ---------------------------
    → Δ ; Θ ⊢ᵉ ⊥ ℓ ⦂ ê₁ ⇒ ê₂


-- | EC coercion sequence typing.
infix 4 _;_⊢ᵉ̅_⦂_⇒_

data _;_⊢ᵉ̅_⦂_⇒_ : ECCtx → SubCtx → ECCoercionSeq → EC⋆ → EC⋆ → Set where

  ⊢[] : ∀ {Δ Θ ê}
    → Δ ⊢ᵉ⋆ ê
      ------------------------
    → Δ ; Θ ⊢ᵉ̅ [] ⦂ ê ⇒ ê

  ⊢; : ∀ {Δ Θ cᵉ c̅ᵉ ê₁ ê₂ ê₃}
    → Δ ; Θ ⊢ᵉ cᵉ ⦂ ê₁ ⇒ ê₂
    → Δ ; Θ ⊢ᵉ̅ c̅ᵉ ⦂ ê₂ ⇒ ê₃
      ---------------------------------
    → Δ ; Θ ⊢ᵉ̅ cᵉ ; c̅ᵉ ⦂ ê₁ ⇒ ê₃


-- | Normal forms for single EC coercions.
data SingleNF : ECSingleCoercion → Set where

  nf-! : ∀ {e}
      ------------------
    → SingleNF (e ！)

  nf-? : ∀ {e ℓ}
      ----------------------
    → SingleNF (e ？ ℓ)

  nf-↑ : ∀ {ê₁ ê₂}
    → ê₁ ≢ ê₂
      ----------------------------
    → SingleNF (ê₁ ↑ ê₂)

  nf-⊥ : ∀ {ℓ}
      ------------------
    → SingleNF (⊥ ℓ)


-- | Irreducible adjacent pairs of single EC coercions.
data IrredPair : ECSingleCoercion → ECSingleCoercion → Set where

  irred-?! : ∀ {e ℓ}
      ------------------------------
    → IrredPair (e ？ ℓ) (e ！)

  irred-↑! : ∀ {e e′}
    → e′ ≢ e
      ------------------------------------
    → IrredPair (ec e′ ↑ ec e) (e ！)

  irred-!↑⋆ : ∀ {e}
      -----------------------------
    → IrredPair (e ！) (⋆ ↑ ⋆)

  irred-?↑ : ∀ {e e′ ℓ}
      ---------------------------------------
    → IrredPair (e ？ ℓ) (ec e ↑ ec e′)


-- | Normal forms for EC coercion sequences.
data NF : ECCoercionSeq → Set where

  nf-empty :
      ---------
      NF []

  nf-singleton : ∀ {cᵉ}
    → SingleNF cᵉ
      ---------------------
    → NF [ cᵉ ]

  nf-step : ∀ {cᵉ₁ cᵉ₂ c̅ᵉ}
    → SingleNF cᵉ₁
    → IrredPair cᵉ₁ cᵉ₂
    → NF (cᵉ₂ ; c̅ᵉ)
      ------------------------
    → NF (cᵉ₁ ; cᵉ₂ ; c̅ᵉ)


-- | Reduction for single EC coercions.
infix 3 _⊢ᵉ_—→_

data _⊢ᵉ_—→_ : SubCtx → ECSingleCoercion → ECCoercionSeq → Set where

  ↑-id : ∀ {Θ ê}
      --------------------
    → Θ ⊢ᵉ ê ↑ ê —→ []


-- | Adjacent-pair reduction for single EC coercions.
infix 3 _⊢ᵉ_;_⟶_

data _⊢ᵉ_;_⟶_ : SubCtx → ECSingleCoercion → ECSingleCoercion → ECCoercionSeq → Set where

  collapse : ∀ {Θ e₁ e₂ ℓ}
    → Θ ⊢ᵉ e₁ <: e₂
      ------------------------------------------
    → Θ ⊢ᵉ e₁ ！ ; e₂ ？ ℓ ⟶ [ ec e₁ ↑ ec e₂ ]

  collide : ∀ {Θ e₁ e₂ ℓ}
    → ¬ (Θ ⊢ᵉ e₁ <: e₂)
      ------------------------------
    → Θ ⊢ᵉ e₁ ！ ; e₂ ？ ℓ ⟶ [ ⊥ ℓ ]

  ↑-collapse : ∀ {Θ ê₁ ê₂ ê₃}
      ------------------------------------------
    → Θ ⊢ᵉ ê₁ ↑ ê₂ ; ê₂ ↑ ê₃ ⟶ [ ê₁ ↑ ê₃ ]

  ⊥-left : ∀ {Θ ℓ cᵉ}
      ---------------------------
    → Θ ⊢ᵉ ⊥ ℓ ; cᵉ ⟶ [ ⊥ ℓ ]

  ⊥-right : ∀ {Θ cᵉ ℓ}
    → ¬ (Blame cᵉ)
      ---------------------------
    → Θ ⊢ᵉ cᵉ ; ⊥ ℓ ⟶ [ ⊥ ℓ ]


-- | Reduction for EC coercion sequences.
infix 3 _⊢ᵉ̅_—→_

data _⊢ᵉ̅_—→_ : SubCtx → ECCoercionSeq → ECCoercionSeq → Set where

  reduce-head : ∀ {Θ cᵉ d̅ᵉ c̅ᵉ}
    → Θ ⊢ᵉ cᵉ —→ d̅ᵉ
      -------------------------------------
    → Θ ⊢ᵉ̅ cᵉ ; c̅ᵉ —→ d̅ᵉ ++ c̅ᵉ

  reduce-neighbors : ∀ {Θ cᵉ₁ cᵉ₂ d̅ᵉ c̅ᵉ}
    → SingleNF cᵉ₁
    → Θ ⊢ᵉ cᵉ₁ ; cᵉ₂ ⟶ d̅ᵉ
      ---------------------------------------
    → Θ ⊢ᵉ̅ cᵉ₁ ; cᵉ₂ ; c̅ᵉ —→ d̅ᵉ ++ c̅ᵉ

  reduce-tail : ∀ {Θ cᵉ₁ cᵉ₂ c̅ᵉ d̅ᵉ}
    → SingleNF cᵉ₁
    → IrredPair cᵉ₁ cᵉ₂
    → Θ ⊢ᵉ̅ cᵉ₂ ; c̅ᵉ —→ d̅ᵉ
      ---------------------------------------
    → Θ ⊢ᵉ̅ cᵉ₁ ; cᵉ₂ ; c̅ᵉ —→ cᵉ₁ ; d̅ᵉ


-- | Multi-step reduction for EC coercion sequences.
infix 3 _⊢ᵉ̅_—↠_

data _⊢ᵉ̅_—↠_ (Θ : SubCtx) : ECCoercionSeq → ECCoercionSeq → Set where

  ↠-refl : ∀ {c̅ᵉ}
      ------------------
    → Θ ⊢ᵉ̅ c̅ᵉ —↠ c̅ᵉ

  ↠-step : ∀ {c̅ᵉ d̅ᵉ e̅ᵉ}
    → Θ ⊢ᵉ̅ c̅ᵉ —→ d̅ᵉ
    → Θ ⊢ᵉ̅ d̅ᵉ —↠ e̅ᵉ
      ------------------
    → Θ ⊢ᵉ̅ c̅ᵉ —↠ e̅ᵉ
