module Theories.CoercionSequences.Meta.Definition where

open import Data.List using (List; []; _∷_; _++_; [_])
open import Data.Product using (∃-syntax; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_)
open import Relation.Nullary using (¬_)

import Theories.CoercionSequences.Code.Definition as OC
import Theories.CoercionSequences.EC.Definition as ECS
open import Theories.EnvClassifiers public
open import Theories.MetaTypes public
open import Theories.BlameLabels public


infix 9 _！
infix 9 _？_
infixr 6 _⇒_
infix 8 ⊥_
infixr 7 _;_


-- | Single meta coercions (cᵐ, dᵐ).
data MSingleCoercion : Set where
  _！      : (G : MType) → Ground G → MSingleCoercion
  _？_     : (G : MType) → BlameLabel → Ground G → MSingleCoercion
  _⇒_      : List MSingleCoercion → List MSingleCoercion → MSingleCoercion
  ‶_″_     : OC.OCoercionSeq → ECS.ECCoercionSeq → MSingleCoercion
  Ref_,_   : List MSingleCoercion → List MSingleCoercion → MSingleCoercion
  ∀̇_       : List MSingleCoercion → MSingleCoercion
  _<:_=>_  : EC → EC → List MSingleCoercion → MSingleCoercion
  ⊥_       : BlameLabel → MSingleCoercion


-- | Meta coercion sequences (c̅ᵐ, d̅ᵐ).
MCoercionSeq = List MSingleCoercion

-- | Coercion sequences are ordinary lists.  We use semicolon for cons to
--   match the paper notation, and Data.List.[_] for singleton sequences.
pattern _;_ cᵐ c̅ᵐ = cᵐ ∷ c̅ᵐ


-- | Singleton blame coercions.
Blame : MSingleCoercion → Set
Blame cᵐ = ∃[ ℓ ] cᵐ ≡ ⊥ ℓ

-- | Singleton projection coercions.
Proj : MSingleCoercion → Set
Proj cᵐ = ∃[ G ] ∃[ ℓ ] ∃[ g ] cᵐ ≡ (G ？ ℓ) g

-- | Singleton identity coercion sequences.
IdSeq : MCoercionSeq → Set
IdSeq c̅ᵐ = c̅ᵐ ≡ []

-- | Singleton blame coercion sequences.
BlameSeq : MCoercionSeq → Set
BlameSeq c̅ᵐ = ∃[ ℓ ] c̅ᵐ ≡ [ ⊥ ℓ ]

-- | Meta coercion typing.
infix 4 _;_⊢ᵐ_⦂_⇒_
infix 4 _;_⊢ᵐ̅_⦂_⇒_

mutual

  data _;_⊢ᵐ_⦂_⇒_ : ECCtx → SubCtx → MSingleCoercion → MType → MType → Set where

    ⊢! : ∀ {Δ Θ G}
      → Δ ⊢ᵐᵗ G
      → (g : Ground G)
        ---------------------------------
      → Δ ; Θ ⊢ᵐ (G ！) g ⦂ G ⇒ ⋆

    ⊢? : ∀ {Δ Θ G}
      → Δ ⊢ᵐᵗ G
      → (ℓ : BlameLabel)
      → (g : Ground G)
        ---------------------------------
      → Δ ; Θ ⊢ᵐ (G ？ ℓ) g ⦂ ⋆ ⇒ G

    ⊢fun : ∀ {Δ Θ A B C D c̅ᵐ d̅ᵐ}
      → Δ ; Θ ⊢ᵐ̅ c̅ᵐ ⦂ C ⇒ A
      → Δ ; Θ ⊢ᵐ̅ d̅ᵐ ⦂ B ⇒ D
        ------------------------------------------------
      → Δ ; Θ ⊢ᵐ c̅ᵐ ⇒ d̅ᵐ ⦂ (A ⇒ B) ⇒ (C ⇒ D)

    ⊢code : ∀ {Δ Θ C₁ C₂ ê₁ ê₂ c̅ᵒ c̅ᵉ}
      →        OC.⊢ᵒ̅ c̅ᵒ ⦂ C₁ ⇒ C₂
      → Δ ECS.; Θ ⊢ᵉ̅ c̅ᵉ ⦂ ê₁ ⇒ ê₂
        ------------------------------------------------------
      → Δ ; Θ ⊢ᵐ ‶ c̅ᵒ ″ c̅ᵉ ⦂ (‶ C₁ ″ ê₁) ⇒ (‶ C₂ ″ ê₂)

    ⊢ref : ∀ {Δ Θ A B c̅ᵐ d̅ᵐ}
      → Δ ; Θ ⊢ᵐ̅ c̅ᵐ ⦂ B ⇒ A
      → Δ ; Θ ⊢ᵐ̅ d̅ᵐ ⦂ A ⇒ B
        ---------------------------------------------
      → Δ ; Θ ⊢ᵐ Ref c̅ᵐ , d̅ᵐ ⦂ (Ref A) ⇒ (Ref B)

    ⊢forall : ∀ {Δ Θ A B c̅ᵐ}
      → Δ ,α ; ⇑ᵉ-subctx Θ ⊢ᵐ̅ c̅ᵐ ⦂ A ⇒ B
        ---------------------------------------
      → Δ ; Θ ⊢ᵐ ∀̇ c̅ᵐ ⦂ (∀̇ A) ⇒ (∀̇ B)

    ⊢sub : ∀ {Δ Θ A B e₁ e₂ c̅ᵐ}
      → Δ ⊢ᵉ e₁
      → Δ ⊢ᵉ e₂
      → Δ ; Θ , e₁ <: e₂ ⊢ᵐ̅ c̅ᵐ ⦂ A ⇒ B
        ------------------------------------------------------------------
      → Δ ; Θ ⊢ᵐ e₁ <: e₂ => c̅ᵐ ⦂ (e₁ <: e₂ => A) ⇒ (e₁ <: e₂ => B)

    ⊢⊥ : ∀ {Δ Θ A B}
      → Δ ⊢ᵐᵗ A
      → Δ ⊢ᵐᵗ B
      → (ℓ : BlameLabel)
        ---------------------------
      → Δ ; Θ ⊢ᵐ ⊥ ℓ ⦂ A ⇒ B

  data _;_⊢ᵐ̅_⦂_⇒_ : ECCtx → SubCtx → MCoercionSeq → MType → MType → Set where

    ⊢[] : ∀ {Δ Θ A}
      → Δ ⊢ᵐᵗ A
        ------------------------
      → Δ ; Θ ⊢ᵐ̅ [] ⦂ A ⇒ A

    ⊢; : ∀ {Δ Θ A B C cᵐ c̅ᵐ}
      → Δ ; Θ ⊢ᵐ cᵐ ⦂ A ⇒ B
      → Δ ; Θ ⊢ᵐ̅ c̅ᵐ ⦂ B ⇒ C
        ------------------------------
      → Δ ; Θ ⊢ᵐ̅ cᵐ ; c̅ᵐ ⦂ A ⇒ C


-- | Irreducible adjacent pairs of single meta coercions.
data IrredPair : MSingleCoercion → MSingleCoercion → Set where

  irred-?! : ∀ {G ℓ} {g h : Ground G}
      ---------------------------------------
    → IrredPair ((G ？ ℓ) g) ((G ！) h)

  irred-?⊥ : ∀ {G ℓ ℓ′} {g : Ground G}
      ---------------------------------
    → IrredPair ((G ？ ℓ) g) (⊥ ℓ′)

  irred-?fun : ∀ {ℓ c̅ᵐ₁ c̅ᵐ₂}
      ---------------------------------------------------
    → IrredPair (((⋆ ⇒ ⋆) ？ ℓ) gfun) (c̅ᵐ₁ ⇒ c̅ᵐ₂)

  irred-fun! : ∀ {c̅ᵐ₁ c̅ᵐ₂}
      ------------------------------------------------
    → IrredPair (c̅ᵐ₁ ⇒ c̅ᵐ₂) (((⋆ ⇒ ⋆) ！) gfun)

  irred-?code : ∀ {ℓ c̅ᵒ c̅ᵉ}
      ------------------------------------------------------
    → IrredPair (((‶ OC.⋆ ″ ⋆) ？ ℓ) gcode) (‶ c̅ᵒ ″ c̅ᵉ)

  irred-code! : ∀ {c̅ᵒ c̅ᵉ}
      ------------------------------------------------------
    → IrredPair (‶ c̅ᵒ ″ c̅ᵉ) (((‶ OC.⋆ ″ ⋆) ！) gcode)

  irred-?ref : ∀ {ℓ c̅ᵐ₁ c̅ᵐ₂}
      ---------------------------------------------------
    → IrredPair (((Ref ⋆) ？ ℓ) gref) (Ref c̅ᵐ₁ , c̅ᵐ₂)

  irred-ref! : ∀ {c̅ᵐ₁ c̅ᵐ₂}
      ---------------------------------------------------
    → IrredPair (Ref c̅ᵐ₁ , c̅ᵐ₂) (((Ref ⋆) ！) gref)

  irred-?∀ : ∀ {ℓ c̅ᵐ}
      ---------------------------------------------
    → IrredPair (((∀̇ ⋆) ？ ℓ) gforall) (∀̇ c̅ᵐ)

  irred-∀! : ∀ {c̅ᵐ}
      ------------------------------------------
    → IrredPair (∀̇ c̅ᵐ) (((∀̇ ⋆) ！) gforall)

  irred-?sub : ∀ {e₁ e₂ ℓ c̅ᵐ}
      ------------------------------------------------------------
    → IrredPair (((e₁ <: e₂ => ⋆) ？ ℓ) gsub) (e₁ <: e₂ => c̅ᵐ)

  irred-sub! : ∀ {e₁ e₂ c̅ᵐ}
      ------------------------------------------------------------
    → IrredPair (e₁ <: e₂ => c̅ᵐ) (((e₁ <: e₂ => ⋆) ！) gsub)


-- | Normal forms for single meta coercions and sequences.
mutual

  data SingleNF : MSingleCoercion → Set where

    nf-! : ∀ {G} {g : Ground G}
        ---------------------------
      → SingleNF ((G ！) g)

    nf-? : ∀ {G ℓ} {g : Ground G}
        ---------------------------
      → SingleNF ((G ？ ℓ) g)

    nf-⊥ : ∀ {ℓ}
        ------------------
      → SingleNF (⊥ ℓ)

    nf-fun : ∀ {c̅ᵐ₁ c̅ᵐ₂}
      → NF c̅ᵐ₁
      → NF c̅ᵐ₂
      → ¬ (IdSeq c̅ᵐ₁ × IdSeq c̅ᵐ₂)
        ---------------------------
      → SingleNF (c̅ᵐ₁ ⇒ c̅ᵐ₂)

    nf-code : ∀ {c̅ᵒ c̅ᵉ}
      →  OC.NF c̅ᵒ
      → ECS.NF c̅ᵉ
      → ¬ (OC.IdSeq c̅ᵒ × ECS.IdSeq c̅ᵉ)
      → ¬  (OC.BlameSeq c̅ᵒ)
      → ¬ (ECS.BlameSeq c̅ᵉ)
        ------------------------------
      → SingleNF (‶ c̅ᵒ ″ c̅ᵉ)

    nf-ref : ∀ {c̅ᵐ₁ c̅ᵐ₂}
      → NF c̅ᵐ₁
      → NF c̅ᵐ₂
      → ¬ (IdSeq c̅ᵐ₁ × IdSeq c̅ᵐ₂)
        ------------------------------
      → SingleNF (Ref c̅ᵐ₁ , c̅ᵐ₂)

    nf-forall : ∀ {c̅ᵐ}
      → NF c̅ᵐ
      → ¬ (IdSeq c̅ᵐ)
        ---------------------
      → SingleNF (∀̇ c̅ᵐ)

    nf-sub : ∀ {e₁ e₂ c̅ᵐ}
      → NF c̅ᵐ
      → ¬ (IdSeq c̅ᵐ)
        ------------------------------
      → SingleNF (e₁ <: e₂ => c̅ᵐ)

  data NF : MCoercionSeq → Set where

    nf-empty :
        ---------
        NF []

    nf-singleton : ∀ {cᵐ}
      → SingleNF cᵐ
        ---------------
      → NF [ cᵐ ]

    nf-step : ∀ {cᵐ₁ cᵐ₂ c̅ᵐ}
      → SingleNF cᵐ₁
      → IrredPair cᵐ₁ cᵐ₂
      → NF (cᵐ₂ ; c̅ᵐ)
        ------------------------
      → NF (cᵐ₁ ; cᵐ₂ ; c̅ᵐ)


-- | Inert meta coercions are value-forming: normal, non-identity, non-blame.
Inert : MCoercionSeq → Set
Inert c̅ᵐ = NF c̅ᵐ × ¬ IdSeq c̅ᵐ × ¬ BlameSeq c̅ᵐ


-- | Adjacent-pair reduction for single meta coercions.
infix 3 _⊢ᵐ_;_⟶_

data _⊢ᵐ_;_⟶_ : SubCtx → MSingleCoercion → MSingleCoercion → MCoercionSeq → Set where

  collapse : ∀ {Θ G ℓ} {g h : Ground G}
      ---------------------------------------------
    → Θ ⊢ᵐ ((G ！) g) ; ((G ？ ℓ) h) ⟶ []

  collide : ∀ {Θ G H ℓ} {g : Ground G} {h : Ground H}
    → G ≢ H
      ---------------------------------------------
    → Θ ⊢ᵐ ((G ！) g) ; ((H ？ ℓ) h) ⟶ [ ⊥ ℓ ]

  seq-fun : ∀ {Θ c̅ᵐ₁ c̅ᵐ₂ d̅ᵐ₁ d̅ᵐ₂}
      ---------------------------------------------------------------------------
    → Θ ⊢ᵐ (c̅ᵐ₁ ⇒ c̅ᵐ₂) ; (d̅ᵐ₁ ⇒ d̅ᵐ₂) ⟶ [ (d̅ᵐ₁ ++ c̅ᵐ₁) ⇒ (c̅ᵐ₂ ++ d̅ᵐ₂) ]

  seq-ref : ∀ {Θ c̅ᵐ₁ c̅ᵐ₂ d̅ᵐ₁ d̅ᵐ₂}
      ------------------------------------------------------------------------------------
    → Θ ⊢ᵐ (Ref c̅ᵐ₁ , c̅ᵐ₂) ; (Ref d̅ᵐ₁ , d̅ᵐ₂) ⟶ [ Ref (d̅ᵐ₁ ++ c̅ᵐ₁) , (c̅ᵐ₂ ++ d̅ᵐ₂) ]

  seq-code : ∀ {Θ c̅ᵒ c̅ᵉ d̅ᵒ d̅ᵉ}
      ---------------------------------------------------------------------
    → Θ ⊢ᵐ (‶ c̅ᵒ ″ c̅ᵉ) ; (‶ d̅ᵒ ″ d̅ᵉ) ⟶ [ ‶ c̅ᵒ ++ d̅ᵒ ″ (c̅ᵉ ++ d̅ᵉ) ]

  seq-forall : ∀ {Θ c̅ᵐ d̅ᵐ}
      ------------------------------------------------
    → Θ ⊢ᵐ (∀̇ c̅ᵐ) ; (∀̇ d̅ᵐ) ⟶ [ ∀̇ (c̅ᵐ ++ d̅ᵐ) ]

  seq-sub : ∀ {Θ c̅ᵐ d̅ᵐ e₁ e₂}
      ------------------------------------------------------------------------------
    → Θ ⊢ᵐ (e₁ <: e₂ => c̅ᵐ) ; (e₁ <: e₂ => d̅ᵐ) ⟶ [ e₁ <: e₂ => (c̅ᵐ ++ d̅ᵐ) ]

  ⊥-left : ∀ {Θ ℓ cᵐ}
      ------------------------------
    → Θ ⊢ᵐ ⊥ ℓ ; cᵐ ⟶ [ ⊥ ℓ ]

  ⊥-right : ∀ {Θ cᵐ ℓ}
    → ¬ (Blame cᵐ)
    → ¬ (Proj cᵐ)
      ------------------------------
    → Θ ⊢ᵐ cᵐ ; ⊥ ℓ ⟶ [ ⊥ ℓ ]


-- | Reduction for single meta coercions and meta coercion sequences.
infix 3 _⊢ᵐ_—→_
infix 3 _⊢ᵐ̅_—→_

mutual

  data _⊢ᵐ_—→_ : SubCtx → MSingleCoercion → MCoercionSeq → Set where

    id-fun :
        ----------------------------------
      ∀ {Θ} → Θ ⊢ᵐ ([] ⇒ []) —→ []

    id-code :
        ----------------------------------
      ∀ {Θ} → Θ ⊢ᵐ ‶ [] ″ [] —→ []

    id-ref :
        ----------------------------------------
      ∀ {Θ} → Θ ⊢ᵐ Ref [] , [] —→ []

    id-forall :
        ----------------------------
      ∀ {Θ} → Θ ⊢ᵐ ∀̇ [] —→ []

    id-sub :
        ----------------------------------------
      ∀ {Θ e₁ e₂} → Θ ⊢ᵐ e₁ <: e₂ => [] —→ []

    ξ-fun-dom : ∀ {Θ c̅ᵐ₁ c̅ᵐ₂ d̅ᵐ₁}
      → Θ ⊢ᵐ̅ c̅ᵐ₁ —→ d̅ᵐ₁
        ---------------------------------------------
      → Θ ⊢ᵐ (c̅ᵐ₁ ⇒ c̅ᵐ₂) —→ [ d̅ᵐ₁ ⇒ c̅ᵐ₂ ]

    ξ-fun-cod : ∀ {Θ c̅ᵐ₁ c̅ᵐ₂ d̅ᵐ₂}
      → NF c̅ᵐ₁
      → Θ ⊢ᵐ̅ c̅ᵐ₂ —→ d̅ᵐ₂
        ---------------------------------------------
      → Θ ⊢ᵐ (c̅ᵐ₁ ⇒ c̅ᵐ₂) —→ [ c̅ᵐ₁ ⇒ d̅ᵐ₂ ]

    ξ-ref-in : ∀ {Θ c̅ᵐ₁ c̅ᵐ₂ d̅ᵐ₁}
      → Θ ⊢ᵐ̅ c̅ᵐ₁ —→ d̅ᵐ₁
        ------------------------------------------------
      → Θ ⊢ᵐ Ref c̅ᵐ₁ , c̅ᵐ₂ —→ [ Ref d̅ᵐ₁ , c̅ᵐ₂ ]

    ξ-ref-out : ∀ {Θ c̅ᵐ₁ c̅ᵐ₂ d̅ᵐ₂}
      → NF c̅ᵐ₁
      → Θ ⊢ᵐ̅ c̅ᵐ₂ —→ d̅ᵐ₂
        ------------------------------------------------
      → Θ ⊢ᵐ Ref c̅ᵐ₁ , c̅ᵐ₂ —→ [ Ref c̅ᵐ₁ , d̅ᵐ₂ ]

    ξ-forall : ∀ {Θ c̅ᵐ d̅ᵐ}
      → ⇑ᵉ-subctx Θ ⊢ᵐ̅ c̅ᵐ —→ d̅ᵐ
        ------------------------------------------
      → Θ ⊢ᵐ ∀̇ c̅ᵐ —→ [ ∀̇ d̅ᵐ ]

    ξ-sub : ∀ {Θ e₁ e₂ c̅ᵐ d̅ᵐ}
      → Θ , e₁ <: e₂ ⊢ᵐ̅ c̅ᵐ —→ d̅ᵐ
        ------------------------------------------------------
      → Θ ⊢ᵐ (e₁ <: e₂ => c̅ᵐ) —→ [ e₁ <: e₂ => d̅ᵐ ]

    ξ-code : ∀ {Θ c̅ᵒ d̅ᵒ c̅ᵉ}
      →    OC.⊢ᵒ̅ c̅ᵒ —→ d̅ᵒ
        ---------------------------------------
      → Θ ⊢ᵐ ‶ c̅ᵒ ″ c̅ᵉ —→ [ ‶ d̅ᵒ ″ c̅ᵉ ]

    ξ-code-ec : ∀ {Θ c̅ᵒ c̅ᵉ d̅ᵉ}
      → OC.NF c̅ᵒ
      → ¬ (OC.BlameSeq c̅ᵒ)
      → Θ ECS.⊢ᵉ̅ c̅ᵉ —→ d̅ᵉ
        ------------------------------------
      → Θ ⊢ᵐ ‶ c̅ᵒ ″ c̅ᵉ —→ [ ‶ c̅ᵒ ″ d̅ᵉ ]

    ξ-code-⊥ : ∀ {Θ c̅ᵉ ℓ}
        ---------------------------------------
      → Θ ⊢ᵐ ‶ [ OC.⊥ ℓ ] ″ c̅ᵉ —→ [ ⊥ ℓ ]

    ξ-code-ec-⊥ : ∀ {Θ c̅ᵒ ℓ}
      → OC.NF c̅ᵒ
      → ¬ (OC.BlameSeq c̅ᵒ)
        ---------------------------------------
      → Θ ⊢ᵐ ‶ c̅ᵒ ″ [ ECS.⊥ ℓ ] —→ [ ⊥ ℓ ]

  data _⊢ᵐ̅_—→_ : SubCtx → MCoercionSeq → MCoercionSeq → Set where

    reduce-head : ∀ {Θ cᵐ d̅ᵐ c̅ᵐ}
      → Θ ⊢ᵐ cᵐ —→ d̅ᵐ
        ------------------------------------
      → Θ ⊢ᵐ̅ (cᵐ ; c̅ᵐ) —→ (d̅ᵐ ++ c̅ᵐ)

    reduce-neighbors : ∀ {Θ cᵐ₁ cᵐ₂ d̅ᵐ c̅ᵐ}
      → SingleNF cᵐ₁
      → Θ ⊢ᵐ cᵐ₁ ; cᵐ₂ ⟶ d̅ᵐ
        ---------------------------------------------
      → Θ ⊢ᵐ̅ (cᵐ₁ ; cᵐ₂ ; c̅ᵐ) —→ (d̅ᵐ ++ c̅ᵐ)

    reduce-tail : ∀ {Θ cᵐ₁ cᵐ₂ c̅ᵐ d̅ᵐ}
      → SingleNF cᵐ₁
      → IrredPair cᵐ₁ cᵐ₂
      → Θ ⊢ᵐ̅ (cᵐ₂ ; c̅ᵐ) —→ d̅ᵐ
        ------------------------------------------------
      → Θ ⊢ᵐ̅ (cᵐ₁ ; cᵐ₂ ; c̅ᵐ) —→ (cᵐ₁ ; d̅ᵐ)


-- | Multi-step reduction for meta coercion sequences.
infix 3 _⊢ᵐ̅_—↠_

data _⊢ᵐ̅_—↠_ (Θ : SubCtx) : MCoercionSeq → MCoercionSeq → Set where

  ↠-refl : ∀ {c̅ᵐ}
      ------------------------
    → Θ ⊢ᵐ̅ c̅ᵐ —↠ c̅ᵐ

  ↠-step : ∀ {c̅ᵐ d̅ᵐ e̅ᵐ}
    → Θ ⊢ᵐ̅ c̅ᵐ —→ d̅ᵐ
    → Θ ⊢ᵐ̅ d̅ᵐ —↠ e̅ᵐ
      ---------------------------
    → Θ ⊢ᵐ̅ c̅ᵐ —↠ e̅ᵐ
