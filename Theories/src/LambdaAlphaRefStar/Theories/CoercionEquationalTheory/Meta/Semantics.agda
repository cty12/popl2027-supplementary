module LambdaAlphaRefStar.Theories.CoercionEquationalTheory.Meta.Semantics where

open import Data.Product using (∃-syntax; _×_) renaming (_,_ to ⟨_,_⟩)
open import Relation.Binary.PropositionalEquality using (_≢_)
open import Relation.Nullary using (¬_)

open import LambdaAlphaRefStar.Theories.CoercionEquationalTheory.EC.SyntaxAndTyping
  using (ECCoercion)
open import LambdaAlphaRefStar.Theories.CoercionEquationalTheory.Code.SyntaxAndTyping
  using (OCoercion)
import LambdaAlphaRefStar.Theories.CoercionEquationalTheory.EC.SyntaxAndTyping
  as EC
import LambdaAlphaRefStar.Theories.CoercionEquationalTheory.Code.SyntaxAndTyping
  as OC
open import LambdaAlphaRefStar.Theories.CoercionEquationalTheory.Meta.SyntaxAndTyping
open import LambdaAlphaRefStar.Theories.CoercionEquationalTheory.EC.Semantics
open import LambdaAlphaRefStar.Theories.CoercionEquationalTheory.Code.Semantics


-- | Frames for meta coercions.
data CFrameᵐ : Set where
  □⨾_ : MCoercion → CFrameᵐ
  _⨾□ : MCoercion → CFrameᵐ
  □⇒_ : MCoercion → CFrameᵐ
  _⇒□ : MCoercion → CFrameᵐ
  ref□_ : MCoercion → CFrameᵐ
  ref_□ : MCoercion → CFrameᵐ

cplugᵐ : MCoercion → CFrameᵐ → MCoercion
cplugᵐ c (□⨾ d) = c ⨾ d
cplugᵐ d (c ⨾□) = c ⨾ d
cplugᵐ c (□⇒ d) = c ⇒ d
cplugᵐ d (c ⇒□) = c ⇒ d
cplugᵐ c (ref□ d) = Ref c , d
cplugᵐ d (ref c □) = Ref c , d

-- | Frames that propagate meta-coercion errors.
data CFrameErrᵐ : Set where
  □⨾_ : MCoercion → CFrameErrᵐ
  _⨾□ : MCoercion → CFrameErrᵐ

cplug-errᵐ : MCoercion → CFrameErrᵐ → MCoercion
cplug-errᵐ c (□⨾ d) = c ⨾ d
cplug-errᵐ d (c ⨾□) = c ⨾ d


infix 6 ⊢ᵐ_≡_

data ⊢ᵐ_≡_ : MCoercion → MCoercion → Set where
  refl  : ∀ {c} → ⊢ᵐ c ≡ c
  sym   : ∀ {c d} → ⊢ᵐ c ≡ d → ⊢ᵐ d ≡ c
  trans : ∀ {c d e} → ⊢ᵐ c ≡ d → ⊢ᵐ d ≡ e → ⊢ᵐ c ≡ e
  assoc : ∀ {c d e} → ⊢ᵐ (c ⨾ d) ⨾ e ≡ c ⨾ (d ⨾ e)
  ‶_″_  : ∀ {cᵒ dᵒ : OCoercion} {cᵉ dᵉ : ECCoercion}
    → ⊢ᵒ cᵒ ≡ dᵒ
    → ⊢ᵉ cᵉ ≡ dᵉ
      ---------------------------------------
    → ⊢ᵐ ‶ cᵒ ″ cᵉ ≡ ‶ dᵒ ″ dᵉ
  cong  : ∀ {c d f} → ⊢ᵐ c ≡ d → ⊢ᵐ cplugᵐ c f ≡ cplugᵐ d f

infix 2 _⊢ᵐ_⟶_
infix 2 _⊢ᵐ_⟼_

data _⊢ᵐ_⟶_ : SubCtx → MCoercion → MCoercion → Set where

  inj-proj : ∀ {Θ G ℓ} {g h : Ground G}
      -------------------------------
    → Θ ⊢ᵐ ((G ！) g) ⨾ ((G ？ ℓ) h) ⟶ id

  inj-proj-err : ∀ {Θ G H ℓ} {g : Ground G} {h : Ground H}
    → G ≢ H
      -------------------------------
    → Θ ⊢ᵐ ((G ！) g) ⨾ ((H ？ ℓ) h) ⟶ ⊥ ℓ

  seq-fun : ∀ {Θ c₁ c₂ d₁ d₂}
      ---------------------------------------------------------------
    → Θ ⊢ᵐ ((c₁ ⇒ c₂) ⨾ (d₁ ⇒ d₂)) ⟶ ((d₁ ⨾ c₁) ⇒ (c₂ ⨾ d₂))

  seq-code : ∀ {Θ} {cᵒ dᵒ : OCoercion} {cᵉ dᵉ : ECCoercion}
      ---------------------------------------------------------------------
    → Θ ⊢ᵐ (‶ cᵒ ″ cᵉ) ⨾ (‶ dᵒ ″ dᵉ) ⟶ ‶ cᵒ OC.⨾ dᵒ ″ (cᵉ EC.⨾ dᵉ)

  seq-ref : ∀ {Θ c₁ c₂ d₁ d₂}
      ------------------------------------------------------------------
    → Θ ⊢ᵐ (Ref c₁ , c₂) ⨾ (Ref d₁ , d₂) ⟶ Ref (d₁ ⨾ c₁) , (c₂ ⨾ d₂)

  seq-forall : ∀ {Θ c d}
      ---------------------------------------------------
    → Θ ⊢ᵐ (∀̇ c) ⨾ (∀̇ d) ⟶ ∀̇ (c ⨾ d)

  seq-sub : ∀ {Θ c d e₁ e₂}
      ------------------------------------------------------------------
    → Θ ⊢ᵐ (e₁ <: e₂ => c) ⨾ (e₁ <: e₂ => d) ⟶ (e₁ <: e₂ => (c ⨾ d))

  id-left : ∀ {Θ c}
      --------------------
    → Θ ⊢ᵐ id ⨾ c ⟶ c

  id-right : ∀ {Θ c}
      --------------------
    → Θ ⊢ᵐ c ⨾ id ⟶ c

  ξ : ∀ {Θ c d f}
    → Θ ⊢ᵐ c ⟶ d
      ---------------------------------
    → Θ ⊢ᵐ cplugᵐ c f ⟶ cplugᵐ d f

  ξ-forall : ∀ {Θ c d}
    → ⇑ᵉ-subctx Θ ⊢ᵐ c ⟶ d
      ----------------------------
    → Θ ⊢ᵐ ∀̇ c ⟶ ∀̇ d

  ξ-sub : ∀ {Θ e₁ e₂ c d}
    → Θ , e₁ <: e₂ ⊢ᵐ c ⟶ d
      ------------------------------------------
    → Θ ⊢ᵐ (e₁ <: e₂ => c) ⟶ (e₁ <: e₂ => d)

  ξ-err : ∀ {Θ f ℓ}
      ------------------------------------
    → Θ ⊢ᵐ cplug-errᵐ (⊥ ℓ) f ⟶ ⊥ ℓ

  ξ-code-o : ∀ {Θ} {cᵒ dᵒ : OCoercion} {cᵉ : ECCoercion}
    → ⊢ᵒ cᵒ ⟶ dᵒ
      ------------------------------------
    → Θ ⊢ᵐ ‶ cᵒ ″ cᵉ ⟶ ‶ dᵒ ″ cᵉ

  ξ-code-ec : ∀ {Θ} {cᵒ : OCoercion} {cᵉ dᵉ : ECCoercion}
    → Θ ⊢ᵉ cᵉ ⟶ dᵉ
      ------------------------------------
    → Θ ⊢ᵐ ‶ cᵒ ″ cᵉ ⟶ ‶ cᵒ ″ dᵉ

  ξ-code-o-err : ∀ {Θ} {cᵉ : ECCoercion} {ℓ}
      ---------------------------------------------
    → Θ ⊢ᵐ ‶ OC.⊥ ℓ ″ cᵉ ⟶ ⊥ ℓ

  ξ-code-ec-err : ∀ {Θ} {cᵒ : OCoercion} {ℓ}
      ---------------------------------------------
    → Θ ⊢ᵐ ‶ cᵒ ″ (EC.⊥ ℓ) ⟶ ⊥ ℓ

data _⊢ᵐ_⟼_ : SubCtx → MCoercion → MCoercion → Set where

  red : ∀ {Θ c₁ c₁′ c₂ c₂′}
    → ⊢ᵐ c₁ ≡ c₁′
    → Θ ⊢ᵐ c₁′ ⟶ c₂′
    → ⊢ᵐ c₂′ ≡ c₂
      ------------------------------
    → Θ ⊢ᵐ c₁ ⟼ c₂

eq-red : ∀ {Θ c₁ c₂}
    → Θ ⊢ᵐ c₁ ⟶ c₂
      ------------------------------
    → Θ ⊢ᵐ c₁ ⟼ c₂
eq-red r = red refl r refl

Irred : ∀ {Θ} → MCoercion → Set
Irred {Θ} c = ¬ (∃[ d ] (Θ ⊢ᵐ c ⟼ d))

Inert : MCoercion → Set
Inert c = (∀ Θ → Irred {Θ} c) × (∀ ℓ → c ≢ ⊥ ℓ)
