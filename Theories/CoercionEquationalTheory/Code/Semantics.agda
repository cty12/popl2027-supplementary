module Theories.CoercionEquationalTheory.Code.Semantics where

open import Relation.Binary.PropositionalEquality using (_≢_)

open import Theories.CoercionEquationalTheory.Code.SyntaxAndTyping


-- | Frames for raw object coercions.
data CFrameᵒ : Set where
  □⨾_ : OCoercion → CFrameᵒ
  _⨾□ : OCoercion → CFrameᵒ
  □⇒_ : OCoercion → CFrameᵒ
  _⇒□ : OCoercion → CFrameᵒ

cplugᵒ : OCoercion → CFrameᵒ → OCoercion
cplugᵒ cᵒ (□⨾ dᵒ) = cᵒ ⨾ dᵒ
cplugᵒ dᵒ (cᵒ ⨾□) = cᵒ ⨾ dᵒ
cplugᵒ cᵒ (□⇒ dᵒ) = cᵒ ⇒ dᵒ
cplugᵒ dᵒ (cᵒ ⇒□) = cᵒ ⇒ dᵒ

-- | Frames that propagate object-coercion errors.
data CFrameErrᵒ : Set where
  □⨾_ : OCoercion → CFrameErrᵒ
  _!⨾□_ : (Gᵒ : OType⋆) → OGround Gᵒ → CFrameErrᵒ
  -- | Different from meta coercions, the code coercion reduction
  --   is eager wrt function type
  □⇒_ : OCoercion → CFrameErrᵒ
  _⇒□ : OCoercion → CFrameErrᵒ

cplug-errᵒ : OCoercion → CFrameErrᵒ → OCoercion
cplug-errᵒ cᵒ (□⨾ dᵒ) = cᵒ ⨾ dᵒ
cplug-errᵒ dᵒ (Gᵒ !⨾□ g) = ((Gᵒ ！) g) ⨾ dᵒ
cplug-errᵒ cᵒ (□⇒ dᵒ) = cᵒ ⇒ dᵒ
cplug-errᵒ dᵒ (cᵒ ⇒□) = cᵒ ⇒ dᵒ

infix 6 ⊢ᵒ_≡_

data ⊢ᵒ_≡_ : OCoercion → OCoercion → Set where
  refl  : ∀ {c} → ⊢ᵒ c ≡ c
  sym   : ∀ {c d} → ⊢ᵒ c ≡ d → ⊢ᵒ d ≡ c
  trans : ∀ {c₁ c₂ c₃} → ⊢ᵒ c₁ ≡ c₂ → ⊢ᵒ c₂ ≡ c₃ → ⊢ᵒ c₁ ≡ c₃
  assoc : ∀ {c d e} → ⊢ᵒ (c ⨾ d) ⨾ e ≡ c ⨾ (d ⨾ e)
  cong  : ∀ {c d f} → ⊢ᵒ c ≡ d → ⊢ᵒ cplugᵒ c f ≡ cplugᵒ d f

infix 2 ⊢ᵒ_⟶_
infix 2 ⊢ᵒ_⟼_

data ⊢ᵒ_⟶_ : OCoercion → OCoercion → Set where
  inj-proj : ∀ {Gᵒ ℓ} {g h : OGround Gᵒ}
      -------------------------------
    → ⊢ᵒ ((Gᵒ ！) g) ⨾ ((Gᵒ ？ ℓ) h) ⟶ id

  inj-proj-err : ∀ {Gᵒ Hᵒ ℓ} {g : OGround Gᵒ} {h : OGround Hᵒ}
    → Gᵒ ≢ Hᵒ
      -------------------------------
    → ⊢ᵒ ((Gᵒ ！) g) ⨾ ((Hᵒ ？ ℓ) h) ⟶ ⊥ ℓ

  seq-fun : ∀ {c₁ c₂ d₁ d₂}
      ---------------------------------------------------------------
    → ⊢ᵒ (c₁ ⇒ c₂) ⨾ (d₁ ⇒ d₂) ⟶ (d₁ ⨾ c₁) ⇒ (c₂ ⨾ d₂)

  id-left : ∀ {c}
      --------------------
    → ⊢ᵒ id ⨾ c ⟶ c

  id-right : ∀ {c}
      --------------------
    → ⊢ᵒ c ⨾ id ⟶ c

  id-fun :
      --------------------
      ⊢ᵒ (id ⇒ id) ⟶ id

  ξ : ∀ {c d f}
    → ⊢ᵒ c ⟶ d
      ---------------------------------------
    → ⊢ᵒ cplugᵒ c f ⟶ cplugᵒ d f

  ξ-err : ∀ {f ℓ}
      ---------------------------------------------------
    → ⊢ᵒ cplug-errᵒ (⊥ ℓ) f ⟶ ⊥ ℓ

data ⊢ᵒ_⟼_ : OCoercion → OCoercion → Set where

  red : ∀ {c₁ c₁′ c₂ c₂′}
    → ⊢ᵒ c₁ ≡ c₁′
    → ⊢ᵒ c₁′ ⟶ c₂′
    → ⊢ᵒ c₂′ ≡ c₂
      ------------------------------
    → ⊢ᵒ c₁ ⟼ c₂
