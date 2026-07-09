module Theories.CoercionEquationalTheory.EC.Semantics where

open import Relation.Nullary using (¬_)

open import Theories.CoercionEquationalTheory.EC.SyntaxAndTyping


-- | Frames for EC coercion reduction
data CFrameᵉ : Set where
  □⨾_ : ECCoercion → CFrameᵉ
  _⨾□ : ECCoercion → CFrameᵉ

cplugᵉ : ECCoercion → CFrameᵉ → ECCoercion
cplugᵉ cᵉ (□⨾ dᵉ) = cᵉ ⨾ dᵉ
cplugᵉ dᵉ (cᵉ ⨾□) = cᵉ ⨾ dᵉ

-- | Frames that propagate error coercions
data CFrameErrᵉ : Set where
  □⨾_ : ECCoercion → CFrameErrᵉ
  _!⨾□ : EC → CFrameErrᵉ

cplug-errᵉ : ECCoercion → CFrameErrᵉ → ECCoercion
cplug-errᵉ cᵉ (□⨾ dᵉ) = cᵉ ⨾ dᵉ
cplug-errᵉ dᵉ (e !⨾□) = e ！ ⨾ dᵉ  -- so that α ! ; β ?² ; ⊥¹  —→* ⊥²

infix 6 ⊢ᵉ_≡_

data ⊢ᵉ_≡_ : ECCoercion → ECCoercion → Set where
  refl  : ∀ {c} → ⊢ᵉ c ≡ c
  sym   : ∀ {c d} → ⊢ᵉ c ≡ d → ⊢ᵉ d ≡ c
  trans : ∀ {c₁ c₂ c₃} → ⊢ᵉ c₁ ≡ c₂ → ⊢ᵉ c₂ ≡ c₃ → ⊢ᵉ c₁ ≡ c₃
  assoc : ∀ {c d e} → ⊢ᵉ (c ⨾ d) ⨾ e ≡ c ⨾ (d ⨾ e)
  cong  : ∀ {c d f} → ⊢ᵉ c ≡ d → ⊢ᵉ cplugᵉ c f ≡ cplugᵉ d f

infix 2 _⊢ᵉ_⟶_
infix 2 _⊢ᵉ_⟼_

data _⊢ᵉ_⟶_ : SubCtx → ECCoercion → ECCoercion → Set where

  inj-proj : ∀ {Θ e e′ ℓ}
    → Θ ⊢ᵉ e <: e′
      ------------------------------------------------
    → Θ ⊢ᵉ (e ！) ⨾ (e′ ？ ℓ) ⟶ (ec e ↑ ec e′)

  inj-proj-err : ∀ {Θ e e′ ℓ}
    → ¬ (Θ ⊢ᵉ e <: e′)
      ------------------------------------
    → Θ ⊢ᵉ (e ！) ⨾ (e′ ？ ℓ) ⟶ ⊥ ℓ

  seq : ∀ {Θ ê₁ ê₂ ê₃}
    → Θ ⊢ᵉ ê₁ <:⋆ ê₂
    → Θ ⊢ᵉ ê₂ <:⋆ ê₃
      ------------------------------------------------
    → Θ ⊢ᵉ (ê₁ ↑ ê₂) ⨾ (ê₂ ↑ ê₃) ⟶ (ê₁ ↑ ê₃)

  err : ∀ {Θ c ℓ}
      ------------------------
    → Θ ⊢ᵉ c ⨾ ⊥ ℓ ⟶ ⊥ ℓ

  ξ : ∀ {Θ c d f}
    → Θ ⊢ᵉ c ⟶ d
      ------------------------------------
    → Θ ⊢ᵉ cplugᵉ c f ⟶ cplugᵉ d f

  ξ-err : ∀ {Θ f ℓ}
      ------------------------------------
    → Θ ⊢ᵉ cplug-errᵉ (⊥ ℓ) f ⟶ ⊥ ℓ

data _⊢ᵉ_⟼_ : SubCtx → ECCoercion → ECCoercion → Set where

  red : ∀ {Θ c₁ c₁′ c₂ c₂′}
    → ⊢ᵉ c₁ ≡ c₁′
    → Θ ⊢ᵉ c₁′ ⟶ c₂′
    → ⊢ᵉ c₂′ ≡ c₂
      ---------------------------
    → Θ ⊢ᵉ c₁ ⟼ c₂
