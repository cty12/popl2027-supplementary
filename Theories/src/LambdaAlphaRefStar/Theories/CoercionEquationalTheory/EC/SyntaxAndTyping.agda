module LambdaAlphaRefStar.Theories.CoercionEquationalTheory.EC.SyntaxAndTyping where

open import LambdaAlphaRefStar.Theories.EnvClassifiers public
open import LambdaAlphaRefStar.Theories.BlameLabels     public

infix 9 _！
infix 9 _？_
infixr 8 _⨾_
infix 8 _↑_
infix 8 ⊥_

-- | Coercions between ECs (cᵉ, dᵉ).
data ECCoercion : Set where
  _！  : EC → ECCoercion
  _？_ : EC → BlameLabel → ECCoercion
  _⨾_ : ECCoercion → ECCoercion → ECCoercion
  _↑_ : EC⋆ → EC⋆ → ECCoercion
  ⊥_  : BlameLabel → ECCoercion


-- | EC coercion typing.
infix 4 _;_⊢ᵉ_⦂_⇒_

data _;_⊢ᵉ_⦂_⇒_ : ECCtx → SubCtx → ECCoercion → EC⋆ → EC⋆ → Set where

  ⊢injᵉ : ∀ {Δ Θ}
    → (e : EC)
    → Δ ⊢ᵉ e
      ---------------------------------------
    → Δ ; Θ ⊢ᵉ e ！ ⦂ ec e ⇒ ⋆

  ⊢projᵉ : ∀ {Δ Θ}
    → (e : EC)
    → Δ ⊢ᵉ e
    → (ℓ : BlameLabel)
      ---------------------------------------
    → Δ ; Θ ⊢ᵉ e ？ ℓ ⦂ ⋆ ⇒ ec e

  ⊢seqᵉ : ∀ {Δ Θ ê₁ ê₂ ê₃ c d}
    → Δ ; Θ ⊢ᵉ c ⦂ ê₁ ⇒ ê₂
    → Δ ; Θ ⊢ᵉ d ⦂ ê₂ ⇒ ê₃
      ---------------------------------------
    → Δ ; Θ ⊢ᵉ c ⨾ d ⦂ ê₁ ⇒ ê₃

  ⊢subᵉ : ∀ {Δ Θ ê₁ ê₂}
    → Δ ⊢ᵉ⋆ ê₁
    → Δ ⊢ᵉ⋆ ê₂
    → Θ ⊢ᵉ ê₁ <:⋆ ê₂
      ---------------------------------------
    → Δ ; Θ ⊢ᵉ ê₁ ↑ ê₂ ⦂ ê₁ ⇒ ê₂

  ⊢errᵉ : ∀ {Δ Θ ê₁ ê₂}
    → Δ ⊢ᵉ⋆ ê₁
    → Δ ⊢ᵉ⋆ ê₂
    → (ℓ : BlameLabel)
      ---------------------------------------
    → Δ ; Θ ⊢ᵉ ⊥ ℓ ⦂ ê₁ ⇒ ê₂


wf-domᵉ : ∀ {Δ Θ c ê₁ ê₂}
  → Δ ; Θ ⊢ᵉ c ⦂ ê₁ ⇒ ê₂
    -----------------------
  → Δ ⊢ᵉ⋆ ê₁
wf-domᵉ (⊢injᵉ e ⊢e) = wf-ec ⊢e
wf-domᵉ (⊢projᵉ e ⊢e ℓ) = wf-⋆
wf-domᵉ (⊢seqᵉ ⊢c ⊢d) = wf-domᵉ ⊢c
wf-domᵉ (⊢subᵉ ⊢ê₁ ⊢ê₂ ê₁<:ê₂) = ⊢ê₁
wf-domᵉ (⊢errᵉ ⊢ê₁ ⊢ê₂ ℓ) = ⊢ê₁

wf-codᵉ : ∀ {Δ Θ c ê₁ ê₂}
  → Δ ; Θ ⊢ᵉ c ⦂ ê₁ ⇒ ê₂
    -----------------------
  → Δ ⊢ᵉ⋆ ê₂
wf-codᵉ (⊢injᵉ e ⊢e) = wf-⋆
wf-codᵉ (⊢projᵉ e ⊢e ℓ) = wf-ec ⊢e
wf-codᵉ (⊢seqᵉ ⊢c ⊢d) = wf-codᵉ ⊢d
wf-codᵉ (⊢subᵉ ⊢ê₁ ⊢ê₂ ê₁<:ê₂) = ⊢ê₂
wf-codᵉ (⊢errᵉ ⊢ê₁ ⊢ê₂ ℓ) = ⊢ê₂
