module LambdaAlphaRefStar.Theories.CoercionEquationalTheory.Code.SyntaxAndTyping where

open import LambdaAlphaRefStar.Theories.CodeTypes public
open import LambdaAlphaRefStar.Theories.BlameLabels public

infix 9 _！
infix 9 _？_
infixr 8 _⨾_
infix 8 ⊥_

-- | Coercions between gradual code types (cᵒ, dᵒ).
data OCoercion : Set where
  id  : OCoercion
  _！ : (Gᵒ : OType⋆) → OGround Gᵒ → OCoercion
  _？_ : (Gᵒ : OType⋆) → BlameLabel → OGround Gᵒ → OCoercion
  _⨾_ : OCoercion → OCoercion → OCoercion
  _⇒_ : OCoercion → OCoercion → OCoercion
  ⊥_ : BlameLabel → OCoercion


-- | Code coercion typing.
infix 4 ⊢ᵒ_⦂_⇒_

data ⊢ᵒ_⦂_⇒_ : OCoercion → OType⋆ → OType⋆ → Set where

  ⊢idᵒ : ∀ O
      ---------------------------
    → ⊢ᵒ id ⦂ O ⇒ O

  ⊢injᵒ : ∀ {Gᵒ}
    → (g : OGround Gᵒ)
      ---------------------------
    → ⊢ᵒ (Gᵒ ！) g ⦂ Gᵒ ⇒ ⋆

  ⊢projᵒ : ∀ {Gᵒ}
    → (ℓ : BlameLabel)
    → (g : OGround Gᵒ)
      ---------------------------
    → ⊢ᵒ (Gᵒ ？ ℓ) g ⦂ ⋆ ⇒ Gᵒ

  ⊢seqᵒ : ∀ {O₁ O₂ O₃ c d}
    → ⊢ᵒ c ⦂ O₁ ⇒ O₂
    → ⊢ᵒ d ⦂ O₂ ⇒ O₃
      ---------------------------
    → ⊢ᵒ c ⨾ d ⦂ O₁ ⇒ O₃

  ⊢funᵒ : ∀ {O₁ O₂ O₃ O₄ c d}
    → ⊢ᵒ c ⦂ O₃ ⇒ O₁
    → ⊢ᵒ d ⦂ O₂ ⇒ O₄
      -------------------------------------------
    → ⊢ᵒ c ⇒ d ⦂ (O₁ ⇒ O₂) ⇒ (O₃ ⇒ O₄)

  ⊢errᵒ : ∀ O₁ O₂
    → (ℓ : BlameLabel)
      ---------------------------
    → ⊢ᵒ ⊥ ℓ ⦂ O₁ ⇒ O₂
