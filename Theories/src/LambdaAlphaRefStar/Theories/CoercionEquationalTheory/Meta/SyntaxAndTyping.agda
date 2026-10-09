module LambdaAlphaRefStar.Theories.CoercionEquationalTheory.Meta.SyntaxAndTyping where

open import LambdaAlphaRefStar.Theories.CoercionEquationalTheory.EC.SyntaxAndTyping
  using (ECCoercion; _;_⊢ᵉ_⦂_⇒_; wf-domᵉ; wf-codᵉ)
open import LambdaAlphaRefStar.Theories.CoercionEquationalTheory.Code.SyntaxAndTyping
  using (OCoercion; ⊢ᵒ_⦂_⇒_)
open import LambdaAlphaRefStar.Theories.EnvClassifiers public
open import LambdaAlphaRefStar.Theories.MetaTypes       public
open import LambdaAlphaRefStar.Theories.BlameLabels     public

infix 9 _！
infix 9 _？_
infixr 8 _⨾_
infix 8 ⊥_

-- | Coercions between metalanguage types (c, d).
data MCoercion : Set where
  id       : MCoercion
  _！      : (G : MType) → Ground G → MCoercion
  _？_     : (G : MType) → BlameLabel → Ground G → MCoercion
  _⨾_      : MCoercion → MCoercion → MCoercion
  _⇒_      : MCoercion → MCoercion → MCoercion
  ‶_″_     : OCoercion → ECCoercion → MCoercion
  Ref_,_   : MCoercion → MCoercion → MCoercion
  ∀̇_       : MCoercion → MCoercion
  _<:_=>_  : EC → EC → MCoercion → MCoercion
  ⊥_       : BlameLabel → MCoercion


-- | Meta coercion typing.
infix 4 _;_⊢ᵐ_⦂_⇒_

data _;_⊢ᵐ_⦂_⇒_ : ECCtx → SubCtx → MCoercion → MType → MType → Set where

  ⊢idᵐ : ∀ {Δ Θ}
    → (A : MType)
    → Δ ⊢ᵐᵗ A
      ---------------------------------------
    → Δ ; Θ ⊢ᵐ id ⦂ A ⇒ A

  ⊢injᵐ : ∀ {Δ Θ G}
    → Δ ⊢ᵐᵗ G
    → (g : Ground G)
      ---------------------------------------
    → Δ ; Θ ⊢ᵐ (G ！) g ⦂ G ⇒ ⋆

  ⊢projᵐ : ∀ {Δ Θ G}
    → Δ ⊢ᵐᵗ G
    → (ℓ : BlameLabel)
    → (g : Ground G)
      ---------------------------------------
    → Δ ; Θ ⊢ᵐ (G ？ ℓ) g ⦂ ⋆ ⇒ G

  ⊢seqᵐ : ∀ {Δ Θ A B C c d}
    → Δ ; Θ ⊢ᵐ c ⦂ A ⇒ B
    → Δ ; Θ ⊢ᵐ d ⦂ B ⇒ C
      ---------------------------------------
    → Δ ; Θ ⊢ᵐ c ⨾ d ⦂ A ⇒ C

  ⊢funᵐ : ∀ {Δ Θ A B C D c d}
    → Δ ; Θ ⊢ᵐ c ⦂ C ⇒ A
    → Δ ; Θ ⊢ᵐ d ⦂ B ⇒ D
      ---------------------------------------
    → Δ ; Θ ⊢ᵐ c ⇒ d ⦂ (A ⇒ B) ⇒ (C ⇒ D)

  ⊢codeᵐ : ∀ {Δ Θ O₁ O₂ ê₁ ê₂ cᵒ cᵉ}
    →       ⊢ᵒ cᵒ ⦂ O₁ ⇒ O₂
    → Δ ; Θ ⊢ᵉ cᵉ ⦂ ê₁ ⇒ ê₂
      ---------------------------------------------------------
    → Δ ; Θ ⊢ᵐ ‶ cᵒ ″ cᵉ ⦂ (‶ O₁ ″ ê₁) ⇒ (‶ O₂ ″ ê₂)

  ⊢refᵐ : ∀ {Δ Θ A B c d}
    → Δ ; Θ ⊢ᵐ c ⦂ B ⇒ A
    → Δ ; Θ ⊢ᵐ d ⦂ A ⇒ B
      ---------------------------------------
    → Δ ; Θ ⊢ᵐ Ref c , d ⦂ (Ref A) ⇒ (Ref B)

  ⊢forallᵐ : ∀ {Δ Θ A B c}
    → Δ ,α ; ⇑ᵉ-subctx Θ ⊢ᵐ c ⦂ A ⇒ B
      ---------------------------------------
    → Δ ; Θ ⊢ᵐ ∀̇ c ⦂ (∀̇ A) ⇒ (∀̇ B)

  ⊢subᵐ : ∀ {Δ Θ A B c}
    → (e₁ e₂ : EC)
    → Δ ⊢ᵉ e₁
    → Δ ⊢ᵉ e₂
    → Δ ; Θ , e₁ <: e₂ ⊢ᵐ c ⦂ A ⇒ B
      -----------------------------------------------------
    → Δ ; Θ ⊢ᵐ e₁ <: e₂ => c ⦂ (e₁ <: e₂ => A) ⇒ (e₁ <: e₂ => B)

  ⊢errᵐ : ∀ {Δ Θ A B}
    → Δ ⊢ᵐᵗ A
    → Δ ⊢ᵐᵗ B
    → (ℓ : BlameLabel)
      ---------------------------------------
    → Δ ; Θ ⊢ᵐ ⊥ ℓ ⦂ A ⇒ B


wf-domᵐ : ∀ {Δ Θ c A B}
  → Δ ; Θ ⊢ᵐ c ⦂ A ⇒ B
    -------------------
  → Δ ⊢ᵐᵗ A
wf-codᵐ : ∀ {Δ Θ c A B}
  → Δ ; Θ ⊢ᵐ c ⦂ A ⇒ B
    -------------------
  → Δ ⊢ᵐᵗ B

wf-domᵐ (⊢idᵐ A ⊢A) = ⊢A
wf-domᵐ (⊢injᵐ ⊢G g) = ⊢G
wf-domᵐ (⊢projᵐ ⊢G ℓ g) = wf-⋆
wf-domᵐ (⊢seqᵐ ⊢c ⊢d) = wf-domᵐ ⊢c
wf-domᵐ (⊢funᵐ ⊢c ⊢d) = wf-fun (wf-codᵐ ⊢c) (wf-domᵐ ⊢d)
wf-domᵐ (⊢codeᵐ ⊢cᵒ ⊢cᵉ) = wf-code (wf-domᵉ ⊢cᵉ)
wf-domᵐ (⊢refᵐ ⊢c ⊢d) = wf-ref (wf-codᵐ ⊢c)
wf-domᵐ (⊢forallᵐ ⊢c) = wf-forall (wf-domᵐ ⊢c)
wf-domᵐ (⊢subᵐ e₁ e₂ ⊢e₁ ⊢e₂ ⊢c) = wf-sub ⊢e₁ ⊢e₂ (wf-domᵐ ⊢c)
wf-domᵐ (⊢errᵐ ⊢A ⊢B ℓ) = ⊢A

wf-codᵐ (⊢idᵐ A ⊢A) = ⊢A
wf-codᵐ (⊢injᵐ ⊢G g) = wf-⋆
wf-codᵐ (⊢projᵐ ⊢G ℓ g) = ⊢G
wf-codᵐ (⊢seqᵐ ⊢c ⊢d) = wf-codᵐ ⊢d
wf-codᵐ (⊢funᵐ ⊢c ⊢d) = wf-fun (wf-domᵐ ⊢c) (wf-codᵐ ⊢d)
wf-codᵐ (⊢codeᵐ ⊢cᵒ ⊢cᵉ) = wf-code (wf-codᵉ ⊢cᵉ)
wf-codᵐ (⊢refᵐ ⊢c ⊢d) = wf-ref (wf-domᵐ ⊢c)
wf-codᵐ (⊢forallᵐ ⊢c) = wf-forall (wf-codᵐ ⊢c)
wf-codᵐ (⊢subᵐ e₁ e₂ ⊢e₁ ⊢e₂ ⊢c) = wf-sub ⊢e₁ ⊢e₂ (wf-codᵐ ⊢c)
wf-codᵐ (⊢errᵐ ⊢A ⊢B ℓ) = ⊢B
