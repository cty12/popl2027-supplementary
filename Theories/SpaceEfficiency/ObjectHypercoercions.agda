module Theories.SpaceEfficiency.ObjectHypercoercions where

open import Theories.BlameLabels public
open import Theories.BaseTypes using (Base)
open import Theories.CodeTypes
open import Relation.Binary.PropositionalEquality using (refl)
open import Relation.Nullary using (Dec; yes; no)


infix 6 ⊢ᵒʰ_⦂_⇒_
infix 6 ⊢ᵒᵗ_⦂_⇒_
infix 6 ⊢ᵒᵐ_⦂_⇒_
infix 6 ⊢ᵒʳ_⦂_⇒_
infix 6 ⊢ᵒ_⦂_⇒_
infix 6 _⨟ᵒᵗʰ_
infix 6 _⨟ᵒᵐ_
infix 6 _⨟ᵒ_
infix 9 _？_
infix 9 _！
infixr 8 _⨾_⨾_


-- Code hypercoercion syntax.
data OHead : Set where

  _？_ :
      OType⋆
    → BlameLabel
      ---------------------------
    → OHead

  id :
      OType⋆
      ---------------------------
    → OHead


data OTail : Set where

  _！ :
      OType⋆
      ---------------------------
    → OTail

  id :
      OType⋆
      ---------------------------
    → OTail


data OHeadTailResult : Set where

  _？_ :
      OType⋆
    → BlameLabel
      ---------------------------
    → OHeadTailResult

  _！ :
      OType⋆
      ---------------------------
    → OHeadTailResult

  id :
      OType⋆
      ---------------------------
    → OHeadTailResult

  err :
      BlameLabel
      ---------------------------
    → OHeadTailResult


data OMiddle : Set
data OHypercoercion : Set

data OMiddle where

  _⇒_ :
      OHypercoercion
    → OHypercoercion
      ---------------------------
    → OMiddle

  err :
      BlameLabel
      ---------------------------
    → OMiddle

  id⋆ :
      OMiddle

  idι :
      (ι : Base)
      ---------------------------
    → OMiddle


data OHypercoercion where

  _⨾_⨾_ :
      OHead
    → OMiddle
    → OTail
      ---------------------------
    → OHypercoercion


-- Extrinsic typing rules for the syntax.
data ⊢ᵒʰ_⦂_⇒_ : OHead → OType⋆ → OType⋆ → Set where

  ⊢projʰ : ∀ {Gᵒ}
    → OGround Gᵒ
    → (ℓ : BlameLabel)
      ---------------------------
    → ⊢ᵒʰ Gᵒ ？ ℓ ⦂ ⋆ ⇒ Gᵒ

  ⊢idʰ :
      (O : OType⋆)
      ---------------------------
    → ⊢ᵒʰ id O ⦂ O ⇒ O


data ⊢ᵒᵗ_⦂_⇒_ : OTail → OType⋆ → OType⋆ → Set where

  ⊢injᵗ : ∀ {Gᵒ}
    → OGround Gᵒ
      ---------------------------
    → ⊢ᵒᵗ Gᵒ ！ ⦂ Gᵒ ⇒ ⋆

  ⊢idᵗ :
      (O : OType⋆)
      ---------------------------
    → ⊢ᵒᵗ id O ⦂ O ⇒ O


data ⊢ᵒʳ_⦂_⇒_ : OHeadTailResult → OType⋆ → OType⋆ → Set where

  ⊢projʳ : ∀ {Gᵒ}
    → OGround Gᵒ
    → (ℓ : BlameLabel)
      ---------------------------
    → ⊢ᵒʳ Gᵒ ？ ℓ ⦂ ⋆ ⇒ Gᵒ

  ⊢injʳ : ∀ {Gᵒ}
    → OGround Gᵒ
      ---------------------------
    → ⊢ᵒʳ Gᵒ ！ ⦂ Gᵒ ⇒ ⋆

  ⊢idʳ :
      (O : OType⋆)
      ---------------------------
    → ⊢ᵒʳ id O ⦂ O ⇒ O

  ⊢errʳ : ∀ {O₁ O₂}
    → (ℓ : BlameLabel)
      ---------------------------
    → ⊢ᵒʳ err ℓ ⦂ O₁ ⇒ O₂


data ⊢ᵒᵐ_⦂_⇒_ : OMiddle → OType⋆ → OType⋆ → Set
data ⊢ᵒ_⦂_⇒_ : OHypercoercion → OType⋆ → OType⋆ → Set

data ⊢ᵒᵐ_⦂_⇒_ where

  ⊢funᵐ : ∀ {O₁ O₂ O₃ O₄ c₁ c₂}
    → ⊢ᵒ c₁ ⦂ O₃ ⇒ O₁
    → ⊢ᵒ c₂ ⦂ O₂ ⇒ O₄
      ---------------------------
    → ⊢ᵒᵐ c₁ ⇒ c₂ ⦂ (O₁ ⇒ O₂) ⇒ (O₃ ⇒ O₄)

  ⊢errᵐ : ∀ {O₁ O₂}
    → (ℓ : BlameLabel)
      ---------------------------
    → ⊢ᵒᵐ err ℓ ⦂ O₁ ⇒ O₂

  ⊢id⋆ᵐ :
      ⊢ᵒᵐ id⋆ ⦂ ⋆ ⇒ ⋆

  ⊢idιᵐ :
      (ι : Base)
      ---------------------------
    → ⊢ᵒᵐ idι ι ⦂ ` ι ⇒ ` ι


data ⊢ᵒ_⦂_⇒_ where

  ⊢hc : ∀ {O₁ O₂ O₃ O₄ h m t}
    → ⊢ᵒʰ h ⦂ O₁ ⇒ O₂
    → ⊢ᵒᵐ m ⦂ O₂ ⇒ O₃
    → ⊢ᵒᵗ t ⦂ O₃ ⇒ O₄
      ---------------------------
    → ⊢ᵒ h ⨾ m ⨾ t ⦂ O₁ ⇒ O₄


-- Code tail-head composition. 
_⨟ᵒᵗʰ_ : OTail → OHead → OHeadTailResult
id O ⨟ᵒᵗʰ G ？ ℓ = G ？ ℓ
id O ⨟ᵒᵗʰ id O′ = id O
G ！ ⨟ᵒᵗʰ id O = G ！
G₁ ！ ⨟ᵒᵗʰ G₂ ？ ℓ with G₁ ≡?ᵒ G₂
... | yes refl = id G₁
... | no _ = err ℓ


data IsErrO : OMiddle → Set where
  error : ∀ {ℓ} → IsErrO (err ℓ)


is-error?ᵒ : (m : OMiddle) → Dec (IsErrO m)
is-error?ᵒ (err ℓ) = yes error
is-error?ᵒ (c₁ ⇒ c₂) = no (λ { () })
is-error?ᵒ id⋆ = no (λ { () })
is-error?ᵒ (idι ι) = no (λ { () })


_⨟ᵒᵐ_ : OMiddle → OMiddle → OMiddle
_⨟ᵒ_ : OHypercoercion → OHypercoercion → OHypercoercion

-- Code middle composition.
id⋆ ⨟ᵒᵐ m₂ = m₂
idι ι ⨟ᵒᵐ m₂ = m₂
err ℓ ⨟ᵒᵐ m₂ = err ℓ
(c₁ ⇒ c₂) ⨟ᵒᵐ err ℓ = err ℓ
(c₁ ⇒ c₂) ⨟ᵒᵐ (c₃ ⇒ c₄)
  with c₃ ⨟ᵒ c₁ | c₂ ⨟ᵒ c₄
... | h₁ ⨾ m₁ ⨾ t₁ | h₂ ⨾ m₂ ⨾ t₂
    with is-error?ᵒ m₁ | is-error?ᵒ m₂
...   | yes (error {ℓ}) | _               = err ℓ
...   | no _            | yes (error {ℓ}) = err ℓ
...   | no _            | no _            = (h₁ ⨾ m₁ ⨾ t₁) ⇒ (h₂ ⨾ m₂ ⨾ t₂)
(c₁ ⇒ c₂) ⨟ᵒᵐ id⋆ = c₁ ⇒ c₂
(c₁ ⇒ c₂) ⨟ᵒᵐ idι ι = c₁ ⇒ c₂

-- Code composition.
h₁ ⨾ m₁ ⨾ t₁ ⨟ᵒ h₂ ⨾ m₂ ⨾ t₂
  with t₁ ⨟ᵒᵗʰ h₂
... | id O = h₁ ⨾ (m₁ ⨟ᵒᵐ m₂) ⨾ t₂
... | err ℓ
    with is-error?ᵒ m₁
...   | yes (error {ℓ′}) = h₁ ⨾ err ℓ′ ⨾ t₂
...   | no _             = h₁ ⨾ err ℓ ⨾ t₂
h₁ ⨾ m₁ ⨾ t₁ ⨟ᵒ h₂ ⨾ m₂ ⨾ t₂
    | G ？ ℓ
    with m₁ | h₁
...   | err ℓ′ | _    = h₁ ⨾ err ℓ′ ⨾ t₂
...   | id⋆   | id ⋆ = G ？ ℓ ⨾ m₂ ⨾ t₂
...   | _     | _    = h₁ ⨾ err ℓ ⨾ t₂ -- unreachable for well-typed hypercoercions
h₁ ⨾ m₁ ⨾ t₁ ⨟ᵒ h₂ ⨾ m₂ ⨾ t₂
    | G ！
    with m₂ | is-error?ᵒ m₁ | t₂
...   | err ℓ | yes (error {ℓ′}) | _    = h₁ ⨾ err ℓ′ ⨾ t₂
...   | err ℓ | no _             | _    = h₁ ⨾ err ℓ ⨾ t₂
...   | id⋆  | _                | id ⋆ = h₁ ⨾ m₁ ⨾ G ！
...   | _    | _                | _    = h₁ ⨾ m₁ ⨾ t₂ -- unreachable for well-typed hypercoercions
