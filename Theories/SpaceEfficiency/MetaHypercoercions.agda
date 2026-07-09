module Theories.SpaceEfficiency.MetaHypercoercions where

open import Theories.EnvClassifiers
open import Theories.BlameLabels public
open import Theories.BaseTypes using (Base)
open import Theories.CodeTypes using (OType⋆)
open import Theories.MetaTypes
open import Relation.Binary.PropositionalEquality using (refl)
open import Relation.Nullary using (Dec; yes; no)

import Theories.SpaceEfficiency.ECHypercoercions as EHC
import Theories.SpaceEfficiency.ObjectHypercoercions as OHC


infix 6 _⊢ᵐʰ_⦂_⇒_
infix 6 _⊢ᵐᵗ_⦂_⇒_
infix 6 _;_⊢ᵐᵐ_⦂_⇒_
infix 6 _⊢ᵐʳ_⦂_⇒_
infix 6 _;_⊢ᵐ_⦂_⇒_
infix 6 _⨟ᵐᵗʰ_
infix 6 _⊢_⨟ᵐᵐ_
infix 6 _⊢_⨟ᵐ_
infix 9 _？_
infix 9 _！
infixr 8 _⨾_⨾_


-- Meta hypercoercion syntax.
data MHead : Set where

  _？_ :
      MType
    → BlameLabel
      ---------------------------
    → MHead

  id :
      MType
      ---------------------------
    → MHead


data MTail : Set where

  _！ :
      MType
      ---------------------------
    → MTail

  id :
      MType
      ---------------------------
    → MTail


data MHeadTailResult : Set where

  _？_ :
      MType
    → BlameLabel
      ---------------------------
    → MHeadTailResult

  _！ :
      MType
      ---------------------------
    → MHeadTailResult

  id :
      MType
      ---------------------------
    → MHeadTailResult

  err :
      BlameLabel
      ---------------------------
    → MHeadTailResult


data MMiddle : Set
data MHypercoercion : Set

data MMiddle where

  _⇒_ :
      MHypercoercion
    → MHypercoercion
      ---------------------------
    → MMiddle

  ‶_″_ :
      OHC.OHypercoercion
    → EHC.ECHypercoercion
      ---------------------------
    → MMiddle

  ref :
      MHypercoercion
    → MHypercoercion
      ---------------------------
    → MMiddle

  ∀̇_ :
      MHypercoercion
      ---------------------------
    → MMiddle

  _<:_=>_ :
      EC
    → EC
    → MHypercoercion
      ---------------------------
    → MMiddle

  err :
      BlameLabel
      ---------------------------
    → MMiddle

  id⋆ :
      MMiddle

  idι :
      (ι : Base)
      ---------------------------
    → MMiddle


data MHypercoercion where

  _⨾_⨾_ :
      MHead
    → MMiddle
    → MTail
      ---------------------------
    → MHypercoercion


-- Extrinsic typing rules for the syntax.
data _⊢ᵐʰ_⦂_⇒_ (Δ : ECCtx) : MHead → MType → MType → Set where

  ⊢projʰ : ∀ {G}
    → Ground G
    → (ℓ : BlameLabel)
      ---------------------------
    → Δ ⊢ᵐʰ G ？ ℓ ⦂ ⋆ ⇒ G

  ⊢idʰ :
      (A : MType)
      ---------------------------
    → Δ ⊢ᵐʰ id A ⦂ A ⇒ A


data _⊢ᵐᵗ_⦂_⇒_ (Δ : ECCtx) : MTail → MType → MType → Set where

  ⊢injᵗ : ∀ {G}
    → Ground G
      ---------------------------
    → Δ ⊢ᵐᵗ G ！ ⦂ G ⇒ ⋆

  ⊢idᵗ :
      (A : MType)
      ---------------------------
    → Δ ⊢ᵐᵗ id A ⦂ A ⇒ A


data _⊢ᵐʳ_⦂_⇒_ (Δ : ECCtx) : MHeadTailResult → MType → MType → Set where

  ⊢projʳ : ∀ {G}
    → Ground G
    → (ℓ : BlameLabel)
      ---------------------------
    → Δ ⊢ᵐʳ G ？ ℓ ⦂ ⋆ ⇒ G

  ⊢injʳ : ∀ {G}
    → Ground G
      ---------------------------
    → Δ ⊢ᵐʳ G ！ ⦂ G ⇒ ⋆

  ⊢idʳ :
      (A : MType)
      ---------------------------
    → Δ ⊢ᵐʳ id A ⦂ A ⇒ A

  ⊢errʳ : ∀ {A B}
    → (ℓ : BlameLabel)
      ---------------------------
    → Δ ⊢ᵐʳ err ℓ ⦂ A ⇒ B


data _;_⊢ᵐᵐ_⦂_⇒_ (Δ : ECCtx) (Θ : SubCtx) : MMiddle → MType → MType → Set
data _;_⊢ᵐ_⦂_⇒_ (Δ : ECCtx) (Θ : SubCtx) : MHypercoercion → MType → MType → Set

data _;_⊢ᵐᵐ_⦂_⇒_ Δ Θ where

  ⊢funᵐ : ∀ {A B C D c₁ c₂}
    → Δ ; Θ ⊢ᵐ c₁ ⦂ C ⇒ A
    → Δ ; Θ ⊢ᵐ c₂ ⦂ B ⇒ D
      ---------------------------
    → Δ ; Θ ⊢ᵐᵐ c₁ ⇒ c₂ ⦂ (A ⇒ B) ⇒ (C ⇒ D)

  ⊢codeᵐ : ∀ {O₁ O₂ ê₁ ê₂ cᵒ cᵉ}
    → OHC.⊢ᵒ cᵒ ⦂ O₁ ⇒ O₂
    → EHC._;_⊢ᵉ_⦂_⇒_ Δ Θ cᵉ ê₁ ê₂
      ---------------------------
    → Δ ; Θ ⊢ᵐᵐ ‶ cᵒ ″ cᵉ ⦂ (‶ O₁ ″ ê₁) ⇒ (‶ O₂ ″ ê₂)

  ⊢refᵐ : ∀ {A B c₁ c₂}
    → Δ ; Θ ⊢ᵐ c₁ ⦂ B ⇒ A
    → Δ ; Θ ⊢ᵐ c₂ ⦂ A ⇒ B
      ---------------------------
    → Δ ; Θ ⊢ᵐᵐ ref c₁ c₂ ⦂ Ref A ⇒ Ref B

  ⊢forallᵐ : ∀ {A B c}
    → (Δ ,α) ; ⇑ᵉ-subctx Θ ⊢ᵐ c ⦂ A ⇒ B
      ---------------------------
    → Δ ; Θ ⊢ᵐᵐ ∀̇ c ⦂ ∀̇ A ⇒ ∀̇ B

  ⊢subᵐ : ∀ {A B c}
    → (e₁ e₂ : EC)
    → Δ ; Θ , e₁ <: e₂ ⊢ᵐ c ⦂ A ⇒ B
      ---------------------------
    → Δ ; Θ ⊢ᵐᵐ e₁ <: e₂ => c ⦂ (e₁ <: e₂ => A) ⇒ (e₁ <: e₂ => B)

  ⊢errᵐ : ∀ {A B}
    → (ℓ : BlameLabel)
      ---------------------------
    → Δ ; Θ ⊢ᵐᵐ err ℓ ⦂ A ⇒ B

  ⊢id⋆ᵐ :
      Δ ; Θ ⊢ᵐᵐ id⋆ ⦂ ⋆ ⇒ ⋆

  ⊢idιᵐ :
      (ι : Base)
      ---------------------------
    → Δ ; Θ ⊢ᵐᵐ idι ι ⦂ ` ι ⇒ ` ι


data _;_⊢ᵐ_⦂_⇒_ Δ Θ where

  ⊢hc : ∀ {A B C D h m t}
    → Δ ⊢ᵐʰ h ⦂ A ⇒ B
    → Δ ; Θ ⊢ᵐᵐ m ⦂ B ⇒ C
    → Δ ⊢ᵐᵗ t ⦂ C ⇒ D
      ---------------------------
    → Δ ; Θ ⊢ᵐ h ⨾ m ⨾ t ⦂ A ⇒ D


-- Meta tail-head composition result syntax.
_⨟ᵐᵗʰ_ : MTail → MHead → MHeadTailResult
id A ⨟ᵐᵗʰ G ？ ℓ = G ？ ℓ
id A ⨟ᵐᵗʰ id B = id A
G ！ ⨟ᵐᵗʰ id A = G ！
G₁ ！ ⨟ᵐᵗʰ G₂ ？ ℓ with G₁ ≡? G₂
... | yes refl = id G₁
... | no _     = err ℓ


data IsErrM : MMiddle → Set where
  error : ∀ {ℓ} → IsErrM (err ℓ)


is-error? : (m : MMiddle) → Dec (IsErrM m)
is-error? (err ℓ) = yes error
is-error? (c₁ ⇒ c₂) = no (λ { () })
is-error? (‶ cᵒ ″ cᵉ) = no (λ { () })
is-error? (ref c₁ c₂) = no (λ { () })
is-error? (∀̇ c) = no (λ { () })
is-error? (e₁ <: e₂ => c) = no (λ { () })
is-error? id⋆ = no (λ { () })
is-error? (idι ι) = no (λ { () })


_⊢_⨟ᵐᵐ_ : SubCtx → MMiddle → MMiddle → MMiddle
_⊢_⨟ᵐ_ : SubCtx → MHypercoercion → MHypercoercion → MHypercoercion

-- Meta middle composition.
Θ ⊢ id⋆ ⨟ᵐᵐ m₂ = m₂
Θ ⊢ idι ι ⨟ᵐᵐ m₂ = m₂
Θ ⊢ err ℓ ⨟ᵐᵐ m₂ = err ℓ
Θ ⊢ c₁₁ ⇒ c₁₂ ⨟ᵐᵐ err ℓ = err ℓ
Θ ⊢ c₁₁ ⇒ c₁₂ ⨟ᵐᵐ (c₂₁ ⇒ c₂₂) = (Θ ⊢ c₂₁ ⨟ᵐ c₁₁) ⇒ (Θ ⊢ c₁₂ ⨟ᵐ c₂₂)
Θ ⊢ c₁₁ ⇒ c₁₂ ⨟ᵐᵐ m₂ = c₁₁ ⇒ c₁₂ -- unreachable for well-typed hypercoercions
Θ ⊢ ref c₁₁ c₁₂ ⨟ᵐᵐ err ℓ = err ℓ
Θ ⊢ ref c₁₁ c₁₂ ⨟ᵐᵐ ref c₂₁ c₂₂ = ref (Θ ⊢ c₂₁ ⨟ᵐ c₁₁) (Θ ⊢ c₁₂ ⨟ᵐ c₂₂)
Θ ⊢ ref c₁₁ c₁₂ ⨟ᵐᵐ m₂ = ref c₁₁ c₁₂ -- unreachable for well-typed hypercoercions
Θ ⊢ ∀̇ c₁ ⨟ᵐᵐ err ℓ = err ℓ
Θ ⊢ ∀̇ c₁ ⨟ᵐᵐ ∀̇ c₂ = ∀̇ ((⇑ᵉ-subctx Θ) ⊢ c₁ ⨟ᵐ c₂)
Θ ⊢ ∀̇ c₁ ⨟ᵐᵐ m₂ = ∀̇ c₁ -- unreachable for well-typed hypercoercions
Θ ⊢ e₁ <: e₂ => c₁ ⨟ᵐᵐ err ℓ = err ℓ
Θ ⊢ e₁ <: e₂ => c₁ ⨟ᵐᵐ e₃ <: e₄ => c₂ = e₁ <: e₂ => ((Θ , e₁ <: e₂) ⊢ c₁ ⨟ᵐ c₂)
Θ ⊢ e₁ <: e₂ => c₁ ⨟ᵐᵐ m₂ = e₁ <: e₂ => c₁ -- unreachable for well-typed hypercoercions
Θ ⊢ ‶ c₁ᵒ ″ c₁ᵉ ⨟ᵐᵐ err ℓ = err ℓ
Θ ⊢ ‶ c₁ᵒ ″ c₁ᵉ ⨟ᵐᵐ ‶ c₂ᵒ ″ c₂ᵉ
  with OHC._⨟ᵒ_ c₁ᵒ c₂ᵒ | EHC._⊢_⨟ᵉ_ Θ c₁ᵉ c₂ᵉ
... | OHC._⨾_⨾_ hᵒ mᵒ tᵒ | EHC._⨾_⨾_ hᵉ mᵉ tᵉ
    with OHC.is-error?ᵒ mᵒ | mᵉ
...   | yes (OHC.error {ℓ}) | _ = err ℓ
...   | no _ | EHC.err ℓ = err ℓ
...   | no _ | _ = ‶ OHC._⨾_⨾_ hᵒ mᵒ tᵒ ″ EHC._⨾_⨾_ hᵉ mᵉ tᵉ
Θ ⊢ ‶ c₁ᵒ ″ c₁ᵉ ⨟ᵐᵐ m₂ = ‶ c₁ᵒ ″ c₁ᵉ -- unreachable for well-typed hypercoercions

-- Meta composition.
Θ ⊢ h₁ ⨾ m₁ ⨾ t₁ ⨟ᵐ h₂ ⨾ m₂ ⨾ t₂
  with t₁ ⨟ᵐᵗʰ h₂
... | id A = h₁ ⨾ (Θ ⊢ m₁ ⨟ᵐᵐ m₂) ⨾ t₂
... | err ℓ
    with is-error? m₁
...   | yes (error {ℓ′}) = h₁ ⨾ err ℓ′ ⨾ t₂
...   | no _             = h₁ ⨾ err ℓ ⨾ t₂
Θ ⊢ h₁ ⨾ m₁ ⨾ t₁ ⨟ᵐ h₂ ⨾ m₂ ⨾ t₂
    | G ？ ℓ
    with m₁ | h₁
...   | err ℓ′ | _    = h₁ ⨾ err ℓ′ ⨾ t₂
...   | id⋆   | id ⋆ = G ？ ℓ ⨾ m₂ ⨾ t₂
...   | _     | _    = h₁ ⨾ err ℓ ⨾ t₂ -- unreachable for well-typed hypercoercions
Θ ⊢ h₁ ⨾ m₁ ⨾ t₁ ⨟ᵐ h₂ ⨾ m₂ ⨾ t₂
    | G ！
    with m₂ | is-error? m₁ | t₂
...   | err ℓ | yes (error {ℓ′}) | _    = h₁ ⨾ err ℓ′ ⨾ t₂
...   | err ℓ | no _             | _    = h₁ ⨾ err ℓ ⨾ t₂
...   | id⋆  | _                | id ⋆ = h₁ ⨾ m₁ ⨾ G ！
...   | _    | _                | _    = h₁ ⨾ m₁ ⨾ t₂ -- unreachable for well-typed hypercoercions
