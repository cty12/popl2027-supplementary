module LambdaAlphaRefStar.Theories.SpaceEfficiency.ECHypercoercions where

open import LambdaAlphaRefStar.Theories.EnvClassifiers
open import LambdaAlphaRefStar.Theories.BlameLabels public
open import LambdaAlphaRefStar.Theories.ECSubtypeDecidable using (ec-<:⋆?)
open import Relation.Nullary using (yes; no)


infix 6 _⊢ᵉʰ_⦂_⇒_
infix 6 _⊢ᵉᵗ_⦂_⇒_
infix 6 _;_⊢ᵉᵐ_⦂_⇒_
infix 6 _;_⊢ᵉʳ_⦂_⇒_
infix 6 _;_⊢ᵉ_⦂_⇒_
infix 6 _⊢_⨟ᵉᵗʰ_
infix 6 _⨟ᵉᵐ_
infix 6 _⊢_⨟ᵉ_
infix 8 _↑_
infix 9 _？_
infix 9 _！
infixr 8 _⨾_⨾_


-- EC hypercoercion syntax.
data ECHead : Set where

  _？_ :
      EC
    → BlameLabel
      ---------------------------
    → ECHead

  id :
      EC⋆
      ---------------------------
    → ECHead


data ECTail : Set where

  _！ :
      EC
      ---------------------------
    → ECTail

  id :
      EC⋆
      ---------------------------
    → ECTail


data ECMiddle : Set where

  _↑_ :
      EC⋆
    → EC⋆
      ---------------------------
    → ECMiddle

  err :
      BlameLabel
      ---------------------------
    → ECMiddle


data ECHeadTailResult : Set where

  _？_ :
      EC
    → BlameLabel
      ---------------------------
    → ECHeadTailResult

  _！ :
      EC
      ---------------------------
    → ECHeadTailResult

  _↑_ :
      EC⋆
    → EC⋆
      ---------------------------
    → ECHeadTailResult

  err :
      BlameLabel
      ---------------------------
    → ECHeadTailResult


data ECHypercoercion : Set where

  _⨾_⨾_ :
      ECHead
    → ECMiddle
    → ECTail
      ---------------------------
    → ECHypercoercion


-- Extrinsic typing rules for the EC syntax.
data _⊢ᵉʰ_⦂_⇒_ (Δ : ECCtx) : ECHead → EC⋆ → EC⋆ → Set where

  ⊢projʰ :
      (e : EC)
    → (ℓ : BlameLabel)
      ---------------------------
    → Δ ⊢ᵉʰ e ？ ℓ ⦂ ⋆ ⇒ ec e

  ⊢idʰ :
      (ê : EC⋆)
      ---------------------------
    → Δ ⊢ᵉʰ id ê ⦂ ê ⇒ ê


data _⊢ᵉᵗ_⦂_⇒_ (Δ : ECCtx) : ECTail → EC⋆ → EC⋆ → Set where

  ⊢injᵗ :
      (e : EC)
      ---------------------------
    → Δ ⊢ᵉᵗ e ！ ⦂ ec e ⇒ ⋆

  ⊢idᵗ :
      (ê : EC⋆)
      ---------------------------
    → Δ ⊢ᵉᵗ id ê ⦂ ê ⇒ ê


data _;_⊢ᵉᵐ_⦂_⇒_ (Δ : ECCtx) (Θ : SubCtx) : ECMiddle → EC⋆ → EC⋆ → Set where

  ⊢subᵐ : ∀ {ê₁ ê₂}
    → Θ ⊢ᵉ ê₁ <:⋆ ê₂
      ---------------------------
    → Δ ; Θ ⊢ᵉᵐ ê₁ ↑ ê₂ ⦂ ê₁ ⇒ ê₂

  ⊢errᵐ : ∀ {ê₁ ê₂}
    → (ℓ : BlameLabel)
      ---------------------------
    → Δ ; Θ ⊢ᵉᵐ err ℓ ⦂ ê₁ ⇒ ê₂


data _;_⊢ᵉʳ_⦂_⇒_ (Δ : ECCtx) (Θ : SubCtx) : ECHeadTailResult → EC⋆ → EC⋆ → Set where

  ⊢projʳ :
      (e : EC)
    → (ℓ : BlameLabel)
      ---------------------------
    → Δ ; Θ ⊢ᵉʳ e ？ ℓ ⦂ ⋆ ⇒ ec e

  ⊢injʳ :
      (e : EC)
      ---------------------------
    → Δ ; Θ ⊢ᵉʳ e ！ ⦂ ec e ⇒ ⋆

  ⊢subʳ : ∀ {ê₁ ê₂}
    → Θ ⊢ᵉ ê₁ <:⋆ ê₂
      ---------------------------
    → Δ ; Θ ⊢ᵉʳ ê₁ ↑ ê₂ ⦂ ê₁ ⇒ ê₂

  ⊢errʳ : ∀ {ê₁ ê₂}
    → (ℓ : BlameLabel)
      ---------------------------
    → Δ ; Θ ⊢ᵉʳ err ℓ ⦂ ê₁ ⇒ ê₂


data _;_⊢ᵉ_⦂_⇒_ (Δ : ECCtx) (Θ : SubCtx) : ECHypercoercion → EC⋆ → EC⋆ → Set where

  ⊢hc : ∀ {ê₁ ê₂ ê₃ ê₄ h m t}
    → Δ     ⊢ᵉʰ h ⦂ ê₁ ⇒ ê₂
    → Δ ; Θ ⊢ᵉᵐ m ⦂ ê₂ ⇒ ê₃
    → Δ     ⊢ᵉᵗ t ⦂ ê₃ ⇒ ê₄
      ---------------------------
    → Δ ; Θ ⊢ᵉ h ⨾ m ⨾ t ⦂ ê₁ ⇒ ê₄


<:⋆-refl : ∀ {Θ} ê → Θ ⊢ᵉ ê <:⋆ ê
<:⋆-refl ⋆ = <:-⋆
<:⋆-refl (ec e) = <:-ec <:-refl


-- EC tail-head composition.
_⊢_⨟ᵉᵗʰ_ : SubCtx → ECTail → ECHead → ECHeadTailResult
Θ ⊢ e₁ ！ ⨟ᵉᵗʰ e₂ ？ ℓ with ec-<:⋆? Θ (ec e₁) (ec e₂)
... | yes _ = ec e₁ ↑ ec e₂
... | no  _ = err ℓ
Θ ⊢ e ！ ⨟ᵉᵗʰ id ⋆ = e ！
Θ ⊢ e₁ ！ ⨟ᵉᵗʰ id (ec e₂) = ec e₁ ↑ ec e₂
Θ ⊢ id ê ⨟ᵉᵗʰ e ？ ℓ = e ？ ℓ
Θ ⊢ id ê₁ ⨟ᵉᵗʰ id ê₂ = ê₁ ↑ ê₂


-- EC middle composition.
_⨟ᵉᵐ_ : ECMiddle → ECMiddle → ECMiddle
err ℓ ⨟ᵉᵐ m₂ = err ℓ
(ê₁ ↑ ê₂) ⨟ᵉᵐ err ℓ = err ℓ
(ê₁ ↑ ê₂) ⨟ᵉᵐ (ê₂′ ↑ ê₃) = ê₁ ↑ ê₃


-- EC hypercoercion composition.
_⊢_⨟ᵉ_ : SubCtx → ECHypercoercion → ECHypercoercion → ECHypercoercion
Θ ⊢ h₁ ⨾ m₁ ⨾ t₁ ⨟ᵉ h₂ ⨾ m₂ ⨾ t₂
  with Θ ⊢ t₁ ⨟ᵉᵗʰ h₂
... | ê₄ ↑ ê₅ = h₁ ⨾ (m₁ ⨟ᵉᵐ (ê₄ ↑ ê₅ ⨟ᵉᵐ m₂)) ⨾ t₂
... | err ℓ
    with m₁
...   | err ℓ′ = h₁ ⨾ err ℓ′ ⨾ t₂
...   | _ ↑ _  = h₁ ⨾ err ℓ ⨾ t₂
Θ ⊢ h₁ ⨾ m₁ ⨾ t₁ ⨟ᵉ h₂ ⨾ m₂ ⨾ t₂
    | e ？ ℓ
    with m₁ | h₁
...   | err ℓ′ | _    = h₁ ⨾ err ℓ′ ⨾ t₂
...   | _ ↑ _  | id ⋆ = e ？ ℓ ⨾ m₂ ⨾ t₂
...   | _ ↑ _  | _ ？ _ = h₁ ⨾ err ℓ ⨾ t₂ -- unreachable for well-typed hypercoercions
...   | _ ↑ _  | id (ec _) = h₁ ⨾ err ℓ ⨾ t₂ -- unreachable for well-typed hypercoercions
Θ ⊢ h₁ ⨾ m₁ ⨾ t₁ ⨟ᵉ h₂ ⨾ m₂ ⨾ t₂
    | e ！
    with m₁ | m₂ | t₂
...   | err ℓ | _     | _    = h₁ ⨾ err ℓ ⨾ t₂
...   | _ ↑ _ | err ℓ | _    = h₁ ⨾ err ℓ ⨾ t₂
...   | _ ↑ _ | _ ↑ _ | id ⋆ = h₁ ⨾ m₁ ⨾ e ！
... | _ ↑ _ | _ ↑ _ | _ ！ = h₁ ⨾ m₁ ⨾ t₂ --unreachable for well-typed hypercoercions
... | _ ↑ _ | _ ↑ _ | id (ec _) = h₁ ⨾ m₁ ⨾ t₂ --unreachable for well-typed hypercoercions
