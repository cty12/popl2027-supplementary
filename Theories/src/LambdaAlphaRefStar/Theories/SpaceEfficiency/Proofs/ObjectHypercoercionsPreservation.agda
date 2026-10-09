module LambdaAlphaRefStar.Theories.SpaceEfficiency.Proofs.ObjectHypercoercionsPreservation where

open import LambdaAlphaRefStar.Theories.CodeTypes
open import LambdaAlphaRefStar.Theories.SpaceEfficiency.ObjectHypercoercions
open import Relation.Binary.PropositionalEquality using (refl)
open import Relation.Nullary using (yes; no)


-- Composition preserves extrinsic typing.
preserve-⨟ᵒᵗʰ : ∀ {t h O₁ O₂ O₃}
  → ⊢ᵒᵗ t ⦂ O₁ ⇒ O₂
  → ⊢ᵒʰ h ⦂ O₂ ⇒ O₃
    ---------------------------------------------
  → ⊢ᵒʳ (t ⨟ᵒᵗʰ h) ⦂ O₁ ⇒ O₃
preserve-⨟ᵒᵗʰ (⊢idᵗ O) (⊢projʰ g ℓ) = ⊢projʳ g ℓ
preserve-⨟ᵒᵗʰ (⊢idᵗ O) (⊢idʰ .O) = ⊢idʳ O
preserve-⨟ᵒᵗʰ (⊢injᵗ g) (⊢idʰ ⋆) = ⊢injʳ g
preserve-⨟ᵒᵗʰ (⊢injᵗ {Gᵒ = G₁} g₁) (⊢projʰ {Gᵒ = G₂} g₂ ℓ) with G₁ ≡?ᵒ G₂
... | yes refl = ⊢idʳ G₁
... | no _     = ⊢errʳ ℓ


mutual
  preserve-⨟ᵒᵐ : ∀ {m₁ m₂ O₁ O₂ O₃}
    → ⊢ᵒᵐ m₁ ⦂ O₁ ⇒ O₂
    → ⊢ᵒᵐ m₂ ⦂ O₂ ⇒ O₃
      ---------------------------------------------
    → ⊢ᵒᵐ (m₁ ⨟ᵒᵐ m₂) ⦂ O₁ ⇒ O₃
  preserve-⨟ᵒᵐ ⊢id⋆ᵐ ⊢m₂ = ⊢m₂
  preserve-⨟ᵒᵐ (⊢idιᵐ ι) ⊢m₂ = ⊢m₂
  preserve-⨟ᵒᵐ (⊢errᵐ ℓ) ⊢m₂ = ⊢errᵐ ℓ
  preserve-⨟ᵒᵐ (⊢funᵐ ⊢c₁ ⊢c₂) (⊢errᵐ ℓ) = ⊢errᵐ ℓ
  preserve-⨟ᵒᵐ (⊢funᵐ {c₁ = c₁} {c₂ = c₂} ⊢c₁ ⊢c₂)
      (⊢funᵐ {c₁ = c₃} {c₂ = c₄} ⊢c₃ ⊢c₄)
      with c₃ ⨟ᵒ c₁ | preserve-⨟ᵒ ⊢c₃ ⊢c₁ | c₂ ⨟ᵒ c₄ | preserve-⨟ᵒ ⊢c₂ ⊢c₄
  ... | h₁ ⨾ m₁ ⨾ t₁ | ⊢hc ⊢h₁ ⊢m₁ ⊢t₁ | h₂ ⨾ m₂ ⨾ t₂ | ⊢hc ⊢h₂ ⊢m₂ ⊢t₂
      with is-error?ᵒ m₁ | is-error?ᵒ m₂
  ...   | yes (error {ℓ}) | _               = ⊢errᵐ ℓ
  ...   | no _            | yes (error {ℓ}) = ⊢errᵐ ℓ
  ...   | no _            | no _            = ⊢funᵐ (⊢hc ⊢h₁ ⊢m₁ ⊢t₁) (⊢hc ⊢h₂ ⊢m₂ ⊢t₂)

  preserve-⨟ᵒ : ∀ {c₁ c₂ O₁ O₂ O₃}
    → ⊢ᵒ c₁ ⦂ O₁ ⇒ O₂
    → ⊢ᵒ c₂ ⦂ O₂ ⇒ O₃
      ---------------------------------------------
    → ⊢ᵒ (c₁ ⨟ᵒ c₂) ⦂ O₁ ⇒ O₃
  preserve-⨟ᵒ
      (⊢hc {h = h₁} {m = m₁} {t = t₁} ⊢h₁ ⊢m₁ ⊢t₁)
      (⊢hc {h = h₂} {m = m₂} {t = t₂} ⊢h₂ ⊢m₂ ⊢t₂)
      with t₁ ⨟ᵒᵗʰ h₂ | preserve-⨟ᵒᵗʰ ⊢t₁ ⊢h₂
  ... | id O | ⊢idʳ .O = ⊢hc ⊢h₁ (preserve-⨟ᵒᵐ ⊢m₁ ⊢m₂) ⊢t₂
  ... | err ℓ | ⊢errʳ .ℓ
      with is-error?ᵒ m₁
  ...   | yes (error {ℓ′}) = ⊢hc ⊢h₁ (⊢errᵐ ℓ′) ⊢t₂
  ...   | no _             = ⊢hc ⊢h₁ (⊢errᵐ ℓ) ⊢t₂
  preserve-⨟ᵒ
      (⊢hc {h = h₁} {m = m₁} {t = t₁} ⊢h₁ ⊢m₁ ⊢t₁)
      (⊢hc {h = h₂} {m = m₂} {t = t₂} ⊢h₂ ⊢m₂ ⊢t₂)
      | G ？ ℓ | ⊢projʳ g .ℓ
      with m₁ | ⊢m₁ | h₁ | ⊢h₁
  ...   | err ℓ′ | ⊢errᵐ .ℓ′ | h₁′   | ⊢h₁′  = ⊢hc ⊢h₁′ (⊢errᵐ ℓ′) ⊢t₂
  ...   | id⋆   | ⊢id⋆ᵐ     | id ⋆ | ⊢idʰ ⋆ = ⊢hc (⊢projʰ g ℓ) ⊢m₂ ⊢t₂
  preserve-⨟ᵒ
      (⊢hc {h = h₁} {m = m₁} {t = t₁} ⊢h₁ ⊢m₁ ⊢t₁)
      (⊢hc {h = h₂} {m = m₂} {t = t₂} ⊢h₂ ⊢m₂ ⊢t₂)
      | G ！ | ⊢injʳ g
      with m₂ | ⊢m₂ | is-error?ᵒ m₁ | t₂ | ⊢t₂
  ...   | err ℓ | ⊢errᵐ .ℓ | yes (error {ℓ′}) | t₂′  | ⊢t₂′   = ⊢hc ⊢h₁ (⊢errᵐ ℓ′) ⊢t₂′
  ...   | err ℓ | ⊢errᵐ .ℓ | no _             | t₂′  | ⊢t₂′   = ⊢hc ⊢h₁ (⊢errᵐ ℓ) ⊢t₂′
  ...   | id⋆  | ⊢id⋆ᵐ     | _                | id ⋆ | ⊢idᵗ ⋆ = ⊢hc ⊢h₁ ⊢m₁ (⊢injᵗ g)
