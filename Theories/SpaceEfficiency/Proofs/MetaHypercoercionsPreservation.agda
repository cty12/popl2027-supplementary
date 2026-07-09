module Theories.SpaceEfficiency.Proofs.MetaHypercoercionsPreservation where

open import Theories.EnvClassifiers
open import Theories.MetaTypes
open import Theories.SpaceEfficiency.MetaHypercoercions
open import Relation.Binary.PropositionalEquality using (refl)
open import Relation.Nullary using (yes; no)

import Theories.SpaceEfficiency.ECHypercoercions as EHC
import Theories.SpaceEfficiency.ObjectHypercoercions as OHC
import Theories.SpaceEfficiency.Proofs.ECHypercoercionsPreservation as EHCP
import Theories.SpaceEfficiency.Proofs.ObjectHypercoercionsPreservation as OHCP


-- Composition preserves extrinsic typing.
preserve-⨟ᵐᵗʰ : ∀ {Δ t h A B C}
  → Δ ⊢ᵐᵗ t ⦂ A ⇒ B
  → Δ ⊢ᵐʰ h ⦂ B ⇒ C
    ---------------------------------------------
  → Δ ⊢ᵐʳ (t ⨟ᵐᵗʰ h) ⦂ A ⇒ C
preserve-⨟ᵐᵗʰ (⊢idᵗ A) (⊢projʰ g ℓ) = ⊢projʳ g ℓ
preserve-⨟ᵐᵗʰ (⊢idᵗ A) (⊢idʰ .A) = ⊢idʳ A
preserve-⨟ᵐᵗʰ (⊢injᵗ g) (⊢idʰ ⋆) = ⊢injʳ g
preserve-⨟ᵐᵗʰ (⊢injᵗ {G = G₁} g₁) (⊢projʰ {G = G₂} g₂ ℓ) with G₁ ≡? G₂
... | yes refl = ⊢idʳ G₁
... | no _     = ⊢errʳ ℓ


mutual
  preserve-⨟ᵐᵐ : ∀ {Δ Θ m₁ m₂ A B C}
    → Δ ; Θ ⊢ᵐᵐ m₁ ⦂ A ⇒ B
    → Δ ; Θ ⊢ᵐᵐ m₂ ⦂ B ⇒ C
      ---------------------------------------------
    → Δ ; Θ ⊢ᵐᵐ (Θ ⊢ m₁ ⨟ᵐᵐ m₂) ⦂ A ⇒ C
  preserve-⨟ᵐᵐ ⊢id⋆ᵐ ⊢m₂ = ⊢m₂
  preserve-⨟ᵐᵐ (⊢idιᵐ ι) ⊢m₂ = ⊢m₂
  preserve-⨟ᵐᵐ (⊢errᵐ ℓ) ⊢m₂ = ⊢errᵐ ℓ
  preserve-⨟ᵐᵐ (⊢funᵐ ⊢c₁₁ ⊢c₁₂) (⊢errᵐ ℓ) = ⊢errᵐ ℓ
  preserve-⨟ᵐᵐ (⊢funᵐ ⊢c₁₁ ⊢c₁₂) (⊢funᵐ ⊢c₂₁ ⊢c₂₂) =
    ⊢funᵐ (preserve-⨟ᵐ ⊢c₂₁ ⊢c₁₁) (preserve-⨟ᵐ ⊢c₁₂ ⊢c₂₂)
  preserve-⨟ᵐᵐ (⊢refᵐ ⊢c₁₁ ⊢c₁₂) (⊢errᵐ ℓ) = ⊢errᵐ ℓ
  preserve-⨟ᵐᵐ (⊢refᵐ ⊢c₁₁ ⊢c₁₂) (⊢refᵐ ⊢c₂₁ ⊢c₂₂) =
    ⊢refᵐ (preserve-⨟ᵐ ⊢c₂₁ ⊢c₁₁) (preserve-⨟ᵐ ⊢c₁₂ ⊢c₂₂)
  preserve-⨟ᵐᵐ (⊢forallᵐ ⊢c₁) (⊢errᵐ ℓ) = ⊢errᵐ ℓ
  preserve-⨟ᵐᵐ (⊢forallᵐ {c = c₁} ⊢c₁) (⊢forallᵐ {c = c₂} ⊢c₂) =
    ⊢forallᵐ (preserve-⨟ᵐ ⊢c₁ ⊢c₂)
  preserve-⨟ᵐᵐ (⊢subᵐ e₁ e₂ ⊢c₁) (⊢errᵐ ℓ) = ⊢errᵐ ℓ
  preserve-⨟ᵐᵐ (⊢subᵐ e₁ e₂ ⊢c₁) (⊢subᵐ .e₁ .e₂ ⊢c₂) =
    ⊢subᵐ e₁ e₂ (preserve-⨟ᵐ ⊢c₁ ⊢c₂)
  preserve-⨟ᵐᵐ (⊢codeᵐ {cᵒ = c₁ᵒ} {cᵉ = c₁ᵉ} ⊢c₁ᵒ ⊢c₁ᵉ) (⊢errᵐ ℓ) = ⊢errᵐ ℓ
  preserve-⨟ᵐᵐ {Θ = Θ} (⊢codeᵐ {cᵒ = c₁ᵒ} {cᵉ = c₁ᵉ} ⊢c₁ᵒ ⊢c₁ᵉ)
      (⊢codeᵐ {cᵒ = c₂ᵒ} {cᵉ = c₂ᵉ} ⊢c₂ᵒ ⊢c₂ᵉ)
      with OHC._⨟ᵒ_ c₁ᵒ c₂ᵒ | OHCP.preserve-⨟ᵒ ⊢c₁ᵒ ⊢c₂ᵒ
         | EHC._⊢_⨟ᵉ_ Θ c₁ᵉ c₂ᵉ | EHCP.preserve-⨟ᵉ {Θ = Θ} ⊢c₁ᵉ ⊢c₂ᵉ
  ... | OHC._⨾_⨾_ hᵒ mᵒ tᵒ | OHC.⊢hc ⊢hᵒ ⊢mᵒ ⊢tᵒ
      | EHC._⨾_⨾_ hᵉ mᵉ tᵉ | EHC.⊢hc ⊢hᵉ ⊢mᵉ ⊢tᵉ
      with OHC.is-error?ᵒ mᵒ | mᵉ | ⊢mᵉ
  ...   | yes (OHC.error {ℓ}) | _        | _              = ⊢errᵐ ℓ
  ...   | no _                | EHC.err ℓ | EHC.⊢errᵐ .ℓ = ⊢errᵐ ℓ
  ...   | no _                | EHC._↑_ _ _ | ⊢mᵉ′ =
    ⊢codeᵐ (OHC.⊢hc ⊢hᵒ ⊢mᵒ ⊢tᵒ) (EHC.⊢hc ⊢hᵉ ⊢mᵉ′ ⊢tᵉ)

  preserve-⨟ᵐ : ∀ {Δ Θ c₁ c₂ A B C}
    → Δ ; Θ ⊢ᵐ c₁ ⦂ A ⇒ B
    → Δ ; Θ ⊢ᵐ c₂ ⦂ B ⇒ C
      ---------------------------------------------
    → Δ ; Θ ⊢ᵐ (Θ ⊢ c₁ ⨟ᵐ c₂) ⦂ A ⇒ C
  preserve-⨟ᵐ {Θ = Θ}
      (⊢hc {h = h₁} {m = m₁} {t = t₁} ⊢h₁ ⊢m₁ ⊢t₁)
      (⊢hc {h = h₂} {m = m₂} {t = t₂} ⊢h₂ ⊢m₂ ⊢t₂)
      with t₁ ⨟ᵐᵗʰ h₂ | preserve-⨟ᵐᵗʰ ⊢t₁ ⊢h₂
  ... | id A | ⊢idʳ .A = ⊢hc ⊢h₁ (preserve-⨟ᵐᵐ ⊢m₁ ⊢m₂) ⊢t₂
  ... | err ℓ | ⊢errʳ .ℓ
      with is-error? m₁
  ...   | yes (error {ℓ′}) = ⊢hc ⊢h₁ (⊢errᵐ ℓ′) ⊢t₂
  ...   | no _             = ⊢hc ⊢h₁ (⊢errᵐ ℓ) ⊢t₂
  preserve-⨟ᵐ {Θ = Θ}
      (⊢hc {h = h₁} {m = m₁} {t = t₁} ⊢h₁ ⊢m₁ ⊢t₁)
      (⊢hc {h = h₂} {m = m₂} {t = t₂} ⊢h₂ ⊢m₂ ⊢t₂)
      | G ？ ℓ | ⊢projʳ g .ℓ
      with m₁ | ⊢m₁ | h₁ | ⊢h₁
  ...   | err ℓ′ | ⊢errᵐ .ℓ′ | h₁′   | ⊢h₁′  = ⊢hc ⊢h₁′ (⊢errᵐ ℓ′) ⊢t₂
  ...   | id⋆   | ⊢id⋆ᵐ     | id ⋆ | ⊢idʰ ⋆ = ⊢hc (⊢projʰ g ℓ) ⊢m₂ ⊢t₂
  preserve-⨟ᵐ {Θ = Θ}
      (⊢hc {h = h₁} {m = m₁} {t = t₁} ⊢h₁ ⊢m₁ ⊢t₁)
      (⊢hc {h = h₂} {m = m₂} {t = t₂} ⊢h₂ ⊢m₂ ⊢t₂)
      | G ！ | ⊢injʳ g
      with m₂ | ⊢m₂ | is-error? m₁ | t₂ | ⊢t₂
  ...   | err ℓ | ⊢errᵐ .ℓ | yes (error {ℓ′}) | t₂′  | ⊢t₂′   = ⊢hc ⊢h₁ (⊢errᵐ ℓ′) ⊢t₂′
  ...   | err ℓ | ⊢errᵐ .ℓ | no _             | t₂′  | ⊢t₂′   = ⊢hc ⊢h₁ (⊢errᵐ ℓ) ⊢t₂′
  ...   | id⋆  | ⊢id⋆ᵐ     | _                | id ⋆ | ⊢idᵗ ⋆ = ⊢hc ⊢h₁ ⊢m₁ (⊢injᵗ g)
