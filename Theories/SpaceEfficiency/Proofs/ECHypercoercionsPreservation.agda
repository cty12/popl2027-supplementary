module LambdaAlphaRefStar.Theories.SpaceEfficiency.Proofs.ECHypercoercionsPreservation where

open import LambdaAlphaRefStar.Theories.EnvClassifiers
open import LambdaAlphaRefStar.Theories.ECSubtypeDecidable using (ec-<:⋆?)
open import LambdaAlphaRefStar.Theories.SpaceEfficiency.ECHypercoercions
open import Relation.Nullary using (yes; no)


-- Composition preserves extrinsic typing.
preserve-⨟ᵉᵗʰ : ∀ {Δ Θ t h ê₁ ê₂ ê₃}
  → Δ ⊢ᵉᵗ t ⦂ ê₁ ⇒ ê₂
  → Δ ⊢ᵉʰ h ⦂ ê₂ ⇒ ê₃
    ---------------------------------------------
  → Δ ; Θ ⊢ᵉʳ (Θ ⊢ t ⨟ᵉᵗʰ h) ⦂ ê₁ ⇒ ê₃
preserve-⨟ᵉᵗʰ {Θ = Θ} (⊢injᵗ e₁) (⊢projʰ e₂ ℓ) with ec-<:⋆? Θ (ec e₁) (ec e₂)
... | yes e₁<:e₂ = ⊢subʳ e₁<:e₂
... | no  _       = ⊢errʳ ℓ
preserve-⨟ᵉᵗʰ (⊢injᵗ e) (⊢idʰ ⋆) = ⊢injʳ e
preserve-⨟ᵉᵗʰ (⊢idᵗ ê) (⊢projʰ e ℓ) = ⊢projʳ e ℓ
preserve-⨟ᵉᵗʰ (⊢idᵗ ê) (⊢idʰ .ê) = ⊢subʳ (<:⋆-refl ê)


preserve-⨟ᵉᵐ : ∀ {Δ Θ m₁ m₂ ê₁ ê₂ ê₃}
  → Δ ; Θ ⊢ᵉᵐ m₁ ⦂ ê₁ ⇒ ê₂
  → Δ ; Θ ⊢ᵉᵐ m₂ ⦂ ê₂ ⇒ ê₃
    ---------------------------------------------
  → Δ ; Θ ⊢ᵉᵐ (m₁ ⨟ᵉᵐ m₂) ⦂ ê₁ ⇒ ê₃
preserve-⨟ᵉᵐ (⊢errᵐ ℓ) m₂ = ⊢errᵐ ℓ
preserve-⨟ᵉᵐ (⊢subᵐ ê₁<:ê₂) (⊢errᵐ ℓ) = ⊢errᵐ ℓ
preserve-⨟ᵉᵐ (⊢subᵐ ê₁<:ê₂) (⊢subᵐ ê₂<:ê₃) =
  ⊢subᵐ (<:⋆-trans ê₁<:ê₂ ê₂<:ê₃)


preserve-⨟ᵉ : ∀ {Δ Θ c₁ c₂ ê₁ ê₂ ê₃}
  → Δ ; Θ ⊢ᵉ c₁ ⦂ ê₁ ⇒ ê₂
  → Δ ; Θ ⊢ᵉ c₂ ⦂ ê₂ ⇒ ê₃
    ---------------------------------------------
  → Δ ; Θ ⊢ᵉ (Θ ⊢ c₁ ⨟ᵉ c₂) ⦂ ê₁ ⇒ ê₃
preserve-⨟ᵉ {Θ = Θ}
    (⊢hc {h = h₁} {m = m₁} {t = t₁} ⊢h₁ ⊢m₁ ⊢t₁)
    (⊢hc {h = h₂} {m = m₂} {t = t₂} ⊢h₂ ⊢m₂ ⊢t₂)
    with Θ ⊢ t₁ ⨟ᵉᵗʰ h₂ | preserve-⨟ᵉᵗʰ {Θ = Θ} ⊢t₁ ⊢h₂
... | ê₄ ↑ ê₅ | ⊢subʳ ê₄<:ê₅ =
  ⊢hc ⊢h₁ (preserve-⨟ᵉᵐ ⊢m₁ (preserve-⨟ᵉᵐ (⊢subᵐ ê₄<:ê₅) ⊢m₂)) ⊢t₂
... | err ℓ | ⊢errʳ .ℓ
    with m₁ | ⊢m₁
...   | err ℓ′ | ⊢errᵐ .ℓ′ = ⊢hc ⊢h₁ (⊢errᵐ ℓ′) ⊢t₂
...   | _ ↑ _  | ⊢subᵐ _   = ⊢hc ⊢h₁ (⊢errᵐ ℓ) ⊢t₂
preserve-⨟ᵉ {Θ = Θ}
    (⊢hc {h = h₁} {m = m₁} {t = t₁} ⊢h₁ ⊢m₁ ⊢t₁)
    (⊢hc {h = h₂} {m = m₂} {t = t₂} ⊢h₂ ⊢m₂ ⊢t₂)
    | e ？ ℓ | ⊢projʳ .e .ℓ
    with m₁ | ⊢m₁ | h₁ | ⊢h₁
...   | err ℓ′ | ⊢errᵐ .ℓ′ | h₁′   | ⊢h₁′  = ⊢hc ⊢h₁′ (⊢errᵐ ℓ′) ⊢t₂
...   | _ ↑ _  | ⊢subᵐ _   | id ⋆ | ⊢idʰ ⋆ = ⊢hc (⊢projʰ e ℓ) ⊢m₂ ⊢t₂
preserve-⨟ᵉ {Θ = Θ}
    (⊢hc {h = h₁} {m = m₁} {t = t₁} ⊢h₁ ⊢m₁ ⊢t₁)
    (⊢hc {h = h₂} {m = m₂} {t = t₂} ⊢h₂ ⊢m₂ ⊢t₂)
    | e ！ | ⊢injʳ .e
    with m₁ | ⊢m₁ | m₂ | ⊢m₂ | t₂ | ⊢t₂
...   | err ℓ | ⊢errᵐ .ℓ | _     | _        | t₂′  | ⊢t₂′   = ⊢hc ⊢h₁ (⊢errᵐ ℓ) ⊢t₂′
...   | _ ↑ _ | ⊢subᵐ _  | err ℓ | ⊢errᵐ .ℓ | t₂′  | ⊢t₂′   = ⊢hc ⊢h₁ (⊢errᵐ ℓ) ⊢t₂′
...   | ê ↑ .(ec e) | ⊢subᵐ ê<:e | .⋆ ↑ .⋆ | ⊢subᵐ <:-⋆ | id ⋆ | ⊢idᵗ ⋆ =
  ⊢hc ⊢h₁ (⊢subᵐ ê<:e) (⊢injᵗ e)
