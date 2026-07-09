module LambdaAlphaRefStar.Theories.CoercionEquationalTheory.EC.Preservation where

open import Data.Product using (_×_) renaming (_,_ to ⟨_,_⟩)

open import LambdaAlphaRefStar.Theories.CoercionEquationalTheory.EC.SyntaxAndTyping
open import LambdaAlphaRefStar.Theories.CoercionEquationalTheory.EC.Semantics


private

  Preserveᵉ : ECCoercion → ECCoercion → Set
  Preserveᵉ c d =
    ∀ {Δ Θ ê₁ ê₂}
    → Δ ; Θ ⊢ᵉ c ⦂ ê₁ ⇒ ê₂
      -----------------------
    → Δ ; Θ ⊢ᵉ d ⦂ ê₁ ⇒ ê₂

  preserve-≡ᵉ-both : ∀ {c d}
    → ⊢ᵉ c ≡ d
      -------------------------------
    → Preserveᵉ c d × Preserveᵉ d c
  preserve-≡ᵉ-both refl =
    ⟨ (λ ⊢c → ⊢c)
    , (λ ⊢c → ⊢c)
    ⟩
  preserve-≡ᵉ-both (sym c≡d) with preserve-≡ᵉ-both c≡d
  ... | ⟨ c⇒d , d⇒c ⟩ =
    ⟨ d⇒c
    , c⇒d
    ⟩
  preserve-≡ᵉ-both (trans c₁≡c₂ c₂≡c₃)
    with preserve-≡ᵉ-both c₁≡c₂ | preserve-≡ᵉ-both c₂≡c₃
  ... | ⟨ c₁⇒c₂ , c₂⇒c₁ ⟩ | ⟨ c₂⇒c₃ , c₃⇒c₂ ⟩ =
    ⟨ (λ ⊢c₁ → c₂⇒c₃ (c₁⇒c₂ ⊢c₁))
    , (λ ⊢c₃ → c₂⇒c₁ (c₃⇒c₂ ⊢c₃))
    ⟩
  preserve-≡ᵉ-both assoc =
    ⟨ (λ { (⊢seqᵉ (⊢seqᵉ ⊢c ⊢d) ⊢e) → ⊢seqᵉ ⊢c (⊢seqᵉ ⊢d ⊢e) })
    , (λ { (⊢seqᵉ ⊢c (⊢seqᵉ ⊢d ⊢e)) → ⊢seqᵉ (⊢seqᵉ ⊢c ⊢d) ⊢e })
    ⟩
  preserve-≡ᵉ-both (cong {f = □⨾ d} c≡c′)
    with preserve-≡ᵉ-both c≡c′
  ... | ⟨ c⇒c′ , c′⇒c ⟩ =
    ⟨ (λ { (⊢seqᵉ ⊢c ⊢d) → ⊢seqᵉ (c⇒c′ ⊢c) ⊢d })
    , (λ { (⊢seqᵉ ⊢c′ ⊢d) → ⊢seqᵉ (c′⇒c ⊢c′) ⊢d })
    ⟩
  preserve-≡ᵉ-both (cong {f = c ⨾□} d≡d′)
    with preserve-≡ᵉ-both d≡d′
  ... | ⟨ d⇒d′ , d′⇒d ⟩ =
    ⟨ (λ { (⊢seqᵉ ⊢c ⊢d) → ⊢seqᵉ ⊢c (d⇒d′ ⊢d) })
    , (λ { (⊢seqᵉ ⊢c ⊢d′) → ⊢seqᵉ ⊢c (d′⇒d ⊢d′) })
    ⟩

  preserve-⟶ᵉ : ∀ {Δ Θ ê₁ ê₂ c d}
    → Θ ⊢ᵉ c ⟶ d
    → Δ ; Θ ⊢ᵉ c ⦂ ê₁ ⇒ ê₂
      -----------------------
    → Δ ; Θ ⊢ᵉ d ⦂ ê₁ ⇒ ê₂
  preserve-⟶ᵉ (inj-proj e<:e′) (⊢seqᵉ (⊢injᵉ e ⊢e) (⊢projᵉ e′ ⊢e′ ℓ)) =
    ⊢subᵉ (wf-ec ⊢e) (wf-ec ⊢e′) (<:-ec e<:e′)
  preserve-⟶ᵉ (inj-proj-err _) (⊢seqᵉ (⊢injᵉ e ⊢e) (⊢projᵉ e′ ⊢e′ ℓ)) =
    ⊢errᵉ (wf-ec ⊢e) (wf-ec ⊢e′) ℓ
  preserve-⟶ᵉ (seq ê₁<:ê₂ ê₂<:ê₃) (⊢seqᵉ (⊢subᵉ ⊢ê₁ _ _) (⊢subᵉ _ ⊢ê₃ _)) =
    ⊢subᵉ ⊢ê₁ ⊢ê₃ (<:⋆-trans ê₁<:ê₂ ê₂<:ê₃)
  preserve-⟶ᵉ err (⊢seqᵉ ⊢c (⊢errᵉ _ ⊢ê₃ ℓ)) =
    ⊢errᵉ (wf-domᵉ ⊢c) ⊢ê₃ ℓ
  preserve-⟶ᵉ (ξ {f = □⨾ d} c⟶c′) (⊢seqᵉ ⊢c ⊢d) =
    ⊢seqᵉ (preserve-⟶ᵉ c⟶c′ ⊢c) ⊢d
  preserve-⟶ᵉ (ξ {f = c ⨾□} d⟶d′) (⊢seqᵉ ⊢c ⊢d) =
    ⊢seqᵉ ⊢c (preserve-⟶ᵉ d⟶d′ ⊢d)
  preserve-⟶ᵉ (ξ-err {f = □⨾ d} {ℓ = ℓ}) (⊢seqᵉ (⊢errᵉ ⊢ê₁ _ ℓ) ⊢d) =
    ⊢errᵉ ⊢ê₁ (wf-codᵉ ⊢d) ℓ
  preserve-⟶ᵉ (ξ-err {f = e !⨾□} {ℓ = ℓ}) (⊢seqᵉ (⊢injᵉ e ⊢e) (⊢errᵉ _ ⊢ê₂ ℓ)) =
    ⊢errᵉ (wf-ec ⊢e) ⊢ê₂ ℓ

preserve-≡ᵉ : ∀ {Δ Θ ê₁ ê₂ c d}
  → ⊢ᵉ c ≡ d
  → Δ ; Θ ⊢ᵉ c ⦂ ê₁ ⇒ ê₂
    ---------------------------
  → Δ ; Θ ⊢ᵉ d ⦂ ê₁ ⇒ ê₂
preserve-≡ᵉ c≡d ⊢c with preserve-≡ᵉ-both c≡d
... | ⟨ c⇒d , _ ⟩ = c⇒d ⊢c

preserve-⟼ᵉ : ∀ {Δ Θ ê₁ ê₂ c d}
  → Θ ⊢ᵉ c ⟼ d
  → Δ ; Θ ⊢ᵉ c ⦂ ê₁ ⇒ ê₂
    ------------------------
  → Δ ; Θ ⊢ᵉ d ⦂ ê₁ ⇒ ê₂
preserve-⟼ᵉ (red c≡c′ c′⟶d′ d′≡d) ⊢c =
  preserve-≡ᵉ d′≡d (preserve-⟶ᵉ c′⟶d′ (preserve-≡ᵉ c≡c′ ⊢c))
