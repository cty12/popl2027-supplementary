module LambdaAlphaRefStar.Theories.CoercionEquationalTheory.Code.Preservation where

open import Data.Product using (_×_) renaming (_,_ to ⟨_,_⟩)

open import LambdaAlphaRefStar.Theories.CoercionEquationalTheory.Code.SyntaxAndTyping
open import LambdaAlphaRefStar.Theories.CoercionEquationalTheory.Code.Semantics


private

  Preserveᵒ : OCoercion → OCoercion → Set
  Preserveᵒ c d =
    ∀ {O₁ O₂}
    → ⊢ᵒ c ⦂ O₁ ⇒ O₂
      -----------------
    → ⊢ᵒ d ⦂ O₁ ⇒ O₂

  preserve-≡ᵒ-both : ∀ {c d}
    → ⊢ᵒ c ≡ d
      -------------------------------
    → Preserveᵒ c d × Preserveᵒ d c
  preserve-≡ᵒ-both refl =
    ⟨ (λ ⊢c → ⊢c)
    , (λ ⊢c → ⊢c)
    ⟩
  preserve-≡ᵒ-both (sym c≡d) with preserve-≡ᵒ-both c≡d
  ... | ⟨ c⇒d , d⇒c ⟩ =
    ⟨ d⇒c
    , c⇒d
    ⟩
  preserve-≡ᵒ-both (trans c₁≡c₂ c₂≡c₃)
    with preserve-≡ᵒ-both c₁≡c₂ | preserve-≡ᵒ-both c₂≡c₃
  ... | ⟨ c₁⇒c₂ , c₂⇒c₁ ⟩ | ⟨ c₂⇒c₃ , c₃⇒c₂ ⟩ =
    ⟨ (λ ⊢c₁ → c₂⇒c₃ (c₁⇒c₂ ⊢c₁))
    , (λ ⊢c₃ → c₂⇒c₁ (c₃⇒c₂ ⊢c₃))
    ⟩
  preserve-≡ᵒ-both assoc =
    ⟨ (λ { (⊢seqᵒ (⊢seqᵒ ⊢c ⊢d) ⊢e) → ⊢seqᵒ ⊢c (⊢seqᵒ ⊢d ⊢e) })
    , (λ { (⊢seqᵒ ⊢c (⊢seqᵒ ⊢d ⊢e)) → ⊢seqᵒ (⊢seqᵒ ⊢c ⊢d) ⊢e })
    ⟩
  preserve-≡ᵒ-both (cong {f = □⨾ d} c≡c′)
    with preserve-≡ᵒ-both c≡c′
  ... | ⟨ c⇒c′ , c′⇒c ⟩ =
    ⟨ (λ { (⊢seqᵒ ⊢c ⊢d) → ⊢seqᵒ (c⇒c′ ⊢c) ⊢d })
    , (λ { (⊢seqᵒ ⊢c′ ⊢d) → ⊢seqᵒ (c′⇒c ⊢c′) ⊢d })
    ⟩
  preserve-≡ᵒ-both (cong {f = c ⨾□} d≡d′)
    with preserve-≡ᵒ-both d≡d′
  ... | ⟨ d⇒d′ , d′⇒d ⟩ =
    ⟨ (λ { (⊢seqᵒ ⊢c ⊢d) → ⊢seqᵒ ⊢c (d⇒d′ ⊢d) })
    , (λ { (⊢seqᵒ ⊢c ⊢d′) → ⊢seqᵒ ⊢c (d′⇒d ⊢d′) })
    ⟩
  preserve-≡ᵒ-both (cong {f = □⇒ d} c≡c′)
    with preserve-≡ᵒ-both c≡c′
  ... | ⟨ c⇒c′ , c′⇒c ⟩ =
    ⟨ (λ { (⊢funᵒ ⊢c ⊢d) → ⊢funᵒ (c⇒c′ ⊢c) ⊢d })
    , (λ { (⊢funᵒ ⊢c′ ⊢d) → ⊢funᵒ (c′⇒c ⊢c′) ⊢d })
    ⟩
  preserve-≡ᵒ-both (cong {f = c ⇒□} d≡d′)
    with preserve-≡ᵒ-both d≡d′
  ... | ⟨ d⇒d′ , d′⇒d ⟩ =
    ⟨ (λ { (⊢funᵒ ⊢c ⊢d) → ⊢funᵒ ⊢c (d⇒d′ ⊢d) })
    , (λ { (⊢funᵒ ⊢c ⊢d′) → ⊢funᵒ ⊢c (d′⇒d ⊢d′) })
    ⟩

  preserve-⟶ᵒ : ∀ {O₁ O₂ c d}
    → ⊢ᵒ c ⟶ d
    → ⊢ᵒ c ⦂ O₁ ⇒ O₂
      -----------------
    → ⊢ᵒ d ⦂ O₁ ⇒ O₂
  preserve-⟶ᵒ inj-proj (⊢seqᵒ (⊢injᵒ g) (⊢projᵒ ℓ h)) =
    ⊢idᵒ _
  preserve-⟶ᵒ (inj-proj-err _) (⊢seqᵒ (⊢injᵒ g) (⊢projᵒ ℓ h)) =
    ⊢errᵒ _ _ ℓ
  preserve-⟶ᵒ seq-fun (⊢seqᵒ (⊢funᵒ ⊢c₁ ⊢c₂) (⊢funᵒ ⊢d₁ ⊢d₂)) =
    ⊢funᵒ (⊢seqᵒ ⊢d₁ ⊢c₁) (⊢seqᵒ ⊢c₂ ⊢d₂)
  preserve-⟶ᵒ id-left (⊢seqᵒ (⊢idᵒ _) ⊢c) =
    ⊢c
  preserve-⟶ᵒ id-right (⊢seqᵒ ⊢c (⊢idᵒ _)) =
    ⊢c
  preserve-⟶ᵒ id-fun (⊢funᵒ (⊢idᵒ O₁) (⊢idᵒ O₂)) =
    ⊢idᵒ (O₁ ⇒ O₂)
  preserve-⟶ᵒ (ξ {f = □⨾ d} c⟶c′) (⊢seqᵒ ⊢c ⊢d) =
    ⊢seqᵒ (preserve-⟶ᵒ c⟶c′ ⊢c) ⊢d
  preserve-⟶ᵒ (ξ {f = c ⨾□} d⟶d′) (⊢seqᵒ ⊢c ⊢d) =
    ⊢seqᵒ ⊢c (preserve-⟶ᵒ d⟶d′ ⊢d)
  preserve-⟶ᵒ (ξ {f = □⇒ d} c⟶c′) (⊢funᵒ ⊢c ⊢d) =
    ⊢funᵒ (preserve-⟶ᵒ c⟶c′ ⊢c) ⊢d
  preserve-⟶ᵒ (ξ {f = c ⇒□} d⟶d′) (⊢funᵒ ⊢c ⊢d) =
    ⊢funᵒ ⊢c (preserve-⟶ᵒ d⟶d′ ⊢d)
  preserve-⟶ᵒ (ξ-err {f = □⨾ d} {ℓ = ℓ}) (⊢seqᵒ (⊢errᵒ _ _ ℓ) ⊢d) =
    ⊢errᵒ _ _ ℓ
  preserve-⟶ᵒ (ξ-err {f = Gᵒ !⨾□ g} {ℓ = ℓ}) (⊢seqᵒ (⊢injᵒ g) (⊢errᵒ _ _ ℓ)) =
    ⊢errᵒ _ _ ℓ
  preserve-⟶ᵒ (ξ-err {f = □⇒ d} {ℓ = ℓ}) (⊢funᵒ (⊢errᵒ _ _ ℓ) ⊢d) =
    ⊢errᵒ _ _ ℓ
  preserve-⟶ᵒ (ξ-err {f = c ⇒□} {ℓ = ℓ}) (⊢funᵒ ⊢c (⊢errᵒ _ _ ℓ)) =
    ⊢errᵒ _ _ ℓ

preserve-≡ᵒ : ∀ {O₁ O₂ c d}
  → ⊢ᵒ c ≡ d
  → ⊢ᵒ c ⦂ O₁ ⇒ O₂
    -----------------
  → ⊢ᵒ d ⦂ O₁ ⇒ O₂
preserve-≡ᵒ c≡d ⊢c with preserve-≡ᵒ-both c≡d
... | ⟨ c⇒d , _ ⟩ = c⇒d ⊢c

preserve-⟼ᵒ : ∀ {O₁ O₂ c d}
  → ⊢ᵒ c ⟼ d
  → ⊢ᵒ c ⦂ O₁ ⇒ O₂
    ------------------
  → ⊢ᵒ d ⦂ O₁ ⇒ O₂
preserve-⟼ᵒ (red c≡c′ c′⟶d′ d′≡d) ⊢c =
  preserve-≡ᵒ d′≡d (preserve-⟶ᵒ c′⟶d′ (preserve-≡ᵒ c≡c′ ⊢c))
