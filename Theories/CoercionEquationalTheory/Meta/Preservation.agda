module Theories.CoercionEquationalTheory.Meta.Preservation where

open import Data.Product using (_×_) renaming (_,_ to ⟨_,_⟩)

import Theories.CoercionEquationalTheory.EC.SyntaxAndTyping as EC
import Theories.CoercionEquationalTheory.Code.SyntaxAndTyping as OC
open import Theories.CoercionEquationalTheory.Meta.SyntaxAndTyping
open import Theories.CoercionEquationalTheory.EC.Preservation
  using (preserve-≡ᵉ; preserve-⟼ᵉ)
open import Theories.CoercionEquationalTheory.Code.Preservation
  using (preserve-≡ᵒ; preserve-⟼ᵒ)
import Theories.CoercionEquationalTheory.EC.Semantics as ECS
import Theories.CoercionEquationalTheory.Code.Semantics as OCS
import Theories.CoercionEquationalTheory.Meta.Semantics as MCS


private

  Preserveᵐ : MCoercion → MCoercion → Set
  Preserveᵐ c d =
    ∀ {Δ Θ A B}
    → Δ ; Θ ⊢ᵐ c ⦂ A ⇒ B
      -----------------------
    → Δ ; Θ ⊢ᵐ d ⦂ A ⇒ B

  preserve-≡ᵐ-both : ∀ {c d}
    → MCS.⊢ᵐ c ≡ d
      -------------------------------
    → Preserveᵐ c d × Preserveᵐ d c
  preserve-≡ᵐ-both MCS.refl =
    ⟨ (λ ⊢c → ⊢c)
    , (λ ⊢c → ⊢c)
    ⟩
  preserve-≡ᵐ-both (MCS.sym c≡d) with preserve-≡ᵐ-both c≡d
  ... | ⟨ c⇒d , d⇒c ⟩ =
    ⟨ d⇒c
    , c⇒d
    ⟩
  preserve-≡ᵐ-both (MCS.trans c₁≡c₂ c₂≡c₃)
    with preserve-≡ᵐ-both c₁≡c₂ | preserve-≡ᵐ-both c₂≡c₃
  ... | ⟨ c₁⇒c₂ , c₂⇒c₁ ⟩ | ⟨ c₂⇒c₃ , c₃⇒c₂ ⟩ =
    ⟨ (λ ⊢c₁ → c₂⇒c₃ (c₁⇒c₂ ⊢c₁))
    , (λ ⊢c₃ → c₂⇒c₁ (c₃⇒c₂ ⊢c₃))
    ⟩
  preserve-≡ᵐ-both MCS.assoc =
    ⟨ (λ { (⊢seqᵐ (⊢seqᵐ ⊢c ⊢d) ⊢e) → ⊢seqᵐ ⊢c (⊢seqᵐ ⊢d ⊢e) })
    , (λ { (⊢seqᵐ ⊢c (⊢seqᵐ ⊢d ⊢e)) → ⊢seqᵐ (⊢seqᵐ ⊢c ⊢d) ⊢e })
    ⟩
  preserve-≡ᵐ-both (MCS.‶ cᵒ≡dᵒ ″ cᵉ≡dᵉ) =
    ⟨ (λ { (⊢codeᵐ ⊢cᵒ ⊢cᵉ) → ⊢codeᵐ (preserve-≡ᵒ cᵒ≡dᵒ ⊢cᵒ) (preserve-≡ᵉ cᵉ≡dᵉ ⊢cᵉ) })
    , (λ { (⊢codeᵐ ⊢dᵒ ⊢dᵉ) → ⊢codeᵐ (preserve-≡ᵒ (OCS.sym cᵒ≡dᵒ) ⊢dᵒ) (preserve-≡ᵉ (ECS.sym cᵉ≡dᵉ) ⊢dᵉ) })
    ⟩
  preserve-≡ᵐ-both (MCS.cong {f = MCS.□⨾ d} c≡c′)
    with preserve-≡ᵐ-both c≡c′
  ... | ⟨ c⇒c′ , c′⇒c ⟩ =
    ⟨ (λ { (⊢seqᵐ ⊢c ⊢d) → ⊢seqᵐ (c⇒c′ ⊢c) ⊢d })
    , (λ { (⊢seqᵐ ⊢c′ ⊢d) → ⊢seqᵐ (c′⇒c ⊢c′) ⊢d })
    ⟩
  preserve-≡ᵐ-both (MCS.cong {f = c MCS.⨾□} d≡d′)
    with preserve-≡ᵐ-both d≡d′
  ... | ⟨ d⇒d′ , d′⇒d ⟩ =
    ⟨ (λ { (⊢seqᵐ ⊢c ⊢d) → ⊢seqᵐ ⊢c (d⇒d′ ⊢d) })
    , (λ { (⊢seqᵐ ⊢c ⊢d′) → ⊢seqᵐ ⊢c (d′⇒d ⊢d′) })
    ⟩
  preserve-≡ᵐ-both (MCS.cong {f = MCS.□⇒ d} c≡c′)
    with preserve-≡ᵐ-both c≡c′
  ... | ⟨ c⇒c′ , c′⇒c ⟩ =
    ⟨ (λ { (⊢funᵐ ⊢c ⊢d) → ⊢funᵐ (c⇒c′ ⊢c) ⊢d })
    , (λ { (⊢funᵐ ⊢c′ ⊢d) → ⊢funᵐ (c′⇒c ⊢c′) ⊢d })
    ⟩
  preserve-≡ᵐ-both (MCS.cong {f = c MCS.⇒□} d≡d′)
    with preserve-≡ᵐ-both d≡d′
  ... | ⟨ d⇒d′ , d′⇒d ⟩ =
    ⟨ (λ { (⊢funᵐ ⊢c ⊢d) → ⊢funᵐ ⊢c (d⇒d′ ⊢d) })
    , (λ { (⊢funᵐ ⊢c ⊢d′) → ⊢funᵐ ⊢c (d′⇒d ⊢d′) })
    ⟩
  preserve-≡ᵐ-both (MCS.cong {f = MCS.ref□ d} c≡c′)
    with preserve-≡ᵐ-both c≡c′
  ... | ⟨ c⇒c′ , c′⇒c ⟩ =
    ⟨ (λ { (⊢refᵐ ⊢c ⊢d) → ⊢refᵐ (c⇒c′ ⊢c) ⊢d })
    , (λ { (⊢refᵐ ⊢c′ ⊢d) → ⊢refᵐ (c′⇒c ⊢c′) ⊢d })
    ⟩
  preserve-≡ᵐ-both (MCS.cong {f = MCS.ref c □} d≡d′)
    with preserve-≡ᵐ-both d≡d′
  ... | ⟨ d⇒d′ , d′⇒d ⟩ =
    ⟨ (λ { (⊢refᵐ ⊢c ⊢d) → ⊢refᵐ ⊢c (d⇒d′ ⊢d) })
    , (λ { (⊢refᵐ ⊢c ⊢d′) → ⊢refᵐ ⊢c (d′⇒d ⊢d′) })
    ⟩
  preserve-≡ᵐ : ∀ {c d}
    → MCS.⊢ᵐ c ≡ d
      ------------
    → Preserveᵐ c d
  preserve-≡ᵐ c≡d with preserve-≡ᵐ-both c≡d
  ... | ⟨ c⇒d , _ ⟩ = c⇒d

  preserve-⟶ᵐ : ∀ {Δ Θ A B c d}
    → Θ MCS.⊢ᵐ c ⟶ d
    → Δ ; Θ ⊢ᵐ c ⦂ A ⇒ B
      -------------------
    → Δ ; Θ ⊢ᵐ d ⦂ A ⇒ B
  preserve-⟶ᵐ MCS.inj-proj (⊢seqᵐ (⊢injᵐ ⊢G g) (⊢projᵐ _ ℓ h)) =
    ⊢idᵐ _ ⊢G
  preserve-⟶ᵐ (MCS.inj-proj-err _) (⊢seqᵐ (⊢injᵐ ⊢G g) (⊢projᵐ ⊢H ℓ h)) =
    ⊢errᵐ ⊢G ⊢H ℓ
  preserve-⟶ᵐ MCS.seq-fun (⊢seqᵐ (⊢funᵐ ⊢c₁ ⊢c₂) (⊢funᵐ ⊢d₁ ⊢d₂)) =
    ⊢funᵐ (⊢seqᵐ ⊢d₁ ⊢c₁) (⊢seqᵐ ⊢c₂ ⊢d₂)
  preserve-⟶ᵐ MCS.seq-code (⊢seqᵐ (⊢codeᵐ ⊢cᵒ ⊢cᵉ) (⊢codeᵐ ⊢dᵒ ⊢dᵉ)) =
    ⊢codeᵐ (OC.⊢seqᵒ ⊢cᵒ ⊢dᵒ) (EC.⊢seqᵉ ⊢cᵉ ⊢dᵉ)
  preserve-⟶ᵐ MCS.seq-ref (⊢seqᵐ (⊢refᵐ ⊢c₁ ⊢c₂) (⊢refᵐ ⊢d₁ ⊢d₂)) =
    ⊢refᵐ (⊢seqᵐ ⊢d₁ ⊢c₁) (⊢seqᵐ ⊢c₂ ⊢d₂)
  preserve-⟶ᵐ MCS.seq-forall (⊢seqᵐ (⊢forallᵐ ⊢c) (⊢forallᵐ ⊢d)) =
    ⊢forallᵐ (⊢seqᵐ ⊢c ⊢d)
  preserve-⟶ᵐ MCS.seq-sub (⊢seqᵐ (⊢subᵐ e₁ e₂ ⊢e₁ ⊢e₂ ⊢c) (⊢subᵐ .e₁ .e₂ _ _ ⊢d)) =
    ⊢subᵐ e₁ e₂ ⊢e₁ ⊢e₂ (⊢seqᵐ ⊢c ⊢d)
  preserve-⟶ᵐ MCS.id-left (⊢seqᵐ (⊢idᵐ _ _) ⊢c) =
    ⊢c
  preserve-⟶ᵐ MCS.id-right (⊢seqᵐ ⊢c (⊢idᵐ _ _)) =
    ⊢c
  preserve-⟶ᵐ (MCS.ξ {f = MCS.□⨾ d} c⟶c′) (⊢seqᵐ ⊢c ⊢d) =
    ⊢seqᵐ (preserve-⟶ᵐ c⟶c′ ⊢c) ⊢d
  preserve-⟶ᵐ (MCS.ξ {f = c MCS.⨾□} d⟶d′) (⊢seqᵐ ⊢c ⊢d) =
    ⊢seqᵐ ⊢c (preserve-⟶ᵐ d⟶d′ ⊢d)
  preserve-⟶ᵐ (MCS.ξ {f = MCS.□⇒ d} c⟶c′) (⊢funᵐ ⊢c ⊢d) =
    ⊢funᵐ (preserve-⟶ᵐ c⟶c′ ⊢c) ⊢d
  preserve-⟶ᵐ (MCS.ξ {f = c MCS.⇒□} d⟶d′) (⊢funᵐ ⊢c ⊢d) =
    ⊢funᵐ ⊢c (preserve-⟶ᵐ d⟶d′ ⊢d)
  preserve-⟶ᵐ (MCS.ξ {f = MCS.ref□ d} c⟶c′) (⊢refᵐ ⊢c ⊢d) =
    ⊢refᵐ (preserve-⟶ᵐ c⟶c′ ⊢c) ⊢d
  preserve-⟶ᵐ (MCS.ξ {f = MCS.ref c □} d⟶d′) (⊢refᵐ ⊢c ⊢d) =
    ⊢refᵐ ⊢c (preserve-⟶ᵐ d⟶d′ ⊢d)
  preserve-⟶ᵐ (MCS.ξ-forall c⟶c′) (⊢forallᵐ ⊢c) =
    ⊢forallᵐ (preserve-⟶ᵐ c⟶c′ ⊢c)
  preserve-⟶ᵐ (MCS.ξ-sub c⟶c′) (⊢subᵐ e₁ e₂ ⊢e₁ ⊢e₂ ⊢c) =
    ⊢subᵐ e₁ e₂ ⊢e₁ ⊢e₂ (preserve-⟶ᵐ c⟶c′ ⊢c)
  preserve-⟶ᵐ (MCS.ξ-err {f = MCS.□⨾ d} {ℓ = ℓ}) (⊢seqᵐ (⊢errᵐ ⊢A _ ℓ) ⊢d) =
    ⊢errᵐ ⊢A (wf-codᵐ ⊢d) ℓ
  preserve-⟶ᵐ (MCS.ξ-err {f = c MCS.⨾□} {ℓ = ℓ}) (⊢seqᵐ ⊢c (⊢errᵐ _ ⊢B ℓ)) =
    ⊢errᵐ (wf-domᵐ ⊢c) ⊢B ℓ
  preserve-⟶ᵐ (MCS.ξ-code-o c⟶d) (⊢codeᵐ ⊢cᵒ ⊢cᵉ) =
    ⊢codeᵐ (preserve-⟼ᵒ (OCS.red OCS.refl c⟶d OCS.refl) ⊢cᵒ) ⊢cᵉ
  preserve-⟶ᵐ (MCS.ξ-code-ec c⟶d) (⊢codeᵐ ⊢cᵒ ⊢cᵉ) =
    ⊢codeᵐ ⊢cᵒ (preserve-⟼ᵉ (ECS.red ECS.refl c⟶d ECS.refl) ⊢cᵉ)
  preserve-⟶ᵐ (MCS.ξ-code-o-err {ℓ = ℓ}) (⊢codeᵐ (OC.⊢errᵒ O₁ O₂ .ℓ) ⊢cᵉ) =
    ⊢errᵐ (wf-code (EC.wf-domᵉ ⊢cᵉ)) (wf-code (EC.wf-codᵉ ⊢cᵉ)) ℓ
  preserve-⟶ᵐ (MCS.ξ-code-ec-err {ℓ = ℓ}) (⊢codeᵐ ⊢cᵒ (EC.⊢errᵉ ⊢ê₁ ⊢ê₂ .ℓ)) =
    ⊢errᵐ (wf-code ⊢ê₁) (wf-code ⊢ê₂) ℓ

preserve-⟼ᵐ : ∀ {Δ Θ A B c d}
  → Θ MCS.⊢ᵐ c ⟼ d
  → Δ ; Θ ⊢ᵐ c ⦂ A ⇒ B
    -------------------
  → Δ ; Θ ⊢ᵐ d ⦂ A ⇒ B
preserve-⟼ᵐ (MCS.red c≡c′ c′⟶d′ d′≡d) ⊢c =
  preserve-≡ᵐ d′≡d (preserve-⟶ᵐ c′⟶d′ (preserve-≡ᵐ c≡c′ ⊢c))
