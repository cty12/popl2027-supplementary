module Theories.Values where

open import Theories.Utils using (⟨_,_,_,_⟩)
open import Theories.CCAlphaRefStarSyntaxAndTypeSystem
open import Theories.CoercionSequences.Meta.Definition using (Inert)


-- | Code language values (Vᵒ).
data CodeValue : CodeTerm → Set where

  is-const : ∀ {ι} {r : base-rep ι}
      ---------------------------------
    → CodeValue ($ r)

  is-var : ∀ {x}
      ------------------------------
    → CodeValue (` x)

  is-lamᵒ-val : ∀ {α M}
    → CodeValue M
      ---------------------------------
    → CodeValue (ƛ̅ ` α ˙ M)

  is-app : ∀ {L M}
    → CodeValue L
    → CodeValue M
      ------------------------------
    → CodeValue (L · M)


codevalue-weaken-ec : ∀ {Δ Θ Γᵒ Γᵐ Σ e₁ e₂ M T}
  → Δ ; ⟨ Θ , Γᵒ , Γᵐ , Σ ⟩ ; e₁ ⊢ᵒ M ⦂ T
  → CodeValue M
  → Θ ⊢ᵉ e₁ <: e₂
    ------------------------------------------
  → Δ ; ⟨ Θ , Γᵒ , Γᵐ , Σ ⟩ ; e₂ ⊢ᵒ M ⦂ T
codevalue-weaken-ec (⊢constᵒ r) is-const e₁<:e₂ =
  ⊢constᵒ r
codevalue-weaken-ec (⊢varᵒ lookup α<:e₁) is-var e₁<:e₂ =
  ⊢varᵒ lookup (<:-trans α<:e₁ e₁<:e₂)
codevalue-weaken-ec (⊢lamᵒ-val α∈Δ owner edge e′<:e₁ ⊢M) (is-lamᵒ-val vᵒ) e₁<:e₂ =
  ⊢lamᵒ-val α∈Δ owner edge (<:-trans e′<:e₁ e₁<:e₂) ⊢M
codevalue-weaken-ec (⊢appᵒ ⊢L ⊢M) (is-app vL vM) e₁<:e₂ =
  ⊢appᵒ (codevalue-weaken-ec ⊢L vL e₁<:e₂)
        (codevalue-weaken-ec ⊢M vM e₁<:e₂)


-- | Uncoerced values (U)
data RawValue : MetaTerm → Set where

  U-const : ∀ {ι} {r : base-rep ι}
      ---------------------
    → RawValue ($ r)

  U-addr : ∀ {a}
      ---------------------
    → RawValue (addr a)

  U-ƛ : ∀ {M}
      ---------------------
    → RawValue (ƛ M)

  U-Λ : ∀ {M}
      ---------------------
    → RawValue (Λ M)

  U-quote : ∀ {e Vᵒ}
    → CodeValue Vᵒ
      ---------------------
    → RawValue (‶ Vᵒ ″ e)

  U-sub : ∀ {e₁ e₂ M}
      ---------------------------
    → RawValue (e₁ <: e₂ => M)


-- | Metalanguage values (V, W)
data Value : MetaTerm → Set where

  V-raw : ∀ {M}
    → RawValue M
      ------------------
    → Value M

  V-cast : ∀ {U c}
    → RawValue U
    → Inert c
      ---------------------
    → Value (U ⟨ c ⟩)
