module Theories.SpaceEfficiency.Proofs.Values where

open import Theories.Utils using (⟨_,_,_,_⟩)
open import Theories.SpaceEfficiency.CCAlphaRefStarSyntaxAndTypeSystem
open import Theories.SpaceEfficiency.CCAlphaRefStarSemantics
  using (CodeValue; is-const; is-var; is-lamᵒ-val; is-app)


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
