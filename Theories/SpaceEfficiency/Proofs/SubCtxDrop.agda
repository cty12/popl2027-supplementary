module LambdaAlphaRefStar.Theories.SpaceEfficiency.Proofs.SubCtxDrop where

open import Data.Product using () renaming (_,_ to ⟨_,_⟩)

open import Utils using (_⊆_; Z; S_; ⟨_,_,_,_⟩)
open import LambdaAlphaRefStar.Theories.SpaceEfficiency.CCAlphaRefStarSyntaxAndTypeSystem
open import LambdaAlphaRefStar.Theories.SpaceEfficiency.Proofs.SubCtxWeakening
  using (mhc-⊆ˢ; meta-⊆ˢ)
import LambdaAlphaRefStar.Theories.SpaceEfficiency.MetaHypercoercions as MH


-- | If the subtyping is already implied, we can drop it from the context.
drop-subctx : ∀ {Θ e₁ e₂}
  → Θ ⊢ᵉ e₁ <: e₂
    ------------------------
  → (Θ , e₁ <: e₂) ⊆ˢ Θ
drop-subctx {Θ = Θ} {e₁ = e₁} {e₂ = e₂} e₁<:e₂ = subctx⊆ subtype-pres globalEdge-pres
  where
  subtype-pres : ∀ {e₃ e₄}
    → Θ , e₁ <: e₂ ⊢ᵉ e₃ <: e₄
    → Θ ⊢ᵉ e₃ <: e₄
  subtype-pres <:-ε = <:-ε
  subtype-pres <:-refl = <:-refl
  subtype-pres (<:-ax Z) = e₁<:e₂
  subtype-pres (<:-ax (S edge)) = <:-ax edge
  subtype-pres (<:-trans e₃<:e e<:e₄) =
    <:-trans (subtype-pres e₃<:e) (subtype-pres e<:e₄)

  globalEdge-pres : GlobalEdges (Θ , e₁ <: e₂) ⊆ GlobalEdges Θ
  globalEdge-pres edge = edge

subtype-drop-hc : ∀ {Δ Θ e₁ e₂ c A B}
  → MH._;_⊢ᵐ_⦂_⇒_ Δ (Θ , e₁ <: e₂) c A B
  → Θ ⊢ᵉ e₁ <: e₂
    --------------------------------------
  → MH._;_⊢ᵐ_⦂_⇒_ Δ Θ c A B
subtype-drop-hc ⊢c e₁<:e₂ = mhc-⊆ˢ (drop-subctx e₁<:e₂) ⊢c

subtype-drop-term : ∀ {Δ Θ Γᵒ Γᵐ Σ e₁ e₂ M A}
  → Δ ; ⟨ Θ , e₁ <: e₂ , Γᵒ , Γᵐ , Σ ⟩ ⊢ᵐ M ⦂ A
  → Θ ⊢ᵉ e₁ <: e₂
    ---------------------------------------
  → Δ ; ⟨ Θ , Γᵒ , Γᵐ , Σ ⟩ ⊢ᵐ M ⦂ A
subtype-drop-term ⊢M e₁<:e₂ = meta-⊆ˢ (drop-subctx e₁<:e₂) ⊢M
