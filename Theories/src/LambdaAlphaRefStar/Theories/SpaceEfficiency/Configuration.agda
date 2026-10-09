module LambdaAlphaRefStar.Theories.SpaceEfficiency.Configuration where

open import Data.List using (List)
open import Utils using (∅; ⟨_,_,_,_⟩)
open import LambdaAlphaRefStar.Theories.ECCtxWeakening using (_⊆ᵉ_)
open import LambdaAlphaRefStar.Theories.SpaceEfficiency.CCAlphaRefStarSyntaxAndTypeSystem
open import LambdaAlphaRefStar.Theories.SpaceEfficiency.Proofs.Heap
  using (_;_;_;_⊢ᴴ_)


-- | Runtime configurations shared by code and meta reduction.
Heap : Set
Heap = List MetaTerm

record Config (Term : Set) : Set where
  constructor config
  field
    Δ  : ECCtx
    Θ  : SubCtx
    Γᵒ : OCtx
    μ  : Heap
    M  : Term

open Config public


infix 4 _⊆ꟲ_

record _⊆ꟲ_ {Term : Set} (C₁ C₂ : Config Term) : Set where
  constructor config⊆
  field
    Δ⊆   : C₁ .Δ ⊆ᵉ C₂ .Δ
    Γᵒ≼  : C₁ .Γᵒ ≼ᵒ C₂ .Γᵒ
    Θ⊆   : C₁ .Θ ⊆ˢ C₂ .Θ

open _⊆ꟲ_ public


record WTMetaConfig (C : Config MetaTerm) (Σ : HeapCtx) (A : MType) : Set where
  constructor wtMetaConfig
  field
    ⊢Θ     : C .Δ ⊢ C .Θ SubCtx
    ⊢Γᵒ    : C .Δ ⊢ C .Γᵒ OCtx
    ⊢Σ     : C .Δ ⊢ Σ HeapCtx
    ⊢μ     : C .Δ ; C .Θ ; C .Γᵒ ; Σ ⊢ᴴ C .μ
    ⊢M     : C .Δ ; ⟨ C .Θ , C .Γᵒ , ∅ , Σ ⟩ ⊢ᵐ C .M ⦂ A

open WTMetaConfig public


record WTCodeConfig (C : Config CodeTerm) (Σ : HeapCtx) (e : EC) (T : OType) : Set where
  constructor wtCodeConfig
  field
    ⊢Θ     : C .Δ ⊢ C .Θ SubCtx
    ⊢Γᵒ    : C .Δ ⊢ C .Γᵒ OCtx
    ⊢Σ     : C .Δ ⊢ Σ HeapCtx
    ⊢μ     : C .Δ ; C .Θ ; C .Γᵒ ; Σ ⊢ᴴ C .μ
    ⊢M     : C .Δ ; ⟨ C .Θ , C .Γᵒ , ∅ , Σ ⟩ ; e ⊢ᵒ C .M ⦂ T

open WTCodeConfig public
