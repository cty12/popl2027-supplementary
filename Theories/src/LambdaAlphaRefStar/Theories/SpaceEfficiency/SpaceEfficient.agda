module LambdaAlphaRefStar.Theories.SpaceEfficiency.SpaceEfficient where

open import Data.Bool using (Bool; true; false)
open import Data.List using ([]; _∷_; _∷ʳ_)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _≤_; _⊔_; z≤n; s≤s)
open import Data.Nat.Properties using
  (≤-refl; ≤-trans; ≤-reflexive; +-comm; +-mono-≤; +-monoʳ-≤; *-assoc; *-distribˡ-+; *-distribʳ-+; *-mono-≤; *-monoʳ-≤; *-suc;
   m≤m+n; m≤n+m; m≤m⊔n; m≤n⊔m; m≤n⇒m≤1+n; ⊔-mono-≤; ⊔-lub)
open import Data.Nat.Solver using (module +-*-Solver)
open import Data.Product using (Σ-syntax; ∃-syntax; _×_) renaming (_,_ to ⟨_,_⟩)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym)

open Data.Nat.Properties.≤-Reasoning

open import LambdaAlphaRefStar.Theories.SurfaceSyntaxAndTypeSystem
  using (CodeSurfaceTerm; MetaSurfaceTerm; _;_;_;_⊢_⦂_)
open import LambdaAlphaRefStar.Theories.SpaceEfficiency.CCAlphaRefStarSyntaxAndTypeSystem hiding (size)
open import LambdaAlphaRefStar.Theories.SpaceEfficiency.CCAlphaRefStarSemantics
open import LambdaAlphaRefStar.Theories.SpaceEfficiency.Configuration
  using (WTMetaConfig)
open import LambdaAlphaRefStar.Theories.SpaceEfficiency.Elaboration
  using (_;_;_;_⊢_↝_⦂_)
open import LambdaAlphaRefStar.Theories.SpaceEfficiency.Compilation
  using (compile)
open import LambdaAlphaRefStar.Theories.SpaceEfficiency.CCAlphaRefStarSizeAndHeight
open import LambdaAlphaRefStar.Theories.SpaceEfficiency.Proofs.SizeHeightBounded
open import LambdaAlphaRefStar.Theories.SpaceEfficiency.Proofs.LeastUpperBoundLemmas
open import LambdaAlphaRefStar.Theories.SpaceEfficiency.AdjacentCastOK
open import LambdaAlphaRefStar.Theories.SpaceEfficiency.Proofs.PreserveOK
open import LambdaAlphaRefStar.Theories.SpaceEfficiency.Proofs.PreserveHeight
open import LambdaAlphaRefStar.Theories.SpaceEfficiency.Proofs.RealSizeTermAndHeapSize
open import LambdaAlphaRefStar.Theories.SpaceEfficiency.Proofs.SizeOK
open import LambdaAlphaRefStar.Theories.SpaceEfficiency.Proofs.CompileEfficient
  using (compile-efficient)
open import LambdaAlphaRefStar.Theories.SpaceEfficiency.Proofs.ElaborationEfficient
  using (elab-efficient)

open import LambdaAlphaRefStar.Theories.SpaceEfficiency.ECHypercoercions
open import LambdaAlphaRefStar.Theories.SpaceEfficiency.ObjectHypercoercions
open import LambdaAlphaRefStar.Theories.SpaceEfficiency.MetaHypercoercions


space-consumption-ok : ∀ {ctx n} (M₀ : MetaTerm)
  → n ∣ false ⊢ᵐ M₀ ok
  → Σ[ k ∈ ℕ ] ∀ (C′ : Config MetaTerm)
  → ctx / config ∅ᵉ ∅ˢ ∅ᵒ [] M₀ —↠ᵐ C′
  → meta-config-real-size C′ ≤ k * meta-config-ideal-size C′
space-consumption-ok M₀ Mok =
  ⟨ (9 * pow2 (meta-config-height C₀)) * 13 , G ⟩
  where
    C₀ : Config MetaTerm
    C₀ = config ∅ᵉ ∅ˢ ∅ᵒ [] M₀

    G : ∀ C′
      → _ / C₀ —↠ᵐ C′
        --------------------------------------------------------------------------------
      → meta-config-real-size C′
          ≤ ((9 * pow2 (meta-config-height C₀)) * 13) * meta-config-ideal-size C′
    G (config Δ Θ Γᵒ μ M) C₀—↠C′
      with multi-preserve-okᵐ μok-[] Mok C₀—↠C′
         | multi-preserve-heap-values-okᵐ μok-[] Mok C₀—↠C′
    ... | ⟨ m , C′ok ⟩ | μ′ok =
      begin
        heap-real-size μ + real-size M
      ≤⟨ +-mono-≤ heap-real≤ term-real≤ ⟩
        f * (13 * heap-ideal-size μ) + f * (13 * ideal-size M)
      ≤⟨ +-mono-≤
           (≤-reflexive (sym (*-assoc f 13 (heap-ideal-size μ))))
           (≤-reflexive (sym (*-assoc f 13 (ideal-size M)))) ⟩
        (f * 13) * heap-ideal-size μ + (f * 13) * ideal-size M
      ≤⟨ ≤-reflexive (sym (*-distribˡ-+ (f * 13) (heap-ideal-size μ) (ideal-size M))) ⟩
        (f * 13) * (heap-ideal-size μ + ideal-size M)
      ∎
      where
        h = meta-config-height C₀
        f = 9 * pow2 h

        C′≤C₀ : meta-config-height (config Δ Θ Γᵒ μ M) ≤ h
        C′≤C₀ =
          multi-preserve-heightᵐ
            {C₁ = C₀}
            {C₂ = config Δ Θ Γᵒ μ M}
            C₀—↠C′

        heap≤h : heap-c-height μ ≤ h
        heap≤h =
          ≤-trans (m≤m⊔n (heap-c-height μ) (c-height M)) C′≤C₀

        term≤h : c-height M ≤ h
        term≤h =
          ≤-trans (m≤n⊔m (heap-c-height μ) (c-height M)) C′≤C₀

        heap-real≤ : heap-real-size μ ≤ f * (13 * heap-ideal-size μ)
        heap-real≤ =
          ≤-trans
            (heap-real-size-tsize-height μ heap≤h)
            (*-mono-≤
              {x = f} {y = f}
              {u = heap-size μ} {v = 13 * heap-ideal-size μ}
              ≤-refl
              (heap-size-OK≤13ideal μ′ok))

        term-real≤ : real-size M ≤ f * (13 * ideal-size M)
        term-real≤ =
          ≤-trans
            (real-size-tsizeᵐ-height {M = M} term≤h)
            (*-mono-≤
              {x = f} {y = f}
              {u = size M} {v = 13 * ideal-size M}
              ≤-refl
              (size-OK≤13ideal C′ok))

space-consumption : ∀ {A ctx} {Mˢ : MetaSurfaceTerm}
  → (d : ∅ᵉ ; ∅ˢ ; [] ; ∅ᵒ ⊢ Mˢ ⦂ A)
  → Σ[ k ∈ ℕ ] ∀ (C′ : Config MetaTerm)
  → ctx / config ∅ᵉ ∅ˢ ∅ᵒ [] (compile d) —↠ᵐ C′
  → meta-config-real-size C′ ≤ k * meta-config-ideal-size C′
space-consumption d
  with compile-efficient d
... | ⟨ n , ⟨ n≤1 , Mok ⟩ ⟩ =
  space-consumption-ok (compile d) Mok

space-consumption-elab : ∀ {A ctx} {Mˢ : MetaSurfaceTerm} {M′ : MetaTerm}
  → ∅ᵉ ; ∅ˢ ; [] ; ∅ᵒ ⊢ Mˢ ↝ M′ ⦂ A
  → Σ[ k ∈ ℕ ] ∀ (C′ : Config MetaTerm)
  → ctx / config ∅ᵉ ∅ˢ ∅ᵒ [] M′ —↠ᵐ C′
  → meta-config-real-size C′ ≤ k * meta-config-ideal-size C′
space-consumption-elab M↝M′
  with elab-efficient M↝M′
... | ⟨ n , ⟨ n≤1 , Mok ⟩ ⟩ =
  space-consumption-ok _ Mok
