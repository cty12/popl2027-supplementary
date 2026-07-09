module LambdaAlphaRefStar.Theories.StaticScopeSafety where

open import Data.List using ([])
open import Data.List.Relation.Unary.All using () renaming ([] to []ᴬ)
open import Data.Maybe using (just)
open import Data.Product using (∃-syntax; _×_) renaming (_,_ to ⟨_,_⟩)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import LambdaAlphaRefStar.Theories.CCAlphaRefStarSyntaxAndTypeSystem
open import LambdaAlphaRefStar.Theories.CCAlphaRefStarSemantics
open import LambdaAlphaRefStar.Theories.CCPreservesErrorFree
  using (ErrorFreeConfig; meta-step-error-free-pres; meta-error-free-not-blame)
open import LambdaAlphaRefStar.Theories.CanonicalForms using (obs)
open import LambdaAlphaRefStar.Theories.Elaboration using (_;_;_;_⊢_↝_⦂_)
open import LambdaAlphaRefStar.Theories.ElaborationErrorFree using (meta-elab-error-free)
open import LambdaAlphaRefStar.Theories.Reify using (reify)
open import LambdaAlphaRefStar.Theories.ScopeSafety using (_—↠ᵐ_; ↠-refl; ↠-step; scope-safety)
open import LambdaAlphaRefStar.Theories.STLC as STLC
open import LambdaAlphaRefStar.Theories.SurfaceFullyStatic using (FullyStaticMetaSurfaceTerm)


error-free-preserveᵐ* : ∀ {C₁ C₂}
  → ErrorFreeConfig C₁
  → C₁ —↠ᵐ C₂
    ------------------
  → ErrorFreeConfig C₂
error-free-preserveᵐ* npC ↠-refl = npC
error-free-preserveᵐ* ⟨ npμ , npM ⟩ (↠-step C₁—→C₂ C₂—↠C₃)
  with meta-step-error-free-pres C₁—→C₂ npμ npM
... | npC₂ =
  error-free-preserveᵐ* npC₂ C₂—↠C₃


error-free-not-blame : ∀ {C}
  → ErrorFreeConfig C
    ------------------
  → NotBlame C
error-free-not-blame ⟨ npμ , npM ⟩ ℓ = meta-error-free-not-blame npM


static-scope-safety : ∀ {M M′ C′ O T}
  → FullyStaticMetaSurfaceTerm M
  → ∅ᵉ ; ∅ˢ ; [] ; ∅ᵒ ⊢ M ↝ M′ ⦂ ‶ O ″ ec ε
  → config ∅ᵉ ∅ˢ ∅ᵒ [] M′ —↠ᵐ C′
  → Irreducible C′
  → O ↪ᵒ T
    ---------------------------------------------------------------------------------------------------------------
  → ∃[ Vᵒ ] ∃[ Mˢ ] obs (Config.M C′) ≡ just Vᵒ × reify (Config.Γᵒ C′ .entries) Vᵒ ≡ just Mˢ × [] STLC.⊢ Mˢ ⦂ T
static-scope-safety {M′ = M′} {C′ = C′} fsM elab C↠C′ irred O↪T
  with meta-elab-error-free fsM []ᴬ elab
... | ⟨ fsA , npM′ ⟩ = scope-safety elab C↠C′ irred
                        (error-free-not-blame {C′} (error-free-preserveᵐ* ⟨ []ᴬ , npM′ ⟩ C↠C′)) O↪T
