module LambdaAlphaRefStar.Theories.ScopeSafety where

open import Data.Bool using (false; true)
open import Data.List using ([]; _∷_)
open import Data.List.Relation.Unary.All using () renaming ([] to []ᴬ)
open import Data.Maybe using (just; _>>=_)
open import Data.Nat using (zero; suc; _≡ᵇ_)
open import Data.Product using (∃-syntax; _×_) renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Function using (case_of_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary.Negation using (contradiction)

open import Utils using (_∋_; index; ≡ᵇ-refl; ⟨_,_,_⟩; ⟨_,_,_,_⟩; ⟨_,_,_,_,_⟩)
open import LambdaAlphaRefStar.Theories.CCAlphaRefStarSyntaxAndTypeSystem
open import LambdaAlphaRefStar.Theories.CCAlphaRefStarSemantics
open import LambdaAlphaRefStar.Theories.CCAlphaRefStarPreservation using (preserveᵐ)
open import LambdaAlphaRefStar.Theories.CCAlphaRefStarProgress using (progressᵐ; doneᵐ; blameᵐ; stepᵐ)
open import LambdaAlphaRefStar.Theories.CanonicalForms using (obs; obs-code)
open import LambdaAlphaRefStar.Theories.Elaboration using (_;_;_;_⊢_↝_⦂_)
open import LambdaAlphaRefStar.Theories.ElaborationPreserves using (meta-elab-preserves)
open import LambdaAlphaRefStar.Theories.Heap using (ht-∅)
open import LambdaAlphaRefStar.Theories.Reify using (ReifyEnv; reify; reifyAt)
open import LambdaAlphaRefStar.Theories.ReifyPreserves using (reify-preserves-types)
open import LambdaAlphaRefStar.Theories.STLC as STLC

open import LambdaAlphaRefStar.Theories.ScopeSafetyValue public

-- | Multi-step meta reduction.
infix 0 _—↠ᵐ_

data _—↠ᵐ_ : Config MetaTerm → Config MetaTerm → Set where

  ↠-refl : ∀ {C}
      ---------------
    → C —↠ᵐ C

  ↠-step : ∀ {C₁ C₂ C₃}
    → C₁ —→ᵐ C₂
    → C₂ —↠ᵐ C₃
      ---------------
    → C₁ —↠ᵐ C₃

preserveᵐ* : ∀ {C₁ C₂ Σ₁ A}
  → WTMetaConfig C₁ Σ₁ A
  → C₁ —↠ᵐ C₂
    -------------------------------
  → ∃[ Σ₂ ] WTMetaConfig C₂ Σ₂ A
preserveᵐ* {Σ₁ = Σ₁} ⊢C ↠-refl =
  ⟨ Σ₁ , ⊢C ⟩
preserveᵐ* ⊢C (↠-step C₁—→C₂ C₂—↠C₃)
  with preserveᵐ ⊢C C₁—→C₂
... | ⟨ _ , ⊢C₂ , _ , _ ⟩ =
  preserveᵐ* ⊢C₂ C₂—↠C₃


mutual

  step-cutoff-zeroᵒ : ∀ {C₁ C₂ e}
    → C₁ ∣ e —→ᵒ C₂
    → C₁ .Θ .cutoff ≡ zero
    → C₁ .Γᵒ .cutoff ≡ zero
      ------------------------------------------------
    → C₂ .Θ .cutoff ≡ zero × C₂ .Γᵒ .cutoff ≡ zero
  step-cutoff-zeroᵒ (ξ-code Fᵒ Mᵒ—→Nᵒ) Θ-cutoff-zero Γᵒ-cutoff-zero =
    step-cutoff-zeroᵒ Mᵒ—→Nᵒ Θ-cutoff-zero Γᵒ-cutoff-zero
  step-cutoff-zeroᵒ (ξ-code-blame Fᵒ) Θ-cutoff-zero Γᵒ-cutoff-zero =
    ⟨ Θ-cutoff-zero , Γᵒ-cutoff-zero ⟩
  step-cutoff-zeroᵒ (ξ-splice M—→N) Θ-cutoff-zero Γᵒ-cutoff-zero =
    step-cutoff-zeroᵐ M—→N Θ-cutoff-zero Γᵒ-cutoff-zero
  step-cutoff-zeroᵒ splice-blame Θ-cutoff-zero Γᵒ-cutoff-zero =
    ⟨ Θ-cutoff-zero , Γᵒ-cutoff-zero ⟩
  step-cutoff-zeroᵒ (splice-β vᵒ) Θ-cutoff-zero Γᵒ-cutoff-zero =
    ⟨ Θ-cutoff-zero , Γᵒ-cutoff-zero ⟩
  step-cutoff-zeroᵒ (splice-sub vᵒ) Θ-cutoff-zero Γᵒ-cutoff-zero =
    ⟨ Θ-cutoff-zero , Γᵒ-cutoff-zero ⟩
  step-cutoff-zeroᵒ code-λ Θ-cutoff-zero Γᵒ-cutoff-zero =
    ⟨ Θ-cutoff-zero , Γᵒ-cutoff-zero ⟩
  step-cutoff-zeroᵒ ξ-code-λ̅-blame Θ-cutoff-zero Γᵒ-cutoff-zero =
    ⟨ Θ-cutoff-zero , Γᵒ-cutoff-zero ⟩
  step-cutoff-zeroᵒ (ξ-code-λ̅ Mᵒ—→Nᵒ) Θ-cutoff-zero Γᵒ-cutoff-zero =
    step-cutoff-zeroᵒ Mᵒ—→Nᵒ Θ-cutoff-zero Γᵒ-cutoff-zero

  step-cutoff-zeroᵐ : ∀ {C₁ C₂}
    → C₁ —→ᵐ C₂
    → C₁ .Θ .cutoff ≡ zero
    → C₁ .Γᵒ .cutoff ≡ zero
      ------------------------------------------------
    → C₂ .Θ .cutoff ≡ zero × C₂ .Γᵒ .cutoff ≡ zero
  step-cutoff-zeroᵐ (ξ-meta F M—→N) Θ-cutoff-zero Γᵒ-cutoff-zero =
    step-cutoff-zeroᵐ M—→N Θ-cutoff-zero Γᵒ-cutoff-zero
  step-cutoff-zeroᵐ (ξ-meta-blame F) Θ-cutoff-zero Γᵒ-cutoff-zero =
    ⟨ Θ-cutoff-zero , Γᵒ-cutoff-zero ⟩
  step-cutoff-zeroᵐ (ξ-quote Mᵒ—→Nᵒ) Θ-cutoff-zero Γᵒ-cutoff-zero =
    step-cutoff-zeroᵒ Mᵒ—→Nᵒ Θ-cutoff-zero Γᵒ-cutoff-zero
  step-cutoff-zeroᵐ quote-blame Θ-cutoff-zero Γᵒ-cutoff-zero =
    ⟨ Θ-cutoff-zero , Γᵒ-cutoff-zero ⟩
  step-cutoff-zeroᵐ (β v) Θ-cutoff-zero Γᵒ-cutoff-zero =
    ⟨ Θ-cutoff-zero , Γᵒ-cutoff-zero ⟩
  step-cutoff-zeroᵐ (β-cast u v inert) Θ-cutoff-zero Γᵒ-cutoff-zero =
    ⟨ Θ-cutoff-zero , Γᵒ-cutoff-zero ⟩
  step-cutoff-zeroᵐ Λ-β Θ-cutoff-zero Γᵒ-cutoff-zero =
    ⟨ Θ-cutoff-zero , Γᵒ-cutoff-zero ⟩
  step-cutoff-zeroᵐ (Λ-β-cast u) Θ-cutoff-zero Γᵒ-cutoff-zero =
    ⟨ Θ-cutoff-zero , Γᵒ-cutoff-zero ⟩
  step-cutoff-zeroᵐ sub-β Θ-cutoff-zero Γᵒ-cutoff-zero =
    ⟨ Θ-cutoff-zero , Γᵒ-cutoff-zero ⟩
  step-cutoff-zeroᵐ (sub-β-cast u) Θ-cutoff-zero Γᵒ-cutoff-zero =
    ⟨ Θ-cutoff-zero , Γᵒ-cutoff-zero ⟩
  step-cutoff-zeroᵐ (sub-cast-success u e₁<:e₂ inert) Θ-cutoff-zero Γᵒ-cutoff-zero =
    ⟨ Θ-cutoff-zero , Γᵒ-cutoff-zero ⟩
  step-cutoff-zeroᵐ (sub-cast-sub-fail u e₁≮:e₂ inert) Θ-cutoff-zero Γᵒ-cutoff-zero =
    ⟨ Θ-cutoff-zero , Γᵒ-cutoff-zero ⟩
  step-cutoff-zeroᵐ (sub-cast-fail u inert mismatch) Θ-cutoff-zero Γᵒ-cutoff-zero =
    ⟨ Θ-cutoff-zero , Γᵒ-cutoff-zero ⟩
  step-cutoff-zeroᵐ (ref v) Θ-cutoff-zero Γᵒ-cutoff-zero =
    ⟨ Θ-cutoff-zero , Γᵒ-cutoff-zero ⟩
  step-cutoff-zeroᵐ (deref lookup) Θ-cutoff-zero Γᵒ-cutoff-zero =
    ⟨ Θ-cutoff-zero , Γᵒ-cutoff-zero ⟩
  step-cutoff-zeroᵐ (assign v write) Θ-cutoff-zero Γᵒ-cutoff-zero =
    ⟨ Θ-cutoff-zero , Γᵒ-cutoff-zero ⟩
  step-cutoff-zeroᵐ (assign-cast v inert) Θ-cutoff-zero Γᵒ-cutoff-zero =
    ⟨ Θ-cutoff-zero , Γᵒ-cutoff-zero ⟩
  step-cutoff-zeroᵐ (deref-cast inert) Θ-cutoff-zero Γᵒ-cutoff-zero =
    ⟨ Θ-cutoff-zero , Γᵒ-cutoff-zero ⟩
  step-cutoff-zeroᵐ (cast-reduce u c⟼d) Θ-cutoff-zero Γᵒ-cutoff-zero =
    ⟨ Θ-cutoff-zero , Γᵒ-cutoff-zero ⟩
  step-cutoff-zeroᵐ (cast-compose u) Θ-cutoff-zero Γᵒ-cutoff-zero =
    ⟨ Θ-cutoff-zero , Γᵒ-cutoff-zero ⟩
  step-cutoff-zeroᵐ (cast-id u) Θ-cutoff-zero Γᵒ-cutoff-zero =
    ⟨ Θ-cutoff-zero , Γᵒ-cutoff-zero ⟩
  step-cutoff-zeroᵐ (cast-blame u) Θ-cutoff-zero Γᵒ-cutoff-zero =
    ⟨ Θ-cutoff-zero , Γᵒ-cutoff-zero ⟩


↠-cutoff-zeroᵐ : ∀ {C₁ C₂}
  → C₁ —↠ᵐ C₂
  → C₁ .Θ .cutoff ≡ zero
  → C₁ .Γᵒ .cutoff ≡ zero
    ------------------------------------------------
  → C₂ .Θ .cutoff ≡ zero × C₂ .Γᵒ .cutoff ≡ zero
↠-cutoff-zeroᵐ ↠-refl Θ-cutoff-zero Γᵒ-cutoff-zero =
  ⟨ Θ-cutoff-zero , Γᵒ-cutoff-zero ⟩
↠-cutoff-zeroᵐ (↠-step C₁—→C₂ C₂—↠C₃) Θ-cutoff-zero Γᵒ-cutoff-zero
  with step-cutoff-zeroᵐ C₁—→C₂ Θ-cutoff-zero Γᵒ-cutoff-zero
... | ⟨ Θ₂-cutoff-zero , Γᵒ₂-cutoff-zero ⟩ =
  ↠-cutoff-zeroᵐ C₂—↠C₃ Θ₂-cutoff-zero Γᵒ₂-cutoff-zero

cc-scope-safety : ∀ {M C′ O T}
  → WTMetaConfig (config ∅ᵉ ∅ˢ ∅ᵒ [] M) [] (‶ O ″ ec ε)
  → config ∅ᵉ ∅ˢ ∅ᵒ [] M —↠ᵐ C′
  → Irreducible C′
  → NotBlame C′
  → O ↪ᵒ T
    ---------------------------------------------------------------------------------------------------------
  → ∃[ Vᵒ ] ∃[ Mˢ ] obs (Config.M C′) ≡ just Vᵒ × reify (C′ .Γᵒ .entries) Vᵒ ≡ just Mˢ × [] STLC.⊢ Mˢ ⦂ T
cc-scope-safety ⊢C C↠C′ irreducible not-blame O↪T
  with preserveᵐ* ⊢C C↠C′
... | ⟨ Σ′ , ⊢C′ ⟩
  with ↠-cutoff-zeroᵐ C↠C′ refl refl | progressᵐ ⊢C′
... | cutoffs | stepᵐ C′→C″ = contradiction C′→C″ irreducible
... | cutoffs | blameᵐ M′≡blame = contradiction M′≡blame (not-blame _)
... | ⟨ Θ-cutoff-zero , Γᵒ-cutoff-zero ⟩ | doneᵐ v =
  let ⟨ Vᵒ , obs≡ , vᵒ , ⊢Vᵒ ⟩ = obs-code v (⊢C′ .⊢M) O↪T in
  let ⟨ Mˢ , reify≡ , ⊢Mˢ ⟩    = scope-safety-val (⊢C′ .⊢Θ) Θ-cutoff-zero (⊢C′ .⊢Γᵒ) Γᵒ-cutoff-zero vᵒ ⊢Vᵒ in
  ⟨ Vᵒ , Mˢ , obs≡ , reify≡ , ⊢Mˢ ⟩

scope-safety : ∀ {M M′ C′} {O : OType⋆} {T : OType}
  → ∅ᵉ ; ∅ˢ ; [] ; ∅ᵒ ⊢ M ↝ M′ ⦂ ‶ O ″ ec ε
  → config ∅ᵉ ∅ˢ ∅ᵒ [] M′ —↠ᵐ C′
  → Irreducible C′
  → NotBlame C′
  → O ↪ᵒ T
    ---------------------------------------------------------------------------------------------------------
  → ∃[ Vᵒ ] ∃[ Mˢ ] obs (Config.M C′) ≡ just Vᵒ × reify (C′ .Γᵒ .entries) Vᵒ ≡ just Mˢ × [] STLC.⊢ Mˢ ⦂ T
scope-safety elab C↠C′ irred not-blame O↪T =
  cc-scope-safety (wtMetaConfig ⊢∅ˢ ⊢∅ᵒ []ᴬ ht-∅ (meta-elab-preserves ⊢∅ˢ []ᴬ ⊢∅ᵒ elab))
                  C↠C′ irred not-blame O↪T
  where
  ⊢∅ˢ : ∅ᵉ ⊢ ∅ˢ SubCtx
  ⊢∅ˢ = ⟨ []ᴬ , ⟨ (λ ()) , (λ ()) ⟩ ⟩
  ⊢∅ᵒ : ∅ᵉ ⊢ ∅ᵒ OCtx
  ⊢∅ᵒ = ⟨ []ᴬ , (λ ()) ⟩
