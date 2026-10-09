module LambdaAlphaRefStar.Theories.SpaceEfficiency.Proofs.ECCtxWeakening where

open import Data.Nat.Properties using (≤-trans; <-≤-trans)

open import Utils using (⟨_,_,_,_⟩)
open import LambdaAlphaRefStar.Theories.SpaceEfficiency.CCAlphaRefStarSyntaxAndTypeSystem
open import LambdaAlphaRefStar.Theories.ECCtxWeakening
  using
    (_⊆ᵉ_; size≤; cutoff≤; ⊆ᵉ-refl; ⊆ᵉ-cons; ⊆ᵉ-snoc; ec-weaken;
     globalEC-weaken; ec⋆-weaken; mtype-weaken; subctx-weaken;
     octx-weaken; mctx-weaken)
  public

import LambdaAlphaRefStar.Theories.SpaceEfficiency.ECHypercoercions as EH
import LambdaAlphaRefStar.Theories.SpaceEfficiency.MetaHypercoercions as MH


------------------------------------------------------------------------
-- EC-context weakening for hypercoercions

ec-hc-ecctx-weaken : ∀ {Δ₁ Δ₂ Θ c ê₁ ê₂}
  → Δ₁ ⊆ᵉ Δ₂
  → EH._;_⊢ᵉ_⦂_⇒_ Δ₁ Θ c ê₁ ê₂
    --------------------------------------
  → EH._;_⊢ᵉ_⦂_⇒_ Δ₂ Θ c ê₁ ê₂

ec-head-ecctx-weaken : ∀ {Δ₁ Δ₂ h ê₁ ê₂}
  → Δ₁ ⊆ᵉ Δ₂
  → EH._⊢ᵉʰ_⦂_⇒_ Δ₁ h ê₁ ê₂
    --------------------------------
  → EH._⊢ᵉʰ_⦂_⇒_ Δ₂ h ê₁ ê₂
ec-head-ecctx-weaken Δ₁⊆Δ₂ (EH.⊢projʰ e ℓ) = EH.⊢projʰ e ℓ
ec-head-ecctx-weaken Δ₁⊆Δ₂ (EH.⊢idʰ ê) = EH.⊢idʰ ê

ec-middle-ecctx-weaken : ∀ {Δ₁ Δ₂ Θ m ê₁ ê₂}
  → Δ₁ ⊆ᵉ Δ₂
  → EH._;_⊢ᵉᵐ_⦂_⇒_ Δ₁ Θ m ê₁ ê₂
    --------------------------------------
  → EH._;_⊢ᵉᵐ_⦂_⇒_ Δ₂ Θ m ê₁ ê₂
ec-middle-ecctx-weaken Δ₁⊆Δ₂ (EH.⊢subᵐ ê₁<:ê₂) = EH.⊢subᵐ ê₁<:ê₂
ec-middle-ecctx-weaken Δ₁⊆Δ₂ (EH.⊢errᵐ ℓ) = EH.⊢errᵐ ℓ

ec-tail-ecctx-weaken : ∀ {Δ₁ Δ₂ t ê₁ ê₂}
  → Δ₁ ⊆ᵉ Δ₂
  → EH._⊢ᵉᵗ_⦂_⇒_ Δ₁ t ê₁ ê₂
    --------------------------------
  → EH._⊢ᵉᵗ_⦂_⇒_ Δ₂ t ê₁ ê₂
ec-tail-ecctx-weaken Δ₁⊆Δ₂ (EH.⊢injᵗ e) = EH.⊢injᵗ e
ec-tail-ecctx-weaken Δ₁⊆Δ₂ (EH.⊢idᵗ ê) = EH.⊢idᵗ ê

ec-hc-ecctx-weaken Δ₁⊆Δ₂ (EH.⊢hc ⊢h ⊢m ⊢t) =
  EH.⊢hc (ec-head-ecctx-weaken Δ₁⊆Δ₂ ⊢h)
         (ec-middle-ecctx-weaken Δ₁⊆Δ₂ ⊢m)
         (ec-tail-ecctx-weaken Δ₁⊆Δ₂ ⊢t)


mutual

  mhc-head-ecctx-weaken : ∀ {Δ₁ Δ₂ h A B}
    → Δ₁ ⊆ᵉ Δ₂
    → MH._⊢ᵐʰ_⦂_⇒_ Δ₁ h A B
      --------------------------------
    → MH._⊢ᵐʰ_⦂_⇒_ Δ₂ h A B
  mhc-head-ecctx-weaken Δ₁⊆Δ₂ (MH.⊢projʰ g ℓ) = MH.⊢projʰ g ℓ
  mhc-head-ecctx-weaken Δ₁⊆Δ₂ (MH.⊢idʰ A) = MH.⊢idʰ A

  mhc-middle-ecctx-weaken : ∀ {Δ₁ Δ₂ Θ m A B}
    → Δ₁ ⊆ᵉ Δ₂
    → MH._;_⊢ᵐᵐ_⦂_⇒_ Δ₁ Θ m A B
      --------------------------------------
    → MH._;_⊢ᵐᵐ_⦂_⇒_ Δ₂ Θ m A B
  mhc-middle-ecctx-weaken Δ₁⊆Δ₂ (MH.⊢funᵐ ⊢c ⊢d) =
    MH.⊢funᵐ (mhc-ecctx-weaken Δ₁⊆Δ₂ ⊢c) (mhc-ecctx-weaken Δ₁⊆Δ₂ ⊢d)
  mhc-middle-ecctx-weaken Δ₁⊆Δ₂ (MH.⊢codeᵐ ⊢cᵒ ⊢cᵉ) =
    MH.⊢codeᵐ ⊢cᵒ (ec-hc-ecctx-weaken Δ₁⊆Δ₂ ⊢cᵉ)
  mhc-middle-ecctx-weaken Δ₁⊆Δ₂ (MH.⊢refᵐ ⊢c ⊢d) =
    MH.⊢refᵐ (mhc-ecctx-weaken Δ₁⊆Δ₂ ⊢c) (mhc-ecctx-weaken Δ₁⊆Δ₂ ⊢d)
  mhc-middle-ecctx-weaken {Δ₁ = Δ₁} {Δ₂ = Δ₂} Δ₁⊆Δ₂ (MH.⊢forallᵐ ⊢c) =
    MH.⊢forallᵐ (mhc-ecctx-weaken (⊆ᵉ-cons {Δ₁ = Δ₁} {Δ₂ = Δ₂} Δ₁⊆Δ₂) ⊢c)
  mhc-middle-ecctx-weaken Δ₁⊆Δ₂ (MH.⊢subᵐ e₁ e₂ ⊢c) =
    MH.⊢subᵐ e₁ e₂ (mhc-ecctx-weaken Δ₁⊆Δ₂ ⊢c)
  mhc-middle-ecctx-weaken Δ₁⊆Δ₂ (MH.⊢errᵐ ℓ) = MH.⊢errᵐ ℓ
  mhc-middle-ecctx-weaken Δ₁⊆Δ₂ MH.⊢id⋆ᵐ = MH.⊢id⋆ᵐ
  mhc-middle-ecctx-weaken Δ₁⊆Δ₂ (MH.⊢idιᵐ ι) = MH.⊢idιᵐ ι

  mhc-tail-ecctx-weaken : ∀ {Δ₁ Δ₂ t A B}
    → Δ₁ ⊆ᵉ Δ₂
    → MH._⊢ᵐᵗ_⦂_⇒_ Δ₁ t A B
      --------------------------------
    → MH._⊢ᵐᵗ_⦂_⇒_ Δ₂ t A B
  mhc-tail-ecctx-weaken Δ₁⊆Δ₂ (MH.⊢injᵗ g) = MH.⊢injᵗ g
  mhc-tail-ecctx-weaken Δ₁⊆Δ₂ (MH.⊢idᵗ A) = MH.⊢idᵗ A

  mhc-ecctx-weaken : ∀ {Δ₁ Δ₂ Θ c A B}
    → Δ₁ ⊆ᵉ Δ₂
    → MH._;_⊢ᵐ_⦂_⇒_ Δ₁ Θ c A B
      -----------------------------------
    → MH._;_⊢ᵐ_⦂_⇒_ Δ₂ Θ c A B
  mhc-ecctx-weaken Δ₁⊆Δ₂ (MH.⊢hc ⊢h ⊢m ⊢t) =
    MH.⊢hc (mhc-head-ecctx-weaken Δ₁⊆Δ₂ ⊢h)
           (mhc-middle-ecctx-weaken Δ₁⊆Δ₂ ⊢m)
           (mhc-tail-ecctx-weaken Δ₁⊆Δ₂ ⊢t)


------------------------------------------------------------------------
-- EC-context weakening for terms

mutual

  code-ecctx-weaken : ∀ {Δ₁ Δ₂ Θ Γᵒ Γᵐ Σ e M T}
    → Δ₁ ⊆ᵉ Δ₂
    → Δ₁ ; ⟨ Θ , Γᵒ , Γᵐ , Σ ⟩ ; e ⊢ᵒ M ⦂ T
      ----------------------------------------------
    → Δ₂ ; ⟨ Θ , Γᵒ , Γᵐ , Σ ⟩ ; e ⊢ᵒ M ⦂ T
  code-ecctx-weaken Δ₁⊆Δ₂ (⊢constᵒ r) =
    ⊢constᵒ r
  code-ecctx-weaken Δ₁⊆Δ₂ (⊢varᵒ lookup α<:e) =
    ⊢varᵒ lookup α<:e
  code-ecctx-weaken {Δ₁ = Δ₁} {Δ₂ = Δ₂} Δ₁⊆Δ₂ (⊢lamᵒ ⊢M) =
    ⊢lamᵒ (code-ecctx-weaken (⊆ᵉ-cons {Δ₁ = Δ₁} {Δ₂ = Δ₂} Δ₁⊆Δ₂) ⊢M)
  code-ecctx-weaken Δ₁⊆Δ₂ (⊢lamᵒ-val (globalEC α<Δ₁ cutoff≤α) owner edge e′<:e ⊢M) =
    ⊢lamᵒ-val (globalEC (<-≤-trans α<Δ₁ (Δ₁⊆Δ₂ .size≤))
                         (≤-trans (Δ₁⊆Δ₂ .cutoff≤) cutoff≤α))
      owner
      edge
      e′<:e
      (code-ecctx-weaken Δ₁⊆Δ₂ ⊢M)
  code-ecctx-weaken Δ₁⊆Δ₂ (⊢appᵒ ⊢L ⊢M) =
    ⊢appᵒ (code-ecctx-weaken Δ₁⊆Δ₂ ⊢L) (code-ecctx-weaken Δ₁⊆Δ₂ ⊢M)
  code-ecctx-weaken Δ₁⊆Δ₂ (⊢splice ⊢M O↪T) =
    ⊢splice (meta-ecctx-weaken Δ₁⊆Δ₂ ⊢M) O↪T
  code-ecctx-weaken Δ₁⊆Δ₂ (⊢blameᵒ ℓ) =
    ⊢blameᵒ ℓ

  meta-ecctx-weaken : ∀ {Δ₁ Δ₂ Θ Γᵒ Γᵐ Σ M A}
    → Δ₁ ⊆ᵉ Δ₂
    → Δ₁ ; ⟨ Θ , Γᵒ , Γᵐ , Σ ⟩ ⊢ᵐ M ⦂ A
      -----------------------------------------
    → Δ₂ ; ⟨ Θ , Γᵒ , Γᵐ , Σ ⟩ ⊢ᵐ M ⦂ A
  meta-ecctx-weaken Δ₁⊆Δ₂ (⊢constᵐ r) =
    ⊢constᵐ r
  meta-ecctx-weaken Δ₁⊆Δ₂ (⊢varᵐ Γᵐ∋A) =
    ⊢varᵐ Γᵐ∋A
  meta-ecctx-weaken Δ₁⊆Δ₂ (⊢addr Σ∋A) =
    ⊢addr Σ∋A
  meta-ecctx-weaken Δ₁⊆Δ₂ (⊢lamᵐ ⊢A ⊢M) =
    ⊢lamᵐ (mtype-weaken Δ₁⊆Δ₂ ⊢A) (meta-ecctx-weaken Δ₁⊆Δ₂ ⊢M)
  meta-ecctx-weaken Δ₁⊆Δ₂ (⊢appᵐ ⊢L ⊢M) =
    ⊢appᵐ (meta-ecctx-weaken Δ₁⊆Δ₂ ⊢L) (meta-ecctx-weaken Δ₁⊆Δ₂ ⊢M)
  meta-ecctx-weaken {Δ₁ = Δ₁} {Δ₂ = Δ₂} Δ₁⊆Δ₂ (⊢eclam ⊢M) =
    ⊢eclam (meta-ecctx-weaken (⊆ᵉ-cons {Δ₁ = Δ₁} {Δ₂ = Δ₂} Δ₁⊆Δ₂) ⊢M)
  meta-ecctx-weaken Δ₁⊆Δ₂ (⊢ecapp ⊢M ⊢e) =
    ⊢ecapp (meta-ecctx-weaken Δ₁⊆Δ₂ ⊢M) (ec-weaken Δ₁⊆Δ₂ ⊢e)
  meta-ecctx-weaken Δ₁⊆Δ₂ (⊢subintro ⊢e₁ ⊢e₂ ⊢M) =
    ⊢subintro
      (ec-weaken Δ₁⊆Δ₂ ⊢e₁)
      (ec-weaken Δ₁⊆Δ₂ ⊢e₂)
      (meta-ecctx-weaken Δ₁⊆Δ₂ ⊢M)
  meta-ecctx-weaken Δ₁⊆Δ₂ (⊢subelim ⊢M e₁<:e₂) =
    ⊢subelim (meta-ecctx-weaken Δ₁⊆Δ₂ ⊢M) e₁<:e₂
  meta-ecctx-weaken Δ₁⊆Δ₂ (⊢subelim⋆ ⊢M ℓ) =
    ⊢subelim⋆ (meta-ecctx-weaken Δ₁⊆Δ₂ ⊢M) ℓ
  meta-ecctx-weaken Δ₁⊆Δ₂ (⊢quote ⊢M ⊢e O↪T) =
    ⊢quote (code-ecctx-weaken Δ₁⊆Δ₂ ⊢M) (ec-weaken Δ₁⊆Δ₂ ⊢e) O↪T
  meta-ecctx-weaken Δ₁⊆Δ₂ (⊢ref ⊢M) =
    ⊢ref (meta-ecctx-weaken Δ₁⊆Δ₂ ⊢M)
  meta-ecctx-weaken Δ₁⊆Δ₂ (⊢assign ⊢M ⊢N) =
    ⊢assign (meta-ecctx-weaken Δ₁⊆Δ₂ ⊢M) (meta-ecctx-weaken Δ₁⊆Δ₂ ⊢N)
  meta-ecctx-weaken Δ₁⊆Δ₂ (⊢deref ⊢M) =
    ⊢deref (meta-ecctx-weaken Δ₁⊆Δ₂ ⊢M)
  meta-ecctx-weaken Δ₁⊆Δ₂ (⊢cast ⊢M ⊢c) =
    ⊢cast (meta-ecctx-weaken Δ₁⊆Δ₂ ⊢M) (mhc-ecctx-weaken Δ₁⊆Δ₂ ⊢c)
  meta-ecctx-weaken Δ₁⊆Δ₂ (⊢blame ⊢A ℓ) =
    ⊢blame (mtype-weaken Δ₁⊆Δ₂ ⊢A) ℓ
