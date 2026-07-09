module LambdaAlphaRefStar.Theories.SpaceEfficiency.Proofs.ECSubstHypercoercions where

open import Data.List using (List; []; _∷_; map)
open import Data.Product using (_×_) renaming (_,_ to ⟨_,_⟩)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; cong; trans)

open import Utils using (_∋_; member-map; member-map-inv)
open import LambdaAlphaRefStar.Theories.SpaceEfficiency.CCAlphaRefStarSyntaxAndTypeSystem
open import LambdaAlphaRefStar.Theories.SpaceEfficiency.CCAlphaRefStarSemantics
  using
    (substᵉ-ehead; substᵉ-emiddle; substᵉ-etail; substᵉ-ehc;
     substᵉ-mhead; substᵉ-mmiddle; substᵉ-mtail; substᵉ-mhc; _[_]ᶜ)

import LambdaAlphaRefStar.Theories.SpaceEfficiency.ECHypercoercions as EH
import LambdaAlphaRefStar.Theories.SpaceEfficiency.MetaHypercoercions as MH


private

  subᵉ-subctx-entry : SubstEC → EC × EC → EC × EC
  subᵉ-subctx-entry σ ⟨ e₁ , e₂ ⟩ = ⟨ subᵉ-ec σ e₁ , subᵉ-ec σ e₂ ⟩

  ∋-subᵉ-subctx : ∀ {σ Θ e₁ e₂}
    → Θ ∋ˢ ⟨ e₁ , e₂ ⟩
      ----------------------------------------------------------
    → subᵉ-subctx σ Θ ∋ˢ ⟨ subᵉ-ec σ e₁ , subᵉ-ec σ e₂ ⟩
  ∋-subᵉ-subctx {σ = σ} edge = member-map {f = subᵉ-subctx-entry σ} edge

  ec-subtype-sub : ∀ σ {Θ e₁ e₂}
    → Θ ⊢ᵉ e₁ <: e₂
      ---------------------------------------------------
    → subᵉ-subctx σ Θ ⊢ᵉ subᵉ-ec σ e₁ <: subᵉ-ec σ e₂
  ec-subtype-sub σ <:-ε = <:-ε
  ec-subtype-sub σ <:-refl = <:-refl
  ec-subtype-sub σ {Θ = Θ} (<:-ax edge) = <:-ax (∋-subᵉ-subctx {σ = σ} {Θ = Θ} edge)
  ec-subtype-sub σ (<:-trans e₁<:e e<:e₂) =
    <:-trans (ec-subtype-sub σ e₁<:e) (ec-subtype-sub σ e<:e₂)

  ec⋆-subtype-sub : ∀ σ {Θ ê₁ ê₂}
    → Θ ⊢ᵉ ê₁ <:⋆ ê₂
      ---------------------------------------------------------
    → subᵉ-subctx σ Θ ⊢ᵉ subᵉ-ec⋆ σ ê₁ <:⋆ subᵉ-ec⋆ σ ê₂
  ec⋆-subtype-sub σ <:-⋆ = <:-⋆
  ec⋆-subtype-sub σ (<:-ec e₁<:e₂) = <:-ec (ec-subtype-sub σ e₁<:e₂)

  subᵉ-ground : ∀ {G}
    → (σ : SubstEC)
    → Ground G
      ----------------------
    → Ground (subᵉ σ G)
  subᵉ-ground σ gbase = gbase
  subᵉ-ground σ gfun = gfun
  subᵉ-ground σ gref = gref
  subᵉ-ground σ gcode = gcode
  subᵉ-ground σ gforall = gforall
  subᵉ-ground σ gsub = gsub

  sub-exts-suc-ec : ∀ σ e
      -------------------------------------------------------------------
    → subᵉ-ec (extsᵉ σ) (⇑ᵉ-ec e) ≡ ⇑ᵉ-ec (subᵉ-ec σ e)
  sub-exts-suc-ec σ ε = refl
  sub-exts-suc-ec σ (` α) = refl

  sub-exts-suc-subctx-edges : (σ : SubstEC) (edges : List (EC × EC))
      ------------------------------------------------------------------------
    → map (subᵉ-subctx-entry (extsᵉ σ))
        (map (λ { ⟨ e₁ , e₂ ⟩ → ⟨ ⇑ᵉ-ec e₁ , ⇑ᵉ-ec e₂ ⟩ }) edges)
      ≡ map (λ { ⟨ e₁ , e₂ ⟩ → ⟨ ⇑ᵉ-ec e₁ , ⇑ᵉ-ec e₂ ⟩ })
        (map (subᵉ-subctx-entry σ) edges)
  sub-exts-suc-subctx-edges σ [] = refl
  sub-exts-suc-subctx-edges σ (⟨ e₁ , e₂ ⟩ ∷ edges)
    rewrite sub-exts-suc-ec σ e₁
          | sub-exts-suc-ec σ e₂ =
      cong (λ xs → ⟨ ⇑ᵉ-ec (subᵉ-ec σ e₁) , ⇑ᵉ-ec (subᵉ-ec σ e₂) ⟩ ∷ xs)
        (sub-exts-suc-subctx-edges σ edges)

  sub-exts-suc-subctx : ∀ σ Θ
      ------------------------------------------------------------------------
    → subᵉ-subctx (extsᵉ σ) (⇑ᵉ-subctx Θ) ≡ ⇑ᵉ-subctx (subᵉ-subctx σ Θ)
  sub-exts-suc-subctx σ Θ =
    subctx-cong (sub-exts-suc-subctx-edges σ (Θ .edges))

  subᵉ-subctx-ext : ∀ σ Θ e₁ e₂
      ---------------------------------------------------------------------------------
    → subᵉ-subctx σ (Θ , e₁ <: e₂) ≡ subᵉ-subctx σ Θ , subᵉ-ec σ e₁ <: subᵉ-ec σ e₂
  subᵉ-subctx-ext σ Θ e₁ e₂ = subctx-cong refl

  single-shift-ec : ∀ e e′
      ------------------------------------------
    → subᵉ-ec (e •ᵉₛ idsᵉ) (⇑ᵉ-ec e′) ≡ e′
  single-shift-ec e ε = refl
  single-shift-ec e (` α) = refl

  single-shift-subctx-edges : ∀ e (edges : List (EC × EC))
      --------------------------------------------------------------------------------
    → map (subᵉ-subctx-entry (e •ᵉₛ idsᵉ))
        (map (λ { ⟨ e₁ , e₂ ⟩ → ⟨ ⇑ᵉ-ec e₁ , ⇑ᵉ-ec e₂ ⟩ }) edges)
      ≡ edges
  single-shift-subctx-edges e [] = refl
  single-shift-subctx-edges e (⟨ e₁ , e₂ ⟩ ∷ edges)
    rewrite single-shift-ec e e₁
          | single-shift-ec e e₂ =
      cong (λ xs → ⟨ e₁ , e₂ ⟩ ∷ xs) (single-shift-subctx-edges e edges)

  single-shift-subctx : ∀ e Θ
      ---------------------------------------------------
    → subᵉ-subctx (e •ᵉₛ idsᵉ) (⇑ᵉ-subctx Θ) ≡ Θ
  single-shift-subctx e Θ = subctx-cong (single-shift-subctx-edges e (Θ .edges))


------------------------------------------------------------------------
-- Generic EC substitution for hypercoercion typing

ehc-head-sub : ∀ {Δ₁ Δ₂ σ h ê₁ ê₂}
  → EH._⊢ᵉʰ_⦂_⇒_ Δ₁ h ê₁ ê₂
    -------------------------------------------------------------------
  → EH._⊢ᵉʰ_⦂_⇒_ Δ₂ (substᵉ-ehead σ h) (subᵉ-ec⋆ σ ê₁) (subᵉ-ec⋆ σ ê₂)
ehc-head-sub (EH.⊢projʰ e ℓ) = EH.⊢projʰ (subᵉ-ec _ e) ℓ
ehc-head-sub (EH.⊢idʰ ê) = EH.⊢idʰ (subᵉ-ec⋆ _ ê)

ehc-middle-sub : ∀ {Δ₁ Δ₂ σ Θ m ê₁ ê₂}
  → EH._;_⊢ᵉᵐ_⦂_⇒_ Δ₁ Θ m ê₁ ê₂
    ----------------------------------------------------------------------------------------------------
  → EH._;_⊢ᵉᵐ_⦂_⇒_ Δ₂ (subᵉ-subctx σ Θ) (substᵉ-emiddle σ m)
      (subᵉ-ec⋆ σ ê₁) (subᵉ-ec⋆ σ ê₂)
ehc-middle-sub {σ = σ} (EH.⊢subᵐ ê₁<:ê₂) = EH.⊢subᵐ (ec⋆-subtype-sub σ ê₁<:ê₂)
ehc-middle-sub (EH.⊢errᵐ ℓ) = EH.⊢errᵐ ℓ

ehc-tail-sub : ∀ {Δ₁ Δ₂ σ t ê₁ ê₂}
  → EH._⊢ᵉᵗ_⦂_⇒_ Δ₁ t ê₁ ê₂
    -------------------------------------------------------------------
  → EH._⊢ᵉᵗ_⦂_⇒_ Δ₂ (substᵉ-etail σ t) (subᵉ-ec⋆ σ ê₁) (subᵉ-ec⋆ σ ê₂)
ehc-tail-sub (EH.⊢injᵗ e) = EH.⊢injᵗ (subᵉ-ec _ e)
ehc-tail-sub (EH.⊢idᵗ ê) = EH.⊢idᵗ (subᵉ-ec⋆ _ ê)

ehc-sub : ∀ {Δ₁ Δ₂ σ Θ c ê₁ ê₂}
  → EH._;_⊢ᵉ_⦂_⇒_ Δ₁ Θ c ê₁ ê₂
    ---------------------------------------------------------------------------------------------
  → EH._;_⊢ᵉ_⦂_⇒_ Δ₂ (subᵉ-subctx σ Θ) (substᵉ-ehc σ c)
      (subᵉ-ec⋆ σ ê₁) (subᵉ-ec⋆ σ ê₂)
ehc-sub (EH.⊢hc ⊢h ⊢m ⊢t) =
  EH.⊢hc (ehc-head-sub ⊢h) (ehc-middle-sub ⊢m) (ehc-tail-sub ⊢t)


mutual

  mhc-head-sub : ∀ {Δ₁ Δ₂ σ h A B}
    → MH._⊢ᵐʰ_⦂_⇒_ Δ₁ h A B
      -------------------------------------------------------------
    → MH._⊢ᵐʰ_⦂_⇒_ Δ₂ (substᵉ-mhead σ h) (subᵉ σ A) (subᵉ σ B)
  mhc-head-sub {σ = σ} (MH.⊢projʰ g ℓ) = MH.⊢projʰ (subᵉ-ground σ g) ℓ
  mhc-head-sub {σ = σ} (MH.⊢idʰ A) = MH.⊢idʰ (subᵉ σ A)

  mhc-middle-sub : ∀ {Δ₁ Δ₂ σ Θ m A B}
    → MH._;_⊢ᵐᵐ_⦂_⇒_ Δ₁ Θ m A B
      ----------------------------------------------------------------------------------
    → MH._;_⊢ᵐᵐ_⦂_⇒_ Δ₂ (subᵉ-subctx σ Θ) (substᵉ-mmiddle σ m)
        (subᵉ σ A) (subᵉ σ B)
  mhc-middle-sub (MH.⊢funᵐ ⊢c ⊢d) =
    MH.⊢funᵐ (mhc-sub ⊢c) (mhc-sub ⊢d)
  mhc-middle-sub (MH.⊢codeᵐ ⊢cᵒ ⊢cᵉ) =
    MH.⊢codeᵐ ⊢cᵒ (ehc-sub ⊢cᵉ)
  mhc-middle-sub (MH.⊢refᵐ ⊢c ⊢d) =
    MH.⊢refᵐ (mhc-sub ⊢c) (mhc-sub ⊢d)
  mhc-middle-sub {Δ₂ = Δ₂} {σ = σ} {Θ = Θ} (MH.⊢forallᵐ {A = A} {B = B} {c = c} ⊢c) =
    MH.⊢forallᵐ
      (subst
        (λ Θ′ → MH._;_⊢ᵐ_⦂_⇒_ (Δ₂ ,α) Θ′ (substᵉ-mhc (extsᵉ σ) c)
                  (subᵉ (extsᵉ σ) A) (subᵉ (extsᵉ σ) B))
        (sub-exts-suc-subctx σ Θ)
        (mhc-sub {σ = extsᵉ σ} ⊢c))
  mhc-middle-sub {Δ₂ = Δ₂} {σ = σ} {Θ = Θ} (MH.⊢subᵐ {A = A} {B = B} {c = c} e₁ e₂ ⊢c) =
    MH.⊢subᵐ (subᵉ-ec σ e₁) (subᵉ-ec σ e₂)
      (subst
        (λ Θ′ → MH._;_⊢ᵐ_⦂_⇒_ Δ₂ Θ′ (substᵉ-mhc σ c) (subᵉ σ A) (subᵉ σ B))
        (subᵉ-subctx-ext σ Θ e₁ e₂)
        (mhc-sub {σ = σ} ⊢c))
  mhc-middle-sub (MH.⊢errᵐ ℓ) = MH.⊢errᵐ ℓ
  mhc-middle-sub MH.⊢id⋆ᵐ = MH.⊢id⋆ᵐ
  mhc-middle-sub (MH.⊢idιᵐ ι) = MH.⊢idιᵐ ι

  mhc-tail-sub : ∀ {Δ₁ Δ₂ σ t A B}
    → MH._⊢ᵐᵗ_⦂_⇒_ Δ₁ t A B
      -------------------------------------------------------------
    → MH._⊢ᵐᵗ_⦂_⇒_ Δ₂ (substᵉ-mtail σ t) (subᵉ σ A) (subᵉ σ B)
  mhc-tail-sub {σ = σ} (MH.⊢injᵗ g) = MH.⊢injᵗ (subᵉ-ground σ g)
  mhc-tail-sub {σ = σ} (MH.⊢idᵗ A) = MH.⊢idᵗ (subᵉ σ A)

  mhc-sub : ∀ {Δ₁ Δ₂ σ Θ c A B}
    → MH._;_⊢ᵐ_⦂_⇒_ Δ₁ Θ c A B
      -------------------------------------------------------------------------
    → MH._;_⊢ᵐ_⦂_⇒_ Δ₂ (subᵉ-subctx σ Θ) (substᵉ-mhc σ c)
        (subᵉ σ A) (subᵉ σ B)
  mhc-sub (MH.⊢hc ⊢h ⊢m ⊢t) =
    MH.⊢hc (mhc-head-sub ⊢h) (mhc-middle-sub ⊢m) (mhc-tail-sub ⊢t)


subst-ec-hc : ∀ {Δ Θ A B c e}
  → MH._;_⊢ᵐ_⦂_⇒_ (Δ ,α) (⇑ᵉ-subctx Θ) c A B
  → Δ ⊢ᵉ e
    ---------------------------------------------------------------
  → MH._;_⊢ᵐ_⦂_⇒_ Δ Θ (c [ e ]ᶜ) (A [ e ]ᵉ) (B [ e ]ᵉ)
subst-ec-hc {Θ = Θ} {e = e} ⊢c ⊢e =
  subst
    (λ Θ′ → MH._;_⊢ᵐ_⦂_⇒_ _ Θ′ _ _ _)
    (single-shift-subctx e Θ)
    (mhc-sub {σ = e •ᵉₛ idsᵉ} ⊢c)
