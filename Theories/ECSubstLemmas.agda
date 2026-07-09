{-# OPTIONS --rewriting #-}

module LambdaAlphaRefStar.Theories.ECSubstLemmas where

open import Agda.Builtin.Equality.Rewrite
open import Data.List using (List; []; _∷_; map)
open import Data.Maybe using (just)
open import Data.Product using (∃-syntax; _×_) renaming (_,_ to ⟨_,_⟩)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; cong; trans)
  renaming (sym to ≡-sym)
open import Relation.Nullary.Negation using (contradiction)

open import Utils
open import LambdaAlphaRefStar.Theories.CCAlphaRefStarSyntaxAndTypeSystem
open import LambdaAlphaRefStar.Theories.ECSubst
open import LambdaAlphaRefStar.Theories.SubCtxWeakening using (code-⊆ˢ; subctx-lex-to-global)
import LambdaAlphaRefStar.Theories.CoercionSequences.EC.Definition as EC
import LambdaAlphaRefStar.Theories.CoercionSequences.Meta.Definition as MC


private

  record ECRenWF (Δ₁ Δ₂ : ECCtx) (ρ : RenameEC) : Set where
    constructor ecRenWF
    field
      injective : ∀ {α β} → ρ α ≡ ρ β → α ≡ β
      lookup-ren : ∀ {α} → α < Δ₁ .size → ρ α < Δ₂ .size
      global-ren : ∀ {α} → GlobalEC Δ₁ α → GlobalEC Δ₂ (ρ α)

  open ECRenWF

  record ECSubstWF (Δ₁ Δ₂ : ECCtx) (σ : SubstEC) : Set where
    constructor ecSubstWF
    field
      lookup-sub : ∀ {α} → α < Δ₁ .size → Δ₂ ⊢ᵉ σ α
      global-sub : ∀ {α} → GlobalEC Δ₁ α → ∃[ β ] (σ α ≡ ` β × GlobalEC Δ₂ β)

  open ECSubstWF

  -- OCtxSub is necessary because applying an EC substitution to a code
  -- context does not necessarily produce a well-formed code context.
  -- Code-context entries store EC variables, not arbitrary ECs, so a valid
  -- code context cannot contain ε as an annotation.  `OCtxSub σ Γᵒ₁ Γᵒ₂`
  -- records the pointwise fact that every annotation α in Γᵒ₁ is mapped by σ
  -- to some variable-shaped EC ` β, and Γᵒ₂ is the corresponding code context
  -- with those β annotations.
  data OEntriesSub (σ : SubstEC) : List (OType × ECVar) → List (OType × ECVar) → Set where

    osub-[] : OEntriesSub σ [] []

    osub-∷ : ∀ {T α β Γᵒ₁ Γᵒ₂}
      → σ α ≡ ` β   -- it must give us an EC variable, not ε
      → OEntriesSub σ Γᵒ₁ Γᵒ₂
        ---------------------------------------------------------
      → OEntriesSub σ (⟨ T , α ⟩ ∷ Γᵒ₁) (⟨ T , β ⟩ ∷ Γᵒ₂)

  record OCtxSub (σ : SubstEC) (Γᵒ₁ Γᵒ₂ : OCtx) : Set where
    constructor octx-sub
    field
      entries-sub : OEntriesSub σ (Γᵒ₁ .entries) (Γᵒ₂ .entries)
      owner-sub : ∀ {α β x T}
        → σ α ≡ ` β
        → lookupOwner (Γᵒ₁ .entries) α ≡ just ⟨ x , T ⟩
          -----------------------------------------------------
        → lookupOwner (Γᵒ₂ .entries) β ≡ just ⟨ x , T ⟩
      global-sub : ∀ {T α β}
        → σ α ≡ ` β
        → GlobalEntries Γᵒ₁ ∋ ⟨ T , α ⟩
          ---------------------------------
        → GlobalEntries Γᵒ₂ ∋ ⟨ T , β ⟩

  open OCtxSub

  owner-sub-octx : ∀ {σ Γᵒ₁ Γᵒ₂ α β x T}
    → OCtxSub σ Γᵒ₁ Γᵒ₂
    → σ α ≡ ` β
    → lookupOwner (Γᵒ₁ .entries) α ≡ just ⟨ x , T ⟩
      -----------------------------------------------------
    → lookupOwner (Γᵒ₂ .entries) β ≡ just ⟨ x , T ⟩
  owner-sub-octx σ[Γᵒ₁]=Γᵒ₂ = σ[Γᵒ₁]=Γᵒ₂ .owner-sub

  global-sub-octx : ∀ {σ Γᵒ₁ Γᵒ₂ T α β}
    → OCtxSub σ Γᵒ₁ Γᵒ₂
    → σ α ≡ ` β
    → GlobalEntries Γᵒ₁ ∋ ⟨ T , α ⟩
      ---------------------------------
    → GlobalEntries Γᵒ₂ ∋ ⟨ T , β ⟩
  global-sub-octx σ[Γᵒ₁]=Γᵒ₂ = σ[Γᵒ₁]=Γᵒ₂ .global-sub



  ext-ren-wf : ∀ {Δ₁ Δ₂ ρ}
    → ECRenWF Δ₁ Δ₂ ρ
      ---------------------------------------
    → ECRenWF (Δ₁ ,α) (Δ₂ ,α) (extᵉ ρ)
  ext-ren-wf {Δ₁ = Δ₁} {Δ₂ = Δ₂} {ρ = ρ} ρ-wf = ecRenWF inj lookup global
    where
      inj : ∀ {α β} → extᵉ ρ α ≡ extᵉ ρ β → α ≡ β
      inj {zero} {zero} eq = refl
      inj {zero} {suc β} ()
      inj {suc α} {zero} ()
      inj {suc α} {suc β} eq = cong suc (ρ-wf .injective (suc-inj eq))
        where
        suc-inj : ∀ {m n} → suc m ≡ suc n → m ≡ n
        suc-inj refl = refl

      lookup : ∀ {α}
        → α < (Δ₁ ,α) .size
          -----------------------------------------
        → extᵉ ρ α < (Δ₂ ,α) .size
      lookup {zero} _ = s≤s z≤n
      lookup {suc α} (s≤s α<Δ₁) = s≤s (ρ-wf .lookup-ren α<Δ₁)

      global : ∀ {α}
        → GlobalEC (Δ₁ ,α) α
          -----------------------------------
        → GlobalEC (Δ₂ ,α) (extᵉ ρ α)
      global {zero} (globalEC α<Δ₁ ())
      global {suc α} (globalEC (s≤s α<Δ₁) (s≤s cutoff≤α))
        with ρ-wf .global-ren (globalEC α<Δ₁ cutoff≤α)
      ... | globalEC ρα<Δ₂ cutoff≤ρα = globalEC (s≤s ρα<Δ₂) (s≤s cutoff≤ρα)

  suc-wf : ∀ Δ
      --------------------------------
    → ECRenWF Δ (Δ ,α) suc
  suc-wf Δ = ecRenWF (λ { refl → refl }) (λ α<Δ → s≤s α<Δ) λ where
    (globalEC α<Δ cutoff≤α) → globalEC (s≤s α<Δ) (s≤s cutoff≤α)

  ec-ren-wf : ∀ {Δ₁ Δ₂ ρ e}
    → ECRenWF Δ₁ Δ₂ ρ
    → Δ₁ ⊢ᵉ e
      --------------------------
    → Δ₂ ⊢ᵉ renᵉ-ec ρ e
  ec-ren-wf ρ-wf wf-ε = wf-ε
  ec-ren-wf ρ-wf (wf-` α∈Δ₁) = wf-` (ρ-wf .lookup-ren α∈Δ₁)

  ec⋆-ren-wf : ∀ {Δ₁ Δ₂ ρ ê}
    → ECRenWF Δ₁ Δ₂ ρ
    → Δ₁ ⊢ᵉ⋆ ê
      -----------------------------
    → Δ₂ ⊢ᵉ⋆ renᵉ-ec⋆ ρ ê
  ec⋆-ren-wf ρ-wf wf-⋆ = wf-⋆
  ec⋆-ren-wf ρ-wf (wf-ec ⊢e) = wf-ec (ec-ren-wf ρ-wf ⊢e)

  mtype-ren-wf : ∀ {Δ₁ Δ₂ ρ A}
    → ECRenWF Δ₁ Δ₂ ρ
    → Δ₁ ⊢ᵐᵗ A
      -------------------------
    → Δ₂ ⊢ᵐᵗ renᵉ ρ A
  mtype-ren-wf ρ-wf wf-⋆ = wf-⋆
  mtype-ren-wf ρ-wf wf-base = wf-base
  mtype-ren-wf ρ-wf (wf-fun ⊢A ⊢B) =
    wf-fun (mtype-ren-wf ρ-wf ⊢A) (mtype-ren-wf ρ-wf ⊢B)
  mtype-ren-wf ρ-wf (wf-ref ⊢A) =
    wf-ref (mtype-ren-wf ρ-wf ⊢A)
  mtype-ren-wf ρ-wf (wf-code ⊢ê) =
    wf-code (ec⋆-ren-wf ρ-wf ⊢ê)
  mtype-ren-wf ρ-wf (wf-forall ⊢A) =
    wf-forall (mtype-ren-wf (ext-ren-wf ρ-wf) ⊢A)
  mtype-ren-wf ρ-wf (wf-sub ⊢e₁ ⊢e₂ ⊢A) =
    wf-sub (ec-ren-wf ρ-wf ⊢e₁)
           (ec-ren-wf ρ-wf ⊢e₂)
           (mtype-ren-wf ρ-wf ⊢A)

  ext-subst-wf : ∀ {Δ₁ Δ₂ σ}
    → ECSubstWF Δ₁ Δ₂ σ
      -------------------------------------------------
    → ECSubstWF (Δ₁ ,α) (Δ₂ ,α) (extsᵉ σ)
  ext-subst-wf {Δ₁ = Δ₁} {Δ₂ = Δ₂} {σ = σ} σ-wf = ecSubstWF lookup global
    where
      lookup : ∀ {α}
        → α < (Δ₁ ,α) .size
          ----------------------------------------
        → Δ₂ ,α ⊢ᵉ extsᵉ σ α
      lookup {zero} _ = wf-` (s≤s z≤n)
      lookup {suc α} (s≤s α<Δ₁) =
        ec-ren-wf (suc-wf Δ₂) (σ-wf .lookup-sub α<Δ₁)

      global : ∀ {α}
        → GlobalEC (Δ₁ ,α) α
          ---------------------------------------------------------------
        → ∃[ β ] (extsᵉ σ α ≡ ` β × GlobalEC (Δ₂ ,α) β)
      global {zero} (globalEC α<Δ₁ ())
      global {suc α} (globalEC (s≤s α<Δ₁) (s≤s cutoff≤α)) with σ-wf .global-sub (globalEC α<Δ₁ cutoff≤α)
      ... | ⟨ β , ⟨ σβ≡`β , globalβ ⟩ ⟩ rewrite σβ≡`β =
        ⟨ suc β , ⟨ refl , globalEC (s≤s (globalβ .<size)) (s≤s (cutoff≤ globalβ)) ⟩ ⟩

  single-subst-wf : ∀ {Δ e}
    → Δ ⊢ᵉ e
      ---------------------------------------------
    → ECSubstWF (Δ ,α) Δ (e •ᵉₛ idsᵉ)
  single-subst-wf {Δ = Δ} {e = e} ⊢e = ecSubstWF lookup global
    where
      lookup : ∀ {α}
        → α < (Δ ,α) .size
          ------------------------------
        → Δ ⊢ᵉ (e •ᵉₛ idsᵉ) α
      lookup {zero} _ = ⊢e
      lookup {suc α} (s≤s α<Δ) = wf-` α<Δ

      global : ∀ {α}
        → GlobalEC (Δ ,α) α
          -------------------------------------------------------
        → ∃[ β ] ((e •ᵉₛ idsᵉ) α ≡ ` β × GlobalEC Δ β)
      global {zero} (globalEC α<Δ ())
      global {suc α} (globalEC (s≤s α<Δ) (s≤s cutoff≤α)) =
        ⟨ _ , ⟨ refl , globalEC α<Δ cutoff≤α ⟩ ⟩

  fresh-subst-wf : ∀ Δ
      ------------------------------------------------------------------------
    → ECSubstWF (Δ ,α) (Δ ,ᵍα) ((` freshᵉ Δ) •ᵉₛ idsᵉ)
  fresh-subst-wf Δ = ecSubstWF lookup global
    where
      lookup : ∀ {α}
        → α < (Δ ,α) .size
          --------------------------------------------
        → Δ ,ᵍα ⊢ᵉ ((` freshᵉ Δ) •ᵉₛ idsᵉ) α
      lookup {zero} _ = wf-` (s≤s ≤-refl)
      lookup {suc α} (s≤s α<Δ) = wf-` (m≤n⇒m≤1+n α<Δ)

      global : ∀ {α}
        → GlobalEC (Δ ,α) α
          ---------------------------------------------------------------------------------
        → ∃[ β ] (((` freshᵉ Δ) •ᵉₛ idsᵉ) α ≡ ` β × GlobalEC (Δ ,ᵍα) β)
      global {zero} (globalEC α<Δ ())
      global {suc α} (globalEC (s≤s α<Δ) (s≤s cutoff≤α)) =
        ⟨ _ , ⟨ refl , globalEC (m≤n⇒m≤1+n α<Δ) cutoff≤α ⟩ ⟩

  ec-sub-wf : ∀ {Δ₁ Δ₂ σ e}
    → ECSubstWF Δ₁ Δ₂ σ
    → Δ₁ ⊢ᵉ e
      --------------------------
    → Δ₂ ⊢ᵉ subᵉ-ec σ e
  ec-sub-wf σ-wf wf-ε = wf-ε
  ec-sub-wf σ-wf (wf-` α∈Δ₁) = σ-wf .lookup-sub α∈Δ₁

  ec⋆-sub-wf : ∀ {Δ₁ Δ₂ σ ê}
    → ECSubstWF Δ₁ Δ₂ σ
    → Δ₁ ⊢ᵉ⋆ ê
      -----------------------------
    → Δ₂ ⊢ᵉ⋆ subᵉ-ec⋆ σ ê
  ec⋆-sub-wf σ-wf wf-⋆ = wf-⋆
  ec⋆-sub-wf σ-wf (wf-ec ⊢e) = wf-ec (ec-sub-wf σ-wf ⊢e)

  mtype-sub-wf : ∀ {Δ₁ Δ₂ σ A}
    → ECSubstWF Δ₁ Δ₂ σ
    → Δ₁ ⊢ᵐᵗ A
      -------------------------
    → Δ₂ ⊢ᵐᵗ subᵉ σ A
  mtype-sub-wf σ-wf wf-⋆ = wf-⋆
  mtype-sub-wf σ-wf wf-base = wf-base
  mtype-sub-wf σ-wf (wf-fun ⊢A ⊢B) =
    wf-fun (mtype-sub-wf σ-wf ⊢A) (mtype-sub-wf σ-wf ⊢B)
  mtype-sub-wf σ-wf (wf-ref ⊢A) =
    wf-ref (mtype-sub-wf σ-wf ⊢A)
  mtype-sub-wf σ-wf (wf-code ⊢ê) =
    wf-code (ec⋆-sub-wf σ-wf ⊢ê)
  mtype-sub-wf σ-wf (wf-forall ⊢A) =
    wf-forall (mtype-sub-wf (ext-subst-wf σ-wf) ⊢A)
  mtype-sub-wf σ-wf (wf-sub ⊢e₁ ⊢e₂ ⊢A) =
    wf-sub (ec-sub-wf σ-wf ⊢e₁)
           (ec-sub-wf σ-wf ⊢e₂)
           (mtype-sub-wf σ-wf ⊢A)

  renᵉ-ec-compose : ∀ ρ τ e
      -------------------------------------------------------------
    → renᵉ-ec ρ (renᵉ-ec τ e) ≡ renᵉ-ec (λ α → ρ (τ α)) e
  renᵉ-ec-compose ρ τ ε = refl
  renᵉ-ec-compose ρ τ (` α) = refl

  renᵉ-ec⋆-compose : ∀ ρ τ ê
      ----------------------------------------------------------------
    → renᵉ-ec⋆ ρ (renᵉ-ec⋆ τ ê) ≡ renᵉ-ec⋆ (λ α → ρ (τ α)) ê
  renᵉ-ec⋆-compose ρ τ ⋆ = refl
  renᵉ-ec⋆-compose ρ τ (ec e) rewrite renᵉ-ec-compose ρ τ e = refl

  renᵉ-mtype-compose : ∀ ρ τ A
      -------------------------------------------------------
    → renᵉ ρ (renᵉ τ A) ≡ renᵉ (λ α → ρ (τ α)) A
  renᵉ-mtype-compose ρ τ ⋆ = refl
  renᵉ-mtype-compose ρ τ (` ι) = refl
  renᵉ-mtype-compose ρ τ (A ⇒ B)
    rewrite renᵉ-mtype-compose ρ τ A
          | renᵉ-mtype-compose ρ τ B = refl
  renᵉ-mtype-compose ρ τ (Ref A)
    rewrite renᵉ-mtype-compose ρ τ A = refl
  renᵉ-mtype-compose ρ τ (‶ O ″ ê)
    rewrite renᵉ-ec⋆-compose ρ τ ê = refl
  renᵉ-mtype-compose ρ τ (∀̇ A)
    rewrite renᵉ-mtype-compose (extᵉ ρ) (extᵉ τ) A =
    cong (λ f → ∀̇ renᵉ f A) (extensionality λ where
      zero → refl
      (suc α) → refl)
  renᵉ-mtype-compose ρ τ (e₁ <: e₂ => A)
    rewrite renᵉ-ec-compose ρ τ e₁
          | renᵉ-ec-compose ρ τ e₂
          | renᵉ-mtype-compose ρ τ A = refl

  renᵉ-subctx-entry : RenameEC → EC × EC → EC × EC
  renᵉ-subctx-entry ρ ⟨ e₁ , e₂ ⟩ = ⟨ renᵉ-ec ρ e₁ , renᵉ-ec ρ e₂ ⟩

  subᵉ-subctx-entry : SubstEC → EC × EC → EC × EC
  subᵉ-subctx-entry σ ⟨ e₁ , e₂ ⟩ = ⟨ subᵉ-ec σ e₁ , subᵉ-ec σ e₂ ⟩

  ren-ext-suc-ec : ∀ ρ e
      -------------------------------------------------------------------
    → renᵉ-ec (extᵉ ρ) (⇑ᵉ-ec e) ≡ ⇑ᵉ-ec (renᵉ-ec ρ e)
  ren-ext-suc-ec ρ ε = refl
  ren-ext-suc-ec ρ (` α) = refl
  {-# REWRITE ren-ext-suc-ec #-}

  ren-ext-suc-subctx-edges : ∀ ρ Θ
      ------------------------------------------------------------------------
    → map (renᵉ-subctx-entry (extᵉ ρ)) (map (renᵉ-subctx-entry suc) Θ)
      ≡ map (renᵉ-subctx-entry suc) (map (renᵉ-subctx-entry ρ) Θ)
  ren-ext-suc-subctx-edges ρ [] = refl
  ren-ext-suc-subctx-edges ρ (_ ∷ Θ) rewrite ren-ext-suc-subctx-edges ρ Θ = refl

  ren-ext-suc-subctx : ∀ ρ Θ
      ------------------------------------------------------------------------
    → renᵉ-subctx (extᵉ ρ) (⇑ᵉ-subctx Θ) ≡ ⇑ᵉ-subctx (renᵉ-subctx ρ Θ)
  ren-ext-suc-subctx ρ Θ =
    subctx-cong (ren-ext-suc-subctx-edges ρ (Θ .edges))

  ren-ext-suc-octx-entries : ∀ ρ Γᵒ
      ---------------------------------------------------------------------
    → map (renᵉ-octx-entry (extᵉ ρ)) (map (renᵉ-octx-entry suc) Γᵒ)
      ≡ map (renᵉ-octx-entry suc) (map (renᵉ-octx-entry ρ) Γᵒ)
  ren-ext-suc-octx-entries ρ [] = refl
  ren-ext-suc-octx-entries ρ (⟨ T , α ⟩ ∷ Γᵒ) rewrite ren-ext-suc-octx-entries ρ Γᵒ = refl
  {-# REWRITE ren-ext-suc-octx-entries #-}

  ren-ext-suc-octx : ∀ ρ Γᵒ
    → renᵉ-octx (extᵉ ρ) (⇑ᵉ-octx Γᵒ) ≡ ⇑ᵉ-octx (renᵉ-octx ρ Γᵒ)
  ren-ext-suc-octx ρ Γᵒ =
    octx-cong (ren-ext-suc-octx-entries ρ (Γᵒ .entries))

  ren-ext-suc-octx-lex : ∀ ρ Γᵒ T
    → renᵉ-octx (extᵉ ρ) (⇑ᵉ-octx Γᵒ , T ＠ zero) ≡ ⇑ᵉ-octx (renᵉ-octx ρ Γᵒ) , T ＠ zero
  ren-ext-suc-octx-lex ρ Γᵒ T =
    octx-cong (cong (⟨ T , zero ⟩ ∷_) (ren-ext-suc-octx-entries ρ (Γᵒ .entries)))

  ren-ext-suc-mtype : ∀ ρ A
      ---------------------------------------------------------
    → renᵉ (extᵉ ρ) (renᵉ suc A) ≡ renᵉ suc (renᵉ ρ A)
  ren-ext-suc-mtype ρ A rewrite renᵉ-mtype-compose (extᵉ ρ) suc A
                              | renᵉ-mtype-compose suc ρ A = refl
  {-# REWRITE ren-ext-suc-mtype #-}

  ren-ext-suc-mctx-map : (ρ : RenameEC) (Γᵐ : MCtx)
      --------------------------------------------------------------------------------
    → map (renᵉ (extᵉ ρ)) (map (renᵉ suc) Γᵐ) ≡ map (renᵉ suc) (map (renᵉ ρ) Γᵐ)
  ren-ext-suc-mctx-map ρ [] = refl
  ren-ext-suc-mctx-map ρ (A ∷ Γᵐ) rewrite ren-ext-suc-mctx-map ρ Γᵐ = refl
  {-# REWRITE ren-ext-suc-mctx-map #-}

  ctx-cong : ∀ {Θ Θ′ : SubCtx} {Γᵒ Γᵒ′ : OCtx} {Γᵐ Γᵐ′ : MCtx} {Σ Σ′ : HeapCtx}
    → Θ ≡ Θ′
    → Γᵒ ≡ Γᵒ′
    → Γᵐ ≡ Γᵐ′
    → Σ ≡ Σ′
      ------------------------------------
    → ⟨ Θ , Γᵒ , Γᵐ , Σ ⟩ ≡ ⟨ Θ′ , Γᵒ′ , Γᵐ′ , Σ′ ⟩
  ctx-cong refl refl refl refl = refl

  lookup-ren-mctx : ∀ {ρ Γᵐ x A}
    → Γᵐ ∋ x ⦂ A
      ---------------------------------
    → renᵉ-mctx ρ Γᵐ ∋ x ⦂ renᵉ ρ A
  lookup-ren-mctx here = here
  lookup-ren-mctx (there lookup) = there (lookup-ren-mctx lookup)

  lookup-sub-mctx : ∀ {σ Γᵐ x A}
    → Γᵐ ∋ x ⦂ A
      ---------------------------------
    → subᵉ-mctx σ Γᵐ ∋ x ⦂ subᵉ σ A
  lookup-sub-mctx here = here
  lookup-sub-mctx (there lookup) = there (lookup-sub-mctx lookup)

  lookup-ren-octx : ∀ {ρ Γᵒ x T α}
    → Γᵒ ∋ᵒ x ⦂ ⟨ T , α ⟩
      ------------------------------------------
    → renᵉ-octx ρ Γᵒ ∋ᵒ x ⦂ ⟨ T , ρ α ⟩
  lookup-ren-octx lookup = lookup-map lookup

  lookup-sub-oentries : ∀ {σ Γᵒ₁ Γᵒ₂ x T α}
    → OEntriesSub σ Γᵒ₁ Γᵒ₂
    → Γᵒ₁ ∋ x ⦂ ⟨ T , α ⟩
      ----------------------------------------------------
    → ∃[ β ] σ α ≡ ` β × Γᵒ₂ ∋ x ⦂ ⟨ T , β ⟩
  lookup-sub-oentries osub-[] ()
  lookup-sub-oentries (osub-∷ σα≡`β σ[Γᵒ₁]=Γᵒ₂) here = ⟨ _ , σα≡`β , here ⟩
  lookup-sub-oentries (osub-∷ _ σ[Γᵒ₁]=Γᵒ₂) (there lookup)
    with lookup-sub-oentries σ[Γᵒ₁]=Γᵒ₂ lookup
  ... | ⟨ β , σα≡`β , lookup′ ⟩ = ⟨ β , σα≡`β , there lookup′ ⟩

  lookup-sub-octx : ∀ {σ Γᵒ₁ Γᵒ₂ x T α}
    → OCtxSub σ Γᵒ₁ Γᵒ₂
    → Γᵒ₁ ∋ᵒ x ⦂ ⟨ T , α ⟩
      ---------------------------------------------------
    → ∃[ β ] σ α ≡ ` β × Γᵒ₂ ∋ᵒ x ⦂ ⟨ T , β ⟩
  lookup-sub-octx σ[Γᵒ₁]=Γᵒ₂ lookup =
    lookup-sub-oentries (σ[Γᵒ₁]=Γᵒ₂ .entries-sub) lookup

  member-sub-oentries : ∀ {σ Γᵒ₁ Γᵒ₂ T α}
    → OEntriesSub σ Γᵒ₁ Γᵒ₂
    → Γᵒ₁ ∋ ⟨ T , α ⟩
      ---------------------------------------
    → ∃[ β ] σ α ≡ ` β × Γᵒ₂ ∋ ⟨ T , β ⟩
  member-sub-oentries osub-[] ()
  member-sub-oentries (osub-∷ σα≡`β σ[Γᵒ₁]=Γᵒ₂) Z = ⟨ _ , σα≡`β , Z ⟩
  member-sub-oentries (osub-∷ _ σ[Γᵒ₁]=Γᵒ₂) (S lookup)
    with member-sub-oentries σ[Γᵒ₁]=Γᵒ₂ lookup
  ... | ⟨ β , σα≡`β , lookup′ ⟩ = ⟨ β , σα≡`β , S lookup′ ⟩

  member-sub-octx : ∀ {σ Γᵒ₁ Γᵒ₂ T α}
    → OCtxSub σ Γᵒ₁ Γᵒ₂
    → Γᵒ₁ ∋ᵒ ⟨ T , α ⟩
      ------------------------------------------
    → ∃[ β ] σ α ≡ ` β × Γᵒ₂ ∋ᵒ ⟨ T , β ⟩
  member-sub-octx σ[Γᵒ₁]=Γᵒ₂ lookup =
    member-sub-oentries (σ[Γᵒ₁]=Γᵒ₂ .entries-sub) lookup

  exts-var : ∀ {σ α β}
    → σ α ≡ ` β
      ---------------------------------
    → extsᵉ σ (suc α) ≡ ` suc β
  exts-var {σ = σ} {α = α} σα≡`β with σ α | σα≡`β
  ... | ε   | ()
  ... | ` _ | refl = refl

  exts-owner-sub : ∀ {σ Γᵒ₁ Γᵒ₂ α β x T}
    → OCtxSub σ Γᵒ₁ Γᵒ₂
    → extsᵉ σ α ≡ ` β
    → lookupOwner ((⇑ᵉ-octx Γᵒ₁) .entries) α ≡ just ⟨ x , T ⟩
      -----------------------------------------------------------------
    → lookupOwner ((⇑ᵉ-octx Γᵒ₂) .entries) β ≡ just ⟨ x , T ⟩
  exts-owner-sub {Γᵒ₁ = Γᵒ₁} {α = zero} σ[Γᵒ₁]=Γᵒ₂ eq owner
    rewrite lookupOwner-⇑ᵉ-zero (Γᵒ₁ .entries) =
    contradiction owner (λ ())
  exts-owner-sub {σ = σ} {Γᵒ₁ = Γᵒ₁} {Γᵒ₂ = Γᵒ₂} {α = suc α} σ[Γᵒ₁]=Γᵒ₂ eq owner
    with σ α in σα≡e | eq
  ... | ε | ()
  ... | ` β | refl
    rewrite lookupOwner-⇑ᵉ (Γᵒ₁ .entries) α
          | lookupOwner-⇑ᵉ (Γᵒ₂ .entries) β
          | σα≡e =
    σ[Γᵒ₁]=Γᵒ₂ .owner-sub {α = α} {β = β} σα≡e owner

  exts-global-sub : ∀ {σ Γᵒ₁ Γᵒ₂ T α β}
    → OCtxSub σ Γᵒ₁ Γᵒ₂
    → extsᵉ σ α ≡ ` β
    → GlobalEntries (⇑ᵉ-octx Γᵒ₁) ∋ ⟨ T , α ⟩
      ------------------------------------------------
    → GlobalEntries (⇑ᵉ-octx Γᵒ₂) ∋ ⟨ T , β ⟩
  exts-global-sub {Γᵒ₁ = Γᵒ₁} {α = zero} σ[Γᵒ₁]=Γᵒ₂ eq member
    with member-map-drop-inv (renᵉ-octx-entry suc) (Γᵒ₁ .cutoff) (Γᵒ₁ .entries) member
  ... | ⟨ ⟨ _ , _ ⟩ , _ , () ⟩
  exts-global-sub {σ = σ} {Γᵒ₁ = Γᵒ₁} {Γᵒ₂ = Γᵒ₂} {T = T} {α = suc α} {β = zero} σ[Γᵒ₁]=Γᵒ₂ eq member
    with σ α | eq
  ... | ε | ()
  ... | ` _ | ()
  exts-global-sub {σ = σ} {Γᵒ₁ = Γᵒ₁} {Γᵒ₂ = Γᵒ₂} {T = T} {α = suc α} {β = suc β} σ[Γᵒ₁]=Γᵒ₂ eq member
    with σ α in σα≡e | eq
  ... | ε | ()
  ... | ` .β | refl
    with member-map-drop-inv (renᵉ-octx-entry suc) (Γᵒ₁ .cutoff) (Γᵒ₁ .entries) member
  ... | ⟨ ⟨ .T , .α ⟩ , member′ , refl ⟩ =
    member-map-drop (renᵉ-octx-entry suc) (Γᵒ₂ .cutoff) (Γᵒ₂ .entries)
      (σ[Γᵒ₁]=Γᵒ₂ .global-sub σα≡e member′)

  single-owner-sub : ∀ {e Γᵒ α β x T}
    → (e •ᵉₛ idsᵉ) α ≡ ` β
    → lookupOwner ((⇑ᵉ-octx Γᵒ) .entries) α ≡ just ⟨ x , T ⟩
      ---------------------------------------------------------
    → lookupOwner (Γᵒ .entries) β ≡ just ⟨ x , T ⟩
  single-owner-sub {Γᵒ = Γᵒ} {α = zero} eq owner
    rewrite lookupOwner-⇑ᵉ-zero (Γᵒ .entries) =
    contradiction owner (λ ())
  single-owner-sub {Γᵒ = Γᵒ} {α = suc α} eq owner with eq
  ... | refl rewrite lookupOwner-⇑ᵉ (Γᵒ .entries) α = owner

  single-global-sub : ∀ {e Γᵒ T α β}
    → (e •ᵉₛ idsᵉ) α ≡ ` β
    → GlobalEntries (⇑ᵉ-octx Γᵒ) ∋ ⟨ T , α ⟩
      ---------------------------------------------
    → GlobalEntries Γᵒ ∋ ⟨ T , β ⟩
  single-global-sub {Γᵒ = Γᵒ} {α = zero} eq member
    with member-map-drop-inv (renᵉ-octx-entry suc) (Γᵒ .cutoff) (Γᵒ .entries) member
  ... | ⟨ ⟨ _ , _ ⟩ , _ , () ⟩
  single-global-sub {Γᵒ = Γᵒ} {T = T} {α = suc α} eq member with eq
  ... | refl with member-map-drop-inv (renᵉ-octx-entry suc) (Γᵒ .cutoff) (Γᵒ .entries) member
  ... | ⟨ ⟨ .T , .α ⟩ , member′ , refl ⟩ = member′

  exts-oentries-sub : ∀ {σ Γᵒ₁ Γᵒ₂}
    → OEntriesSub σ Γᵒ₁ Γᵒ₂
      -----------------------------------------------------------------------------------------
    → OEntriesSub (extsᵉ σ) (map (renᵉ-octx-entry suc) Γᵒ₁) (map (renᵉ-octx-entry suc) Γᵒ₂)
  exts-oentries-sub osub-[] = osub-[]
  exts-oentries-sub {σ = σ} (osub-∷ {T = T} {α = α} {β = β} σα≡`β σ[Γᵒ₁]=Γᵒ₂) =
    osub-∷ {σ = extsᵉ σ} {T = T} {α = suc α} {β = suc β}
      (exts-var {σ = σ} {α = α} {β = β} σα≡`β) (exts-oentries-sub σ[Γᵒ₁]=Γᵒ₂)

  lex-exts-octx-sub : ∀ {σ Γᵒ₁ Γᵒ₂ T}
    → OCtxSub σ Γᵒ₁ Γᵒ₂
      ---------------------------------------------------------------------------------
    → OCtxSub (extsᵉ σ) (⇑ᵉ-octx Γᵒ₁ , T ＠ zero) (⇑ᵉ-octx Γᵒ₂ , T ＠ zero)
  lex-exts-octx-sub {σ = σ} {Γᵒ₁ = Γᵒ₁} {Γᵒ₂ = Γᵒ₂} {T = T₀} σ[Γᵒ₁]=Γᵒ₂ =
    octx-sub {σ = extsᵉ σ}
      {Γᵒ₁ = ⇑ᵉ-octx Γᵒ₁ , T₀ ＠ zero}
      {Γᵒ₂ = ⇑ᵉ-octx Γᵒ₂ , T₀ ＠ zero}
      (osub-∷ refl (exts-oentries-sub (σ[Γᵒ₁]=Γᵒ₂ .entries-sub)))
      (λ {α} {β} {x} {T} →
        owner {α = α} {β = β} {x = x} {T = T})
      (λ {T} {α} {β} →
        exts-global-sub {σ = σ} {Γᵒ₁ = Γᵒ₁} {Γᵒ₂ = Γᵒ₂} {T = T} {α = α} {β = β} σ[Γᵒ₁]=Γᵒ₂)
    where
      owner : ∀ {α β x T}
        → extsᵉ σ α ≡ ` β
        → lookupOwner (⟨ T₀ , zero ⟩ ∷ (⇑ᵉ-octx Γᵒ₁) .entries) α ≡ just ⟨ x , T ⟩
          ----------------------------------------------------------------------------------
        → lookupOwner (⟨ T₀ , zero ⟩ ∷ (⇑ᵉ-octx Γᵒ₂) .entries) β ≡ just ⟨ x , T ⟩
      owner {α = zero} refl refl = refl
      owner {α = suc α} {β = zero} eq owner′ with σ α | eq
      ... | ε | ()
      ... | ` β | ()
      owner {α = suc α} {β = suc β} {x = zero} eq owner′ =
        contradiction owner′
          (lookupOwner-cons-miss-zero-impossible {Γᵒ = (⇑ᵉ-octx Γᵒ₁) .entries} {α = suc α} {β = zero} {S = T₀} (λ ()))
      owner {α = suc α} {β = suc β} {x = suc x} eq owner′ with σ α | eq
      ... | ε | ()
      ... | ` .β | refl =
        lookupOwner-cons-miss {Γᵒ = (⇑ᵉ-octx Γᵒ₂) .entries} {α = suc β} {β = zero} {S = T₀} (λ ())
          (exts-owner-sub σ[Γᵒ₁]=Γᵒ₂ eq
            (lookupOwner-cons-miss-inv {Γᵒ = (⇑ᵉ-octx Γᵒ₁) .entries} {α = suc α} {β = zero} {x = x} {S = T₀} (λ ()) owner′))

  exts-octx-sub : ∀ {σ Γᵒ₁ Γᵒ₂}
    → OCtxSub σ Γᵒ₁ Γᵒ₂
      ---------------------------------------------------------
    → OCtxSub (extsᵉ σ) (⇑ᵉ-octx Γᵒ₁) (⇑ᵉ-octx Γᵒ₂)
  exts-octx-sub σ[Γᵒ₁]=Γᵒ₂ =
    octx-sub (exts-oentries-sub (σ[Γᵒ₁]=Γᵒ₂ .entries-sub))
      (exts-owner-sub σ[Γᵒ₁]=Γᵒ₂)
      (exts-global-sub σ[Γᵒ₁]=Γᵒ₂)

  single-oentries-sub : ∀ {e : EC} Γᵒ
      --------------------------------------------------------------------------
    → OEntriesSub (e •ᵉₛ idsᵉ) (map (renᵉ-octx-entry suc) Γᵒ) Γᵒ
  single-oentries-sub [] = osub-[]
  single-oentries-sub (⟨ T , α ⟩ ∷ Γᵒ) = osub-∷ {α = suc α} {β = α} refl (single-oentries-sub Γᵒ)

  single-octx-sub : ∀ {e : EC} Γᵒ
      ---------------------------------------------
    → OCtxSub (e •ᵉₛ idsᵉ) (⇑ᵉ-octx Γᵒ) Γᵒ
  single-octx-sub {e = e} Γᵒ =
    octx-sub {Γᵒ₁ = ⇑ᵉ-octx Γᵒ} {Γᵒ₂ = Γᵒ}
      (single-oentries-sub (Γᵒ .entries))
      (λ {α} {β} {x} {T} →
        single-owner-sub {e = e} {Γᵒ = Γᵒ} {α = α} {β = β} {x = x} {T = T})
      (λ {T} {α} {β} →
        single-global-sub {e = e} {Γᵒ = Γᵒ} {T = T} {α = α} {β = β})

  fresh-owner-sub : ∀ {Δ Γᵒ S α β x T}
    → Δ ⊢ Γᵒ OCtx
    → ((` freshᵉ Δ) •ᵉₛ idsᵉ) α ≡ ` β
    → lookupOwner (⟨ S , zero ⟩ ∷ (⇑ᵉ-octx Γᵒ) .entries) α ≡ just ⟨ x , T ⟩
      ---------------------------------------------------------------------------------
    → lookupOwner (⟨ S , freshᵉ Δ ⟩ ∷ Γᵒ .entries) β ≡ just ⟨ x , T ⟩
  fresh-owner-sub {Δ = Δ} {Γᵒ = Γᵒ} {S = S₀} {α = zero} ⊢Γᵒ eq owner with eq
  ... | refl with owner
  ... | refl = lookupOwner-here {Γᵒ = Γᵒ .entries} {T = S₀} {α = freshᵉ Δ}
  fresh-owner-sub {Δ = Δ} {Γᵒ = Γᵒ} {S = S₀} {α = suc α} {x = zero} ⊢Γᵒ refl owner =
    contradiction owner
      (lookupOwner-cons-miss-zero-impossible {Γᵒ = (⇑ᵉ-octx Γᵒ) .entries} {α = suc α} {β = zero} {S = S₀} (λ ()))
  fresh-owner-sub {Δ = Δ} {Γᵒ = Γᵒ} {S = S₀} {α = suc α} {x = suc x} {T = T₀} ⟨ scoped , unique ⟩ refl owner
    with lookupOwner-cons-miss-inv {Γᵒ = (⇑ᵉ-octx Γᵒ) .entries} {α = suc α} {β = zero} {x = x} {S = S₀} (λ ()) owner
  ... | shifted rewrite lookupOwner-⇑ᵉ (Γᵒ .entries) α =
    lookupOwner-cons-miss {Γᵒ = Γᵒ .entries} {α = α} {β = freshᵉ Δ} {S = S₀}
      (λ fresh≡α →
        wf-var-≢fresh {Δ = Δ} {α = α}
          (lookupOwner-wf {Δ = Δ} {Γᵒ = Γᵒ .entries} {α = α} {x = x} {T = T₀}
            scoped shifted)
          (≡-sym fresh≡α))
      shifted

  fresh-octx-sub : ∀ {Δ Γᵒ S}
    → Δ ⊢ Γᵒ OCtx
      -----------------------------------------------------------------------------------------------------
    → OCtxSub ((` freshᵉ Δ) •ᵉₛ idsᵉ) (⇑ᵉ-octx Γᵒ , S ＠ zero) (Γᵒ , S ＠ freshᵉ Δ)
  fresh-octx-sub {Δ = Δ} {Γᵒ = Γᵒ} {S = S} ⊢Γᵒ =
    octx-sub {σ = (` freshᵉ Δ) •ᵉₛ idsᵉ}
      {Γᵒ₁ = ⇑ᵉ-octx Γᵒ , S ＠ zero}
      {Γᵒ₂ = Γᵒ , S ＠ freshᵉ Δ}
      (osub-∷ refl (single-oentries-sub (Γᵒ .entries)))
      (λ {α} {β} {x} {T} →
        fresh-owner-sub {Δ = Δ} {Γᵒ = Γᵒ} {S = S} {α = α} {β = β} {x = x} {T = T} ⊢Γᵒ)
      (λ {T} {α} {β} →
        single-global-sub {e = ` freshᵉ Δ} {Γᵒ = Γᵒ} {T = T} {α = α} {β = β})

  ∋-renᵉ-subctx : ∀ {ρ Θ e₁ e₂}
    → Θ ∋ˢ ⟨ e₁ , e₂ ⟩
      ------------------------------------------------------
    → renᵉ-subctx ρ Θ ∋ˢ ⟨ renᵉ-ec ρ e₁ , renᵉ-ec ρ e₂ ⟩
  ∋-renᵉ-subctx {ρ = ρ} edge = member-map {f = renᵉ-subctx-entry ρ} edge

  global-renᵉ-subctx : ∀ {ρ Θ e₁ e₂}
    → GlobalEdges Θ ∋ ⟨ e₁ , e₂ ⟩
      ------------------------------------------------------------------
    → GlobalEdges (renᵉ-subctx ρ Θ) ∋ ⟨ renᵉ-ec ρ e₁ , renᵉ-ec ρ e₂ ⟩
  global-renᵉ-subctx {ρ = ρ} {Θ = Θ} edge =
    member-map-drop (renᵉ-subctx-entry ρ) (Θ .cutoff) (Θ .edges) edge

  ec-subtype-ren : ∀ ρ {Θ e₁ e₂}
    → Θ ⊢ᵉ e₁ <: e₂
      ---------------------------------------------------
    → renᵉ-subctx ρ Θ ⊢ᵉ renᵉ-ec ρ e₁ <: renᵉ-ec ρ e₂
  ec-subtype-ren ρ <:-ε = <:-ε
  ec-subtype-ren ρ <:-refl = <:-refl
  ec-subtype-ren ρ {Θ = Θ} {e₁ = e₁} {e₂ = e₂} (<:-ax edge) =
    <:-ax (∋-renᵉ-subctx {ρ = ρ} {Θ = Θ} {e₁ = e₁} {e₂ = e₂} edge)
  ec-subtype-ren ρ (<:-trans e₁<:e e<:e₂) = <:-trans (ec-subtype-ren ρ e₁<:e) (ec-subtype-ren ρ e<:e₂)

  ec⋆-subtype-ren : ∀ ρ {Θ ê₁ ê₂}
    → Θ ⊢ᵉ ê₁ <:⋆ ê₂
      ------------------------------------------------------
    → renᵉ-subctx ρ Θ ⊢ᵉ renᵉ-ec⋆ ρ ê₁ <:⋆ renᵉ-ec⋆ ρ ê₂
  ec⋆-subtype-ren ρ <:-⋆ = <:-⋆
  ec⋆-subtype-ren ρ (<:-ec e₁<:e₂) = <:-ec (ec-subtype-ren ρ e₁<:e₂)

  ∋-subᵉ-subctx : ∀ {σ Θ e₁ e₂}
    → Θ ∋ˢ ⟨ e₁ , e₂ ⟩
      ----------------------------------------------------
    → subᵉ-subctx σ Θ ∋ˢ ⟨ subᵉ-ec σ e₁ , subᵉ-ec σ e₂ ⟩
  ∋-subᵉ-subctx {σ = σ} edge = member-map {f = subᵉ-subctx-entry σ} edge

  global-subᵉ-subctx : ∀ {σ Θ e₁ e₂}
    → GlobalEdges Θ ∋ ⟨ e₁ , e₂ ⟩
      ------------------------------------------------------------------
    → GlobalEdges (subᵉ-subctx σ Θ) ∋ ⟨ subᵉ-ec σ e₁ , subᵉ-ec σ e₂ ⟩
  global-subᵉ-subctx {σ = σ} {Θ = Θ} edge =
    member-map-drop (subᵉ-subctx-entry σ) (Θ .cutoff) (Θ .edges) edge

  ec-subtype-sub : ∀ σ {Θ e₁ e₂}
    → Θ ⊢ᵉ e₁ <: e₂
      ---------------------------------------------------
    → subᵉ-subctx σ Θ ⊢ᵉ subᵉ-ec σ e₁ <: subᵉ-ec σ e₂
  ec-subtype-sub σ <:-ε = <:-ε
  ec-subtype-sub σ <:-refl = <:-refl
  ec-subtype-sub σ {Θ = Θ} {e₁ = e₁} {e₂ = e₂} (<:-ax edge) =
    <:-ax (∋-subᵉ-subctx {σ = σ} {Θ = Θ} {e₁ = e₁} {e₂ = e₂} edge)
  ec-subtype-sub σ (<:-trans e₁<:e e<:e₂) =
    <:-trans (ec-subtype-sub σ e₁<:e) (ec-subtype-sub σ e<:e₂)

  ec⋆-subtype-sub : ∀ σ {Θ ê₁ ê₂}
    → Θ ⊢ᵉ ê₁ <:⋆ ê₂
      ---------------------------------------------------------
    → subᵉ-subctx σ Θ ⊢ᵉ subᵉ-ec⋆ σ ê₁ <:⋆ subᵉ-ec⋆ σ ê₂
  ec⋆-subtype-sub σ <:-⋆ = <:-⋆
  ec⋆-subtype-sub σ (<:-ec e₁<:e₂) = <:-ec (ec-subtype-sub σ e₁<:e₂)

  ren-sub-ec : ∀ ρ τ σ σ′ e
    → (∀ α → renᵉ-ec ρ (σ α) ≡ subᵉ-ec σ′ (renᵉ-ec τ (` α)))
      --------------------------------------------------------------------
    → renᵉ-ec ρ (subᵉ-ec σ e) ≡ subᵉ-ec σ′ (renᵉ-ec τ e)
  ren-sub-ec ρ τ σ σ′ ε σ-comm = refl
  ren-sub-ec ρ τ σ σ′ (` α) σ-comm = σ-comm α

  ren-sub-ec⋆ : ∀ ρ τ σ σ′ ê
    → (∀ α → renᵉ-ec ρ (σ α) ≡ subᵉ-ec σ′ (renᵉ-ec τ (` α)))
      -----------------------------------------------------------------------
    → renᵉ-ec⋆ ρ (subᵉ-ec⋆ σ ê) ≡ subᵉ-ec⋆ σ′ (renᵉ-ec⋆ τ ê)
  ren-sub-ec⋆ ρ τ σ σ′ ⋆ σ-comm = refl
  ren-sub-ec⋆ ρ τ σ σ′ (ec e) σ-comm
    rewrite ren-sub-ec ρ τ σ σ′ e σ-comm = refl

  ren-sub-exts : ∀ ρ τ σ σ′
    → (∀ α → renᵉ-ec ρ (σ α) ≡ subᵉ-ec σ′ (renᵉ-ec τ (` α)))
      --------------------------------------------------------------------------------------------
    → ∀ α → renᵉ-ec (extᵉ ρ) (extsᵉ σ α) ≡ subᵉ-ec (extsᵉ σ′) (renᵉ-ec (extᵉ τ) (` α))
  ren-sub-exts ρ τ σ σ′ σ-comm zero = refl
  ren-sub-exts ρ τ σ σ′ σ-comm (suc α)
    rewrite σ-comm α = refl

  ren-sub-mtype : ∀ ρ τ σ σ′ A
    → (∀ α → renᵉ-ec ρ (σ α) ≡ subᵉ-ec σ′ (renᵉ-ec τ (` α)))
      -------------------------------------------------------------
    → renᵉ ρ (subᵉ σ A) ≡ subᵉ σ′ (renᵉ τ A)
  ren-sub-mtype ρ τ σ σ′ ⋆ σ-comm = refl
  ren-sub-mtype ρ τ σ σ′ (` ι) σ-comm = refl
  ren-sub-mtype ρ τ σ σ′ (A ⇒ B) σ-comm
    rewrite ren-sub-mtype ρ τ σ σ′ A σ-comm
          | ren-sub-mtype ρ τ σ σ′ B σ-comm = refl
  ren-sub-mtype ρ τ σ σ′ (Ref A) σ-comm
    rewrite ren-sub-mtype ρ τ σ σ′ A σ-comm = refl
  ren-sub-mtype ρ τ σ σ′ (‶ O ″ ê) σ-comm
    rewrite ren-sub-ec⋆ ρ τ σ σ′ ê σ-comm = refl
  ren-sub-mtype ρ τ σ σ′ (∀̇ A) σ-comm
    rewrite ren-sub-mtype (extᵉ ρ) (extᵉ τ) (extsᵉ σ) (extsᵉ σ′) A
              (ren-sub-exts ρ τ σ σ′ σ-comm) = refl
  ren-sub-mtype ρ τ σ σ′ (e₁ <: e₂ => A) σ-comm
    rewrite ren-sub-ec ρ τ σ σ′ e₁ σ-comm
          | ren-sub-ec ρ τ σ σ′ e₂ σ-comm
          | ren-sub-mtype ρ τ σ σ′ A σ-comm = refl

  ren-single-cond : ∀ ρ e α
      ------------------------------------------------------------------------------------------------------------------
    → renᵉ-ec ρ ((e •ᵉₛ idsᵉ) α) ≡ subᵉ-ec ((renᵉ-ec ρ e) •ᵉₛ idsᵉ) (renᵉ-ec (extᵉ ρ) (` α))
  ren-single-cond ρ e zero = refl
  ren-single-cond ρ e (suc α) = refl

  ren-single-mtype : ∀ ρ A e
      ---------------------------------------------------------------------------
    → renᵉ ρ (A [ e ]ᵉ) ≡ renᵉ (extᵉ ρ) A [ renᵉ-ec ρ e ]ᵉ
  ren-single-mtype ρ A e =
    ren-sub-mtype ρ (extᵉ ρ) (e •ᵉₛ idsᵉ) ((renᵉ-ec ρ e) •ᵉₛ idsᵉ) A
      (ren-single-cond ρ e)
  {-# REWRITE ren-single-mtype #-}

  sub-sub-ec : ∀ σ τ τ′ e
    → (∀ α → subᵉ-ec σ (τ α) ≡ τ′ α)
      ------------------------------------------------
    → subᵉ-ec σ (subᵉ-ec τ e) ≡ subᵉ-ec τ′ e
  sub-sub-ec σ τ τ′ ε σ∘τ=τ′ = refl
  sub-sub-ec σ τ τ′ (` α) σ∘τ=τ′ = σ∘τ=τ′ α

  sub-sub-ec⋆ : ∀ σ τ τ′ ê
    → (∀ α → subᵉ-ec σ (τ α) ≡ τ′ α)
      ---------------------------------------------------
    → subᵉ-ec⋆ σ (subᵉ-ec⋆ τ ê) ≡ subᵉ-ec⋆ τ′ ê
  sub-sub-ec⋆ σ τ τ′ ⋆ σ∘τ=τ′ = refl
  sub-sub-ec⋆ σ τ τ′ (ec e) σ∘τ=τ′
    rewrite sub-sub-ec σ τ τ′ e σ∘τ=τ′ = refl

  sub-sub-exts-suc : ∀ σ w w′
    → subᵉ-ec σ w ≡ w′
      ------------------------------------------------------
    → subᵉ-ec (extsᵉ σ) (renᵉ-ec suc w) ≡ renᵉ-ec suc w′
  sub-sub-exts-suc σ ε ε refl = refl
  sub-sub-exts-suc σ ε (` β) ()
  sub-sub-exts-suc σ (` β) w′ eq with σ β | w′ | eq
  ... | ε | ε | refl = refl
  ... | ` γ | ` .γ | refl = refl

  sub-sub-exts : ∀ σ τ τ′
    → (∀ α → subᵉ-ec σ (τ α) ≡ τ′ α)
      ---------------------------------------------------------
    → ∀ α → subᵉ-ec (extsᵉ σ) (extsᵉ τ α) ≡ extsᵉ τ′ α
  sub-sub-exts σ τ τ′ σ∘τ=τ′ zero = refl
  sub-sub-exts σ τ τ′ σ∘τ=τ′ (suc α) =
    sub-sub-exts-suc σ (τ α) (τ′ α) (σ∘τ=τ′ α)

  sub-sub-mtype : ∀ σ τ τ′ A
    → (∀ α → subᵉ-ec σ (τ α) ≡ τ′ α)
      -------------------------------------------
    → subᵉ σ (subᵉ τ A) ≡ subᵉ τ′ A
  sub-sub-mtype σ τ τ′ ⋆ σ∘τ=τ′ = refl
  sub-sub-mtype σ τ τ′ (` ι) σ∘τ=τ′ = refl
  sub-sub-mtype σ τ τ′ (A ⇒ B) σ∘τ=τ′
    rewrite sub-sub-mtype σ τ τ′ A σ∘τ=τ′
          | sub-sub-mtype σ τ τ′ B σ∘τ=τ′ = refl
  sub-sub-mtype σ τ τ′ (Ref A) σ∘τ=τ′
    rewrite sub-sub-mtype σ τ τ′ A σ∘τ=τ′ = refl
  sub-sub-mtype σ τ τ′ (‶ O ″ ê) σ∘τ=τ′
    rewrite sub-sub-ec⋆ σ τ τ′ ê σ∘τ=τ′ = refl
  sub-sub-mtype σ τ τ′ (∀̇ A) σ∘τ=τ′
    rewrite sub-sub-mtype (extsᵉ σ) (extsᵉ τ) (extsᵉ τ′) A
              (sub-sub-exts σ τ τ′ σ∘τ=τ′) = refl
  sub-sub-mtype σ τ τ′ (e₁ <: e₂ => A) σ∘τ=τ′
    rewrite sub-sub-ec σ τ τ′ e₁ σ∘τ=τ′
          | sub-sub-ec σ τ τ′ e₂ σ∘τ=τ′
          | sub-sub-mtype σ τ τ′ A σ∘τ=τ′ = refl

  sub-single-cond : ∀ σ e α
      ------------------------------------------------
    → subᵉ-ec ((subᵉ-ec σ e) •ᵉₛ idsᵉ) (extsᵉ σ α)
      ≡ subᵉ-ec σ ((e •ᵉₛ idsᵉ) α)
  sub-single-cond σ e zero = refl
  sub-single-cond σ e (suc α) with σ α
  ... | ε = refl
  ... | ` β = refl

  sub-single-mtype-rewrite : ∀ σ A e
      ------------------------------------------------------------------------------
    → subᵉ ((subᵉ-ec σ e) •ᵉₛ idsᵉ) (subᵉ (extsᵉ σ) A) ≡ subᵉ σ (A [ e ]ᵉ)
  sub-single-mtype-rewrite σ A e =
    trans
      (sub-sub-mtype ((subᵉ-ec σ e) •ᵉₛ idsᵉ) (extsᵉ σ) (λ α → subᵉ-ec σ ((e •ᵉₛ idsᵉ) α)) A
        (sub-single-cond σ e))
      (≡-sym
        (sub-sub-mtype σ (e •ᵉₛ idsᵉ) (λ α → subᵉ-ec σ ((e •ᵉₛ idsᵉ) α)) A
          (λ α → refl)))
  {-# REWRITE sub-single-mtype-rewrite #-}

  sub-exts-suc-ec : ∀ σ e
      -------------------------------------------------------------------
    → subᵉ-ec (extsᵉ σ) (⇑ᵉ-ec e) ≡ ⇑ᵉ-ec (subᵉ-ec σ e)
  sub-exts-suc-ec σ ε = refl
  sub-exts-suc-ec σ (` α) = refl
  {-# REWRITE sub-exts-suc-ec #-}

  sub-exts-suc-subctx-edges : ∀ σ Θ
      ------------------------------------------------------------------------
    → map (subᵉ-subctx-entry (extsᵉ σ)) (map (renᵉ-subctx-entry suc) Θ)
      ≡ map (renᵉ-subctx-entry suc) (map (subᵉ-subctx-entry σ) Θ)
  sub-exts-suc-subctx-edges σ [] = refl
  sub-exts-suc-subctx-edges σ (_ ∷ Θ) rewrite sub-exts-suc-subctx-edges σ Θ = refl

  sub-exts-suc-subctx : ∀ σ Θ
      ------------------------------------------------------------------------
    → subᵉ-subctx (extsᵉ σ) (⇑ᵉ-subctx Θ) ≡ ⇑ᵉ-subctx (subᵉ-subctx σ Θ)
  sub-exts-suc-subctx σ Θ =
    subctx-cong (sub-exts-suc-subctx-edges σ (Θ .edges))

  sub-exts-suc-mtype : ∀ σ A
      ----------------------------------------------------------
    → subᵉ (extsᵉ σ) (renᵉ suc A) ≡ renᵉ suc (subᵉ σ A)
  sub-exts-suc-mtype σ A = ≡-sym (ren-sub-mtype suc suc σ (extsᵉ σ) A (λ α → refl))
  {-# REWRITE sub-exts-suc-mtype #-}

  sub-exts-suc-mctx-map : (σ : SubstEC) (Γᵐ : MCtx)
      ------------------------------------------------------------------------------------
    → map (subᵉ (extsᵉ σ)) (map (renᵉ suc) Γᵐ) ≡ map (renᵉ suc) (map (subᵉ σ) Γᵐ)
  sub-exts-suc-mctx-map σ [] = refl
  sub-exts-suc-mctx-map σ (A ∷ Γᵐ) rewrite sub-exts-suc-mctx-map σ Γᵐ = refl
  {-# REWRITE sub-exts-suc-mctx-map #-}

  renᵉ-subctx-ext : ∀ ρ Θ e₁ e₂
      ---------------------------------------------------------------------------------
    → renᵉ-subctx ρ (Θ , e₁ <: e₂) ≡ renᵉ-subctx ρ Θ , renᵉ-ec ρ e₁ <: renᵉ-ec ρ e₂
  renᵉ-subctx-ext ρ Θ e₁ e₂ = subctx-cong refl

  subᵉ-subctx-ext : ∀ σ Θ e₁ e₂
      ---------------------------------------------------------------------------------
    → subᵉ-subctx σ (Θ , e₁ <: e₂) ≡ subᵉ-subctx σ Θ , subᵉ-ec σ e₁ <: subᵉ-ec σ e₂
  subᵉ-subctx-ext σ Θ e₁ e₂ = subctx-cong refl

  ren-ext-suc-subctx-ext : ∀ ρ Θ e
      ---------------------------------------------------------------------------------------------------------------
    → renᵉ-subctx (extᵉ ρ) (⇑ᵉ-subctx Θ , ⇑ᵉ-ec e <: ` zero)
      ≡ ⇑ᵉ-subctx (renᵉ-subctx ρ Θ) , ⇑ᵉ-ec (renᵉ-ec ρ e) <: ` zero
  ren-ext-suc-subctx-ext ρ Θ e =
    trans (renᵉ-subctx-ext (extᵉ ρ) (⇑ᵉ-subctx Θ) (⇑ᵉ-ec e) (` zero))
      (cong (λ Θ′ → Θ′ , ⇑ᵉ-ec (renᵉ-ec ρ e) <: ` zero)
        (ren-ext-suc-subctx ρ Θ))

  sub-exts-suc-subctx-ext : ∀ σ Θ e
      ---------------------------------------------------------------------------------------------------------------
    → subᵉ-subctx (extsᵉ σ) (⇑ᵉ-subctx Θ , ⇑ᵉ-ec e <: ` zero)
      ≡ ⇑ᵉ-subctx (subᵉ-subctx σ Θ) , ⇑ᵉ-ec (subᵉ-ec σ e) <: ` zero
  sub-exts-suc-subctx-ext σ Θ e =
    trans (subᵉ-subctx-ext (extsᵉ σ) (⇑ᵉ-subctx Θ) (⇑ᵉ-ec e) (` zero))
      (cong (λ Θ′ → Θ′ , ⇑ᵉ-ec (subᵉ-ec σ e) <: ` zero)
        (sub-exts-suc-subctx σ Θ))

  ec-coercion-ren : ∀ {Δ₁ Δ₂ ρ Θ c ê₁ ê₂}
    → ECRenWF Δ₁ Δ₂ ρ
    → Δ₁ EC.; Θ ⊢ᵉ c ⦂ ê₁ ⇒ ê₂
      ---------------------------------------------------------------------------------
    → Δ₂ EC.; renᵉ-subctx ρ Θ ⊢ᵉ renᵉ-ecoercion ρ c ⦂ renᵉ-ec⋆ ρ ê₁ ⇒ renᵉ-ec⋆ ρ ê₂
  ec-coercion-ren ρ-wf (EC.⊢! e ⊢e) = EC.⊢! (renᵉ-ec _ e) (ec-ren-wf ρ-wf ⊢e)
  ec-coercion-ren ρ-wf (EC.⊢? e ⊢e ℓ) = EC.⊢? (renᵉ-ec _ e) (ec-ren-wf ρ-wf ⊢e) ℓ
  ec-coercion-ren ρ-wf (EC.⊢↑ ⊢ê₁ ⊢ê₂ ê₁<:ê₂) =
    EC.⊢↑ (ec⋆-ren-wf ρ-wf ⊢ê₁) (ec⋆-ren-wf ρ-wf ⊢ê₂) (ec⋆-subtype-ren _ ê₁<:ê₂)
  ec-coercion-ren ρ-wf (EC.⊢⊥ ⊢ê₁ ⊢ê₂ ℓ) =
    EC.⊢⊥ (ec⋆-ren-wf ρ-wf ⊢ê₁) (ec⋆-ren-wf ρ-wf ⊢ê₂) ℓ

  ec-coercionSeq-ren : ∀ {Δ₁ Δ₂ ρ Θ c ê₁ ê₂}
    → ECRenWF Δ₁ Δ₂ ρ
    → Δ₁ EC.; Θ ⊢ᵉ̅ c ⦂ ê₁ ⇒ ê₂
      -----------------------------------------------------------------------------------
    → Δ₂ EC.; renᵉ-subctx ρ Θ ⊢ᵉ̅ renᵉ-ecoercionSeq ρ c ⦂ renᵉ-ec⋆ ρ ê₁ ⇒ renᵉ-ec⋆ ρ ê₂
  ec-coercionSeq-ren ρ-wf (EC.⊢[] ⊢ê) = EC.⊢[] (ec⋆-ren-wf ρ-wf ⊢ê)
  ec-coercionSeq-ren ρ-wf (EC.⊢; ⊢c ⊢c̅) =
    EC.⊢; (ec-coercion-ren ρ-wf ⊢c) (ec-coercionSeq-ren ρ-wf ⊢c̅)

  meta-coercion-ren-single : ∀ {Δ₁ Δ₂ ρ Θ c A B}
    → ECRenWF Δ₁ Δ₂ ρ
    → Δ₁ MC.; Θ ⊢ᵐ c ⦂ A ⇒ B
      ---------------------------------------------------------------------------
    → Δ₂ MC.; renᵉ-subctx ρ Θ ⊢ᵐ renᵉ-mcoercion ρ c ⦂ renᵉ ρ A ⇒ renᵉ ρ B
  meta-coercion-ren : ∀ {Δ₁ Δ₂ ρ Θ c A B}
    → ECRenWF Δ₁ Δ₂ ρ
    → Δ₁ MC.; Θ ⊢ᵐ̅ c ⦂ A ⇒ B
      ----------------------------------------------------------------------------
    → Δ₂ MC.; renᵉ-subctx ρ Θ ⊢ᵐ̅ renᵉ-mcoercionSeq ρ c ⦂ renᵉ ρ A ⇒ renᵉ ρ B

  meta-coercion-ren-single ρ-wf (MC.⊢! ⊢G g) =
    MC.⊢! (mtype-ren-wf ρ-wf ⊢G) (renᵉ-ground _ g)
  meta-coercion-ren-single ρ-wf (MC.⊢? ⊢G ℓ g) =
    MC.⊢? (mtype-ren-wf ρ-wf ⊢G) ℓ (renᵉ-ground _ g)
  meta-coercion-ren-single ρ-wf (MC.⊢fun ⊢c ⊢d) =
    MC.⊢fun (meta-coercion-ren ρ-wf ⊢c) (meta-coercion-ren ρ-wf ⊢d)
  meta-coercion-ren-single ρ-wf (MC.⊢code ⊢cᵒ ⊢cᵉ) =
    MC.⊢code ⊢cᵒ (ec-coercionSeq-ren ρ-wf ⊢cᵉ)
  meta-coercion-ren-single ρ-wf (MC.⊢ref ⊢c ⊢d) =
    MC.⊢ref (meta-coercion-ren ρ-wf ⊢c) (meta-coercion-ren ρ-wf ⊢d)
  meta-coercion-ren-single {Δ₂ = Δ₂} {ρ = ρ} {Θ = Θ} ρ-wf (MC.⊢forall ⊢c) =
    MC.⊢forall (subst (λ □ → Δ₂ ,α MC.; □ ⊢ᵐ̅ _ ⦂ _ ⇒ _)
                    (ren-ext-suc-subctx ρ Θ) (meta-coercion-ren (ext-ren-wf ρ-wf) ⊢c))
  meta-coercion-ren-single {Δ₂ = Δ₂} {ρ = ρ} {Θ = Θ} ρ-wf (MC.⊢sub {A = A} {B = B} {e₁ = e₁} {e₂ = e₂} {c̅ᵐ = c} ⊢e₁ ⊢e₂ ⊢c) =
    MC.⊢sub (ec-ren-wf ρ-wf ⊢e₁)
             (ec-ren-wf ρ-wf ⊢e₂)
             (subst (λ Θ′ → Δ₂ MC.; Θ′ ⊢ᵐ̅ renᵉ-mcoercionSeq ρ c ⦂ renᵉ ρ A ⇒ renᵉ ρ B)
               (renᵉ-subctx-ext ρ Θ e₁ e₂) (meta-coercion-ren ρ-wf ⊢c))
  meta-coercion-ren-single ρ-wf (MC.⊢⊥ ⊢A ⊢B ℓ) =
    MC.⊢⊥ (mtype-ren-wf ρ-wf ⊢A) (mtype-ren-wf ρ-wf ⊢B) ℓ

  meta-coercion-ren ρ-wf (MC.⊢[] ⊢A) =
    MC.⊢[] (mtype-ren-wf ρ-wf ⊢A)
  meta-coercion-ren ρ-wf (MC.⊢; ⊢c ⊢c̅) =
    MC.⊢; (meta-coercion-ren-single ρ-wf ⊢c)
           (meta-coercion-ren ρ-wf ⊢c̅)

  ec-coercion-sub : ∀ {Δ₁ Δ₂ σ Θ c ê₁ ê₂}
    → ECSubstWF Δ₁ Δ₂ σ
    → Δ₁ EC.; Θ ⊢ᵉ c ⦂ ê₁ ⇒ ê₂
      ------------------------------------------------------------------------------------
    → Δ₂ EC.; subᵉ-subctx σ Θ ⊢ᵉ substᵉ-ecoercion σ c ⦂ subᵉ-ec⋆ σ ê₁ ⇒ subᵉ-ec⋆ σ ê₂
  ec-coercion-sub {σ = σ} σ-wf (EC.⊢! e ⊢e) = EC.⊢! (subᵉ-ec σ e) (ec-sub-wf σ-wf ⊢e)
  ec-coercion-sub {σ = σ} σ-wf (EC.⊢? e ⊢e ℓ) = EC.⊢? (subᵉ-ec σ e) (ec-sub-wf σ-wf ⊢e) ℓ
  ec-coercion-sub σ-wf (EC.⊢↑ ⊢ê₁ ⊢ê₂ ê₁<:ê₂) =
    EC.⊢↑ (ec⋆-sub-wf σ-wf ⊢ê₁) (ec⋆-sub-wf σ-wf ⊢ê₂) (ec⋆-subtype-sub _ ê₁<:ê₂)
  ec-coercion-sub σ-wf (EC.⊢⊥ ⊢ê₁ ⊢ê₂ ℓ) =
    EC.⊢⊥ (ec⋆-sub-wf σ-wf ⊢ê₁) (ec⋆-sub-wf σ-wf ⊢ê₂) ℓ

  ec-coercionSeq-sub : ∀ {Δ₁ Δ₂ σ Θ c ê₁ ê₂}
    → ECSubstWF Δ₁ Δ₂ σ
    → Δ₁ EC.; Θ ⊢ᵉ̅ c ⦂ ê₁ ⇒ ê₂
      --------------------------------------------------------------------------------------
    → Δ₂ EC.; subᵉ-subctx σ Θ ⊢ᵉ̅ substᵉ-ecoercionSeq σ c ⦂ subᵉ-ec⋆ σ ê₁ ⇒ subᵉ-ec⋆ σ ê₂
  ec-coercionSeq-sub σ-wf (EC.⊢[] ⊢ê) = EC.⊢[] (ec⋆-sub-wf σ-wf ⊢ê)
  ec-coercionSeq-sub σ-wf (EC.⊢; ⊢c ⊢c̅) =
    EC.⊢; (ec-coercion-sub σ-wf ⊢c) (ec-coercionSeq-sub σ-wf ⊢c̅)

  meta-coercion-sub-single : ∀ {Δ₁ Δ₂ σ Θ c A B}
    → ECSubstWF Δ₁ Δ₂ σ
    → Δ₁ MC.; Θ ⊢ᵐ c ⦂ A ⇒ B
      ----------------------------------------------------------------------------
    → Δ₂ MC.; subᵉ-subctx σ Θ ⊢ᵐ substᵉ-mcoercion σ c ⦂ subᵉ σ A ⇒ subᵉ σ B
  meta-coercion-sub : ∀ {Δ₁ Δ₂ σ Θ c A B}
    → ECSubstWF Δ₁ Δ₂ σ
    → Δ₁ MC.; Θ ⊢ᵐ̅ c ⦂ A ⇒ B
      -----------------------------------------------------------------------------
    → Δ₂ MC.; subᵉ-subctx σ Θ ⊢ᵐ̅ substᵉ-mcoercionSeq σ c ⦂ subᵉ σ A ⇒ subᵉ σ B

  meta-coercion-sub-single {σ = σ} σ-wf (MC.⊢! ⊢G g) =
    MC.⊢! (mtype-sub-wf σ-wf ⊢G) (subᵉ-ground σ g)
  meta-coercion-sub-single {σ = σ} σ-wf (MC.⊢? ⊢G ℓ g) =
    MC.⊢? (mtype-sub-wf σ-wf ⊢G) ℓ (subᵉ-ground σ g)
  meta-coercion-sub-single σ-wf (MC.⊢fun ⊢c ⊢d) =
    MC.⊢fun (meta-coercion-sub σ-wf ⊢c) (meta-coercion-sub σ-wf ⊢d)
  meta-coercion-sub-single σ-wf (MC.⊢code ⊢cᵒ ⊢cᵉ) =
    MC.⊢code ⊢cᵒ (ec-coercionSeq-sub σ-wf ⊢cᵉ)
  meta-coercion-sub-single σ-wf (MC.⊢ref ⊢c ⊢d) =
    MC.⊢ref (meta-coercion-sub σ-wf ⊢c) (meta-coercion-sub σ-wf ⊢d)
  meta-coercion-sub-single {Δ₂ = Δ₂} {σ = σ} {Θ = Θ} σ-wf (MC.⊢forall ⊢c) =
    MC.⊢forall (subst (λ Θ′ → Δ₂ ,α MC.; Θ′ ⊢ᵐ̅ _ ⦂ _ ⇒ _)
                    (sub-exts-suc-subctx σ Θ) (meta-coercion-sub (ext-subst-wf σ-wf) ⊢c))
  meta-coercion-sub-single {Δ₂ = Δ₂} {σ = σ} {Θ = Θ} σ-wf (MC.⊢sub {A = A} {B = B} {e₁ = e₁} {e₂ = e₂} {c̅ᵐ = c} ⊢e₁ ⊢e₂ ⊢c) =
    MC.⊢sub (ec-sub-wf σ-wf ⊢e₁) (ec-sub-wf σ-wf ⊢e₂)
      (subst (λ Θ′ → Δ₂ MC.; Θ′ ⊢ᵐ̅ substᵉ-mcoercionSeq σ c ⦂ subᵉ σ A ⇒ subᵉ σ B)
        (subᵉ-subctx-ext σ Θ e₁ e₂) (meta-coercion-sub σ-wf ⊢c))
  meta-coercion-sub-single σ-wf (MC.⊢⊥ ⊢A ⊢B ℓ) =
    MC.⊢⊥ (mtype-sub-wf σ-wf ⊢A) (mtype-sub-wf σ-wf ⊢B) ℓ

  meta-coercion-sub σ-wf (MC.⊢[] ⊢A) =
    MC.⊢[] (mtype-sub-wf σ-wf ⊢A)
  meta-coercion-sub σ-wf (MC.⊢; ⊢c ⊢c̅) =
    MC.⊢; (meta-coercion-sub-single σ-wf ⊢c)
           (meta-coercion-sub σ-wf ⊢c̅)

  mutual

    code-ec-ren : ∀ {Δ₁ Δ₂ ρ Θ Γᵒ Γᵐ Σ e Mᵒ T}
      → ECRenWF Δ₁ Δ₂ ρ
      → Δ₁ ; ⟨ Θ , Γᵒ , Γᵐ , Σ ⟩ ; e ⊢ᵒ Mᵒ ⦂ T
        ---------------------------------------------------------------------------------------------------------------------
      → Δ₂ ; ⟨ renᵉ-subctx ρ Θ , renᵉ-octx ρ Γᵒ , renᵉ-mctx ρ Γᵐ , renᵉ-mctx ρ Σ ⟩ ; renᵉ-ec ρ e ⊢ᵒ renᵉ-code ρ Mᵒ ⦂ T

    meta-ec-ren : ∀ {Δ₁ Δ₂ ρ Θ Γᵒ Γᵐ Σ M A}
      → ECRenWF Δ₁ Δ₂ ρ
      → Δ₁ ; ⟨ Θ , Γᵒ , Γᵐ , Σ ⟩ ⊢ᵐ M ⦂ A
        ---------------------------------------------------------------------------------------------------------------
      → Δ₂ ; ⟨ renᵉ-subctx ρ Θ , renᵉ-octx ρ Γᵒ , renᵉ-mctx ρ Γᵐ , renᵉ-mctx ρ Σ ⟩ ⊢ᵐ renᵉ-meta ρ M ⦂ renᵉ ρ A

    code-ec-ren ρ-wf (⊢constᵒ r) = ⊢constᵒ r
    code-ec-ren {ρ = ρ} {Γᵒ = Γᵒ} ρ-wf (⊢varᵒ lookup α<:e) =
      ⊢varᵒ (lookup-ren-octx {Γᵒ = Γᵒ} lookup) (ec-subtype-ren ρ α<:e)
    code-ec-ren {Δ₂ = Δ₂} {ρ = ρ} {Θ = Θ} {Γᵒ = Γᵒ} {Γᵐ = Γᵐ} {Σ = Σ} {e = e}
                ρ-wf (⊢lamᵒ {T₁ = T₁} {T₂ = T₂} {M = M} ⊢M) =
      ⊢lamᵒ (subst
          (λ Γ → Δ₂ ,α ; Γ ; ` zero ⊢ᵒ renᵉ-code (extᵉ ρ) M ⦂ T₂)
          (ctx-cong (ren-ext-suc-subctx-ext ρ Θ e) (ren-ext-suc-octx-lex ρ Γᵒ T₁) refl refl)
          (code-ec-ren {ρ = extᵉ ρ} {⇑ᵉ-subctx Θ , ⇑ᵉ-ec e <: ` zero}
                       {⇑ᵉ-octx Γᵒ , T₁ ＠ zero} {⇑ᵉ-mctx Γᵐ} {⇑ᵉ-heapctx Σ}
                       (ext-ren-wf ρ-wf) ⊢M))
    code-ec-ren {ρ = ρ} {Θ = Θ} ρ-wf (⊢lamᵒ-val {Γᵒ = Γᵒ} α∈Δ owner edge e′<:e ⊢M) =
      ⊢lamᵒ-val (ρ-wf .global-ren α∈Δ)
        (member-map-drop (renᵉ-octx-entry ρ) (Γᵒ .cutoff) (Γᵒ .entries) owner)
        (global-renᵉ-subctx {ρ = ρ} {Θ = Θ} edge)
        (ec-subtype-ren ρ e′<:e)
        (code-ec-ren ρ-wf ⊢M)
    code-ec-ren ρ-wf (⊢appᵒ ⊢L ⊢M) = ⊢appᵒ (code-ec-ren ρ-wf ⊢L) (code-ec-ren ρ-wf ⊢M)
    code-ec-ren ρ-wf (⊢splice ⊢M O↪T) = ⊢splice (meta-ec-ren ρ-wf ⊢M) O↪T
    code-ec-ren ρ-wf (⊢blameᵒ ℓ) = ⊢blameᵒ ℓ

    meta-ec-ren ρ-wf (⊢constᵐ r) = ⊢constᵐ r
    meta-ec-ren ρ-wf (⊢varᵐ Γᵐ∋A) = ⊢varᵐ (lookup-ren-mctx Γᵐ∋A)
    meta-ec-ren ρ-wf (⊢addr Σ∋A) = ⊢addr (lookup-ren-mctx Σ∋A)
    meta-ec-ren ρ-wf (⊢lamᵐ ⊢A ⊢M) = ⊢lamᵐ (mtype-ren-wf ρ-wf ⊢A) (meta-ec-ren ρ-wf ⊢M)
    meta-ec-ren ρ-wf (⊢appᵐ ⊢L ⊢M) = ⊢appᵐ (meta-ec-ren ρ-wf ⊢L) (meta-ec-ren ρ-wf ⊢M)
    meta-ec-ren {Δ₂ = Δ₂} {ρ = ρ} {Θ = Θ} {Γᵒ = Γᵒ} {Γᵐ = Γᵐ} {Σ = Σ}
                ρ-wf (⊢eclam {A = A} {M = M} ⊢M) =
      ⊢eclam (subst
          (λ Γ → Δ₂ ,α ; Γ ⊢ᵐ renᵉ-meta (extᵉ ρ) M ⦂ renᵉ (extᵉ ρ) A)
          (ctx-cong (ren-ext-suc-subctx ρ Θ) (ren-ext-suc-octx ρ Γᵒ) refl refl)
          (meta-ec-ren {ρ = extᵉ ρ} {⇑ᵉ-subctx Θ}
                       {⇑ᵉ-octx Γᵒ} {⇑ᵉ-mctx Γᵐ} {⇑ᵉ-heapctx Σ}
                       (ext-ren-wf ρ-wf) ⊢M))
    meta-ec-ren ρ-wf (⊢ecapp ⊢M ⊢e) = ⊢ecapp (meta-ec-ren ρ-wf ⊢M) (ec-ren-wf ρ-wf ⊢e)
    meta-ec-ren {Δ₂ = Δ₂} {ρ = ρ} {Θ = Θ} {Γᵒ = Γᵒ} {Γᵐ = Γᵐ} {Σ = Σ}
                ρ-wf (⊢subintro {A = A} {M = M} {e₁ = e₁} {e₂ = e₂} ⊢e₁ ⊢e₂ ⊢M) =
      ⊢subintro (ec-ren-wf ρ-wf ⊢e₁) (ec-ren-wf ρ-wf ⊢e₂)
        (subst (λ Γ → Δ₂ ; Γ ⊢ᵐ renᵉ-meta ρ M ⦂ renᵉ ρ A)
          (ctx-cong (renᵉ-subctx-ext ρ Θ e₁ e₂) refl refl refl)
          (meta-ec-ren ρ-wf ⊢M))
    meta-ec-ren {ρ = ρ} ρ-wf (⊢subelim ⊢M e₁<:e₂) = ⊢subelim (meta-ec-ren ρ-wf ⊢M) (ec-subtype-ren ρ e₁<:e₂)
    meta-ec-ren ρ-wf (⊢subelim⋆ ⊢M ℓ) = ⊢subelim⋆ (meta-ec-ren ρ-wf ⊢M) ℓ
    meta-ec-ren ρ-wf (⊢quote ⊢M ⊢e O↪T) = ⊢quote (code-ec-ren ρ-wf ⊢M) (ec-ren-wf ρ-wf ⊢e) O↪T
    meta-ec-ren ρ-wf (⊢ref ⊢M) = ⊢ref (meta-ec-ren ρ-wf ⊢M)
    meta-ec-ren ρ-wf (⊢assign ⊢M ⊢N) = ⊢assign (meta-ec-ren ρ-wf ⊢M) (meta-ec-ren ρ-wf ⊢N)
    meta-ec-ren ρ-wf (⊢deref ⊢M) = ⊢deref (meta-ec-ren ρ-wf ⊢M)
    meta-ec-ren ρ-wf (⊢cast ⊢M ⊢c) = ⊢cast (meta-ec-ren ρ-wf ⊢M) (meta-coercion-ren ρ-wf ⊢c)
    meta-ec-ren ρ-wf (⊢blame ⊢A ℓ) = ⊢blame (mtype-ren-wf ρ-wf ⊢A) ℓ

  mutual

    code-ec-sub : ∀ {Δ₁ Δ₂ σ Θ Γᵒ₁ Γᵒ₂ Γᵐ Σ e Mᵒ T}
      → ECSubstWF Δ₁ Δ₂ σ
      → OCtxSub σ Γᵒ₁ Γᵒ₂
      → Δ₁ ; ⟨ Θ , Γᵒ₁ , Γᵐ , Σ ⟩ ; e ⊢ᵒ Mᵒ ⦂ T
        ------------------------------------------------------------------------
      → Δ₂ ; ⟨ subᵉ-subctx σ Θ , Γᵒ₂ , subᵉ-mctx σ Γᵐ , subᵉ-mctx σ Σ ⟩
          ; subᵉ-ec σ e ⊢ᵒ substᵉ-code σ Mᵒ ⦂ T

    meta-ec-sub : ∀ {Δ₁ Δ₂ σ Θ Γᵒ₁ Γᵒ₂ Γᵐ Σ M A}
      → ECSubstWF Δ₁ Δ₂ σ
      → OCtxSub σ Γᵒ₁ Γᵒ₂
      → Δ₁ ; ⟨ Θ , Γᵒ₁ , Γᵐ , Σ ⟩ ⊢ᵐ M ⦂ A
        ------------------------------------------------------------------------
      → Δ₂ ; ⟨ subᵉ-subctx σ Θ , Γᵒ₂ , subᵉ-mctx σ Γᵐ , subᵉ-mctx σ Σ ⟩
          ⊢ᵐ substᵉ-meta σ M ⦂ subᵉ σ A

    code-ec-sub σ-wf σ[Γᵒ₁]=Γᵒ₂ (⊢constᵒ r) = ⊢constᵒ r
    code-ec-sub {σ = σ} {Θ = Θ} {e = e} σ-wf σ[Γᵒ₁]=Γᵒ₂ (⊢varᵒ lookup α<:e)
      with lookup-sub-octx σ[Γᵒ₁]=Γᵒ₂ lookup
    ... | ⟨ β , σα≡`β , lookup′ ⟩ =
      ⊢varᵒ lookup′ (subst (λ □ → subᵉ-subctx σ Θ ⊢ᵉ □ <: subᵉ-ec σ e)
                     σα≡`β (ec-subtype-sub σ α<:e))
    code-ec-sub {Δ₂ = Δ₂} {σ = σ} {Θ = Θ} {Γᵒ₂ = Γᵒ₂} {Γᵐ = Γᵐ} {Σ = Σ} {e = e}
                σ-wf σ[Γᵒ₁]=Γᵒ₂ (⊢lamᵒ {T₁ = T₁} {T₂ = T₂} {M = M} ⊢M) =
      ⊢lamᵒ (subst
          (λ Γ → Δ₂ ,α ; Γ ; ` zero ⊢ᵒ substᵉ-code (extsᵉ σ) M ⦂ T₂)
          (ctx-cong (sub-exts-suc-subctx-ext σ Θ e) refl refl refl)
          (code-ec-sub {σ = extsᵉ σ} {⇑ᵉ-subctx Θ , ⇑ᵉ-ec e <: ` zero}
                       {Γᵒ₂ = ⇑ᵉ-octx Γᵒ₂ , T₁ ＠ zero} {⇑ᵉ-mctx Γᵐ} {⇑ᵉ-heapctx Σ}
                       (ext-subst-wf σ-wf) (lex-exts-octx-sub {T = T₁} σ[Γᵒ₁]=Γᵒ₂) ⊢M))
    code-ec-sub {Δ₂ = Δ₂} {σ = σ} {Θ = Θ} {Γᵒ₂ = Γᵒ₂} {Γᵐ = Γᵐ} {Σ = Σ} {e = e₀}
                σ-wf σ[Γᵒ₁]=Γᵒ₂
                (⊢lamᵒ-val {Γᵒ = Γᵒ} {T₁ = T₁} {T₂ = T₂} {e₁ = e′} {M = M} {α = α} α∈Δ owner edge e′<:e₀ ⊢M)
      with σ-wf .global-sub α∈Δ
    ... | ⟨ β , ⟨ σα≡`β , β∈Δ ⟩ ⟩ =
      let Γ = ⟨ subᵉ-subctx σ Θ , Γᵒ₂ , subᵉ-mctx σ Γᵐ , subᵉ-mctx σ Σ ⟩ in
      subst (λ e′ → Δ₂ ; Γ ; subᵉ-ec σ e₀ ⊢ᵒ ƛ̅ e′ ˙ substᵉ-code σ M ⦂ T₁ ⇒ T₂)
        (≡-sym σα≡`β)
        (⊢lamᵒ-val β∈Δ (global-sub-octx σ[Γᵒ₁]=Γᵒ₂ σα≡`β owner)
          (subst (λ □ → GlobalEdges (subᵉ-subctx σ Θ) ∋ ⟨ subᵉ-ec σ e′ , □ ⟩) σα≡`β
            (global-subᵉ-subctx {σ = σ} {Θ = Θ} edge))
          (ec-subtype-sub σ e′<:e₀)
          (subst (λ □ → Δ₂ ; Γ ; □ ⊢ᵒ substᵉ-code σ M ⦂ T₂) σα≡`β (code-ec-sub σ-wf σ[Γᵒ₁]=Γᵒ₂ ⊢M)))
    code-ec-sub σ-wf σ[Γᵒ₁]=Γᵒ₂ (⊢appᵒ ⊢L ⊢M) =
      ⊢appᵒ (code-ec-sub σ-wf σ[Γᵒ₁]=Γᵒ₂ ⊢L) (code-ec-sub σ-wf σ[Γᵒ₁]=Γᵒ₂ ⊢M)
    code-ec-sub σ-wf σ[Γᵒ₁]=Γᵒ₂ (⊢splice ⊢M O↪T) = ⊢splice (meta-ec-sub σ-wf σ[Γᵒ₁]=Γᵒ₂ ⊢M) O↪T
    code-ec-sub σ-wf σ[Γᵒ₁]=Γᵒ₂ (⊢blameᵒ ℓ) = ⊢blameᵒ ℓ

    meta-ec-sub σ-wf σ[Γᵒ₁]=Γᵒ₂ (⊢constᵐ r) = ⊢constᵐ r
    meta-ec-sub σ-wf σ[Γᵒ₁]=Γᵒ₂ (⊢varᵐ Γᵐ∋A) = ⊢varᵐ (lookup-sub-mctx Γᵐ∋A)
    meta-ec-sub σ-wf σ[Γᵒ₁]=Γᵒ₂ (⊢addr Σ∋A) = ⊢addr (lookup-sub-mctx Σ∋A)
    meta-ec-sub σ-wf σ[Γᵒ₁]=Γᵒ₂ (⊢lamᵐ ⊢A ⊢M) =
      ⊢lamᵐ (mtype-sub-wf σ-wf ⊢A) (meta-ec-sub σ-wf σ[Γᵒ₁]=Γᵒ₂ ⊢M)
    meta-ec-sub σ-wf σ[Γᵒ₁]=Γᵒ₂ (⊢appᵐ ⊢L ⊢M) =
      ⊢appᵐ (meta-ec-sub σ-wf σ[Γᵒ₁]=Γᵒ₂ ⊢L) (meta-ec-sub σ-wf σ[Γᵒ₁]=Γᵒ₂ ⊢M)
    meta-ec-sub {Δ₂ = Δ₂} {σ = σ} {Θ = Θ} {Γᵒ₂ = Γᵒ₂} {Γᵐ = Γᵐ} {Σ = Σ}
                σ-wf σ[Γᵒ₁]=Γᵒ₂ (⊢eclam {A = A} {M = M} ⊢M) =
      ⊢eclam (subst
          (λ Γ → Δ₂ ,α ; Γ ⊢ᵐ substᵉ-meta (extsᵉ σ) M ⦂ subᵉ (extsᵉ σ) A)
          (ctx-cong (sub-exts-suc-subctx σ Θ) refl refl refl)
          (meta-ec-sub {σ = extsᵉ σ} {⇑ᵉ-subctx Θ}
                       {Γᵒ₂ = ⇑ᵉ-octx Γᵒ₂} {⇑ᵉ-mctx Γᵐ} {⇑ᵉ-heapctx Σ}
                       (ext-subst-wf σ-wf) (exts-octx-sub σ[Γᵒ₁]=Γᵒ₂) ⊢M))
    meta-ec-sub {σ = σ} σ-wf σ[Γᵒ₁]=Γᵒ₂ (⊢ecapp {A = A} {e = e} ⊢M ⊢e) =
      ⊢ecapp {A = subᵉ (extsᵉ σ) A} (meta-ec-sub σ-wf σ[Γᵒ₁]=Γᵒ₂ ⊢M) (ec-sub-wf σ-wf ⊢e)
    meta-ec-sub {Δ₂ = Δ₂} {σ = σ} {Θ = Θ} {Γᵒ₂ = Γᵒ₂} {Γᵐ = Γᵐ} {Σ = Σ}
                σ-wf σ[Γᵒ₁]=Γᵒ₂
                (⊢subintro {A = A} {M = M} {e₁ = e₁} {e₂ = e₂} ⊢e₁ ⊢e₂ ⊢M) =
      ⊢subintro (ec-sub-wf σ-wf ⊢e₁) (ec-sub-wf σ-wf ⊢e₂)
        (subst (λ Γ → Δ₂ ; Γ ⊢ᵐ substᵉ-meta σ M ⦂ subᵉ σ A)
          (ctx-cong (subᵉ-subctx-ext σ Θ e₁ e₂) refl refl refl)
          (meta-ec-sub σ-wf σ[Γᵒ₁]=Γᵒ₂ ⊢M))
    meta-ec-sub {σ = σ} σ-wf σ[Γᵒ₁]=Γᵒ₂ (⊢subelim ⊢M e₁<:e₂) =
      ⊢subelim (meta-ec-sub σ-wf σ[Γᵒ₁]=Γᵒ₂ ⊢M) (ec-subtype-sub σ e₁<:e₂)
    meta-ec-sub σ-wf σ[Γᵒ₁]=Γᵒ₂ (⊢subelim⋆ ⊢M ℓ) = ⊢subelim⋆ (meta-ec-sub σ-wf σ[Γᵒ₁]=Γᵒ₂ ⊢M) ℓ
    meta-ec-sub σ-wf σ[Γᵒ₁]=Γᵒ₂ (⊢quote ⊢M ⊢e O↪T) =
      ⊢quote (code-ec-sub σ-wf σ[Γᵒ₁]=Γᵒ₂ ⊢M) (ec-sub-wf σ-wf ⊢e) O↪T
    meta-ec-sub σ-wf σ[Γᵒ₁]=Γᵒ₂ (⊢ref ⊢M) = ⊢ref (meta-ec-sub σ-wf σ[Γᵒ₁]=Γᵒ₂ ⊢M)
    meta-ec-sub σ-wf σ[Γᵒ₁]=Γᵒ₂ (⊢assign ⊢M ⊢N) =
      ⊢assign (meta-ec-sub σ-wf σ[Γᵒ₁]=Γᵒ₂ ⊢M) (meta-ec-sub σ-wf σ[Γᵒ₁]=Γᵒ₂ ⊢N)
    meta-ec-sub σ-wf σ[Γᵒ₁]=Γᵒ₂ (⊢deref ⊢M) = ⊢deref (meta-ec-sub σ-wf σ[Γᵒ₁]=Γᵒ₂ ⊢M)
    meta-ec-sub σ-wf σ[Γᵒ₁]=Γᵒ₂ (⊢cast ⊢M ⊢c) =
      ⊢cast (meta-ec-sub σ-wf σ[Γᵒ₁]=Γᵒ₂ ⊢M) (meta-coercion-sub σ-wf ⊢c)
    meta-ec-sub σ-wf σ[Γᵒ₁]=Γᵒ₂ (⊢blame ⊢A ℓ) = ⊢blame (mtype-sub-wf σ-wf ⊢A) ℓ

  single-shift-ec : ∀ e e′
      ------------------------------------------
    → subᵉ-ec (e •ᵉₛ idsᵉ) (⇑ᵉ-ec e′) ≡ e′
  single-shift-ec e ε = refl
  single-shift-ec e (` α) = refl
  {-# REWRITE single-shift-ec #-}

  single-shift-subctx-edges : ∀ e Θ
      ---------------------------------------------------
    → map (subᵉ-subctx-entry (e •ᵉₛ idsᵉ)) (map (renᵉ-subctx-entry suc) Θ) ≡ Θ
  single-shift-subctx-edges e [] = refl
  single-shift-subctx-edges e (⟨ e₁ , e₂ ⟩ ∷ Θ)
    rewrite single-shift-subctx-edges e Θ = refl

  single-shift-subctx : ∀ e Θ
      ---------------------------------------------------
    → subᵉ-subctx (e •ᵉₛ idsᵉ) (⇑ᵉ-subctx Θ) ≡ Θ
  single-shift-subctx e Θ = subctx-cong (single-shift-subctx-edges e (Θ .edges))

  single-shift-subctx-ext : ∀ e Θ e′
      ---------------------------------------------------------------------------
    → subᵉ-subctx (e •ᵉₛ idsᵉ) (⇑ᵉ-subctx Θ , ⇑ᵉ-ec e′ <: ` zero) ≡ Θ , e′ <: e
  single-shift-subctx-ext e Θ e′ =
    trans (subᵉ-subctx-ext (e •ᵉₛ idsᵉ) (⇑ᵉ-subctx Θ) (⇑ᵉ-ec e′) (` zero))
      (cong (λ Θ′ → Θ′ , e′ <: e) (single-shift-subctx e Θ))

  sub-ren-cancel-ec : ∀ σ ρ e
    → (∀ α → subᵉ-ec σ (renᵉ-ec ρ (` α)) ≡ ` α)
      ------------------------------------------------
    → subᵉ-ec σ (renᵉ-ec ρ e) ≡ e
  sub-ren-cancel-ec σ ρ ε cancel = refl
  sub-ren-cancel-ec σ ρ (` α) cancel = cancel α

  sub-ren-cancel-ec⋆ : ∀ σ ρ ê
    → (∀ α → subᵉ-ec σ (renᵉ-ec ρ (` α)) ≡ ` α)
      ------------------------------------------------
    → subᵉ-ec⋆ σ (renᵉ-ec⋆ ρ ê) ≡ ê
  sub-ren-cancel-ec⋆ σ ρ ⋆ cancel = refl
  sub-ren-cancel-ec⋆ σ ρ (ec e) cancel rewrite sub-ren-cancel-ec σ ρ e cancel = refl

  sub-ren-cancel-exts : ∀ σ ρ
    → (∀ α → subᵉ-ec σ (renᵉ-ec ρ (` α)) ≡ ` α)
      ---------------------------------------------------------------
    → ∀ α → subᵉ-ec (extsᵉ σ) (renᵉ-ec (extᵉ ρ) (` α)) ≡ ` α
  sub-ren-cancel-exts σ ρ cancel zero = refl
  sub-ren-cancel-exts σ ρ cancel (suc α) rewrite cancel α = refl

  sub-ren-cancel-mtype : ∀ σ ρ A
    → (∀ α → subᵉ-ec σ (renᵉ-ec ρ (` α)) ≡ ` α)
      ---------------------------------------------
    → subᵉ σ (renᵉ ρ A) ≡ A
  sub-ren-cancel-mtype σ ρ ⋆ cancel = refl
  sub-ren-cancel-mtype σ ρ (` ι) cancel = refl
  sub-ren-cancel-mtype σ ρ (A ⇒ B) cancel
    rewrite sub-ren-cancel-mtype σ ρ A cancel
          | sub-ren-cancel-mtype σ ρ B cancel = refl
  sub-ren-cancel-mtype σ ρ (Ref A) cancel
    rewrite sub-ren-cancel-mtype σ ρ A cancel = refl
  sub-ren-cancel-mtype σ ρ (‶ O ″ ê) cancel
    rewrite sub-ren-cancel-ec⋆ σ ρ ê cancel = refl
  sub-ren-cancel-mtype σ ρ (∀̇ A) cancel
    rewrite sub-ren-cancel-mtype (extsᵉ σ) (extᵉ ρ) A (sub-ren-cancel-exts σ ρ cancel) = refl
  sub-ren-cancel-mtype σ ρ (e₁ <: e₂ => A) cancel
    rewrite sub-ren-cancel-ec σ ρ e₁ cancel
          | sub-ren-cancel-ec σ ρ e₂ cancel
          | sub-ren-cancel-mtype σ ρ A cancel = refl

  single-shift-mtype : ∀ e A
      -------------------------------------------
    → subᵉ (e •ᵉₛ idsᵉ) (renᵉ suc A) ≡ A
  single-shift-mtype e A = sub-ren-cancel-mtype (e •ᵉₛ idsᵉ) suc A (λ α → refl)
  {-# REWRITE single-shift-mtype #-}

  single-shift-mctx-map : (e : EC) (Γᵐ : MCtx)
      ------------------------------------------------------------
    → map (subᵉ (e •ᵉₛ idsᵉ)) (map (renᵉ suc) Γᵐ) ≡ Γᵐ
  single-shift-mctx-map e [] = refl
  single-shift-mctx-map e (A ∷ Γᵐ) rewrite single-shift-mctx-map e Γᵐ = refl
  {-# REWRITE single-shift-mctx-map #-}


{- Below are the main lemmas for preservation! -}

-- | EC successor renaming into a meta term.
meta-ec-ren-suc : ∀ {Δ Θ Γᵒ Γᵐ Σ M A}
  → Δ ; ⟨ Θ , Γᵒ , Γᵐ , Σ ⟩ ⊢ᵐ M ⦂ A
    ------------------------------------------------------------------------
  → Δ ,α ; ⇑ᵉ-ctx ⟨ Θ , Γᵒ , Γᵐ , Σ ⟩ ⊢ᵐ renᵉ-meta suc M ⦂ renᵉ suc A
meta-ec-ren-suc {Δ = Δ} ⊢M = meta-ec-ren (suc-wf Δ) ⊢M

-- | Single EC substitution into an object term, specialized to runtime
-- | allocation for code lambdas.
subst-ec-code : ∀ {Δ Θ Γᵒ Γᵐ Σ e Mᵒ S T}
  → Δ ⊢ Γᵒ OCtx
  → Δ ,α ; ⟨ ⇑ᵉ-subctx Θ , ⇑ᵉ-ec e <: ` zero , ⇑ᵉ-octx Γᵒ , S ＠ zero , ⇑ᵉ-mctx Γᵐ , ⇑ᵉ-heapctx Σ ⟩ ; ` zero ⊢ᵒ Mᵒ ⦂ T
    ------------------------------------------------------------------------------------------------------------------------------
  → Δ ,ᵍα ; ⟨ Θ ,ᵍ e <: ` freshᵉ Δ , Γᵒ , S ＠ freshᵉ Δ , Γᵐ , Σ ⟩ ; ` freshᵉ Δ ⊢ᵒ Mᵒ [ ` freshᵉ Δ ]ᵉᵒ ⦂ T
subst-ec-code {Δ = Δ} {Θ = Θ} {Γᵒ = Γᵒ} {Γᵐ = Γᵐ} {Σ = Σ} {e = e} {Mᵒ = Mᵒ} {S = S} {T = T} ⊢Γᵒ ⊢Mᵒ =
  code-⊆ˢ subctx-lex-to-global
    (subst (λ □ → Δ ,ᵍα ; □ ; ` freshᵉ Δ ⊢ᵒ Mᵒ [ ` freshᵉ Δ ]ᵉᵒ ⦂ T)
      (ctx-cong (single-shift-subctx-ext (` freshᵉ Δ) Θ e) refl refl refl)
      (code-ec-sub {σ = (` freshᵉ Δ) •ᵉₛ idsᵉ} {Θ = ⇑ᵉ-subctx Θ , ⇑ᵉ-ec e <: ` zero}
                   {Γᵒ₂ = Γᵒ , S ＠ freshᵉ Δ} {Γᵐ = ⇑ᵉ-mctx Γᵐ} {Σ = ⇑ᵉ-heapctx Σ}
                   (fresh-subst-wf Δ) (fresh-octx-sub {Δ = Δ} {Γᵒ = Γᵒ} {S = S} ⊢Γᵒ) ⊢Mᵒ))

-- | Single EC substitution into a meta term.
subst-ec-meta : ∀ {Δ Θ Γᵒ Γᵐ Σ e M A}
  → Δ ,α ; ⇑ᵉ-ctx ⟨ Θ , Γᵒ , Γᵐ , Σ ⟩ ⊢ᵐ M ⦂ A
  → Δ ⊢ᵉ e
    ------------------------------------------------------------
  → Δ ; ⟨ Θ , Γᵒ , Γᵐ , Σ ⟩ ⊢ᵐ M [ e ]ᵉᵐ ⦂ A [ e ]ᵉ
subst-ec-meta {Θ = Θ} {Γᵒ} {Γᵐ} {Σ} {e} {M} {A} ⊢M ⊢e =
  subst (λ □ → _ ; □ ⊢ᵐ M [ e ]ᵉᵐ ⦂ A [ e ]ᵉ)
    (ctx-cong (single-shift-subctx e Θ) refl refl refl)
    (meta-ec-sub {σ = e •ᵉₛ idsᵉ} {Θ = ⇑ᵉ-subctx Θ} {Γᵒ₂ = Γᵒ} {Γᵐ = ⇑ᵉ-mctx Γᵐ} {Σ = ⇑ᵉ-heapctx Σ}
                 (single-subst-wf ⊢e) (single-octx-sub {e = e} Γᵒ) ⊢M)

-- | Single EC substitution into a meta coercion.
subst-ec-coercion : ∀ {Δ Θ e c A B}
  → Δ ,α MC.; ⇑ᵉ-subctx Θ ⊢ᵐ̅ c ⦂ A ⇒ B
  → Δ ⊢ᵉ e
    ------------------------------------------------
  → Δ MC.; Θ ⊢ᵐ̅ substᵉ-mcoercionSeq (e •ᵉₛ idsᵉ) c ⦂ A [ e ]ᵉ ⇒ B [ e ]ᵉ
subst-ec-coercion {Θ = Θ} {e} ⊢c ⊢e =
  subst (λ □ → _ MC.; □ ⊢ᵐ̅ _ ⦂ _ ⇒ _)
        (single-shift-subctx e Θ) (meta-coercion-sub (single-subst-wf ⊢e) ⊢c)
