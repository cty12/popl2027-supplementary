module LambdaAlphaRefStar.Theories.MetaSubstLemmas where

open import Data.Nat using (zero; suc)
open import Data.Maybe using (just)
open import Data.Product renaming (_,_ to ⟨_,_⟩)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Utils using (_∋_⦂_; S_; here; there; ⟨_,_,_⟩; ⟨_,_,_,_⟩)
open import LambdaAlphaRefStar.Theories.CCAlphaRefStarSyntaxAndTypeSystem
open import LambdaAlphaRefStar.Theories.CodeSubstLemmas using (CodeRenWF; codeRenWF; meta-code-ren)
open import LambdaAlphaRefStar.Theories.ECSubst using (renᵉ-meta)
open import LambdaAlphaRefStar.Theories.ECSubstLemmas using (meta-ec-ren-suc)
open import LambdaAlphaRefStar.Theories.MetaSubst
open import LambdaAlphaRefStar.Theories.SubCtxWeakening using (meta-subctx-weaken)


private

  MetaRenWF : RenameMeta → MCtx → MCtx → Set
  MetaRenWF ρ Γᵐ₁ Γᵐ₂ = ∀ {x A} → Γᵐ₁ ∋ x ⦂ A → Γᵐ₂ ∋ ρ x ⦂ A

  MetaSubstWF : ECCtx → SubCtx → OCtx → MCtx → MCtx → HeapCtx → SubstMeta → Set
  MetaSubstWF Δ Θ Γᵒ Γᵐ₁ Γᵐ₂ Σ σ =
    ∀ {x A} → Γᵐ₁ ∋ x ⦂ A → Δ ; ⟨ Θ , Γᵒ , Γᵐ₂ , Σ ⟩ ⊢ᵐ σ x ⦂ A

  ⇑ᵉ-meta-ren-wf : ∀ {ρ Γᵐ₁ Γᵐ₂}
    → MetaRenWF ρ Γᵐ₁ Γᵐ₂
      ------------------------------------------------
    → MetaRenWF ρ (⇑ᵉ-mctx Γᵐ₁) (⇑ᵉ-mctx Γᵐ₂)
  ⇑ᵉ-meta-ren-wf {Γᵐ₁ = Γᵐ₁} {Γᵐ₂ = Γᵐ₂} ρ-wf lookup′
    with lookup-⇑ᵉ-mctx-inv {Γᵐ = Γᵐ₁} lookup′
  ... | ⟨ A , refl , lookup₀ ⟩ = lookup-⇑ᵉ-mctx {Γᵐ = Γᵐ₂} (ρ-wf lookup₀)

  ext-meta-ren-wf : ∀ {ρ Γᵐ₁ Γᵐ₂ A}
    → MetaRenWF ρ Γᵐ₁ Γᵐ₂
      ---------------------------------------------
    → MetaRenWF (extᵐ ρ) (Γᵐ₁ ⸴ A) (Γᵐ₂ ⸴ A)
  ext-meta-ren-wf ρ-wf here = here
  ext-meta-ren-wf ρ-wf (there lookup) = there (ρ-wf lookup)

  mutual

    code-meta-ren : ∀ {Δ Θ Γᵒ Γᵐ₁ Γᵐ₂ Σ e Mᵒ T ρ}
      → MetaRenWF ρ Γᵐ₁ Γᵐ₂
      → Δ ; ⟨ Θ , Γᵒ , Γᵐ₁ , Σ ⟩ ; e ⊢ᵒ Mᵒ ⦂ T
        ------------------------------------------------------------
      → Δ ; ⟨ Θ , Γᵒ , Γᵐ₂ , Σ ⟩ ; e ⊢ᵒ renᵐ-code ρ Mᵒ ⦂ T
    code-meta-ren ρ-wf (⊢constᵒ r) = ⊢constᵒ r
    code-meta-ren ρ-wf (⊢varᵒ lookup α<:e) = ⊢varᵒ lookup α<:e
    code-meta-ren ρ-wf (⊢lamᵒ ⊢M) = ⊢lamᵒ (code-meta-ren (⇑ᵉ-meta-ren-wf ρ-wf) ⊢M)
    code-meta-ren ρ-wf (⊢lamᵒ-val α∈Δ owner edge e′<:e ⊢M) =
      ⊢lamᵒ-val α∈Δ owner edge e′<:e (code-meta-ren ρ-wf ⊢M)
    code-meta-ren ρ-wf (⊢appᵒ ⊢L ⊢M) =
      ⊢appᵒ (code-meta-ren ρ-wf ⊢L) (code-meta-ren ρ-wf ⊢M)
    code-meta-ren ρ-wf (⊢splice ⊢M O↪T) = ⊢splice (meta-meta-ren ρ-wf ⊢M) O↪T
    code-meta-ren ρ-wf (⊢blameᵒ ℓ) = ⊢blameᵒ ℓ

    meta-meta-ren : ∀ {Δ Θ Γᵒ Γᵐ₁ Γᵐ₂ Σ M A ρ}
      → MetaRenWF ρ Γᵐ₁ Γᵐ₂
      → Δ ; ⟨ Θ , Γᵒ , Γᵐ₁ , Σ ⟩ ⊢ᵐ M ⦂ A
        ------------------------------------------------------
      → Δ ; ⟨ Θ , Γᵒ , Γᵐ₂ , Σ ⟩ ⊢ᵐ renᵐ-meta ρ M ⦂ A
    meta-meta-ren ρ-wf (⊢constᵐ r) = ⊢constᵐ r
    meta-meta-ren ρ-wf (⊢varᵐ lookup) = ⊢varᵐ (ρ-wf lookup)
    meta-meta-ren ρ-wf (⊢addr lookup) = ⊢addr lookup
    meta-meta-ren ρ-wf (⊢lamᵐ ⊢A ⊢M) =
      ⊢lamᵐ ⊢A (meta-meta-ren (ext-meta-ren-wf ρ-wf) ⊢M)
    meta-meta-ren ρ-wf (⊢appᵐ ⊢L ⊢M) =
      ⊢appᵐ (meta-meta-ren ρ-wf ⊢L) (meta-meta-ren ρ-wf ⊢M)
    meta-meta-ren ρ-wf (⊢eclam ⊢M) = ⊢eclam (meta-meta-ren (⇑ᵉ-meta-ren-wf ρ-wf) ⊢M)
    meta-meta-ren ρ-wf (⊢ecapp ⊢M ⊢e) = ⊢ecapp (meta-meta-ren ρ-wf ⊢M) ⊢e
    meta-meta-ren ρ-wf (⊢subintro ⊢e₁ ⊢e₂ ⊢M) =
      ⊢subintro ⊢e₁ ⊢e₂ (meta-meta-ren ρ-wf ⊢M)
    meta-meta-ren ρ-wf (⊢subelim ⊢M e₁<:e₂) =
      ⊢subelim (meta-meta-ren ρ-wf ⊢M) e₁<:e₂
    meta-meta-ren ρ-wf (⊢subelim⋆ ⊢M ℓ) = ⊢subelim⋆ (meta-meta-ren ρ-wf ⊢M) ℓ
    meta-meta-ren ρ-wf (⊢quote ⊢M ⊢e O↪T) = ⊢quote (code-meta-ren ρ-wf ⊢M) ⊢e O↪T
    meta-meta-ren ρ-wf (⊢ref ⊢M) = ⊢ref (meta-meta-ren ρ-wf ⊢M)
    meta-meta-ren ρ-wf (⊢assign ⊢M ⊢N) =
      ⊢assign (meta-meta-ren ρ-wf ⊢M) (meta-meta-ren ρ-wf ⊢N)
    meta-meta-ren ρ-wf (⊢deref ⊢M) = ⊢deref (meta-meta-ren ρ-wf ⊢M)
    meta-meta-ren ρ-wf (⊢cast ⊢M ⊢c) = ⊢cast (meta-meta-ren ρ-wf ⊢M) ⊢c
    meta-meta-ren ρ-wf (⊢blame ⊢A ℓ) = ⊢blame ⊢A ℓ

  ⇑ᵉ-meta-subst-wf : ∀ {Δ Θ Γᵒ Γᵐ₁ Γᵐ₂ Σ σ}
    → MetaSubstWF Δ Θ Γᵒ Γᵐ₁ Γᵐ₂ Σ σ
      ------------------------------------------------------
    → MetaSubstWF (Δ ,α) (⇑ᵉ-subctx Θ) (⇑ᵉ-octx Γᵒ)
                  (⇑ᵉ-mctx Γᵐ₁) (⇑ᵉ-mctx Γᵐ₂) (⇑ᵉ-heapctx Σ) (⇑ᵉˢ σ)
  ⇑ᵉ-meta-subst-wf {Γᵐ₁ = Γᵐ₁} σ-wf lookup′
    with lookup-⇑ᵉ-mctx-inv {Γᵐ = Γᵐ₁} lookup′
  ... | ⟨ A , refl , lookup₀ ⟩ = meta-ec-ren-suc (σ-wf lookup₀)

  ext-meta-subst-wf : ∀ {Δ Θ Γᵒ Γᵐ₁ Γᵐ₂ Σ σ A}
    → MetaSubstWF Δ Θ Γᵒ Γᵐ₁ Γᵐ₂ Σ σ
      ---------------------------------------------------------
    → MetaSubstWF Δ Θ Γᵒ (Γᵐ₁ ⸴ A) (Γᵐ₂ ⸴ A) Σ (extsᵐ σ)
  ext-meta-subst-wf {Γᵐ₂ = Γᵐ₂} {A = A} σ-wf here = ⊢varᵐ here
  ext-meta-subst-wf σ-wf (there lookup) = meta-meta-ren there (σ-wf lookup)

  lex-code-ren-wf : ∀ Δ Γᵒ T
      ----------------------------------
    → CodeRenWF (Δ ,α) suc Γᵒ (Γᵒ , T ＠ zero)
  lex-code-ren-wf Δ Γᵒ T =
    codeRenWF (λ lookup → there lookup) (λ member → S member) (λ member → member)

  code-lam-meta-subst-wf : ∀ {Δ Θ Γᵒ Γᵐ₁ Γᵐ₂ Σ σ e T}
    → MetaSubstWF Δ Θ Γᵒ Γᵐ₁ Γᵐ₂ Σ σ
      ---------------------------------------------------------------------------------------
    → MetaSubstWF (Δ ,α) (⇑ᵉ-subctx Θ , ⇑ᵉ-ec e <: ` zero) (⇑ᵉ-octx Γᵒ , T ＠ zero)
                  (⇑ᵉ-mctx Γᵐ₁) (⇑ᵉ-mctx Γᵐ₂) (⇑ᵉ-heapctx Σ) (⇑ᵒˢ (⇑ᵉˢ σ))
  code-lam-meta-subst-wf {Δ = Δ} {Γᵒ = Γᵒ} {Γᵐ₁ = Γᵐ₁} {T = T} σ-wf lookup′
    with lookup-⇑ᵉ-mctx-inv {Γᵐ = Γᵐ₁} lookup′
  ... | ⟨ A , refl , lookup₀ ⟩ =
    meta-code-ren (lex-code-ren-wf Δ (⇑ᵉ-octx Γᵒ) T)
      (meta-subctx-weaken (meta-ec-ren-suc (σ-wf lookup₀)))

  mutual

    code-meta-sub : ∀ {Δ Θ Γᵒ Γᵐ₁ Γᵐ₂ Σ e Mᵒ T σ}
      → MetaSubstWF Δ Θ Γᵒ Γᵐ₁ Γᵐ₂ Σ σ
      → Δ ; ⟨ Θ , Γᵒ , Γᵐ₁ , Σ ⟩ ; e ⊢ᵒ Mᵒ ⦂ T
        ------------------------------------------------------------
      → Δ ; ⟨ Θ , Γᵒ , Γᵐ₂ , Σ ⟩ ; e ⊢ᵒ substᵐ-code σ Mᵒ ⦂ T
    code-meta-sub σ-wf (⊢constᵒ r) = ⊢constᵒ r
    code-meta-sub σ-wf (⊢varᵒ lookup α<:e) = ⊢varᵒ lookup α<:e
    code-meta-sub σ-wf (⊢lamᵒ ⊢M) = ⊢lamᵒ (code-meta-sub (code-lam-meta-subst-wf σ-wf) ⊢M)
    code-meta-sub σ-wf (⊢lamᵒ-val α∈Δ owner edge e′<:e ⊢M) =
      ⊢lamᵒ-val α∈Δ owner edge e′<:e (code-meta-sub σ-wf ⊢M)
    code-meta-sub σ-wf (⊢appᵒ ⊢L ⊢M) =
      ⊢appᵒ (code-meta-sub σ-wf ⊢L) (code-meta-sub σ-wf ⊢M)
    code-meta-sub σ-wf (⊢splice ⊢M O↪T) = ⊢splice (meta-meta-sub σ-wf ⊢M) O↪T
    code-meta-sub σ-wf (⊢blameᵒ ℓ) = ⊢blameᵒ ℓ

    meta-meta-sub : ∀ {Δ Θ Γᵒ Γᵐ₁ Γᵐ₂ Σ M A σ}
      → MetaSubstWF Δ Θ Γᵒ Γᵐ₁ Γᵐ₂ Σ σ
      → Δ ; ⟨ Θ , Γᵒ , Γᵐ₁ , Σ ⟩ ⊢ᵐ M ⦂ A
        ------------------------------------------------------
      → Δ ; ⟨ Θ , Γᵒ , Γᵐ₂ , Σ ⟩ ⊢ᵐ substᵐ-meta σ M ⦂ A
    meta-meta-sub σ-wf (⊢constᵐ r) = ⊢constᵐ r
    meta-meta-sub σ-wf (⊢varᵐ lookup) = σ-wf lookup
    meta-meta-sub σ-wf (⊢addr lookup) = ⊢addr lookup
    meta-meta-sub σ-wf (⊢lamᵐ ⊢A ⊢M) =
      ⊢lamᵐ ⊢A (meta-meta-sub (ext-meta-subst-wf σ-wf) ⊢M)
    meta-meta-sub σ-wf (⊢appᵐ ⊢L ⊢M) =
      ⊢appᵐ (meta-meta-sub σ-wf ⊢L) (meta-meta-sub σ-wf ⊢M)
    meta-meta-sub σ-wf (⊢eclam ⊢M) = ⊢eclam (meta-meta-sub (⇑ᵉ-meta-subst-wf σ-wf) ⊢M)
    meta-meta-sub σ-wf (⊢ecapp ⊢M ⊢e) = ⊢ecapp (meta-meta-sub σ-wf ⊢M) ⊢e
    meta-meta-sub σ-wf (⊢subintro ⊢e₁ ⊢e₂ ⊢M) =
      ⊢subintro ⊢e₁ ⊢e₂ (meta-meta-sub (λ lookup → meta-subctx-weaken (σ-wf lookup)) ⊢M)
    meta-meta-sub σ-wf (⊢subelim ⊢M e₁<:e₂) =
      ⊢subelim (meta-meta-sub σ-wf ⊢M) e₁<:e₂
    meta-meta-sub σ-wf (⊢subelim⋆ ⊢M ℓ) = ⊢subelim⋆ (meta-meta-sub σ-wf ⊢M) ℓ
    meta-meta-sub σ-wf (⊢quote ⊢M ⊢e O↪T) = ⊢quote (code-meta-sub σ-wf ⊢M) ⊢e O↪T
    meta-meta-sub σ-wf (⊢ref ⊢M) = ⊢ref (meta-meta-sub σ-wf ⊢M)
    meta-meta-sub σ-wf (⊢assign ⊢M ⊢N) =
      ⊢assign (meta-meta-sub σ-wf ⊢M) (meta-meta-sub σ-wf ⊢N)
    meta-meta-sub σ-wf (⊢deref ⊢M) = ⊢deref (meta-meta-sub σ-wf ⊢M)
    meta-meta-sub σ-wf (⊢cast ⊢M ⊢c) = ⊢cast (meta-meta-sub σ-wf ⊢M) ⊢c
    meta-meta-sub σ-wf (⊢blame ⊢A ℓ) = ⊢blame ⊢A ℓ

  single-meta-subst-wf : ∀ {Δ Θ Γᵒ Γᵐ Σ A N}
    → Δ ; ⟨ Θ , Γᵒ , Γᵐ , Σ ⟩ ⊢ᵐ N ⦂ A
      ---------------------------------------------------
    → MetaSubstWF Δ Θ Γᵒ (Γᵐ ⸴ A) Γᵐ Σ (N •ᵐₛ idsᵐ)
  single-meta-subst-wf ⊢N here = ⊢N
  single-meta-subst-wf ⊢N (there lookup) = ⊢varᵐ lookup


subst-meta : ∀ {Δ Θ Γᵒ Γᵐ Σ M N A B}
  → Δ ; ⟨ Θ , Γᵒ , Γᵐ ⸴ A , Σ ⟩ ⊢ᵐ M ⦂ B
  → Δ ; ⟨ Θ , Γᵒ , Γᵐ , Σ ⟩ ⊢ᵐ N ⦂ A
    ---------------------------------------------
  → Δ ; ⟨ Θ , Γᵒ , Γᵐ , Σ ⟩ ⊢ᵐ M [ N ]ᵐ ⦂ B
subst-meta ⊢M ⊢N = meta-meta-sub (single-meta-subst-wf ⊢N) ⊢M
