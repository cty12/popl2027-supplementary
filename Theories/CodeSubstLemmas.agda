module LambdaAlphaRefStar.Theories.CodeSubstLemmas where

open import Data.List using ([]; _∷_)
open import Data.Maybe using (just; nothing)
open import Data.Nat using (zero; suc)
open import Data.Product using (∃-syntax; _×_) renaming (_,_ to ⟨_,_⟩)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; trans) renaming (sym to ≡-sym)
open import Relation.Nullary using (yes; no)
open import Relation.Nullary.Negation using (contradiction)

open import Utils
open import LambdaAlphaRefStar.Theories.CCAlphaRefStarSyntaxAndTypeSystem
open import LambdaAlphaRefStar.Theories.CodeSubst
open import LambdaAlphaRefStar.Theories.ECSubst using (_[_]ᵉᵒ)
open import LambdaAlphaRefStar.Theories.ECSubstLemmas using (subst-ec-code)


record CodeRenWF (Δ : ECCtx) (ρ : RenameCode) (Γᵒ₁ Γᵒ₂ : OCtx) : Set where
  constructor codeRenWF
  field
    lookup-ren : ∀ {x T α} → Γᵒ₁ ∋ᵒ x ⦂ ⟨ T , α ⟩ → Γᵒ₂ ∋ᵒ ρ x ⦂ ⟨ T , α ⟩

    member-ren : ∀ {T α} → Γᵒ₁ ∋ᵒ ⟨ T , α ⟩ → Γᵒ₂ ∋ᵒ ⟨ T , α ⟩

    global-ren : ∀ {T α}
      → GlobalEntries Γᵒ₁ ∋ ⟨ T , α ⟩
        --------------------------------
      → GlobalEntries Γᵒ₂ ∋ ⟨ T , α ⟩

open CodeRenWF

private
  global-⇑ᵉ-code-ren-wf : ∀ {Δ ρ Γᵒ₁ Γᵒ₂ T α}
    → CodeRenWF Δ ρ Γᵒ₁ Γᵒ₂
    → GlobalEntries (⇑ᵉ-octx Γᵒ₁) ∋ ⟨ T , α ⟩
      ------------------------------------------------
    → GlobalEntries (⇑ᵉ-octx Γᵒ₂) ∋ ⟨ T , α ⟩
  global-⇑ᵉ-code-ren-wf {Γᵒ₁ = Γᵒ₁} {Γᵒ₂ = Γᵒ₂} ρ-wf member
    with member-map-drop-inv (renᵉ-octx-entry suc) (Γᵒ₁ .cutoff) (Γᵒ₁ .entries) member
  ... | ⟨ ⟨ T , α ⟩ , member′ , refl ⟩ =
    member-map-drop (renᵉ-octx-entry suc) (Γᵒ₂ .cutoff) (Γᵒ₂ .entries)
      (ρ-wf .global-ren member′)

  global-move-to-global-code-ren-wf : ∀ {Δ Γᵒ T₀ T α}
    → GlobalEntries (Γᵒ , T₀ ＠ freshᵉ Δ) ∋ ⟨ T , α ⟩
      -------------------------------------------------------
    → GlobalEntries (Γᵒ ,ᵍ T₀ ＠ freshᵉ Δ) ∋ ⟨ T , α ⟩
  global-move-to-global-code-ren-wf {Γᵒ = Γᵒ} member =
    drop-snoc (Γᵒ .cutoff) (Γᵒ .entries) member


-- | A few renamings that we care about are well-formed
⇑ᵉ-code-ren-wf : ∀ {Δ ρ Γᵒ₁ Γᵒ₂}
  → CodeRenWF Δ ρ Γᵒ₁ Γᵒ₂
    ------------------------------------------------
  → CodeRenWF (Δ ,α) ρ (⇑ᵉ-octx Γᵒ₁) (⇑ᵉ-octx Γᵒ₂)
⇑ᵉ-code-ren-wf {ρ = ρ} {Γᵒ₁ = Γᵒ₁} {Γᵒ₂ = Γᵒ₂} ρ-wf =
  codeRenWF lookup member (global-⇑ᵉ-code-ren-wf ρ-wf)
  where
  lookup : ∀ {x T α} → ⇑ᵉ-octx Γᵒ₁ ∋ᵒ x ⦂ ⟨ T , α ⟩ → ⇑ᵉ-octx Γᵒ₂ ∋ᵒ ρ x ⦂ ⟨ T , α ⟩
  lookup lookup′ with lookup-map-inv {f = renᵉ-octx-entry suc} lookup′
  ... | ⟨ ⟨ _ , β ⟩ , lookup₀ , refl ⟩ = lookup-map (ρ-wf .lookup-ren lookup₀)

  member : ∀ {T α} → ⇑ᵉ-octx Γᵒ₁ ∋ᵒ ⟨ T , α ⟩ → ⇑ᵉ-octx Γᵒ₂ ∋ᵒ ⟨ T , α ⟩
  member member′ with member-map-inv {f = renᵉ-octx-entry suc} member′
  ... | ⟨ ⟨ _ , β ⟩ , member₀ , refl ⟩ = member-map (ρ-wf .member-ren member₀)

ext-code-ren-wf : ∀ {Δ ρ Γᵒ₁ Γᵒ₂ T}
  → CodeRenWF Δ ρ Γᵒ₁ Γᵒ₂
    ------------------------------------------------------------------------
  → CodeRenWF (Δ ,α) (extᵒ ρ) (⇑ᵉ-octx Γᵒ₁ , T ＠ zero) (⇑ᵉ-octx Γᵒ₂ , T ＠ zero)
ext-code-ren-wf {Δ = Δ} {ρ = ρ} {Γᵒ₁ = Γᵒ₁} {Γᵒ₂ = Γᵒ₂} {T = T₀} ρ-wf =
  codeRenWF lookup member owner
  where
    lookup : ∀ {x T α}
      → (⇑ᵉ-octx Γᵒ₁ , T₀ ＠ zero) ∋ᵒ x ⦂ ⟨ T , α ⟩
      → (⇑ᵉ-octx Γᵒ₂ , T₀ ＠ zero) ∋ᵒ extᵒ ρ x ⦂ ⟨ T , α ⟩
    lookup here = here
    lookup (there lookup′) with lookup-map-inv {f = renᵉ-octx-entry suc} lookup′
    ... | ⟨ ⟨ _ , β ⟩ , lookup₀ , refl ⟩ = there (lookup-map (ρ-wf .lookup-ren lookup₀))

    member : ∀ {T α}
      → (⇑ᵉ-octx Γᵒ₁ , T₀ ＠ zero) ∋ᵒ ⟨ T , α ⟩
      → (⇑ᵉ-octx Γᵒ₂ , T₀ ＠ zero) ∋ᵒ ⟨ T , α ⟩
    member Z = Z
    member (S member′) with member-map-inv {f = renᵉ-octx-entry suc} member′
    ... | ⟨ ⟨ _ , β ⟩ , member₀ , refl ⟩ = S (member-map (ρ-wf .member-ren member₀))

    owner : ∀ {T α}
      → GlobalEntries (⇑ᵉ-octx Γᵒ₁ , T₀ ＠ zero) ∋ ⟨ T , α ⟩
      → GlobalEntries (⇑ᵉ-octx Γᵒ₂ , T₀ ＠ zero) ∋ ⟨ T , α ⟩
    owner = global-⇑ᵉ-code-ren-wf ρ-wf

move-to-global-code-ren-wf : ∀ Δ Γᵒ T
  → Δ ⊢ Γᵒ OCtx
    ---------------------------------------------------------------------------------------
  → CodeRenWF (Δ ,ᵍα) (freshᵒ Γᵒ •ᵒ idᵒ) (Γᵒ , T ＠ freshᵉ Δ) (Γᵒ ,ᵍ T ＠ freshᵉ Δ)
move-to-global-code-ren-wf Δ Γᵒ T ⊢Γᵒ =
  codeRenWF lookup member owner
  where
  lookup : ∀ {x S β} → (Γᵒ , T ＠ freshᵉ Δ) ∋ᵒ x ⦂ ⟨ S , β ⟩
    → (Γᵒ ,ᵍ T ＠ freshᵉ Δ) ∋ᵒ (freshᵒ Γᵒ •ᵒ idᵒ) x ⦂ ⟨ S , β ⟩
  lookup here = ∋-snoc-last (Γᵒ .entries)
  lookup (there lookup′) = lookup-snoc {Γ = Γᵒ .entries} lookup′

  member : ∀ {S β} → (Γᵒ , T ＠ freshᵉ Δ) ∋ᵒ ⟨ S , β ⟩
    → (Γᵒ ,ᵍ T ＠ freshᵉ Δ) ∋ᵒ ⟨ S , β ⟩
  member member′ with member->lookup {Γ = (Γᵒ , T ＠ freshᵉ Δ) .entries} member′
  ... | ⟨ x , lookup′ ⟩ = lookup->member {Γ = (Γᵒ ,ᵍ T ＠ freshᵉ Δ) .entries} (lookup lookup′)

  owner : ∀ {S α}
    → GlobalEntries (Γᵒ , T ＠ freshᵉ Δ) ∋ ⟨ S , α ⟩
    → GlobalEntries (Γᵒ ,ᵍ T ＠ freshᵉ Δ) ∋ ⟨ S , α ⟩
  owner = global-move-to-global-code-ren-wf {Δ = Δ} {Γᵒ = Γᵒ} {T₀ = T}


mutual

  code-ren : ∀ {Δ Θ Γᵒ₁ Γᵒ₂ Γᵐ Σ e Mᵒ T ρ}
    → CodeRenWF Δ ρ Γᵒ₁ Γᵒ₂
    → Δ ; ⟨ Θ , Γᵒ₁ , Γᵐ , Σ ⟩ ; e ⊢ᵒ Mᵒ ⦂ T
      ---------------------------------------------------------
    → Δ ; ⟨ Θ , Γᵒ₂ , Γᵐ , Σ ⟩ ; e ⊢ᵒ renᵒ-code ρ Mᵒ ⦂ T
  code-ren ρ-wf (⊢constᵒ r) = ⊢constᵒ r
  code-ren ρ-wf (⊢varᵒ lookup α<:e) = ⊢varᵒ (ρ-wf .lookup-ren lookup) α<:e
  code-ren ρ-wf (⊢lamᵒ ⊢M) = ⊢lamᵒ (code-ren (ext-code-ren-wf ρ-wf) ⊢M)
  code-ren ρ-wf (⊢lamᵒ-val α∈Δ owner edge e′<:e ⊢M) =
    ⊢lamᵒ-val α∈Δ (ρ-wf .global-ren owner) edge e′<:e (code-ren ρ-wf ⊢M)
  code-ren ρ-wf (⊢appᵒ ⊢L ⊢M) = ⊢appᵒ (code-ren ρ-wf ⊢L) (code-ren ρ-wf ⊢M)
  code-ren ρ-wf (⊢splice ⊢M O↪T) = ⊢splice (meta-code-ren ρ-wf ⊢M) O↪T
  code-ren ρ-wf (⊢blameᵒ ℓ) = ⊢blameᵒ ℓ

  meta-code-ren : ∀ {Δ Θ Γᵒ₁ Γᵒ₂ Γᵐ Σ M A ρ}
    → CodeRenWF Δ ρ Γᵒ₁ Γᵒ₂
    → Δ ; ⟨ Θ , Γᵒ₁ , Γᵐ , Σ ⟩ ⊢ᵐ M ⦂ A
      ---------------------------------------------------
    → Δ ; ⟨ Θ , Γᵒ₂ , Γᵐ , Σ ⟩ ⊢ᵐ renᵒ-meta ρ M ⦂ A
  meta-code-ren ρ-wf (⊢constᵐ r) = ⊢constᵐ r
  meta-code-ren ρ-wf (⊢varᵐ Γᵐ∋A) = ⊢varᵐ Γᵐ∋A
  meta-code-ren ρ-wf (⊢addr Σ∋A) = ⊢addr Σ∋A
  meta-code-ren ρ-wf (⊢lamᵐ ⊢A ⊢M) = ⊢lamᵐ ⊢A (meta-code-ren ρ-wf ⊢M)
  meta-code-ren ρ-wf (⊢appᵐ ⊢L ⊢M) = ⊢appᵐ (meta-code-ren ρ-wf ⊢L) (meta-code-ren ρ-wf ⊢M)
  meta-code-ren ρ-wf (⊢eclam ⊢M) = ⊢eclam (meta-code-ren (⇑ᵉ-code-ren-wf ρ-wf) ⊢M)
  meta-code-ren ρ-wf (⊢ecapp ⊢M ⊢e) = ⊢ecapp (meta-code-ren ρ-wf ⊢M) ⊢e
  meta-code-ren ρ-wf (⊢subintro ⊢e₁ ⊢e₂ ⊢M) = ⊢subintro ⊢e₁ ⊢e₂ (meta-code-ren ρ-wf ⊢M)
  meta-code-ren ρ-wf (⊢subelim ⊢M e₁<:e₂) = ⊢subelim (meta-code-ren ρ-wf ⊢M) e₁<:e₂
  meta-code-ren ρ-wf (⊢subelim⋆ ⊢M ℓ) = ⊢subelim⋆ (meta-code-ren ρ-wf ⊢M) ℓ
  meta-code-ren ρ-wf (⊢quote ⊢M ⊢e O↪T) = ⊢quote (code-ren ρ-wf ⊢M) ⊢e O↪T
  meta-code-ren ρ-wf (⊢ref ⊢M) = ⊢ref (meta-code-ren ρ-wf ⊢M)
  meta-code-ren ρ-wf (⊢assign ⊢M ⊢N) = ⊢assign (meta-code-ren ρ-wf ⊢M) (meta-code-ren ρ-wf ⊢N)
  meta-code-ren ρ-wf (⊢deref ⊢M) = ⊢deref (meta-code-ren ρ-wf ⊢M)
  meta-code-ren ρ-wf (⊢cast ⊢M ⊢c) = ⊢cast (meta-code-ren ρ-wf ⊢M) ⊢c
  meta-code-ren ρ-wf (⊢blame ⊢A ℓ) = ⊢blame ⊢A ℓ


subst-code-λ-body : ∀ {Δ Θ Γᵒ Γᵐ Σ e T S Nᵒ}
  → Δ ⊢ Γᵒ OCtx
  → Δ ,α ; ⟨ ⇑ᵉ-subctx Θ , ⇑ᵉ-ec e <: ` zero , ⇑ᵉ-octx Γᵒ , T ＠ zero , ⇑ᵉ-mctx Γᵐ , ⇑ᵉ-heapctx Σ ⟩ ; ` zero ⊢ᵒ Nᵒ ⦂ S
    ---------------------------------------------------------------------------------------------------------------------------------
  → Δ ,ᵍα ; ⟨ Θ ,ᵍ e <: ` freshᵉ Δ , Γᵒ ,ᵍ T ＠ freshᵉ Δ , Γᵐ , Σ ⟩ ; ` freshᵉ Δ ⊢ᵒ Nᵒ [ ` freshᵉ Δ ]ᵉᵒ [ ` freshᵒ Γᵒ ]ᵒ ⦂ S
subst-code-λ-body {Δ} {Θ} {Γᵒ} {Γᵐ} {Σ} {e} {T} ⊢Γᵒ ⊢Nᵒ =
  subst (λ □ → Δ ,ᵍα ; _ ; _ ⊢ᵒ □ ⦂ _)
        (≡-sym (subst-code-var-ren (freshᵒ Γᵒ) _))
        (code-ren (move-to-global-code-ren-wf Δ Γᵒ T ⊢Γᵒ) (subst-ec-code ⊢Γᵒ ⊢Nᵒ))
