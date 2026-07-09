module Theories.SpaceEfficiency.Proofs.CodeCtxWeakening where

open import Data.Nat using (suc; zero)
open import Data.Product renaming (_,_ to ⟨_,_⟩)
open import Relation.Binary.PropositionalEquality using (subst; cong; refl)
  renaming (sym to ≡-sym)

open import Theories.Utils using (_∋_; _⊆_; _≼_; ≼-member; ⟨_,_,_⟩; ⟨_,_,_,_⟩; lookup-snoc; lookup-map; ∋-∷ʳ;
  lookup-map-inv; member-map-drop; member-map-drop-inv; here; there)
open import Theories.SpaceEfficiency.CCAlphaRefStarSyntaxAndTypeSystem


------------------------------------------------------------------------
-- Code-context lookup-stability weakening

⇑ᵉ-octx-≼ : ∀ {Γᵒ₁ Γᵒ₂}
  → Γᵒ₁ .entries ≼ Γᵒ₂ .entries
    -----------------------------------------
  → (⇑ᵉ-octx Γᵒ₁) .entries ≼ (⇑ᵉ-octx Γᵒ₂) .entries
⇑ᵉ-octx-≼ {Γᵒ₁ = Γᵒ₁} {Γᵒ₂ = Γᵒ₂} Γᵒ₁≼Γᵒ₂ lookup
  with lookup-map-inv {f = renᵉ-octx-entry suc} lookup
... | ⟨ ⟨ _ , α ⟩ , lookup′ , refl ⟩ =
  lookup-map (Γᵒ₁≼Γᵒ₂ lookup′)

⇑ᵉ-octx-≼ᵒ : ∀ {Γᵒ₁ Γᵒ₂}
  → Γᵒ₁ ≼ᵒ Γᵒ₂
    -----------------------------
  → ⇑ᵉ-octx Γᵒ₁ ≼ᵒ ⇑ᵉ-octx Γᵒ₂
⇑ᵉ-octx-≼ᵒ {Γᵒ₁ = Γᵒ₁} {Γᵒ₂ = Γᵒ₂} Γᵒ₁≼Γᵒ₂ =
  octx≼ (⇑ᵉ-octx-≼ {Γᵒ₁ = Γᵒ₁} {Γᵒ₂ = Γᵒ₂} (Γᵒ₁≼Γᵒ₂ .entries≼)) global
  where
  global : GlobalEntries (⇑ᵉ-octx Γᵒ₁) ⊆ GlobalEntries (⇑ᵉ-octx Γᵒ₂)
  global member with member-map-drop-inv (renᵉ-octx-entry suc) (Γᵒ₁ .cutoff) (Γᵒ₁ .entries) member
  ... | ⟨ ⟨ T , β ⟩ , member′ , refl ⟩ =
    member-map-drop (renᵉ-octx-entry suc) (Γᵒ₂ .cutoff) (Γᵒ₂ .entries)
      (Γᵒ₁≼Γᵒ₂ .globalEntries⊆ member′)

lam-octx-≼ : ∀ {Γᵒ₁ Γᵒ₂ T α}
  → Γᵒ₁ .entries ≼ Γᵒ₂ .entries
    --------------------------------------------------------------------
  → (⇑ᵉ-octx Γᵒ₁ , T ＠ α) .entries ≼ (⇑ᵉ-octx Γᵒ₂ , T ＠ α) .entries
lam-octx-≼ Γᵒ₁≼Γᵒ₂ here = here
lam-octx-≼ {Γᵒ₁ = Γᵒ₁} {Γᵒ₂ = Γᵒ₂} Γᵒ₁≼Γᵒ₂ (there lookup) =
  there (⇑ᵉ-octx-≼ {Γᵒ₁ = Γᵒ₁} {Γᵒ₂ = Γᵒ₂} Γᵒ₁≼Γᵒ₂ lookup)

lam-octx-≼ᵒ : ∀ {Γᵒ₁ Γᵒ₂ T α}
  → Γᵒ₁ ≼ᵒ Γᵒ₂
    ---------------------------------------------
  → (⇑ᵉ-octx Γᵒ₁ , T ＠ α) ≼ᵒ (⇑ᵉ-octx Γᵒ₂ , T ＠ α)
lam-octx-≼ᵒ {Γᵒ₁ = Γᵒ₁} {Γᵒ₂ = Γᵒ₂} Γᵒ₁≼Γᵒ₂ =
  octx≼ (lam-octx-≼ {Γᵒ₁ = Γᵒ₁} {Γᵒ₂ = Γᵒ₂} (Γᵒ₁≼Γᵒ₂ .entries≼))
        ((⇑ᵉ-octx-≼ᵒ Γᵒ₁≼Γᵒ₂) .globalEntries⊆)

mutual

  code-octx-≼ : ∀ {Δ Θ Γᵒ₁ Γᵒ₂ Γᵐ Σ e M T}
    → Γᵒ₁ ≼ᵒ Γᵒ₂
    → Δ ; ⟨ Θ , Γᵒ₁ , Γᵐ , Σ ⟩ ; e ⊢ᵒ M ⦂ T
      ------------------------------------------------
    → Δ ; ⟨ Θ , Γᵒ₂ , Γᵐ , Σ ⟩ ; e ⊢ᵒ M ⦂ T
  code-octx-≼ Γᵒ₁≼Γᵒ₂ (⊢constᵒ r) =
    ⊢constᵒ r
  code-octx-≼ Γᵒ₁≼Γᵒ₂ (⊢varᵒ lookup α<:e) =
    ⊢varᵒ (Γᵒ₁≼Γᵒ₂ .entries≼ lookup) α<:e
  code-octx-≼ {Γᵒ₁ = Γᵒ₁} {Γᵒ₂ = Γᵒ₂} Γᵒ₁≼Γᵒ₂ (⊢lamᵒ {T₁ = T₁} ⊢M) =
    ⊢lamᵒ
      (code-octx-≼
        {Γᵒ₁ = ⇑ᵉ-octx Γᵒ₁ , T₁ ＠ zero}
        {Γᵒ₂ = ⇑ᵉ-octx Γᵒ₂ , T₁ ＠ zero}
        (lam-octx-≼ᵒ {Γᵒ₁ = Γᵒ₁} {Γᵒ₂ = Γᵒ₂} {T = T₁} {α = zero} Γᵒ₁≼Γᵒ₂)
        ⊢M)
  code-octx-≼ Γᵒ₁≼Γᵒ₂ (⊢lamᵒ-val α<Δ owner edge e′<:e ⊢M) =
    ⊢lamᵒ-val α<Δ (Γᵒ₁≼Γᵒ₂ .globalEntries⊆ owner) edge e′<:e
      (code-octx-≼ Γᵒ₁≼Γᵒ₂ ⊢M)
  code-octx-≼ Γᵒ₁≼Γᵒ₂ (⊢appᵒ ⊢L ⊢M) =
    ⊢appᵒ (code-octx-≼ Γᵒ₁≼Γᵒ₂ ⊢L) (code-octx-≼ Γᵒ₁≼Γᵒ₂ ⊢M)
  code-octx-≼ Γᵒ₁≼Γᵒ₂ (⊢splice ⊢M O=T) =
    ⊢splice (meta-octx-≼ Γᵒ₁≼Γᵒ₂ ⊢M) O=T
  code-octx-≼ Γᵒ₁≼Γᵒ₂ (⊢blameᵒ ℓ) =
    ⊢blameᵒ ℓ

  meta-octx-≼ : ∀ {Δ Θ Γᵒ₁ Γᵒ₂ Γᵐ Σ M A}
    → Γᵒ₁ ≼ᵒ Γᵒ₂
    → Δ ; ⟨ Θ , Γᵒ₁ , Γᵐ , Σ ⟩ ⊢ᵐ M ⦂ A
      -------------------------------------------
    → Δ ; ⟨ Θ , Γᵒ₂ , Γᵐ , Σ ⟩ ⊢ᵐ M ⦂ A
  meta-octx-≼ Γᵒ₁≼Γᵒ₂ (⊢constᵐ r) =
    ⊢constᵐ r
  meta-octx-≼ Γᵒ₁≼Γᵒ₂ (⊢varᵐ Γᵐ∋A) =
    ⊢varᵐ Γᵐ∋A
  meta-octx-≼ Γᵒ₁≼Γᵒ₂ (⊢addr Σ∋A) =
    ⊢addr Σ∋A
  meta-octx-≼ Γᵒ₁≼Γᵒ₂ (⊢lamᵐ ⊢A ⊢M) =
    ⊢lamᵐ ⊢A (meta-octx-≼ Γᵒ₁≼Γᵒ₂ ⊢M)
  meta-octx-≼ Γᵒ₁≼Γᵒ₂ (⊢appᵐ ⊢L ⊢M) =
    ⊢appᵐ (meta-octx-≼ Γᵒ₁≼Γᵒ₂ ⊢L) (meta-octx-≼ Γᵒ₁≼Γᵒ₂ ⊢M)
  meta-octx-≼ {Γᵒ₁ = Γᵒ₁} {Γᵒ₂ = Γᵒ₂} Γᵒ₁≼Γᵒ₂ (⊢eclam ⊢M) =
    ⊢eclam (meta-octx-≼ (⇑ᵉ-octx-≼ᵒ {Γᵒ₁ = Γᵒ₁} {Γᵒ₂ = Γᵒ₂} Γᵒ₁≼Γᵒ₂) ⊢M)
  meta-octx-≼ Γᵒ₁≼Γᵒ₂ (⊢ecapp ⊢M ⊢e) =
    ⊢ecapp (meta-octx-≼ Γᵒ₁≼Γᵒ₂ ⊢M) ⊢e
  meta-octx-≼ Γᵒ₁≼Γᵒ₂ (⊢subintro ⊢e₁ ⊢e₂ ⊢M) =
    ⊢subintro ⊢e₁ ⊢e₂ (meta-octx-≼ Γᵒ₁≼Γᵒ₂ ⊢M)
  meta-octx-≼ Γᵒ₁≼Γᵒ₂ (⊢subelim ⊢M e₁<:e₂) =
    ⊢subelim (meta-octx-≼ Γᵒ₁≼Γᵒ₂ ⊢M) e₁<:e₂
  meta-octx-≼ Γᵒ₁≼Γᵒ₂ (⊢subelim⋆ ⊢M ℓ) =
    ⊢subelim⋆ (meta-octx-≼ Γᵒ₁≼Γᵒ₂ ⊢M) ℓ
  meta-octx-≼ Γᵒ₁≼Γᵒ₂ (⊢quote ⊢M ⊢e O=T) =
    ⊢quote (code-octx-≼ Γᵒ₁≼Γᵒ₂ ⊢M) ⊢e O=T
  meta-octx-≼ Γᵒ₁≼Γᵒ₂ (⊢ref ⊢M) =
    ⊢ref (meta-octx-≼ Γᵒ₁≼Γᵒ₂ ⊢M)
  meta-octx-≼ Γᵒ₁≼Γᵒ₂ (⊢assign ⊢M ⊢N) =
    ⊢assign (meta-octx-≼ Γᵒ₁≼Γᵒ₂ ⊢M) (meta-octx-≼ Γᵒ₁≼Γᵒ₂ ⊢N)
  meta-octx-≼ Γᵒ₁≼Γᵒ₂ (⊢deref ⊢M) =
    ⊢deref (meta-octx-≼ Γᵒ₁≼Γᵒ₂ ⊢M)
  meta-octx-≼ Γᵒ₁≼Γᵒ₂ (⊢cast ⊢M ⊢c) =
    ⊢cast (meta-octx-≼ Γᵒ₁≼Γᵒ₂ ⊢M) ⊢c
  meta-octx-≼ Γᵒ₁≼Γᵒ₂ (⊢blame ⊢A ℓ) =
    ⊢blame ⊢A ℓ


------------------------------------------------------------------------
-- One-step code-context weakening

code-octx-weaken : ∀ {Δ Θ Γᵒ Γᵐ Σ e M T S β}
  → Δ ; ⟨ Θ , Γᵒ , Γᵐ , Σ ⟩ ; e ⊢ᵒ M ⦂ T
    --------------------------------------------------------------
  → Δ ; ⟨ Θ , Γᵒ ,ᵍ S ＠ β , Γᵐ , Σ ⟩ ; e ⊢ᵒ M ⦂ T
code-octx-weaken = code-octx-≼ ≼ᵒ-snoc

meta-octx-weaken : ∀ {Δ Θ Γᵒ Γᵐ Σ M A S β}
  → Δ ; ⟨ Θ , Γᵒ , Γᵐ , Σ ⟩ ⊢ᵐ M ⦂ A
    -----------------------------------------------------
  → Δ ; ⟨ Θ , Γᵒ ,ᵍ S ＠ β , Γᵐ , Σ ⟩ ⊢ᵐ M ⦂ A
meta-octx-weaken = meta-octx-≼ ≼ᵒ-snoc
