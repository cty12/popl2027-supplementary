module Theories.WellTypedTermImpliesWellFormedTypes where

open import Data.List using (List; []; _∷_; map)
open import Data.List.Relation.Unary.All using (All) renaming ([] to []ᴬ; _∷_ to _∷ᴬ_)
open import Data.Product using (Σ-syntax; _×_; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; cong; trans) renaming (sym to ≡-sym)

open import Theories.Utils using (_∋_; _∋_⦂_; member-map-drop-inv; here; there)
open import Theories.CCAlphaRefStarSyntaxAndTypeSystem
open import Theories.CoercionSequences.Meta.Preservation as MCP using (wf-codᵐ̅)


-- +--------------------------------+ --
-- | Well-formedness infrastructure | --
-- +--------------------------------+ --

RenWF : ECCtx → ECCtx → RenameEC → Set
RenWF Δ₁ Δ₂ ρ = ∀ {α} → α < Δ₁ .size → ρ α < Δ₂ .size

SubstWF : ECCtx → ECCtx → SubstEC → Set
SubstWF Δ₁ Δ₂ σ = ∀ {α} → α < Δ₁ .size → Δ₂ ⊢ᵉ σ α

suc-ren-wf : ∀ {Δ} → RenWF Δ (Δ ,α) suc
suc-ren-wf α<Δ = s≤s α<Δ

ext-ren-wf : ∀ {Δ₁ Δ₂ ρ}
  → RenWF Δ₁ Δ₂ ρ
    ------------------------------------
  → RenWF (Δ₁ ,α) (Δ₂ ,α) (extᵉ ρ)
ext-ren-wf ρ-wf {zero} _ = s≤s z≤n
ext-ren-wf ρ-wf {suc α} (s≤s α<Δ₁) = s≤s (ρ-wf α<Δ₁)

wf-renᵉ-ec : ∀ {Δ₁ Δ₂ ρ e}
  → RenWF Δ₁ Δ₂ ρ
  → Δ₁ ⊢ᵉ e
    --------------------------
  → Δ₂ ⊢ᵉ renᵉ-ec ρ e
wf-renᵉ-ec ρ-wf wf-ε = wf-ε
wf-renᵉ-ec ρ-wf (wf-` α<Δ₁) = wf-` (ρ-wf α<Δ₁)

wf-renᵉ-ec⋆ : ∀ {Δ₁ Δ₂ ρ ê}
  → RenWF Δ₁ Δ₂ ρ
  → Δ₁ ⊢ᵉ⋆ ê
    -----------------------------
  → Δ₂ ⊢ᵉ⋆ renᵉ-ec⋆ ρ ê
wf-renᵉ-ec⋆ ρ-wf wf-⋆ = wf-⋆
wf-renᵉ-ec⋆ ρ-wf (wf-ec ⊢e) = wf-ec (wf-renᵉ-ec ρ-wf ⊢e)

wf-renᵉ-mtype : ∀ {Δ₁ Δ₂ ρ A}
  → RenWF Δ₁ Δ₂ ρ
  → Δ₁ ⊢ᵐᵗ A
    -------------------------
  → Δ₂ ⊢ᵐᵗ renᵉ ρ A
wf-renᵉ-mtype ρ-wf wf-⋆ = wf-⋆
wf-renᵉ-mtype ρ-wf wf-base = wf-base
wf-renᵉ-mtype ρ-wf (wf-fun ⊢A ⊢B) =
  wf-fun (wf-renᵉ-mtype ρ-wf ⊢A) (wf-renᵉ-mtype ρ-wf ⊢B)
wf-renᵉ-mtype ρ-wf (wf-ref ⊢A) =
  wf-ref (wf-renᵉ-mtype ρ-wf ⊢A)
wf-renᵉ-mtype ρ-wf (wf-code ⊢ê) =
  wf-code (wf-renᵉ-ec⋆ ρ-wf ⊢ê)
wf-renᵉ-mtype {Δ₁ = Δ₁} {Δ₂ = Δ₂} ρ-wf (wf-forall ⊢A) =
  wf-forall (wf-renᵉ-mtype (ext-ren-wf {Δ₁ = Δ₁} {Δ₂ = Δ₂} ρ-wf) ⊢A)
wf-renᵉ-mtype ρ-wf (wf-sub ⊢e₁ ⊢e₂ ⊢A) =
  wf-sub (wf-renᵉ-ec ρ-wf ⊢e₁)
         (wf-renᵉ-ec ρ-wf ⊢e₂)
         (wf-renᵉ-mtype ρ-wf ⊢A)

wf-⇑ᵉ-subctx-edges : ∀ {Δ} {edges : List (EC × EC)}
  → All (λ { ⟨ e₁ , e₂ ⟩ → Δ ⊢ᵉ e₁ × Δ ⊢ᵉ e₂ }) edges
    -------------------------------------------------------------------------------
  → All (λ { ⟨ e₁ , e₂ ⟩ → Δ ,α ⊢ᵉ e₁ × Δ ,α ⊢ᵉ e₂ })
        (map (λ { ⟨ e₁ , e₂ ⟩ → ⟨ ⇑ᵉ-ec e₁ , ⇑ᵉ-ec e₂ ⟩ }) edges)
wf-⇑ᵉ-subctx-edges []ᴬ = []ᴬ
wf-⇑ᵉ-subctx-edges {Δ = Δ} (⟨ ⊢e₁ , ⊢e₂ ⟩ ∷ᴬ ⊢Θ) =
  ⟨ wf-renᵉ-ec (suc-ren-wf {Δ = Δ}) ⊢e₁
  , wf-renᵉ-ec (suc-ren-wf {Δ = Δ}) ⊢e₂
  ⟩ ∷ᴬ wf-⇑ᵉ-subctx-edges ⊢Θ

⇑ᵉ-target-eq : ∀ {e₁ e₂ e₃ e₄ e₅ e₆ α}
  → ⟨ ⇑ᵉ-ec e₁ , ⇑ᵉ-ec e₂ ⟩ ≡ ⟨ e₅ , ` α ⟩
  → ⟨ ⇑ᵉ-ec e₃ , ⇑ᵉ-ec e₄ ⟩ ≡ ⟨ e₆ , ` α ⟩
    ---------------------------------------------
  → ⇑ᵉ-ec e₂ ≡ ⇑ᵉ-ec e₄
⇑ᵉ-target-eq eq₁ eq₂ = trans (cong proj₂ eq₁) (≡-sym (cong proj₂ eq₂))

wf-⇑ᵉ-subctx : ∀ {Δ Θ}
  → Δ ⊢ Θ SubCtx
    ---------------------------------
  → Δ ,α ⊢ ⇑ᵉ-subctx Θ SubCtx
wf-⇑ᵉ-subctx {Δ} {Θ} ⟨ ⊢edges , ⟨ ⊢global , unique ⟩ ⟩ =
  ⟨ wf-⇑ᵉ-subctx-edges ⊢edges ,
    ⟨ wf-⇑ᵉ-subctx-global {Δ} {Θ} ⊢global ,
      wf-⇑ᵉ-subctx-unique {Δ} {Θ} ⊢global unique
    ⟩ ⟩
  where
  wf-⇑ᵉ-subctx-global : ∀ {Δ Θ e₁ e₂}
    → (∀ {e₃ e₄}
          → GlobalEdges Θ ∋ ⟨ e₃ , e₄ ⟩
          → Σ[ α ∈ ECVar ] ((e₄ ≡ ` α) × GlobalEC Δ α))
    → GlobalEdges (⇑ᵉ-subctx Θ) ∋ ⟨ e₁ , e₂ ⟩
    → Σ[ α ∈ ECVar ] ((e₂ ≡ ` α) × GlobalEC (Δ ,α) α)
  wf-⇑ᵉ-subctx-global {Θ = Θ} ⊢global edge
    with member-map-drop-inv (λ { ⟨ e₁ , e₂ ⟩ → ⟨ ⇑ᵉ-ec e₁ , ⇑ᵉ-ec e₂ ⟩ }) (Θ .cutoff) (Θ .edges) edge
  ... | ⟨ ⟨ e₁ , e₂ ⟩ , ⟨ edge′ , refl ⟩ ⟩
    with ⊢global edge′
  ... | ⟨ α , ⟨ refl , globalα ⟩ ⟩ = ⟨ suc α , ⟨ refl , globalEC-suc globalα ⟩ ⟩

  wf-⇑ᵉ-subctx-unique : ∀ {Δ Θ}
    → (∀ {e₁ e₂}
          → GlobalEdges Θ ∋ ⟨ e₁ , e₂ ⟩
          → Σ[ α ∈ ECVar ] ((e₂ ≡ ` α) × GlobalEC Δ α))
    → UniqueGlobalAncestor Θ
    → UniqueGlobalAncestor (⇑ᵉ-subctx Θ)
  wf-⇑ᵉ-subctx-unique {Θ = Θ} ⊢global unique edge₁ edge₂
    with member-map-drop-inv (λ { ⟨ e₁ , e₂ ⟩ → ⟨ ⇑ᵉ-ec e₁ , ⇑ᵉ-ec e₂ ⟩ })
           (Θ .cutoff) (Θ .edges) edge₁
       | member-map-drop-inv (λ { ⟨ e₁ , e₂ ⟩ → ⟨ ⇑ᵉ-ec e₁ , ⇑ᵉ-ec e₂ ⟩ })
           (Θ .cutoff) (Θ .edges) edge₂
  ... | ⟨ ⟨ e₁ , e₂ ⟩ , ⟨ edge₁′ , eq₁ ⟩ ⟩
      | ⟨ ⟨ e₃ , e₄ ⟩ , ⟨ edge₂′ , eq₂ ⟩ ⟩
    with ⊢global edge₁′ | ⊢global edge₂′
  ... | ⟨ α , ⟨ e₂≡`α , globalα ⟩ ⟩
      | ⟨ β , ⟨ e₄≡`β , globalβ ⟩ ⟩
    rewrite e₂≡`α | e₄≡`β | `-injective (⇑ᵉ-injective (⇑ᵉ-target-eq eq₁ eq₂)) =
    trans (≡-sym (cong proj₁ eq₁))
      (trans (cong ⇑ᵉ-ec (unique edge₁′ edge₂′)) (cong proj₁ eq₂))



wf-⇑ᵉ-octx : ∀ {Δ Γᵒ}
  → Δ ⊢ Γᵒ OCtx
    -------------------------
  → Δ ,α ⊢ ⇑ᵉ-octx Γᵒ OCtx
wf-⇑ᵉ-octx {Δ = Δ} {Γᵒ = Γᵒ} = octx-wf-suc {Δ = Δ} {Γᵒ = Γᵒ}

wf-⇑ᵉ-mctx : ∀ {Δ Γᵐ}
  → Δ ⊢ Γᵐ MCtx
    -------------------------
  → Δ ,α ⊢ ⇑ᵉ-mctx Γᵐ MCtx
wf-⇑ᵉ-mctx []ᴬ = []ᴬ
wf-⇑ᵉ-mctx {Δ = Δ} (⊢A ∷ᴬ ⊢Γᵐ) =
  wf-renᵉ-mtype (suc-ren-wf {Δ = Δ}) ⊢A ∷ᴬ wf-⇑ᵉ-mctx ⊢Γᵐ

wf-⇑ᵉ-heapctx : ∀ {Δ Σ}
  → Δ ⊢ Σ HeapCtx
    -----------------------------
  → Δ ,α ⊢ ⇑ᵉ-heapctx Σ HeapCtx
wf-⇑ᵉ-heapctx = wf-⇑ᵉ-mctx

wf-⇑ᵉ-ctx : ∀ {Δ Γ}
  → Δ ⊢ Γ Ctx
    --------------------------
  → Δ ,α ⊢ ⇑ᵉ-ctx Γ Ctx
wf-⇑ᵉ-ctx {Δ = Δ} (wf-ctx {Θ = Θ} {Γᵒ = Γᵒ} ⊢Θ ⊢Γᵒ ⊢Γᵐ ⊢Σ) =
  wf-ctx (wf-⇑ᵉ-subctx {Θ = Θ} ⊢Θ)
         (wf-⇑ᵉ-octx {Δ = Δ} {Γᵒ = Γᵒ} ⊢Γᵒ)
         (wf-⇑ᵉ-mctx ⊢Γᵐ)
         (wf-⇑ᵉ-heapctx ⊢Σ)

ext-subst-wf : ∀ {Δ₁ Δ₂ σ}
  → SubstWF Δ₁ Δ₂ σ
    ----------------------------------------
  → SubstWF (Δ₁ ,α) (Δ₂ ,α) (extsᵉ σ)
ext-subst-wf σ-wf {zero} _ = wf-` (s≤s z≤n)
ext-subst-wf {Δ₂ = Δ₂} σ-wf {suc α} (s≤s α<Δ₁) =
  wf-renᵉ-ec (suc-ren-wf {Δ = Δ₂}) (σ-wf α<Δ₁)

wf-subᵉ-ec : ∀ {Δ₁ Δ₂ σ e}
  → SubstWF Δ₁ Δ₂ σ
  → Δ₁ ⊢ᵉ e
    --------------------------
  → Δ₂ ⊢ᵉ subᵉ-ec σ e
wf-subᵉ-ec σ-wf wf-ε = wf-ε
wf-subᵉ-ec σ-wf (wf-` α<Δ₁) = σ-wf α<Δ₁

wf-subᵉ-ec⋆ : ∀ {Δ₁ Δ₂ σ ê}
  → SubstWF Δ₁ Δ₂ σ
  → Δ₁ ⊢ᵉ⋆ ê
    -----------------------------
  → Δ₂ ⊢ᵉ⋆ subᵉ-ec⋆ σ ê
wf-subᵉ-ec⋆ σ-wf wf-⋆ = wf-⋆
wf-subᵉ-ec⋆ σ-wf (wf-ec ⊢e) = wf-ec (wf-subᵉ-ec σ-wf ⊢e)

wf-subᵉ-mtype : ∀ {Δ₁ Δ₂ σ A}
  → SubstWF Δ₁ Δ₂ σ
  → Δ₁ ⊢ᵐᵗ A
    -------------------------
  → Δ₂ ⊢ᵐᵗ subᵉ σ A
wf-subᵉ-mtype σ-wf wf-⋆ = wf-⋆
wf-subᵉ-mtype σ-wf wf-base = wf-base
wf-subᵉ-mtype σ-wf (wf-fun ⊢A ⊢B) =
  wf-fun (wf-subᵉ-mtype σ-wf ⊢A) (wf-subᵉ-mtype σ-wf ⊢B)
wf-subᵉ-mtype σ-wf (wf-ref ⊢A) =
  wf-ref (wf-subᵉ-mtype σ-wf ⊢A)
wf-subᵉ-mtype σ-wf (wf-code ⊢ê) =
  wf-code (wf-subᵉ-ec⋆ σ-wf ⊢ê)
wf-subᵉ-mtype {Δ₁ = Δ₁} {Δ₂ = Δ₂} σ-wf (wf-forall ⊢A) =
  wf-forall (wf-subᵉ-mtype (ext-subst-wf {Δ₁ = Δ₁} {Δ₂ = Δ₂} σ-wf) ⊢A)
wf-subᵉ-mtype σ-wf (wf-sub ⊢e₁ ⊢e₂ ⊢A) =
  wf-sub (wf-subᵉ-ec σ-wf ⊢e₁)
         (wf-subᵉ-ec σ-wf ⊢e₂)
         (wf-subᵉ-mtype σ-wf ⊢A)

single-subst-wf : ∀ {Δ e}
  → Δ ⊢ᵉ e
    --------------------------------
  → SubstWF (Δ ,α) Δ (e •ᵉₛ idsᵉ)
single-subst-wf ⊢e {zero} _ = ⊢e
single-subst-wf ⊢e {suc α} (s≤s α<Δ) = wf-` α<Δ

wf-single-subᵉ-mtype : ∀ {Δ e A}
  → Δ ⊢ᵉ e
  → Δ ,α ⊢ᵐᵗ A
    --------------------
  → Δ ⊢ᵐᵗ A [ e ]ᵉ
wf-single-subᵉ-mtype ⊢e ⊢A = wf-subᵉ-mtype (single-subst-wf ⊢e) ⊢A

lookup-mtype-wf : ∀ {Δ Γ x A}
  → Δ ⊢ Γ MCtx
  → Γ ∋ x ⦂ A
    ----------
  → Δ ⊢ᵐᵗ A
lookup-mtype-wf (⊢A ∷ᴬ ⊢Γ) here = ⊢A
lookup-mtype-wf (⊢B ∷ᴬ ⊢Γ) (there Γ∋A) =
  lookup-mtype-wf ⊢Γ Γ∋A


-- +-----------------------------------------------------+ --
-- | Well-typed meta terms imply well-formed meta types. | --
-- +-----------------------------------------------------+ --

wt-impl-wf-mtype : ∀ {Δ Γ M A}
  → Δ ⊢ Γ Ctx
  → Δ ; Γ ⊢ᵐ M ⦂ A
    ---------------
  → Δ ⊢ᵐᵗ A
wt-impl-wf-mtype ⊢Γ (⊢constᵐ r) = wf-base
wt-impl-wf-mtype
  (wf-ctx ⊢Θ ⊢Γᵒ ⊢Γᵐ ⊢Σ)
  (⊢varᵐ Γᵐ∋A) =
  lookup-mtype-wf ⊢Γᵐ Γᵐ∋A
wt-impl-wf-mtype
  (wf-ctx ⊢Θ ⊢Γᵒ ⊢Γᵐ ⊢Σ)
  (⊢addr Σ∋A) =
  wf-ref (lookup-mtype-wf ⊢Σ Σ∋A)
wt-impl-wf-mtype
  (wf-ctx ⊢Θ ⊢Γᵒ ⊢Γᵐ ⊢Σ)
  (⊢lamᵐ ⊢A ⊢M) =
  wf-fun ⊢A
         (wt-impl-wf-mtype
           (wf-ctx ⊢Θ ⊢Γᵒ (⊢A ∷ᴬ ⊢Γᵐ) ⊢Σ)
           ⊢M)
wt-impl-wf-mtype ⊢Γ (⊢appᵐ ⊢L ⊢M)
  with wt-impl-wf-mtype ⊢Γ ⊢L
... | wf-fun ⊢A ⊢B = ⊢B
wt-impl-wf-mtype ⊢Γ (⊢eclam ⊢M) =
  wf-forall
    (wt-impl-wf-mtype (wf-⇑ᵉ-ctx ⊢Γ) ⊢M)
wt-impl-wf-mtype ⊢Γ (⊢ecapp ⊢M ⊢e)
  with wt-impl-wf-mtype ⊢Γ ⊢M
... | wf-forall ⊢A = wf-single-subᵉ-mtype ⊢e ⊢A
wt-impl-wf-mtype {Δ = Δ}
  (wf-ctx {Θ = Θ} ⊢Θ ⊢Γᵒ ⊢Γᵐ ⊢Σ)
  (⊢subintro ⊢e₁ ⊢e₂ ⊢M) =
  wf-sub ⊢e₁ ⊢e₂
    (wt-impl-wf-mtype
      (wf-ctx (subctx-wf-lex-ext {Δ = Δ} {Θ = Θ} ⊢Θ ⊢e₁ ⊢e₂) ⊢Γᵒ ⊢Γᵐ ⊢Σ)
      ⊢M)
wt-impl-wf-mtype ⊢Γ (⊢subelim ⊢M e₁<:e₂)
  with wt-impl-wf-mtype ⊢Γ ⊢M
... | wf-sub ⊢e₁ ⊢e₂ ⊢A = ⊢A
wt-impl-wf-mtype ⊢Γ (⊢subelim⋆ ⊢M ℓ) = wf-⋆
wt-impl-wf-mtype ⊢Γ (⊢quote ⊢M ⊢e O=T) =
  wf-code (wf-ec ⊢e)
wt-impl-wf-mtype ⊢Γ (⊢ref ⊢M) =
  wf-ref (wt-impl-wf-mtype ⊢Γ ⊢M)
wt-impl-wf-mtype ⊢Γ (⊢assign ⊢M ⊢N) = wf-base
wt-impl-wf-mtype ⊢Γ (⊢deref ⊢M)
  with wt-impl-wf-mtype ⊢Γ ⊢M
... | wf-ref ⊢A = ⊢A
wt-impl-wf-mtype ⊢Γ (⊢cast ⊢M ⊢c) =
  wf-codᵐ̅ ⊢c
wt-impl-wf-mtype ⊢Γ (⊢blame ⊢A ℓ) = ⊢A
