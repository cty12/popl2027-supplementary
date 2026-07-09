module Theories.SubCtxWeakening where

open import Data.List using (List; []; _∷_; map)
open import Data.Nat using (suc; s≤s)
open import Data.Product using (_×_; ∃-syntax) renaming (_,_ to ⟨_,_⟩)
open import Relation.Binary.PropositionalEquality using (refl; subst)

open import Theories.Utils using
  (_∋_; _∋_⦂_; _⊆_; Z; S_; here; there; ∋-∷ʳ; ∋-∷ʳ-last; ∋-snoc-last; lookup-snoc;
  member-map; member-map-inv; member-map-drop; member-map-drop-inv;
  drop-snoc; drop-snoc-last; ⟨_,_,_,_⟩)
open import Theories.CCAlphaRefStarSyntaxAndTypeSystem
import Theories.CoercionSequences.EC.Definition as EC
import Theories.CoercionSequences.Meta.Definition as MC

private

  renᵉ-subctx-entry : RenameEC → EC × EC → EC × EC
  renᵉ-subctx-entry ρ ⟨ e₁ , e₂ ⟩ = ⟨ renᵉ-ec ρ e₁ , renᵉ-ec ρ e₂ ⟩

  ∋-renᵉ-subctx : ∀ {ρ Θ e₁ e₂}
    → Θ ∋ˢ ⟨ e₁ , e₂ ⟩
      ----------------------------------------------------------
    → renᵉ-subctx ρ Θ ∋ˢ ⟨ renᵉ-ec ρ e₁ , renᵉ-ec ρ e₂ ⟩
  ∋-renᵉ-subctx {ρ = ρ} edge = member-map {f = renᵉ-subctx-entry ρ} edge

  renᵉ-<: : ∀ ρ {Θ e₁ e₂}
    → Θ ⊢ᵉ e₁ <: e₂
      ---------------------------------------------------
    → renᵉ-subctx ρ Θ ⊢ᵉ renᵉ-ec ρ e₁ <: renᵉ-ec ρ e₂
  renᵉ-<: ρ <:-ε = <:-ε
  renᵉ-<: ρ <:-refl = <:-refl
  renᵉ-<: ρ {Θ = Θ} (<:-ax edge) = <:-ax (∋-renᵉ-subctx {ρ = ρ} {Θ = Θ} edge)
  renᵉ-<: ρ (<:-trans e₁<:e e<:e₂) =
    <:-trans (renᵉ-<: ρ e₁<:e) (renᵉ-<: ρ e<:e₂)

  subtype-ren : ∀ ρ {Θ₁ Θ₂ e₁ e₂}
    → Θ₁ ⊆ˢ Θ₂
    → renᵉ-subctx ρ Θ₁ ⊢ᵉ e₁ <: e₂
      --------------------------------
    → renᵉ-subctx ρ Θ₂ ⊢ᵉ e₁ <: e₂
  subtype-ren ρ Θ₁⊆Θ₂ <:-ε = <:-ε
  subtype-ren ρ Θ₁⊆Θ₂ <:-refl = <:-refl
  subtype-ren ρ Θ₁⊆Θ₂ (<:-ax edge)
    with member-map-inv {f = renᵉ-subctx-entry ρ} edge
  ... | ⟨ ⟨ e₁ , e₂ ⟩ , ⟨ edge′ , refl ⟩ ⟩ =
    renᵉ-<: ρ (Θ₁⊆Θ₂ .subtype⊆ (<:-ax edge′))
  subtype-ren ρ Θ₁⊆Θ₂ (<:-trans e₁<:e e<:e₂) =
    <:-trans (subtype-ren ρ Θ₁⊆Θ₂ e₁<:e)
             (subtype-ren ρ Θ₁⊆Θ₂ e<:e₂)

  global-ren : ∀ ρ {Θ₁ Θ₂ e₁ e₂}
    → Θ₁ ⊆ˢ Θ₂
    → GlobalEdges (renᵉ-subctx ρ Θ₁) ∋ ⟨ e₁ , e₂ ⟩
      ------------------------------------------------
    → GlobalEdges (renᵉ-subctx ρ Θ₂) ∋ ⟨ e₁ , e₂ ⟩
  global-ren ρ {Θ₁ = Θ₁} {Θ₂ = Θ₂} Θ₁⊆Θ₂ edge
    with member-map-drop-inv (renᵉ-subctx-entry ρ) (Θ₁ .cutoff) (Θ₁ .edges) edge
  ... | ⟨ ⟨ e₁ , e₂ ⟩ , ⟨ edge′ , refl ⟩ ⟩ =
    member-map-drop (renᵉ-subctx-entry ρ) (Θ₂ .cutoff) (Θ₂ .edges)
      (Θ₁⊆Θ₂ .globalEdge⊆ edge′)

  global-lex-weaken : ∀ {Θ e₁ e₂ e₃ e₄}
    → GlobalEdges Θ ∋ ⟨ e₁ , e₂ ⟩
      ------------------------------------------
    → GlobalEdges (Θ , e₃ <: e₄) ∋ ⟨ e₁ , e₂ ⟩
  global-lex-weaken edge = edge

  ec-<:-weakenᵍ : ∀ {Θ e₁ e₂ e₃ e₄}
    → Θ ⊢ᵉ e₁ <: e₂
      -----------------------------------
    → Θ ,ᵍ e₃ <: e₄ ⊢ᵉ e₁ <: e₂
  ec-<:-weakenᵍ <:-ε = <:-ε
  ec-<:-weakenᵍ <:-refl = <:-refl
  ec-<:-weakenᵍ (<:-ax edge) = <:-ax (∋-∷ʳ edge)
  ec-<:-weakenᵍ (<:-trans e₁<:e e<:e₂) =
    <:-trans (ec-<:-weakenᵍ e₁<:e) (ec-<:-weakenᵍ e<:e₂)

  global-global-weaken : ∀ {Θ e₁ e₂ e₃ e₄}
    → GlobalEdges Θ ∋ ⟨ e₁ , e₂ ⟩
      -------------------------------------------
    → GlobalEdges (Θ ,ᵍ e₃ <: e₄) ∋ ⟨ e₁ , e₂ ⟩
  global-global-weaken {Θ = Θ} edge =
    drop-snoc (Θ .cutoff) (Θ .edges) edge

  global-lex-drop : ∀ {Θ e₁ e₂ e₃ e₄}
    → GlobalEdges (Θ , e₃ <: e₄) ∋ ⟨ e₁ , e₂ ⟩
      ------------------------------------------
    → GlobalEdges Θ ∋ ⟨ e₁ , e₂ ⟩
  global-lex-drop edge = edge

  subtype-ext : ∀ {Θ₁ Θ₂ e₁ e₂}
    → Θ₁ ⊆ˢ Θ₂
      ----------------------------------
    → (Θ₁ , e₁ <: e₂) ⊆ˢ (Θ₂ , e₁ <: e₂)
  subtype-ext {Θ₁ = Θ₁} {Θ₂ = Θ₂} {e₁ = e₁} {e₂ = e₂} Θ₁⊆Θ₂ =
    subctx⊆ subtype-pres globalEdge-pres
    where
    subtype-pres : ∀ {e₃ e₄}
      → Θ₁ , e₁ <: e₂ ⊢ᵉ e₃ <: e₄
      → Θ₂ , e₁ <: e₂ ⊢ᵉ e₃ <: e₄
    subtype-pres <:-ε = <:-ε
    subtype-pres <:-refl = <:-refl
    subtype-pres (<:-ax Z) = <:-ax Z
    subtype-pres (<:-ax (S edge)) = ec-<:-weaken (Θ₁⊆Θ₂ .subtype⊆ (<:-ax edge))
    subtype-pres (<:-trans e₃<:e e<:e₄) =
      <:-trans (subtype-pres e₃<:e) (subtype-pres e<:e₄)

    globalEdge-pres : GlobalEdges (Θ₁ , e₁ <: e₂) ⊆ GlobalEdges (Θ₂ , e₁ <: e₂)
    globalEdge-pres = Θ₁⊆Θ₂ .globalEdge⊆

  subctx-ren : ∀ ρ {Θ₁ Θ₂}
    → Θ₁ ⊆ˢ Θ₂
      -------------------------------------
    → renᵉ-subctx ρ Θ₁ ⊆ˢ renᵉ-subctx ρ Θ₂
  subctx-ren ρ Θ₁⊆Θ₂ = subctx⊆ (subtype-ren ρ Θ₁⊆Θ₂) (global-ren ρ Θ₁⊆Θ₂)

  subctx-⇑ᵉ : ∀ {Θ₁ Θ₂}
    → Θ₁ ⊆ˢ Θ₂
      -------------------------------
    → ⇑ᵉ-subctx Θ₁ ⊆ˢ ⇑ᵉ-subctx Θ₂
  subctx-⇑ᵉ = subctx-ren suc


subctx-refl : ∀ {Θ} → Θ ⊆ˢ Θ
subctx-refl = subctx⊆ (λ x → x) (λ x → x)

subctx-lex-weaken : ∀ {Θ e₁ e₂}
    ----------------------
  → Θ ⊆ˢ Θ , e₁ <: e₂
subctx-lex-weaken {Θ = Θ} {e₁ = e₁} {e₂ = e₂} =
  subctx⊆ ec-<:-weaken
    (global-lex-weaken {Θ = Θ} {e₃ = e₁} {e₄ = e₂})

subctx-global-weaken : ∀ {Θ e₁ e₂}
    -----------------------
  → Θ ⊆ˢ Θ ,ᵍ e₁ <: e₂
subctx-global-weaken {Θ = Θ} =
  subctx⊆ ec-<:-weakenᵍ (global-global-weaken {Θ = Θ})

subctx-lex-to-global : ∀ {Θ e₁ e₂}
    -----------------------------------
  → Θ , e₁ <: e₂ ⊆ˢ Θ ,ᵍ e₁ <: e₂
subctx-lex-to-global {Θ = Θ} {e₁ = e₁} {e₂ = e₂} = subctx⊆ subtype-pres globalEdge-pres
  where
  subtype-pres : ∀ {e₃ e₄}
    → Θ , e₁ <: e₂ ⊢ᵉ e₃ <: e₄
      -----------------------
    → Θ ,ᵍ e₁ <: e₂ ⊢ᵉ e₃ <: e₄
  subtype-pres <:-ε = <:-ε
  subtype-pres <:-refl = <:-refl
  subtype-pres (<:-ax Z) = <:-ax (∋-∷ʳ-last (Θ .edges))
  subtype-pres (<:-ax (S edge)) = ec-<:-weakenᵍ (<:-ax edge)
  subtype-pres (<:-trans e₃<:e e<:e₄) =
    <:-trans (subtype-pres e₃<:e) (subtype-pres e<:e₄)

  globalEdge-pres : GlobalEdges (Θ , e₁ <: e₂) ⊆ GlobalEdges (Θ ,ᵍ e₁ <: e₂)
  globalEdge-pres = global-global-weaken {Θ = Θ}

global-subedge-last : ∀ Θ {e₁ e₂}
    ------------------------------------
  → GlobalEdges (Θ ,ᵍ e₁ <: e₂) ∋ ⟨ e₁ , e₂ ⟩
global-subedge-last Θ =
  drop-snoc-last (Θ .cutoff) (Θ .edges) (Θ .cutoff≤length)


<:⋆-⊆ˢ : ∀ {Θ₁ Θ₂ ê₁ ê₂}
  → Θ₁ ⊆ˢ Θ₂
  → Θ₁ ⊢ᵉ ê₁ <:⋆ ê₂
    ---------------------------
  → Θ₂ ⊢ᵉ ê₁ <:⋆ ê₂
<:⋆-⊆ˢ Θ₁⊆Θ₂ <:-⋆ = <:-⋆
<:⋆-⊆ˢ Θ₁⊆Θ₂ (<:-ec e₁<:e₂) = <:-ec (Θ₁⊆Θ₂ .subtype⊆ e₁<:e₂)

ec-coercion-⊆ˢ : ∀ {Δ Θ₁ Θ₂ c ê₁ ê₂}
  → Θ₁ ⊆ˢ Θ₂
  → Δ EC.; Θ₁ ⊢ᵉ c ⦂ ê₁ ⇒ ê₂
    ---------------------------------
  → Δ EC.; Θ₂ ⊢ᵉ c ⦂ ê₁ ⇒ ê₂
ec-coercion-⊆ˢ Θ₁⊆Θ₂ (EC.⊢! e ⊢e) =
  EC.⊢! e ⊢e
ec-coercion-⊆ˢ Θ₁⊆Θ₂ (EC.⊢? e ⊢e ℓ) =
  EC.⊢? e ⊢e ℓ
ec-coercion-⊆ˢ Θ₁⊆Θ₂ (EC.⊢↑ ⊢ê₁ ⊢ê₂ ê₁<:ê₂) =
  EC.⊢↑ ⊢ê₁ ⊢ê₂ (<:⋆-⊆ˢ Θ₁⊆Θ₂ ê₁<:ê₂)
ec-coercion-⊆ˢ Θ₁⊆Θ₂ (EC.⊢⊥ ⊢ê₁ ⊢ê₂ ℓ) =
  EC.⊢⊥ ⊢ê₁ ⊢ê₂ ℓ

ec-coercionSeq-⊆ˢ : ∀ {Δ Θ₁ Θ₂ c̅ ê₁ ê₂}
  → Θ₁ ⊆ˢ Θ₂
  → Δ EC.; Θ₁ ⊢ᵉ̅ c̅ ⦂ ê₁ ⇒ ê₂
    ----------------------------------
  → Δ EC.; Θ₂ ⊢ᵉ̅ c̅ ⦂ ê₁ ⇒ ê₂
ec-coercionSeq-⊆ˢ Θ₁⊆Θ₂ (EC.⊢[] ⊢ê) =
  EC.⊢[] ⊢ê
ec-coercionSeq-⊆ˢ Θ₁⊆Θ₂ (EC.⊢; ⊢c ⊢c̅) =
  EC.⊢; (ec-coercion-⊆ˢ Θ₁⊆Θ₂ ⊢c)
        (ec-coercionSeq-⊆ˢ Θ₁⊆Θ₂ ⊢c̅)

meta-coercion-single-⊆ˢ : ∀ {Δ Θ₁ Θ₂ c A B}
  → Θ₁ ⊆ˢ Θ₂
  → Δ MC.; Θ₁ ⊢ᵐ c ⦂ A ⇒ B
    ---------------------------
  → Δ MC.; Θ₂ ⊢ᵐ c ⦂ A ⇒ B
meta-coercion-⊆ˢ : ∀ {Δ Θ₁ Θ₂ c A B}
  → Θ₁ ⊆ˢ Θ₂
  → Δ MC.; Θ₁ ⊢ᵐ̅ c ⦂ A ⇒ B
    ----------------------------
  → Δ MC.; Θ₂ ⊢ᵐ̅ c ⦂ A ⇒ B

meta-coercion-single-⊆ˢ Θ₁⊆Θ₂ (MC.⊢! ⊢G g) =
  MC.⊢! ⊢G g
meta-coercion-single-⊆ˢ Θ₁⊆Θ₂ (MC.⊢? ⊢G ℓ g) =
  MC.⊢? ⊢G ℓ g
meta-coercion-single-⊆ˢ Θ₁⊆Θ₂ (MC.⊢fun ⊢c ⊢d) =
  MC.⊢fun (meta-coercion-⊆ˢ Θ₁⊆Θ₂ ⊢c)
          (meta-coercion-⊆ˢ Θ₁⊆Θ₂ ⊢d)
meta-coercion-single-⊆ˢ Θ₁⊆Θ₂ (MC.⊢code ⊢cᵒ ⊢cᵉ) =
  MC.⊢code ⊢cᵒ (ec-coercionSeq-⊆ˢ Θ₁⊆Θ₂ ⊢cᵉ)
meta-coercion-single-⊆ˢ Θ₁⊆Θ₂ (MC.⊢ref ⊢c ⊢d) =
  MC.⊢ref (meta-coercion-⊆ˢ Θ₁⊆Θ₂ ⊢c)
          (meta-coercion-⊆ˢ Θ₁⊆Θ₂ ⊢d)
meta-coercion-single-⊆ˢ Θ₁⊆Θ₂ (MC.⊢forall ⊢c) =
  MC.⊢forall (meta-coercion-⊆ˢ (subctx-⇑ᵉ Θ₁⊆Θ₂) ⊢c)
meta-coercion-single-⊆ˢ Θ₁⊆Θ₂ (MC.⊢sub ⊢e₁ ⊢e₂ ⊢c) =
  MC.⊢sub ⊢e₁ ⊢e₂ (meta-coercion-⊆ˢ (subtype-ext Θ₁⊆Θ₂) ⊢c)
meta-coercion-single-⊆ˢ Θ₁⊆Θ₂ (MC.⊢⊥ ⊢A ⊢B ℓ) =
  MC.⊢⊥ ⊢A ⊢B ℓ

meta-coercion-⊆ˢ Θ₁⊆Θ₂ (MC.⊢[] ⊢A) =
  MC.⊢[] ⊢A
meta-coercion-⊆ˢ Θ₁⊆Θ₂ (MC.⊢; ⊢c ⊢c̅) =
  MC.⊢; (meta-coercion-single-⊆ˢ Θ₁⊆Θ₂ ⊢c)
         (meta-coercion-⊆ˢ Θ₁⊆Θ₂ ⊢c̅)

mutual

  code-⊆ˢ : ∀ {Δ Θ₁ Θ₂ Γᵒ Γᵐ Σ e M T}
    → Θ₁ ⊆ˢ Θ₂
    → Δ ; ⟨ Θ₁ , Γᵒ , Γᵐ , Σ ⟩ ; e ⊢ᵒ M ⦂ T
      ------------------------------------------------
    → Δ ; ⟨ Θ₂ , Γᵒ , Γᵐ , Σ ⟩ ; e ⊢ᵒ M ⦂ T

  meta-⊆ˢ : ∀ {Δ Θ₁ Θ₂ Γᵒ Γᵐ Σ M A}
    → Θ₁ ⊆ˢ Θ₂
    → Δ ; ⟨ Θ₁ , Γᵒ , Γᵐ , Σ ⟩ ⊢ᵐ M ⦂ A
      -------------------------------------------
    → Δ ; ⟨ Θ₂ , Γᵒ , Γᵐ , Σ ⟩ ⊢ᵐ M ⦂ A

  code-⊆ˢ Θ₁⊆Θ₂ (⊢constᵒ r) =
    ⊢constᵒ r
  code-⊆ˢ Θ₁⊆Θ₂ (⊢varᵒ lookup α<:e) =
    ⊢varᵒ lookup (Θ₁⊆Θ₂ .subtype⊆ α<:e)
  code-⊆ˢ Θ₁⊆Θ₂ (⊢lamᵒ ⊢M) =
    ⊢lamᵒ (code-⊆ˢ (subtype-ext (subctx-⇑ᵉ Θ₁⊆Θ₂)) ⊢M)
  code-⊆ˢ Θ₁⊆Θ₂ (⊢lamᵒ-val α<Δ owner edge e′<:e ⊢M) =
    ⊢lamᵒ-val α<Δ owner (Θ₁⊆Θ₂ .globalEdge⊆ edge) (Θ₁⊆Θ₂ .subtype⊆ e′<:e)
      (code-⊆ˢ Θ₁⊆Θ₂ ⊢M)
  code-⊆ˢ Θ₁⊆Θ₂ (⊢appᵒ ⊢L ⊢M) =
    ⊢appᵒ (code-⊆ˢ Θ₁⊆Θ₂ ⊢L)
          (code-⊆ˢ Θ₁⊆Θ₂ ⊢M)
  code-⊆ˢ Θ₁⊆Θ₂ (⊢splice ⊢M O↪T) =
    ⊢splice (meta-⊆ˢ Θ₁⊆Θ₂ ⊢M) O↪T
  code-⊆ˢ Θ₁⊆Θ₂ (⊢blameᵒ ℓ) =
    ⊢blameᵒ ℓ

  meta-⊆ˢ Θ₁⊆Θ₂ (⊢constᵐ r) =
    ⊢constᵐ r
  meta-⊆ˢ Θ₁⊆Θ₂ (⊢varᵐ Γᵐ∋A) =
    ⊢varᵐ Γᵐ∋A
  meta-⊆ˢ Θ₁⊆Θ₂ (⊢addr Σ∋A) =
    ⊢addr Σ∋A
  meta-⊆ˢ Θ₁⊆Θ₂ (⊢lamᵐ ⊢A ⊢M) =
    ⊢lamᵐ ⊢A (meta-⊆ˢ Θ₁⊆Θ₂ ⊢M)
  meta-⊆ˢ Θ₁⊆Θ₂ (⊢appᵐ ⊢L ⊢M) =
    ⊢appᵐ (meta-⊆ˢ Θ₁⊆Θ₂ ⊢L)
          (meta-⊆ˢ Θ₁⊆Θ₂ ⊢M)
  meta-⊆ˢ Θ₁⊆Θ₂ (⊢eclam ⊢M) =
    ⊢eclam (meta-⊆ˢ (subctx-⇑ᵉ Θ₁⊆Θ₂) ⊢M)
  meta-⊆ˢ Θ₁⊆Θ₂ (⊢ecapp ⊢M ⊢e) =
    ⊢ecapp (meta-⊆ˢ Θ₁⊆Θ₂ ⊢M) ⊢e
  meta-⊆ˢ Θ₁⊆Θ₂ (⊢subintro ⊢e₁ ⊢e₂ ⊢M) =
    ⊢subintro ⊢e₁ ⊢e₂ (meta-⊆ˢ (subtype-ext Θ₁⊆Θ₂) ⊢M)
  meta-⊆ˢ Θ₁⊆Θ₂ (⊢subelim ⊢M e₁<:e₂) =
    ⊢subelim (meta-⊆ˢ Θ₁⊆Θ₂ ⊢M) (Θ₁⊆Θ₂ .subtype⊆ e₁<:e₂)
  meta-⊆ˢ Θ₁⊆Θ₂ (⊢subelim⋆ ⊢M ℓ) =
    ⊢subelim⋆ (meta-⊆ˢ Θ₁⊆Θ₂ ⊢M) ℓ
  meta-⊆ˢ Θ₁⊆Θ₂ (⊢quote ⊢M ⊢e O↪T) =
    ⊢quote (code-⊆ˢ Θ₁⊆Θ₂ ⊢M) ⊢e O↪T
  meta-⊆ˢ Θ₁⊆Θ₂ (⊢ref ⊢M) =
    ⊢ref (meta-⊆ˢ Θ₁⊆Θ₂ ⊢M)
  meta-⊆ˢ Θ₁⊆Θ₂ (⊢assign ⊢M ⊢N) =
    ⊢assign (meta-⊆ˢ Θ₁⊆Θ₂ ⊢M)
            (meta-⊆ˢ Θ₁⊆Θ₂ ⊢N)
  meta-⊆ˢ Θ₁⊆Θ₂ (⊢deref ⊢M) =
    ⊢deref (meta-⊆ˢ Θ₁⊆Θ₂ ⊢M)
  meta-⊆ˢ Θ₁⊆Θ₂ (⊢cast ⊢M ⊢c) =
    ⊢cast (meta-⊆ˢ Θ₁⊆Θ₂ ⊢M)
          (meta-coercion-⊆ˢ Θ₁⊆Θ₂ ⊢c)
  meta-⊆ˢ Θ₁⊆Θ₂ (⊢blame ⊢A ℓ) =
    ⊢blame ⊢A ℓ


code-subctx-weaken : ∀ {Δ Θ Γᵒ Γᵐ Σ e e₁ e₂ M T}
  → Δ ; ⟨ Θ , Γᵒ , Γᵐ , Σ ⟩ ; e ⊢ᵒ M ⦂ T
    ---------------------------------------------------
  → Δ ; ⟨ Θ , e₁ <: e₂ , Γᵒ , Γᵐ , Σ ⟩ ; e ⊢ᵒ M ⦂ T
code-subctx-weaken = code-⊆ˢ subctx-lex-weaken

meta-subctx-weaken : ∀ {Δ Θ Γᵒ Γᵐ Σ e₁ e₂ M A}
  → Δ ; ⟨ Θ , Γᵒ , Γᵐ , Σ ⟩ ⊢ᵐ M ⦂ A
    ----------------------------------------------
  → Δ ; ⟨ Θ , e₁ <: e₂ , Γᵒ , Γᵐ , Σ ⟩ ⊢ᵐ M ⦂ A
meta-subctx-weaken = meta-⊆ˢ subctx-lex-weaken
