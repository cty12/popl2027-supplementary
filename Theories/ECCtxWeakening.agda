module LambdaAlphaRefStar.Theories.ECCtxWeakening where

open import Data.List using (List; []; _∷_)
open import Data.List.Relation.Unary.All using (All) renaming ([] to []ᴬ; _∷_ to _∷ᴬ_)
open import Data.Nat.Properties using (≤-trans; <-≤-trans)
open import Data.Product using (_×_) renaming (_,_ to ⟨_,_⟩)

open import Utils using (⟨_,_,_⟩; ⟨_,_,_,_⟩)
open import LambdaAlphaRefStar.Theories.CCAlphaRefStarSyntaxAndTypeSystem
import LambdaAlphaRefStar.Theories.CoercionSequences.EC.Definition as EC
import LambdaAlphaRefStar.Theories.CoercionSequences.Meta.Definition as MC


------------------------------------------------------------------------
-- EC-context weakening

infix 4 _⊆ᵉ_

record _⊆ᵉ_ (Δ₁ Δ₂ : ECCtx) : Set where
  constructor ecctx⊆
  field
    size≤ : Δ₁ .size ≤ Δ₂ .size
    cutoff≤ : Δ₂ .cutoff ≤ Δ₁ .cutoff

open _⊆ᵉ_ public

⊆ᵉ-refl : ∀ {Δ}
    --------
  → Δ ⊆ᵉ Δ
⊆ᵉ-refl = ecctx⊆ ≤-refl ≤-refl

⊆ᵉ-cons : ∀ {Δ₁ Δ₂}
  → Δ₁ ⊆ᵉ Δ₂
    ---------------------
  → Δ₁ ,α ⊆ᵉ Δ₂ ,α
⊆ᵉ-cons Δ₁⊆Δ₂ = ecctx⊆ (s≤s (Δ₁⊆Δ₂ .size≤)) (s≤s (Δ₁⊆Δ₂ .cutoff≤))

⊆ᵉ-snoc : ∀ {Δ}
    ---------------
  → Δ ⊆ᵉ Δ ,ᵍα
⊆ᵉ-snoc = ecctx⊆ (m≤n⇒m≤1+n ≤-refl) ≤-refl

ec-weaken : ∀ {Δ₁ Δ₂ e}
  → Δ₁ ⊆ᵉ Δ₂
  → Δ₁ ⊢ᵉ e
    ------------
  → Δ₂ ⊢ᵉ e
ec-weaken Δ₁⊆Δ₂ wf-ε = wf-ε
ec-weaken Δ₁⊆Δ₂ (wf-` α∈Δ₁) = wf-` (<-≤-trans α∈Δ₁ (Δ₁⊆Δ₂ .size≤))

globalEC-weaken : ∀ {Δ₁ Δ₂ α}
  → Δ₁ ⊆ᵉ Δ₂
  → GlobalEC Δ₁ α
    ------------------
  → GlobalEC Δ₂ α
globalEC-weaken Δ₁⊆Δ₂ (globalEC α<Δ₁ cutoff≤α) =
  globalEC (<-≤-trans α<Δ₁ (Δ₁⊆Δ₂ .size≤)) (≤-trans (Δ₁⊆Δ₂ .cutoff≤) cutoff≤α)

ec⋆-weaken : ∀ {Δ₁ Δ₂ ê}
  → Δ₁ ⊆ᵉ Δ₂
  → Δ₁ ⊢ᵉ⋆ ê
    ---------------
  → Δ₂ ⊢ᵉ⋆ ê
ec⋆-weaken Δ₁⊆Δ₂ wf-⋆ = wf-⋆
ec⋆-weaken Δ₁⊆Δ₂ (wf-ec ⊢e) = wf-ec (ec-weaken Δ₁⊆Δ₂ ⊢e)

mtype-weaken : ∀ {Δ₁ Δ₂ A}
  → Δ₁ ⊆ᵉ Δ₂
  → Δ₁ ⊢ᵐᵗ A
    ------------
  → Δ₂ ⊢ᵐᵗ A
mtype-weaken Δ₁⊆Δ₂ wf-⋆ = wf-⋆
mtype-weaken Δ₁⊆Δ₂ wf-base = wf-base
mtype-weaken Δ₁⊆Δ₂ (wf-fun ⊢A ⊢B) =
  wf-fun (mtype-weaken Δ₁⊆Δ₂ ⊢A) (mtype-weaken Δ₁⊆Δ₂ ⊢B)
mtype-weaken Δ₁⊆Δ₂ (wf-ref ⊢A) =
  wf-ref (mtype-weaken Δ₁⊆Δ₂ ⊢A)
mtype-weaken Δ₁⊆Δ₂ (wf-code wf-⋆) =
  wf-code wf-⋆
mtype-weaken Δ₁⊆Δ₂ (wf-code (wf-ec ⊢e)) =
  wf-code (wf-ec (ec-weaken Δ₁⊆Δ₂ ⊢e))
mtype-weaken {Δ₁ = Δ₁} {Δ₂ = Δ₂} Δ₁⊆Δ₂ (wf-forall ⊢A) =
  wf-forall (mtype-weaken (⊆ᵉ-cons {Δ₁ = Δ₁} {Δ₂ = Δ₂} Δ₁⊆Δ₂) ⊢A)
mtype-weaken Δ₁⊆Δ₂ (wf-sub ⊢e₁ ⊢e₂ ⊢A) =
  wf-sub (ec-weaken Δ₁⊆Δ₂ ⊢e₁)
         (ec-weaken Δ₁⊆Δ₂ ⊢e₂)
         (mtype-weaken Δ₁⊆Δ₂ ⊢A)

subctx-weaken-edges : ∀ {Δ₁ Δ₂} {edges : List (EC × EC)}
  → Δ₁ ⊆ᵉ Δ₂
  → All (λ { ⟨ e₁ , e₂ ⟩ → Δ₁ ⊢ᵉ e₁ × Δ₁ ⊢ᵉ e₂ }) edges
    ------------------------------------------------------------------
  → All (λ { ⟨ e₁ , e₂ ⟩ → Δ₂ ⊢ᵉ e₁ × Δ₂ ⊢ᵉ e₂ }) edges
subctx-weaken-edges Δ₁⊆Δ₂ []ᴬ = []ᴬ
subctx-weaken-edges Δ₁⊆Δ₂ (⟨ ⊢e₁ , ⊢e₂ ⟩ ∷ᴬ ⊢Θ) =
  ⟨ ec-weaken Δ₁⊆Δ₂ ⊢e₁ , ec-weaken Δ₁⊆Δ₂ ⊢e₂ ⟩ ∷ᴬ subctx-weaken-edges Δ₁⊆Δ₂ ⊢Θ

subctx-weaken : ∀ {Δ₁ Δ₂ Θ}
  → Δ₁ ⊆ᵉ Δ₂
  → Δ₁ ⊢ Θ SubCtx
    ------------------
  → Δ₂ ⊢ Θ SubCtx
subctx-weaken Δ₁⊆Δ₂ ⟨ ⊢edges , ⟨ ⊢global , unique ⟩ ⟩ =
  ⟨ subctx-weaken-edges Δ₁⊆Δ₂ ⊢edges ,
    ⟨ (λ edge →
        let ⟨ α , eq , globalα ⟩ = ⊢global edge in
        ⟨ α , eq , globalEC-weaken Δ₁⊆Δ₂ globalα ⟩)
    , unique
    ⟩ ⟩

octx-weaken : ∀ {Δ₁ Δ₂ Γᵒ}
  → Δ₁ ⊆ᵉ Δ₂
  → Δ₁ ⊢ Γᵒ OCtx
    ------------------
  → Δ₂ ⊢ Γᵒ OCtx
octx-weaken {Γᵒ = Γᵒ} Δ₁⊆Δ₂ ⟨ scoped , unique ⟩ =
  ⟨ scoped-weaken Δ₁⊆Δ₂ scoped , unique ⟩
  where
  scoped-weaken : ∀ {Δ₁ Δ₂ entries}
    → Δ₁ ⊆ᵉ Δ₂
    → All (λ { ⟨ _ , α ⟩ → α < Δ₁ .size }) entries
      ------------------------------------------------
    → All (λ { ⟨ _ , α ⟩ → α < Δ₂ .size }) entries
  scoped-weaken Δ₁⊆Δ₂ []ᴬ = []ᴬ
  scoped-weaken Δ₁⊆Δ₂ (α∈Δ₁ ∷ᴬ ⊢Γᵒ) =
    <-≤-trans α∈Δ₁ (Δ₁⊆Δ₂ .size≤) ∷ᴬ
      scoped-weaken Δ₁⊆Δ₂ ⊢Γᵒ

mctx-weaken : ∀ {Δ₁ Δ₂ Γᵐ}
  → Δ₁ ⊆ᵉ Δ₂
  → Δ₁ ⊢ Γᵐ MCtx
    ------------------
  → Δ₂ ⊢ Γᵐ MCtx
mctx-weaken Δ₁⊆Δ₂ []ᴬ = []ᴬ
mctx-weaken Δ₁⊆Δ₂ (⊢A ∷ᴬ ⊢Γᵐ) =
  mtype-weaken Δ₁⊆Δ₂ ⊢A ∷ᴬ mctx-weaken Δ₁⊆Δ₂ ⊢Γᵐ

ec-coercion-ecctx-weaken : ∀ {Δ₁ Δ₂ Θ c ê₁ ê₂}
  → Δ₁ ⊆ᵉ Δ₂
  → Δ₁ EC.; Θ ⊢ᵉ c ⦂ ê₁ ⇒ ê₂
    ---------------------------------
  → Δ₂ EC.; Θ ⊢ᵉ c ⦂ ê₁ ⇒ ê₂
ec-coercion-ecctx-weaken Δ₁⊆Δ₂ (EC.⊢! e ⊢e) =
  EC.⊢! e (ec-weaken Δ₁⊆Δ₂ ⊢e)
ec-coercion-ecctx-weaken Δ₁⊆Δ₂ (EC.⊢? e ⊢e ℓ) =
  EC.⊢? e (ec-weaken Δ₁⊆Δ₂ ⊢e) ℓ
ec-coercion-ecctx-weaken Δ₁⊆Δ₂ (EC.⊢↑ ⊢ê₁ ⊢ê₂ ê₁<:ê₂) =
  EC.⊢↑ (ec⋆-weaken Δ₁⊆Δ₂ ⊢ê₁) (ec⋆-weaken Δ₁⊆Δ₂ ⊢ê₂) ê₁<:ê₂
ec-coercion-ecctx-weaken Δ₁⊆Δ₂ (EC.⊢⊥ ⊢ê₁ ⊢ê₂ ℓ) =
  EC.⊢⊥ (ec⋆-weaken Δ₁⊆Δ₂ ⊢ê₁) (ec⋆-weaken Δ₁⊆Δ₂ ⊢ê₂) ℓ

ec-coercionSeq-ecctx-weaken : ∀ {Δ₁ Δ₂ Θ c̅ ê₁ ê₂}
  → Δ₁ ⊆ᵉ Δ₂
  → Δ₁ EC.; Θ ⊢ᵉ̅ c̅ ⦂ ê₁ ⇒ ê₂
    ----------------------------------
  → Δ₂ EC.; Θ ⊢ᵉ̅ c̅ ⦂ ê₁ ⇒ ê₂
ec-coercionSeq-ecctx-weaken Δ₁⊆Δ₂ (EC.⊢[] ⊢ê) =
  EC.⊢[] (ec⋆-weaken Δ₁⊆Δ₂ ⊢ê)
ec-coercionSeq-ecctx-weaken Δ₁⊆Δ₂ (EC.⊢; ⊢c ⊢c̅) =
  EC.⊢; (ec-coercion-ecctx-weaken Δ₁⊆Δ₂ ⊢c)
        (ec-coercionSeq-ecctx-weaken Δ₁⊆Δ₂ ⊢c̅)

meta-coercion-single-ecctx-weaken : ∀ {Δ₁ Δ₂ Θ c A B}
  → Δ₁ ⊆ᵉ Δ₂
  → Δ₁ MC.; Θ ⊢ᵐ c ⦂ A ⇒ B
    ----------------------------
  → Δ₂ MC.; Θ ⊢ᵐ c ⦂ A ⇒ B
meta-coercion-ecctx-weaken : ∀ {Δ₁ Δ₂ Θ c A B}
  → Δ₁ ⊆ᵉ Δ₂
  → Δ₁ MC.; Θ ⊢ᵐ̅ c ⦂ A ⇒ B
    -----------------------------
  → Δ₂ MC.; Θ ⊢ᵐ̅ c ⦂ A ⇒ B

meta-coercion-single-ecctx-weaken Δ₁⊆Δ₂ (MC.⊢! ⊢G g) =
  MC.⊢! (mtype-weaken Δ₁⊆Δ₂ ⊢G) g
meta-coercion-single-ecctx-weaken Δ₁⊆Δ₂ (MC.⊢? ⊢G ℓ g) =
  MC.⊢? (mtype-weaken Δ₁⊆Δ₂ ⊢G) ℓ g
meta-coercion-single-ecctx-weaken Δ₁⊆Δ₂ (MC.⊢fun ⊢c ⊢d) =
  MC.⊢fun (meta-coercion-ecctx-weaken Δ₁⊆Δ₂ ⊢c)
          (meta-coercion-ecctx-weaken Δ₁⊆Δ₂ ⊢d)
meta-coercion-single-ecctx-weaken Δ₁⊆Δ₂ (MC.⊢code ⊢cᵒ ⊢cᵉ) =
  MC.⊢code ⊢cᵒ (ec-coercionSeq-ecctx-weaken Δ₁⊆Δ₂ ⊢cᵉ)
meta-coercion-single-ecctx-weaken Δ₁⊆Δ₂ (MC.⊢ref ⊢c ⊢d) =
  MC.⊢ref (meta-coercion-ecctx-weaken Δ₁⊆Δ₂ ⊢c)
          (meta-coercion-ecctx-weaken Δ₁⊆Δ₂ ⊢d)
meta-coercion-single-ecctx-weaken {Δ₁ = Δ₁} {Δ₂ = Δ₂} Δ₁⊆Δ₂ (MC.⊢forall ⊢c) =
  MC.⊢forall (meta-coercion-ecctx-weaken (⊆ᵉ-cons {Δ₁ = Δ₁} {Δ₂ = Δ₂} Δ₁⊆Δ₂) ⊢c)
meta-coercion-single-ecctx-weaken Δ₁⊆Δ₂ (MC.⊢sub ⊢e₁ ⊢e₂ ⊢c) =
  MC.⊢sub (ec-weaken Δ₁⊆Δ₂ ⊢e₁)
           (ec-weaken Δ₁⊆Δ₂ ⊢e₂)
           (meta-coercion-ecctx-weaken Δ₁⊆Δ₂ ⊢c)
meta-coercion-single-ecctx-weaken Δ₁⊆Δ₂ (MC.⊢⊥ ⊢A ⊢B ℓ) =
  MC.⊢⊥ (mtype-weaken Δ₁⊆Δ₂ ⊢A) (mtype-weaken Δ₁⊆Δ₂ ⊢B) ℓ

meta-coercion-ecctx-weaken Δ₁⊆Δ₂ (MC.⊢[] ⊢A) =
  MC.⊢[] (mtype-weaken Δ₁⊆Δ₂ ⊢A)
meta-coercion-ecctx-weaken Δ₁⊆Δ₂ (MC.⊢; ⊢c ⊢c̅) =
  MC.⊢; (meta-coercion-single-ecctx-weaken Δ₁⊆Δ₂ ⊢c)
         (meta-coercion-ecctx-weaken Δ₁⊆Δ₂ ⊢c̅)

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
    ⊢cast (meta-ecctx-weaken Δ₁⊆Δ₂ ⊢M) (meta-coercion-ecctx-weaken Δ₁⊆Δ₂ ⊢c)
  meta-ecctx-weaken Δ₁⊆Δ₂ (⊢blame ⊢A ℓ) =
    ⊢blame (mtype-weaken Δ₁⊆Δ₂ ⊢A) ℓ
