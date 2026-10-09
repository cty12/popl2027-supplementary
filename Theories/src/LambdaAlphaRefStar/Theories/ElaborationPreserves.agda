module LambdaAlphaRefStar.Theories.ElaborationPreserves where

open import Data.List.Relation.Unary.All renaming ([] to []ᴬ; _∷_ to _∷ᴬ_)
open import Data.Product renaming (_,_ to ⟨_,_⟩)

open import Utils using (∅; ⟨_,_,_,_⟩)
open import LambdaAlphaRefStar.Theories.CCAlphaRefStarSyntaxAndTypeSystem
open import LambdaAlphaRefStar.Theories.CoercePreserves
open import LambdaAlphaRefStar.Theories.Elaboration
open import LambdaAlphaRefStar.Theories.WellTypedTermImpliesWellFormedTypes


mutual

  code-synth-preserves : ∀ {Δ Θ Γᵐ Γᵒ e M M′ T}
    → Δ ⊢ Θ SubCtx
    → Δ ⊢ Γᵐ MCtx
    → Δ ⊢ Γᵒ OCtx
    → Δ ⊢ᵉ e
    → Δ ; Θ ; Γᵐ ; Γᵒ ; e ⊢ M ↝ M′ ⭆ T
      ------------------------------------------------
    → Δ ; ⟨ Θ , Γᵒ , Γᵐ , ∅ ⟩ ; e ⊢ᵒ M′ ⦂ T
  code-synth-preserves ⊢Θ ⊢Γᵐ ⊢Γᵒ ⊢e code-const = ⊢constᵒ _
  code-synth-preserves ⊢Θ ⊢Γᵐ ⊢Γᵒ ⊢e (code-var lookup sub) = ⊢varᵒ lookup sub
  code-synth-preserves {Δ = Δ} {Θ = Θ} {Γᵐ = Γᵐ} {Γᵒ = Γᵒ} {e = e}
      ⊢Θ ⊢Γᵐ ⊢Γᵒ ⊢e (code-abs {T₁ = T₁} elab) =
    ⊢lamᵒ
      (code-synth-preserves
        (subctx-wf-lex-ext
          {Δ ,α}
          {⇑ᵉ-subctx Θ}
          (wf-⇑ᵉ-subctx {Δ = Δ} {Θ = Θ} ⊢Θ)
          (wf-renᵉ-ec (suc-ren-wf {Δ = Δ}) ⊢e)
          (wf-` (s≤s z≤n)))
        (wf-⇑ᵉ-mctx {Δ = Δ} {Γᵐ = Γᵐ} ⊢Γᵐ)
        (let ⟨ scoped , unique ⟩ = wf-⇑ᵉ-octx {Δ = Δ} {Γᵒ = Γᵒ} ⊢Γᵒ in
         ⟨ s≤s z≤n ∷ᴬ scoped , unique ⟩)
        (wf-` (s≤s z≤n))
        elab)
  code-synth-preserves ⊢Θ ⊢Γᵐ ⊢Γᵒ ⊢e (code-app elabL elabM) =
    ⊢appᵒ (code-synth-preserves ⊢Θ ⊢Γᵐ ⊢Γᵒ ⊢e elabL)
           (code-check-preserves ⊢Θ ⊢Γᵐ ⊢Γᵒ ⊢e elabM)

  code-check-preserves : ∀ {Δ Θ Γᵐ Γᵒ e M M′ T}
    → Δ ⊢ Θ SubCtx
    → Δ ⊢ Γᵐ MCtx
    → Δ ⊢ Γᵒ OCtx
    → Δ ⊢ᵉ e
    → Δ ; Θ ; Γᵐ ; Γᵒ ; e ⊢ M ↝ M′ ⭅ T
      -------------------------------------------------
    → Δ ; ⟨ Θ , Γᵒ , Γᵐ , ∅ ⟩ ; e ⊢ᵒ M′ ⦂ T
  code-check-preserves {Δ = Δ} {Θ = Θ} {Γᵐ = Γᵐ} {Γᵒ = Γᵒ} {e = e}
      ⊢Θ ⊢Γᵐ ⊢Γᵒ ⊢e (splice elabM A≲T O↪T) =
    ⊢splice
      (⊢cast ⊢M
        (coerceᵐ-preserves
          (wt-impl-wf-mtype (wf-ctx ⊢Θ ⊢Γᵒ ⊢Γᵐ []ᴬ) ⊢M)
          (wf-code (wf-ec ⊢e))
          A≲T))
      O↪T
    where
    ⊢M = meta-elab-preserves ⊢Θ ⊢Γᵐ ⊢Γᵒ elabM
  code-check-preserves ⊢Θ ⊢Γᵐ ⊢Γᵒ ⊢e (check elabM) =
    code-synth-preserves ⊢Θ ⊢Γᵐ ⊢Γᵒ ⊢e elabM

  meta-elab-preserves : ∀ {Δ Θ Γᵐ Γᵒ M M′ A}
    → Δ ⊢ Θ SubCtx
    → Δ ⊢ Γᵐ MCtx
    → Δ ⊢ Γᵒ OCtx
    → Δ ; Θ ; Γᵐ ; Γᵒ ⊢ M ↝ M′ ⦂ A
      ---------------------------------------------
    → Δ ; ⟨ Θ , Γᵒ , Γᵐ , ∅ ⟩ ⊢ᵐ M′ ⦂ A
  meta-elab-preserves ⊢Θ ⊢Γᵐ ⊢Γᵒ meta-const = ⊢constᵐ _
  meta-elab-preserves ⊢Θ ⊢Γᵐ ⊢Γᵒ (meta-var lookup) = ⊢varᵐ lookup
  meta-elab-preserves ⊢Θ ⊢Γᵐ ⊢Γᵒ (meta-abs ⊢A elabM) =
    ⊢lamᵐ ⊢A (meta-elab-preserves ⊢Θ (⊢A ∷ᴬ ⊢Γᵐ) ⊢Γᵒ elabM)
  meta-elab-preserves ⊢Θ ⊢Γᵐ ⊢Γᵒ (meta-app elabL elabM B≲A₁) =
    ⊢appᵐ ⊢L (⊢cast ⊢M (coerceᵐ-preserves ⊢B ⊢A₁ B≲A₁))
    where
    ⊢Γ = wf-ctx ⊢Θ ⊢Γᵒ ⊢Γᵐ []ᴬ
    ⊢L = meta-elab-preserves ⊢Θ ⊢Γᵐ ⊢Γᵒ elabL
    ⊢M = meta-elab-preserves ⊢Θ ⊢Γᵐ ⊢Γᵒ elabM
    ⊢B = wt-impl-wf-mtype ⊢Γ ⊢M
    ⊢A₁ = wf-dom (wt-impl-wf-mtype ⊢Γ ⊢L)
      where
      wf-dom : ∀ {Δ A B} → Δ ⊢ᵐᵗ A ⇒ B → Δ ⊢ᵐᵗ A
      wf-dom (wf-fun ⊢A ⊢B) = ⊢A
  meta-elab-preserves {Θ = Θ} ⊢Θ ⊢Γᵐ ⊢Γᵒ (meta-app⋆ {A = A} {ℓ = ℓ} elabL elabM) =
    ⊢appᵐ
      (⊢cast (meta-elab-preserves ⊢Θ ⊢Γᵐ ⊢Γᵒ elabL)
        (coerceᵐ-preserves wf-⋆ (wf-fun wf-⋆ wf-⋆) (csub-⋆-left {Θ} {⋆ ⇒ ⋆})))
      (⊢cast ⊢M (coerceᵐ-preserves ⊢A wf-⋆ (csub-⋆-right {Θ} {A})))
    where
    ⊢M = meta-elab-preserves ⊢Θ ⊢Γᵐ ⊢Γᵒ elabM
    ⊢A = wt-impl-wf-mtype (wf-ctx ⊢Θ ⊢Γᵒ ⊢Γᵐ []ᴬ) ⊢M
  meta-elab-preserves {Δ = Δ} {Θ = Θ} {Γᵐ = Γᵐ} {Γᵒ = Γᵒ} ⊢Θ ⊢Γᵐ ⊢Γᵒ (meta-ecabs elabM) =
    ⊢eclam
      (meta-elab-preserves
        (wf-⇑ᵉ-subctx {Δ = Δ} {Θ = Θ} ⊢Θ)
        (wf-⇑ᵉ-mctx {Δ = Δ} {Γᵐ = Γᵐ} ⊢Γᵐ)
        (wf-⇑ᵉ-octx {Δ = Δ} {Γᵒ = Γᵒ} ⊢Γᵒ)
        elabM)
  meta-elab-preserves ⊢Θ ⊢Γᵐ ⊢Γᵒ (meta-ecapp ⊢e elabM) =
    ⊢ecapp (meta-elab-preserves ⊢Θ ⊢Γᵐ ⊢Γᵒ elabM) ⊢e
  meta-elab-preserves {Θ = Θ} ⊢Θ ⊢Γᵐ ⊢Γᵒ (meta-ecapp⋆ {ℓ = ℓ} ⊢e elabM) =
    ⊢ecapp
      (⊢cast (meta-elab-preserves ⊢Θ ⊢Γᵐ ⊢Γᵒ elabM)
        (coerceᵐ-preserves wf-⋆ (wf-forall wf-⋆) (csub-⋆-left {Θ} {∀̇ ⋆})))
      ⊢e
  meta-elab-preserves {Δ = Δ} {Θ = Θ} ⊢Θ ⊢Γᵐ ⊢Γᵒ (meta-subintro ⊢e₁ ⊢e₂ elabM) =
    ⊢subintro ⊢e₁ ⊢e₂
      (meta-elab-preserves
        (subctx-wf-lex-ext {Δ = Δ} {Θ = Θ} ⊢Θ ⊢e₁ ⊢e₂)
        ⊢Γᵐ
        ⊢Γᵒ
        elabM)
  meta-elab-preserves ⊢Θ ⊢Γᵐ ⊢Γᵒ (meta-subelim sub elabM) =
    ⊢subelim (meta-elab-preserves ⊢Θ ⊢Γᵐ ⊢Γᵒ elabM) sub
  meta-elab-preserves ⊢Θ ⊢Γᵐ ⊢Γᵒ (meta-subelim⋆ elabM) =
    ⊢subelim⋆ (meta-elab-preserves ⊢Θ ⊢Γᵐ ⊢Γᵒ elabM) _
  meta-elab-preserves ⊢Θ ⊢Γᵐ ⊢Γᵒ (meta-quote ⊢e elabM O↪T) =
    ⊢quote (code-synth-preserves ⊢Θ ⊢Γᵐ ⊢Γᵒ ⊢e elabM) ⊢e O↪T
  meta-elab-preserves ⊢Θ ⊢Γᵐ ⊢Γᵒ (meta-ref elabM) =
    ⊢ref (meta-elab-preserves ⊢Θ ⊢Γᵐ ⊢Γᵒ elabM)
  meta-elab-preserves ⊢Θ ⊢Γᵐ ⊢Γᵒ (meta-assign elabL elabM B≲A) =
    ⊢assign ⊢L (⊢cast ⊢M (coerceᵐ-preserves ⊢B ⊢A B≲A))
    where
    ⊢Γ = wf-ctx ⊢Θ ⊢Γᵒ ⊢Γᵐ []ᴬ
    ⊢L = meta-elab-preserves ⊢Θ ⊢Γᵐ ⊢Γᵒ elabL
    ⊢M = meta-elab-preserves ⊢Θ ⊢Γᵐ ⊢Γᵒ elabM
    ⊢B = wt-impl-wf-mtype ⊢Γ ⊢M
    ⊢A = wf-ref-dom (wt-impl-wf-mtype ⊢Γ ⊢L)
      where
      wf-ref-dom : ∀ {Δ A} → Δ ⊢ᵐᵗ Ref A → Δ ⊢ᵐᵗ A
      wf-ref-dom (wf-ref ⊢A) = ⊢A
  meta-elab-preserves {Θ = Θ} ⊢Θ ⊢Γᵐ ⊢Γᵒ (meta-assign⋆ {A = A} {ℓ = ℓ} elabL elabM) =
    ⊢assign
      (⊢cast (meta-elab-preserves ⊢Θ ⊢Γᵐ ⊢Γᵒ elabL)
        (coerceᵐ-preserves wf-⋆ (wf-ref wf-⋆) (csub-⋆-left {Θ} {Ref ⋆})))
      (⊢cast ⊢M (coerceᵐ-preserves ⊢A wf-⋆ (csub-⋆-right {Θ} {A})))
    where
    ⊢M = meta-elab-preserves ⊢Θ ⊢Γᵐ ⊢Γᵒ elabM
    ⊢A = wt-impl-wf-mtype (wf-ctx ⊢Θ ⊢Γᵒ ⊢Γᵐ []ᴬ) ⊢M
  meta-elab-preserves ⊢Θ ⊢Γᵐ ⊢Γᵒ (meta-deref elabM) =
    ⊢deref (meta-elab-preserves ⊢Θ ⊢Γᵐ ⊢Γᵒ elabM)
  meta-elab-preserves {Θ = Θ} ⊢Θ ⊢Γᵐ ⊢Γᵒ (meta-deref⋆ {ℓ = ℓ} elabM) =
    ⊢deref
      (⊢cast (meta-elab-preserves ⊢Θ ⊢Γᵐ ⊢Γᵒ elabM)
        (coerceᵐ-preserves wf-⋆ (wf-ref wf-⋆) (csub-⋆-left {Θ} {Ref ⋆})))
