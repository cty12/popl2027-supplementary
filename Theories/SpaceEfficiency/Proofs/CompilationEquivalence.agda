module Theories.SpaceEfficiency.Proofs.CompilationEquivalence where

open import Data.Product using (Σ-syntax) renaming (_,_ to ⟨_,_⟩)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Theories.SurfaceSyntaxAndTypeSystem
open import Theories.SpaceEfficiency.CCAlphaRefStarSyntaxAndTypeSystem
open import Theories.SpaceEfficiency.Elaboration
open import Theories.SpaceEfficiency.Compilation


mutual

  compileᵒ⇒-elab : ∀ {Δ Θ Γᵐ Γᵒ e M T}
    → (d : Δ ; Θ ; Γᵐ ; Γᵒ ; e ⊢ M ⭆ T)
      -------------------------------------------------------------
    → Δ ; Θ ; Γᵐ ; Γᵒ ; e ⊢ M ↝ compileᵒ⇒ d ⭆ T
  compileᵒ⇒-elab code-constˢ = code-const
  compileᵒ⇒-elab (code-varˢ lookup sub) = code-var lookup sub
  compileᵒ⇒-elab (code-absˢ d) = code-abs (compileᵒ⇒-elab d)
  compileᵒ⇒-elab (code-appˢ dL dM) =
    code-app (compileᵒ⇒-elab dL) (compileᵒ⇐-elab dM)

  compileᵒ⇐-elab : ∀ {Δ Θ Γᵐ Γᵒ e M T}
    → (d : Δ ; Θ ; Γᵐ ; Γᵒ ; e ⊢ M ⭅ T)
      -------------------------------------------------------------
    → Δ ; Θ ; Γᵐ ; Γᵒ ; e ⊢ M ↝ compileᵒ⇐ d ⭅ T
  compileᵒ⇐-elab (spliceˢ d A≲T) =
    splice (compile-elab d) A≲T
  compileᵒ⇐-elab (checkˢ d) =
    check (compileᵒ⇒-elab d)

  compile-elab : ∀ {Δ Θ Γᵐ Γᵒ M A}
    → (d : Δ ; Θ ; Γᵐ ; Γᵒ ⊢ M ⦂ A)
      ------------------------------------------------
    → Δ ; Θ ; Γᵐ ; Γᵒ ⊢ M ↝ compile d ⦂ A
  compile-elab meta-constˢ = meta-const
  compile-elab (meta-varˢ lookup) = meta-var lookup
  compile-elab (meta-absˢ ⊢A dM) =
    meta-abs ⊢A (compile-elab dM)
  compile-elab (meta-appˢ dL dM B≲A₁) =
    meta-app (compile-elab dL) (compile-elab dM) B≲A₁
  compile-elab (meta-app⋆ˢ dL dM) =
    meta-app⋆ (compile-elab dL) (compile-elab dM)
  compile-elab (meta-ecabsˢ dM) =
    meta-ecabs (compile-elab dM)
  compile-elab (meta-ecappˢ ⊢e dM) =
    meta-ecapp ⊢e (compile-elab dM)
  compile-elab (meta-ecapp⋆ˢ ⊢e dM) =
    meta-ecapp⋆ ⊢e (compile-elab dM)
  compile-elab (meta-subintroˢ ⊢e₁ ⊢e₂ dM) =
    meta-subintro ⊢e₁ ⊢e₂ (compile-elab dM)
  compile-elab (meta-subelimˢ sub dM) =
    meta-subelim sub (compile-elab dM)
  compile-elab (meta-subelim⋆ˢ dM) =
    meta-subelim⋆ (compile-elab dM)
  compile-elab (meta-quoteˢ ⊢e dM) =
    meta-quote ⊢e (compileᵒ⇒-elab dM)
  compile-elab (meta-refˢ dM) =
    meta-ref (compile-elab dM)
  compile-elab (meta-assignˢ dL dM B≲A) =
    meta-assign (compile-elab dL) (compile-elab dM) B≲A
  compile-elab (meta-assign⋆ˢ dL dM) =
    meta-assign⋆ (compile-elab dL) (compile-elab dM)
  compile-elab (meta-derefˢ dM) =
    meta-deref (compile-elab dM)
  compile-elab (meta-deref⋆ˢ dM) =
    meta-deref⋆ (compile-elab dM)


mutual

  elabᵒ⇒-compile : ∀ {Δ Θ Γᵐ Γᵒ e M M′ T}
    → Δ ; Θ ; Γᵐ ; Γᵒ ; e ⊢ M ↝ M′ ⭆ T
      -------------------------------------------------------------------------
    → Σ[ d ∈ Δ ; Θ ; Γᵐ ; Γᵒ ; e ⊢ M ⭆ T ] compileᵒ⇒ d ≡ M′
  elabᵒ⇒-compile code-const =
    ⟨ code-constˢ , refl ⟩
  elabᵒ⇒-compile (code-var lookup sub) =
    ⟨ code-varˢ lookup sub , refl ⟩
  elabᵒ⇒-compile (code-abs N↝N′)
    with elabᵒ⇒-compile N↝N′
  ... | ⟨ dN , refl ⟩ =
    ⟨ code-absˢ dN , refl ⟩
  elabᵒ⇒-compile (code-app L↝L′ M↝M′)
    with elabᵒ⇒-compile L↝L′ | elabᵒ⇐-compile M↝M′
  ... | ⟨ dL , refl ⟩ | ⟨ dM , refl ⟩ =
    ⟨ code-appˢ dL dM , refl ⟩

  elabᵒ⇐-compile : ∀ {Δ Θ Γᵐ Γᵒ e M M′ T}
    → Δ ; Θ ; Γᵐ ; Γᵒ ; e ⊢ M ↝ M′ ⭅ T
      -------------------------------------------------------------------------
    → Σ[ d ∈ Δ ; Θ ; Γᵐ ; Γᵒ ; e ⊢ M ⭅ T ] compileᵒ⇐ d ≡ M′
  elabᵒ⇐-compile (splice M↝M′ A≲T)
    with elab-compile M↝M′
  ... | ⟨ dM , refl ⟩ =
    ⟨ spliceˢ dM A≲T , refl ⟩
  elabᵒ⇐-compile (check M↝M′)
    with elabᵒ⇒-compile M↝M′
  ... | ⟨ dM , refl ⟩ =
    ⟨ checkˢ dM , refl ⟩

  elab-compile : ∀ {Δ Θ Γᵐ Γᵒ M M′ A}
    → Δ ; Θ ; Γᵐ ; Γᵒ ⊢ M ↝ M′ ⦂ A
      ----------------------------------------------------------------
    → Σ[ d ∈ Δ ; Θ ; Γᵐ ; Γᵒ ⊢ M ⦂ A ] compile d ≡ M′
  elab-compile meta-const =
    ⟨ meta-constˢ , refl ⟩
  elab-compile (meta-var lookup) =
    ⟨ meta-varˢ lookup , refl ⟩
  elab-compile (meta-abs ⊢A M↝M′)
    with elab-compile M↝M′
  ... | ⟨ dM , refl ⟩ =
    ⟨ meta-absˢ ⊢A dM , refl ⟩
  elab-compile (meta-app L↝L′ M↝M′ B≲A₁)
    with elab-compile L↝L′ | elab-compile M↝M′
  ... | ⟨ dL , refl ⟩ | ⟨ dM , refl ⟩ =
    ⟨ meta-appˢ dL dM B≲A₁ , refl ⟩
  elab-compile (meta-app⋆ L↝L′ M↝M′)
    with elab-compile L↝L′ | elab-compile M↝M′
  ... | ⟨ dL , refl ⟩ | ⟨ dM , refl ⟩ =
    ⟨ meta-app⋆ˢ dL dM , refl ⟩
  elab-compile (meta-ecabs M↝M′)
    with elab-compile M↝M′
  ... | ⟨ dM , refl ⟩ =
    ⟨ meta-ecabsˢ dM , refl ⟩
  elab-compile (meta-ecapp ⊢e M↝M′)
    with elab-compile M↝M′
  ... | ⟨ dM , refl ⟩ =
    ⟨ meta-ecappˢ ⊢e dM , refl ⟩
  elab-compile (meta-ecapp⋆ ⊢e M↝M′)
    with elab-compile M↝M′
  ... | ⟨ dM , refl ⟩ =
    ⟨ meta-ecapp⋆ˢ ⊢e dM , refl ⟩
  elab-compile (meta-subintro ⊢e₁ ⊢e₂ M↝M′)
    with elab-compile M↝M′
  ... | ⟨ dM , refl ⟩ =
    ⟨ meta-subintroˢ ⊢e₁ ⊢e₂ dM , refl ⟩
  elab-compile (meta-subelim sub M↝M′)
    with elab-compile M↝M′
  ... | ⟨ dM , refl ⟩ =
    ⟨ meta-subelimˢ sub dM , refl ⟩
  elab-compile (meta-subelim⋆ M↝M′)
    with elab-compile M↝M′
  ... | ⟨ dM , refl ⟩ =
    ⟨ meta-subelim⋆ˢ dM , refl ⟩
  elab-compile (meta-quote ⊢e M↝M′)
    with elabᵒ⇒-compile M↝M′
  ... | ⟨ dM , refl ⟩ =
    ⟨ meta-quoteˢ ⊢e dM , refl ⟩
  elab-compile (meta-ref M↝M′)
    with elab-compile M↝M′
  ... | ⟨ dM , refl ⟩ =
    ⟨ meta-refˢ dM , refl ⟩
  elab-compile (meta-assign L↝L′ M↝M′ B≲A)
    with elab-compile L↝L′ | elab-compile M↝M′
  ... | ⟨ dL , refl ⟩ | ⟨ dM , refl ⟩ =
    ⟨ meta-assignˢ dL dM B≲A , refl ⟩
  elab-compile (meta-assign⋆ L↝L′ M↝M′)
    with elab-compile L↝L′ | elab-compile M↝M′
  ... | ⟨ dL , refl ⟩ | ⟨ dM , refl ⟩ =
    ⟨ meta-assign⋆ˢ dL dM , refl ⟩
  elab-compile (meta-deref M↝M′)
    with elab-compile M↝M′
  ... | ⟨ dM , refl ⟩ =
    ⟨ meta-derefˢ dM , refl ⟩
  elab-compile (meta-deref⋆ M↝M′)
    with elab-compile M↝M′
  ... | ⟨ dM , refl ⟩ =
    ⟨ meta-deref⋆ˢ dM , refl ⟩
