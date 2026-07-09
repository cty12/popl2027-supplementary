module Theories.SpaceEfficiency.Compilation where

open import Theories.SurfaceSyntaxAndTypeSystem
open import Theories.ConsistentSubtyping
open import Theories.SpaceEfficiency.CCAlphaRefStarSyntaxAndTypeSystem
open import Theories.SpaceEfficiency.Elaboration
  using (coerce; coercionᵐ)


mutual

  compileᵒ⇒ : ∀ {Δ Θ Γᵐ Γᵒ e M T}
    → Δ ; Θ ; Γᵐ ; Γᵒ ; e ⊢ M ⭆ T
      --------
    → CodeTerm
  compileᵒ⇒ (code-constˢ {k = k}) = $ k
  compileᵒ⇒ (code-varˢ {x = x} lookup sub) = ` x
  compileᵒ⇒ (code-absˢ {T₁ = T₁} N⊢) = ƛ T₁ ˙ compileᵒ⇒ N⊢
  compileᵒ⇒ (code-appˢ L⊢ M⊢) = compileᵒ⇒ L⊢ · compileᵒ⇐ M⊢

  compileᵒ⇐ : ∀ {Δ Θ Γᵐ Γᵒ e M T}
    → Δ ; Θ ; Γᵐ ; Γᵒ ; e ⊢ M ⭅ T
      --------
    → CodeTerm
  compileᵒ⇐ {Δ = Δ} {Θ = Θ} (spliceˢ {ℓ = ℓ} M⊢ A≲T) =
    ~ (compile M⊢ ⟨ coercionᵐ (coerce {Δ = Δ} {Θ = Θ} A≲T ℓ) ⟩)
  compileᵒ⇐ (checkˢ M⊢) = compileᵒ⇒ M⊢

  compile : ∀ {Δ Θ Γᵐ Γᵒ M A}
    → Δ ; Θ ; Γᵐ ; Γᵒ ⊢ M ⦂ A
      --------
    → MetaTerm
  compile (meta-constˢ {k = k}) = $ k
  compile (meta-varˢ {x = x} lookup) = ` x
  compile (meta-absˢ ⊢A M⊢) = ƛ compile M⊢
  compile {Δ = Δ} {Θ = Θ} (meta-appˢ {ℓ = ℓ} L⊢ M⊢ B≲A₁) =
    compile L⊢ · (compile M⊢ ⟨ coercionᵐ (coerce {Δ = Δ} {Θ = Θ} B≲A₁ ℓ) ⟩)
  compile {Δ = Δ} {Θ = Θ} (meta-app⋆ˢ {A = A} {ℓ = ℓ} L⊢ M⊢) =
    (compile L⊢ ⟨ coercionᵐ (coerce {Δ = Δ} {Θ = Θ} (csub-⋆-left {A = ⋆ ⇒ ⋆}) ℓ) ⟩) ·
    (compile M⊢ ⟨ coercionᵐ (coerce {Δ = Δ} {Θ = Θ} (csub-⋆-right {A = A}) ℓ) ⟩)
  compile (meta-ecabsˢ M⊢) = Λ compile M⊢
  compile (meta-ecappˢ {e = e} ⊢e M⊢) = compile M⊢ ·[ e ]
  compile {Δ = Δ} {Θ = Θ} (meta-ecapp⋆ˢ {e = e} {ℓ = ℓ} ⊢e M⊢) =
    (compile M⊢ ⟨ coercionᵐ (coerce {Δ = Δ} {Θ = Θ} (csub-⋆-left {A = ∀̇ ⋆}) ℓ) ⟩) ·[ e ]
  compile (meta-subintroˢ {e₁ = e₁} {e₂ = e₂} ⊢e₁ ⊢e₂ M⊢) =
    e₁ <: e₂ => compile M⊢
  compile (meta-subelimˢ sub M⊢) = compile M⊢ ●
  compile (meta-subelim⋆ˢ {ℓ = ℓ} M⊢) = compile M⊢ ★ ℓ
  compile (meta-quoteˢ {e = e} ⊢e M⊢) = ‶ compileᵒ⇒ M⊢ ″ e
  compile (meta-refˢ M⊢) = ref (compile M⊢)
  compile {Δ = Δ} {Θ = Θ} (meta-assignˢ {ℓ = ℓ} L⊢ M⊢ B≲A) =
    compile L⊢ := (compile M⊢ ⟨ coercionᵐ (coerce {Δ = Δ} {Θ = Θ} B≲A ℓ) ⟩)
  compile {Δ = Δ} {Θ = Θ} (meta-assign⋆ˢ {A = A} {ℓ = ℓ} L⊢ M⊢) =
    (compile L⊢ ⟨ coercionᵐ (coerce {Δ = Δ} {Θ = Θ} (csub-⋆-left {A = Ref ⋆}) ℓ) ⟩) :=
    (compile M⊢ ⟨ coercionᵐ (coerce {Δ = Δ} {Θ = Θ} (csub-⋆-right {A = A}) ℓ) ⟩)
  compile (meta-derefˢ M⊢) = ! compile M⊢
  compile {Δ = Δ} {Θ = Θ} (meta-deref⋆ˢ {ℓ = ℓ} M⊢) =
    ! (compile M⊢ ⟨ coercionᵐ (coerce {Δ = Δ} {Θ = Θ} (csub-⋆-left {A = Ref ⋆}) ℓ) ⟩)
