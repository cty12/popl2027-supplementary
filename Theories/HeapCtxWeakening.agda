module Theories.HeapCtxWeakening where

open import Data.List using (_∷ʳ_)
open import Data.Nat using (suc)
open import Relation.Binary.PropositionalEquality using (subst; refl)
  renaming (sym to ≡-sym)

open import Theories.Utils using (_≼_; lookup-snoc; ⟨_,_,_⟩; ⟨_,_,_,_⟩)
open import Theories.CCAlphaRefStarSyntaxAndTypeSystem


------------------------------------------------------------------------
-- Heap-context lookup-stability weakening

⇑ᵉ-mctx-≼ : ∀ {Γᵐ₁ Γᵐ₂}
  → Γᵐ₁ ≼ Γᵐ₂
    ---------------------------
  → ⇑ᵉ-mctx Γᵐ₁ ≼ ⇑ᵉ-mctx Γᵐ₂
⇑ᵉ-mctx-≼ {Γᵐ₁ = Γᵐ₁} {Γᵐ₂ = Γᵐ₂} Γᵐ₁≼Γᵐ₂ lookup
  with lookup-⇑ᵉ-mctx-inv {Γᵐ = Γᵐ₁} lookup
... | ⟨ A , refl , lookup′ ⟩ =
  lookup-⇑ᵉ-mctx (Γᵐ₁≼Γᵐ₂ lookup′)

mutual

  code-heapctx-≼ : ∀ {Δ Θ Γᵒ Γᵐ Σ₁ Σ₂ e M T}
    → Σ₁ ≼ Σ₂
    → Δ ; ⟨ Θ , Γᵒ , Γᵐ , Σ₁ ⟩ ; e ⊢ᵒ M ⦂ T
      -----------------------------------------------
    → Δ ; ⟨ Θ , Γᵒ , Γᵐ , Σ₂ ⟩ ; e ⊢ᵒ M ⦂ T
  code-heapctx-≼ Σ₁≼Σ₂ (⊢constᵒ r) =
    ⊢constᵒ r
  code-heapctx-≼ Σ₁≼Σ₂ (⊢varᵒ lookup α<:e) =
    ⊢varᵒ lookup α<:e
  code-heapctx-≼ Σ₁≼Σ₂ (⊢lamᵒ ⊢M) =
    ⊢lamᵒ (code-heapctx-≼ (⇑ᵉ-mctx-≼ Σ₁≼Σ₂) ⊢M)
  code-heapctx-≼ Σ₁≼Σ₂ (⊢lamᵒ-val α<Δ owner edge e′<:e ⊢M) =
    ⊢lamᵒ-val α<Δ owner edge e′<:e (code-heapctx-≼ Σ₁≼Σ₂ ⊢M)
  code-heapctx-≼ Σ₁≼Σ₂ (⊢appᵒ ⊢L ⊢M) =
    ⊢appᵒ (code-heapctx-≼ Σ₁≼Σ₂ ⊢L) (code-heapctx-≼ Σ₁≼Σ₂ ⊢M)
  code-heapctx-≼ Σ₁≼Σ₂ (⊢splice ⊢M O=T) =
    ⊢splice (meta-heapctx-≼ Σ₁≼Σ₂ ⊢M) O=T
  code-heapctx-≼ Σ₁≼Σ₂ (⊢blameᵒ ℓ) =
    ⊢blameᵒ ℓ

  meta-heapctx-≼ : ∀ {Δ Θ Γᵒ Γᵐ Σ₁ Σ₂ M A}
    → Σ₁ ≼ Σ₂
    → Δ ; ⟨ Θ , Γᵒ , Γᵐ , Σ₁ ⟩ ⊢ᵐ M ⦂ A
      ------------------------------------------
    → Δ ; ⟨ Θ , Γᵒ , Γᵐ , Σ₂ ⟩ ⊢ᵐ M ⦂ A
  meta-heapctx-≼ Σ₁≼Σ₂ (⊢constᵐ r) =
    ⊢constᵐ r
  meta-heapctx-≼ Σ₁≼Σ₂ (⊢varᵐ Γᵐ∋A) =
    ⊢varᵐ Γᵐ∋A
  meta-heapctx-≼ Σ₁≼Σ₂ (⊢addr Σ∋A) =
    ⊢addr (Σ₁≼Σ₂ Σ∋A)
  meta-heapctx-≼ Σ₁≼Σ₂ (⊢lamᵐ ⊢A ⊢M) =
    ⊢lamᵐ ⊢A (meta-heapctx-≼ Σ₁≼Σ₂ ⊢M)
  meta-heapctx-≼ Σ₁≼Σ₂ (⊢appᵐ ⊢L ⊢M) =
    ⊢appᵐ (meta-heapctx-≼ Σ₁≼Σ₂ ⊢L) (meta-heapctx-≼ Σ₁≼Σ₂ ⊢M)
  meta-heapctx-≼ Σ₁≼Σ₂ (⊢eclam ⊢M) =
    ⊢eclam (meta-heapctx-≼ (⇑ᵉ-mctx-≼ Σ₁≼Σ₂) ⊢M)
  meta-heapctx-≼ Σ₁≼Σ₂ (⊢ecapp ⊢M ⊢e) =
    ⊢ecapp (meta-heapctx-≼ Σ₁≼Σ₂ ⊢M) ⊢e
  meta-heapctx-≼ Σ₁≼Σ₂ (⊢subintro ⊢e₁ ⊢e₂ ⊢M) =
    ⊢subintro ⊢e₁ ⊢e₂ (meta-heapctx-≼ Σ₁≼Σ₂ ⊢M)
  meta-heapctx-≼ Σ₁≼Σ₂ (⊢subelim ⊢M e₁<:e₂) =
    ⊢subelim (meta-heapctx-≼ Σ₁≼Σ₂ ⊢M) e₁<:e₂
  meta-heapctx-≼ Σ₁≼Σ₂ (⊢subelim⋆ ⊢M ℓ) =
    ⊢subelim⋆ (meta-heapctx-≼ Σ₁≼Σ₂ ⊢M) ℓ
  meta-heapctx-≼ Σ₁≼Σ₂ (⊢quote ⊢M ⊢e O=T) =
    ⊢quote (code-heapctx-≼ Σ₁≼Σ₂ ⊢M) ⊢e O=T
  meta-heapctx-≼ Σ₁≼Σ₂ (⊢ref ⊢M) =
    ⊢ref (meta-heapctx-≼ Σ₁≼Σ₂ ⊢M)
  meta-heapctx-≼ Σ₁≼Σ₂ (⊢assign ⊢M ⊢N) =
    ⊢assign (meta-heapctx-≼ Σ₁≼Σ₂ ⊢M) (meta-heapctx-≼ Σ₁≼Σ₂ ⊢N)
  meta-heapctx-≼ Σ₁≼Σ₂ (⊢deref ⊢M) =
    ⊢deref (meta-heapctx-≼ Σ₁≼Σ₂ ⊢M)
  meta-heapctx-≼ Σ₁≼Σ₂ (⊢cast ⊢M ⊢c) =
    ⊢cast (meta-heapctx-≼ Σ₁≼Σ₂ ⊢M) ⊢c
  meta-heapctx-≼ Σ₁≼Σ₂ (⊢blame ⊢A ℓ) =
    ⊢blame ⊢A ℓ


------------------------------------------------------------------------
-- One-step heap-context weakening

mutual

  code-heapctx-weaken : ∀ {Δ Θ Γᵒ Γᵐ Σ e M T B}
    → Δ ; ⟨ Θ , Γᵒ , Γᵐ , Σ ⟩ ; e ⊢ᵒ M ⦂ T
      ------------------------------------------------
    → Δ ; ⟨ Θ , Γᵒ , Γᵐ , Σ ∷ʳ B ⟩ ; e ⊢ᵒ M ⦂ T
  code-heapctx-weaken (⊢constᵒ r) = ⊢constᵒ r
  code-heapctx-weaken (⊢varᵒ x α<:e) = ⊢varᵒ x α<:e
  code-heapctx-weaken {Δ = Δ} {Θ = Θ} {Γᵒ = Γᵒ} {Γᵐ = Γᵐ} {Σ = Σ} {e = e} {B = B}
                      (⊢lamᵒ {T₁ = T₁} {T₂ = T₂} {M = M} ⊢M) =
    ⊢lamᵒ
      (subst
        (λ Σ′ → Δ ,α ;
          ⟨ ⇑ᵉ-subctx Θ , ⇑ᵉ-ec e <: ` zero , ⇑ᵉ-octx Γᵒ , T₁ ＠ zero , ⇑ᵉ-mctx Γᵐ , Σ′ ⟩
          ; ` zero ⊢ᵒ M ⦂ T₂)
        (≡-sym (⇑ᵉ-heapctx-snoc Σ B))
        (code-heapctx-weaken {B = renᵉ suc B} ⊢M))
  code-heapctx-weaken (⊢lamᵒ-val α<Δ owner edge e′<:e ⊢M) =
    ⊢lamᵒ-val α<Δ owner edge e′<:e (code-heapctx-weaken ⊢M)
  code-heapctx-weaken (⊢appᵒ ⊢L ⊢M) =
    ⊢appᵒ (code-heapctx-weaken ⊢L) (code-heapctx-weaken ⊢M)
  code-heapctx-weaken (⊢splice ⊢M O=T) =
    ⊢splice (meta-heapctx-weaken ⊢M) O=T
  code-heapctx-weaken (⊢blameᵒ ℓ) =
    ⊢blameᵒ ℓ

  meta-heapctx-weaken : ∀ {Δ Θ Γᵒ Γᵐ Σ M A B}
    → Δ ; ⟨ Θ , Γᵒ , Γᵐ , Σ ⟩ ⊢ᵐ M ⦂ A
      ------------------------------------------
    → Δ ; ⟨ Θ , Γᵒ , Γᵐ , Σ ∷ʳ B ⟩ ⊢ᵐ M ⦂ A
  meta-heapctx-weaken (⊢constᵐ r) = ⊢constᵐ r
  meta-heapctx-weaken (⊢varᵐ x) = ⊢varᵐ x
  meta-heapctx-weaken (⊢addr x) = ⊢addr (lookup-snoc x)
  meta-heapctx-weaken (⊢lamᵐ ⊢A ⊢M) = ⊢lamᵐ ⊢A (meta-heapctx-weaken ⊢M)
  meta-heapctx-weaken (⊢appᵐ ⊢L ⊢M) =
    ⊢appᵐ (meta-heapctx-weaken ⊢L) (meta-heapctx-weaken ⊢M)
  meta-heapctx-weaken {Δ = Δ} {Θ = Θ} {Γᵒ = Γᵒ} {Γᵐ = Γᵐ} {Σ = Σ} {B = B}
                      (⊢eclam {A = A} {M = M} ⊢M) =
    ⊢eclam
      (subst
        (λ Σ′ → Δ ,α ; ⟨ ⇑ᵉ-subctx Θ , ⇑ᵉ-octx Γᵒ , ⇑ᵉ-mctx Γᵐ , Σ′ ⟩ ⊢ᵐ M ⦂ A)
        (≡-sym (⇑ᵉ-heapctx-snoc Σ B))
        (meta-heapctx-weaken {B = renᵉ suc B} ⊢M))
  meta-heapctx-weaken (⊢ecapp ⊢M ⊢e) =
    ⊢ecapp (meta-heapctx-weaken ⊢M) ⊢e
  meta-heapctx-weaken (⊢subintro ⊢e₁ ⊢e₂ ⊢M) =
    ⊢subintro ⊢e₁ ⊢e₂ (meta-heapctx-weaken ⊢M)
  meta-heapctx-weaken (⊢subelim ⊢M e₁<:e₂) =
    ⊢subelim (meta-heapctx-weaken ⊢M) e₁<:e₂
  meta-heapctx-weaken (⊢subelim⋆ ⊢M ℓ) =
    ⊢subelim⋆ (meta-heapctx-weaken ⊢M) ℓ
  meta-heapctx-weaken (⊢quote ⊢M ⊢e O=T) =
    ⊢quote (code-heapctx-weaken ⊢M) ⊢e O=T
  meta-heapctx-weaken (⊢ref ⊢M) = ⊢ref (meta-heapctx-weaken ⊢M)
  meta-heapctx-weaken (⊢assign ⊢M ⊢N) =
    ⊢assign (meta-heapctx-weaken ⊢M) (meta-heapctx-weaken ⊢N)
  meta-heapctx-weaken (⊢deref ⊢M) = ⊢deref (meta-heapctx-weaken ⊢M)
  meta-heapctx-weaken (⊢cast ⊢M ⊢c) = ⊢cast (meta-heapctx-weaken ⊢M) ⊢c
  meta-heapctx-weaken (⊢blame ⊢A ℓ) = ⊢blame ⊢A ℓ
