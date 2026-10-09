module LambdaAlphaRefStar.Theories.ScopeSafetyValue where

open import Data.Bool using (false; true)
open import Data.List using ([]; _∷_)
open import Data.Maybe using (just; _>>=_)
open import Data.Nat using (zero; suc; _≡ᵇ_)
open import Data.Product using (∃-syntax; _×_) renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Function using (case_of_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)
open import Relation.Nullary using (¬_)
open import Relation.Nullary.Negation using (contradiction)

open import Utils using (_∋_; index; ≡ᵇ-refl; ⟨_,_,_⟩; ⟨_,_,_,_⟩; ⟨_,_,_,_,_⟩)
open import LambdaAlphaRefStar.Theories.CCAlphaRefStarSyntaxAndTypeSystem
open import LambdaAlphaRefStar.Theories.CCAlphaRefStarSemantics
open import LambdaAlphaRefStar.Theories.CCAlphaRefStarPreservation using (preserveᵐ)
open import LambdaAlphaRefStar.Theories.Values using (CodeValue; Value; is-const; is-var; is-lamᵒ-val; is-app)
open import LambdaAlphaRefStar.Theories.Reify using (ReifyEnv; reify; reifyAt)
open import LambdaAlphaRefStar.Theories.ReifyPreserves using (reify-preserves-types)
open import LambdaAlphaRefStar.Theories.STLC as STLC

-- | A code variable is visible at e when its owner EC is below e.
VisibleCodeVar : SubCtx → OCtx → EC → Var → Set
VisibleCodeVar Θ Γᵒ e x = ∃[ T ] ∃[ α ] (Γᵒ ∋ᵒ x ⦂ ⟨ T , α ⟩ × Θ ⊢ᵉ ` α <: e)

EnvHasVar : ReifyEnv → Var → Set
EnvHasVar ρ x = ∃[ n ] index ρ x ≡ just n

-- | The reify environment covers the globally allocated variables visible
-- from the current EC.
ReifyEnvCovers : SubCtx → OCtx → ReifyEnv → EC → Set
ReifyEnvCovers Θ Γᵒ ρ e = ∀ {x} → VisibleCodeVar Θ Γᵒ e x → EnvHasVar ρ x


ancestor-case : ∀ {Δ Θ e α β}
  → Δ ⊢ Θ SubCtx
  → Θ .cutoff ≡ zero
  → GlobalEdges Θ ∋ ⟨ e , ` α ⟩
  → Θ ⊢ᵉ ` β <: ` α
    ---------------------------------
  → (β ≡ α) ⊎ (Θ ⊢ᵉ ` β <: e)
ancestor-case ⊢Θ cutoff-zero edge <:-refl = inj₁ refl
ancestor-case {Θ = Θ} ⟨ _ , _ , unique ⟩ cutoff-zero edge (<:-ax edge′)
  rewrite unique edge (zero-cutoff→all-global {Θ = Θ} cutoff-zero edge′) = inj₂ <:-refl
ancestor-case ⊢Θ cutoff-zero edge (<:-trans {e₂ = ε} β<:ε ε<:α)
  with only-root-<:ε ⊢Θ cutoff-zero β<:ε
... | ()
ancestor-case ⊢Θ cutoff-zero edge (<:-trans {e₂ = ` γ} β<:γ γ<:α)
  with ancestor-case ⊢Θ cutoff-zero edge γ<:α
... | inj₁ refl = ancestor-case ⊢Θ cutoff-zero edge β<:γ
... | inj₂ γ<:e = inj₂ (<:-trans β<:γ γ<:e)

reifyAt-total : ∀ {Δ Θ Γᵒ Σ ρ Vᵒ T e}
  → Δ ⊢ Θ SubCtx
  → Θ .cutoff ≡ zero
  → Δ ⊢ Γᵒ OCtx
  → Γᵒ .cutoff ≡ zero
  → ReifyEnvCovers Θ Γᵒ ρ e
  → CodeValue Vᵒ
  → Δ ; ⟨ Θ , Γᵒ , [] , Σ ⟩ ; e ⊢ᵒ Vᵒ ⦂ T
    -------------------------------------------------------
  → ∃[ Mˢ ] reifyAt (Γᵒ .entries) ρ Vᵒ ≡ just Mˢ
reifyAt-total ⊢Θ′ Θ-cutoff-zero ⊢Γᵒ Γᵒ-cutoff-zero env is-const (⊢constᵒ r) =
  ⟨ STLC.$ r , refl ⟩
reifyAt-total {ρ = ρ} ⊢Θ′ Θ-cutoff-zero ⊢Γᵒ Γᵒ-cutoff-zero env is-var (⊢varᵒ lookup α<:e)
  with env ⟨ _ , _ , lookup , α<:e ⟩
... | ⟨ n , index≡ ⟩ rewrite index≡ =
  ⟨ STLC.` n , refl ⟩
reifyAt-total {Δ = Δ} {Θ = Θ} {Γᵒ = octx zero entries cutoff≤length}
    {Σ = Σ} {ρ = ρ} {e = e₂}
    ⊢Θ′ Θ-cutoff-zero ⟨ scoped , uniqueOwner ⟩ refl env (is-lamᵒ-val vᵒ)
    (⊢lamᵒ-val {T₁ = T₁} {T₂ = T₂} {e₁ = e₁} {M = M} {α = α}
      α∈Δ owner edge e₁<:e₂ ⊢M)
  with global-member-owner {Δ = Δ} {Γᵒ = octx zero entries cutoff≤length} {T = T₁} {α = α}
         ⟨ scoped , uniqueOwner ⟩ refl owner
... | ⟨ x , owner-lookup ⟩ rewrite owner-lookup
  = reify-lam-result
      (reifyAt-total {Δ = Δ} {Θ = Θ} {Γᵒ = octx zero entries cutoff≤length} {Σ = Σ} {ρ = x ∷ ρ}
        {Vᵒ = M} {T = T₂} {e = ` α} ⊢Θ′ Θ-cutoff-zero ⟨ scoped , uniqueOwner ⟩ refl
        env-under-lam
        vᵒ ⊢M)
  where
  reify-lam-result : (∃[ Mˢ ] reifyAt entries (x ∷ ρ) M ≡ just Mˢ)
    → ∃[ Nˢ ]
        ((just ⟨ x , T₁ ⟩ >>= λ { ⟨ x′ , T ⟩ →
            reifyAt entries (x′ ∷ ρ) M >>= λ M′ → just (STLC.ƛ T ˙ M′) })
         ≡ just Nˢ)
  reify-lam-result ⟨ Mˢ , reify≡ ⟩ rewrite reify≡ = ⟨ STLC.ƛ T₁ ˙ Mˢ , refl ⟩

  env-under-lam : ReifyEnvCovers Θ (octx zero entries cutoff≤length) (x ∷ ρ) (` α)
  env-under-lam {x = y} ⟨ S , γ , lookup , γ<:α ⟩ with x ≡ᵇ y in x≡ᵇy
  ... | true =
    ⟨ zero , refl ⟩
  ... | false with ancestor-case ⊢Θ′ Θ-cutoff-zero edge γ<:α
  ... | inj₁ refl with lookupOwner-index {Γᵒ = entries} {x = y} {T = S} {α = α} uniqueOwner lookup
  ... | owner-y rewrite owner-lookup with owner-y
  ... | refl rewrite ≡ᵇ-refl x with x≡ᵇy
  ... | ()
  env-under-lam {x = y} ⟨ T , γ , lookup , γ<:α ⟩
    | false | inj₂ γ<:e₁
    with env ⟨ T , γ , lookup , <:-trans γ<:e₁ e₁<:e₂ ⟩
  ... | ⟨ n , index-y ⟩ rewrite index-y =
    ⟨ suc n , refl ⟩
reifyAt-total {Γᵒ = Γᵒ} {ρ = ρ} ⊢Θ′ Θ-cutoff-zero ⊢Γᵒ Γᵒ-cutoff-zero env (is-app vL vM) (⊢appᵒ ⊢L ⊢M)
  with reifyAt-total {ρ = ρ} ⊢Θ′ Θ-cutoff-zero ⊢Γᵒ Γᵒ-cutoff-zero env vL ⊢L
... | ⟨ Lˢ , reify-L ⟩ rewrite reify-L
  with reifyAt-total {ρ = ρ} ⊢Θ′ Θ-cutoff-zero ⊢Γᵒ Γᵒ-cutoff-zero env vM ⊢M
... | ⟨ Mˢ , reify-M ⟩ rewrite reify-M =
  ⟨ Lˢ STLC.· Mˢ , refl ⟩

-- | Corollary of `reifyAt-total` and `reify-preserves-types`.
scope-safety-val : ∀ {Δ Θ Γᵒ Σ Vᵒ T}
  → Δ ⊢ Θ SubCtx
  → Θ .cutoff ≡ zero
  → Δ ⊢ Γᵒ OCtx
  → Γᵒ .cutoff ≡ zero
  → CodeValue Vᵒ
  → Δ ; ⟨ Θ , Γᵒ , [] , Σ ⟩ ; ε ⊢ᵒ Vᵒ ⦂ T
    ------------------------------------------------------------------
  → ∃[ Mˢ ] reify (Γᵒ .entries) Vᵒ ≡ just Mˢ × ([] STLC.⊢ Mˢ ⦂ T)
scope-safety-val ⊢Θ Θ-cutoff-zero ⊢Γᵒ Γᵒ-cutoff-zero vᵒ ⊢Vᵒ
  with reifyAt-total {ρ = []} {e = ε} ⊢Θ Θ-cutoff-zero ⊢Γᵒ Γᵒ-cutoff-zero
       -- there's no variable visible at ε
       (λ {⟨ _ , _ , _ , α<:ε ⟩ → case only-root-<:ε ⊢Θ Θ-cutoff-zero α<:ε of λ where ()})
       vᵒ ⊢Vᵒ
... | ⟨ Mˢ , reify≡ ⟩ = ⟨ Mˢ , reify≡ , reify-preserves-types ⊢Γᵒ Γᵒ-cutoff-zero ⊢Vᵒ reify≡ ⟩
