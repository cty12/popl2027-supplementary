module Theories.ReifyPreserves where

open import Data.Bool using (T; true; false)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (just; nothing; _>>=_)
open import Data.Nat using (zero; suc; _≡ᵇ_)
open import Data.Nat.Properties using (≡ᵇ⇒≡)
open import Data.Product using (_×_; proj₁) renaming (_,_ to ⟨_,_⟩)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; cong; subst)
  renaming (sym to ≡-sym)
open import Relation.Nullary using (yes; no)
open import Relation.Nullary.Negation using (contradiction)

open import Theories.Utils using (index; _∋_⦂_; here; there; ⟨_,_,_,_⟩)
open import Theories.CCAlphaRefStarSyntaxAndTypeSystem
open import Theories.Values using (CodeValue; is-const; is-var; is-lamᵒ-val; is-app)
open import Theories.Reify using (ReifyEnv; reify; reifyAt)
open import Theories.STLC as STLC


private

  lookup-unique : ∀ {A : Set} {Γ : List A} {x T T′}
    → Γ ∋ x ⦂ T
    → Γ ∋ x ⦂ T′
      ----------
    → T ≡ T′
  lookup-unique here here = refl
  lookup-unique (there lookup) (there lookup′) =
    lookup-unique lookup lookup′

  lookupOwner->lookup : ∀ {Γᵒ α x T}
    → lookupOwner Γᵒ α ≡ just ⟨ x , T ⟩
      --------------------------------
    → Γᵒ ∋ x ⦂ ⟨ T , α ⟩
  lookupOwner->lookup {Γᵒ = []} ()
  lookupOwner->lookup {Γᵒ = ⟨ S , β ⟩ ∷ Γᵒ} {α = α} owner with β ≟ α | owner
  ... | yes refl | refl = here
  ... | no _ | owner′ with lookupOwner Γᵒ α in eq
  ... | nothing = contradiction owner′ (λ ())
  ... | just ⟨ x , T ⟩ with owner′
  ... | refl = there (lookupOwner->lookup eq)

  -- | The reify environment and STLC context agree with the code context:
  -- if reification maps a global code variable to a lexical index, then the
  -- STLC context contains the type stored at that code-variable entry.
  ReifyEnvWT : List (OType × ECVar) → ReifyEnv → STLC.STLCCtx → Set
  ReifyEnvWT Γᵒ ρ Γˢ =
    ∀ {x n T α}
      → index ρ x ≡ just n
      → Γᵒ ∋ x ⦂ ⟨ T , α ⟩
        --------------------
      → Γˢ ∋ n ⦂ T

  index-tail-not-zero : (ρ : ReifyEnv) → (x : Var)
    → (index ρ x >>= (λ i → just (suc i))) ≢ just zero
  index-tail-not-zero ρ x eq with index ρ x
  ... | nothing = contradiction eq (λ ())
  ... | just n = contradiction eq (λ ())

  env-ext : ∀ {Γᵒ ρ Γˢ x S α}
    → ReifyEnvWT Γᵒ ρ Γˢ
    → Γᵒ ∋ x ⦂ ⟨ S , α ⟩
      ----------------------------------
    → ReifyEnvWT Γᵒ (x ∷ ρ) (S ∷ Γˢ)
  env-ext {ρ = ρ} {x = x} env lookupₓ {x = y} {zero} index-y lookupᵧ with x ≡ᵇ y in x≡ᵇy
  ... | true rewrite ≡ᵇ⇒≡ x y (subst T (≡-sym x≡ᵇy) tt) =
    subst (λ □ → _ ∋ zero ⦂ □) (cong proj₁ (lookup-unique lookupₓ lookupᵧ)) here
  ... | false = contradiction index-y (index-tail-not-zero ρ y)
  env-ext {ρ = ρ} {x = x} env lookupₓ {x = y} {suc n} index-y lookupᵧ with x ≡ᵇ y
  ... | true = contradiction index-y (λ ())
  ... | false with index ρ y in index-tail
  ... | nothing = contradiction index-y (λ ())
  ... | just n′ with index-y
  ... | refl = there (env index-tail lookupᵧ)

  reifyAt-code-value : ∀ {Γᵒ ρ Vᵒ Mˢ}
    → reifyAt Γᵒ ρ Vᵒ ≡ just Mˢ
      ---------------------------
    → CodeValue Vᵒ
  reifyAt-code-value {Vᵒ = $ r} refl =
    is-const
  reifyAt-code-value {Γᵒ = Γᵒ} {ρ = ρ} {Vᵒ = ` x} reify≡ with index ρ x
  ... | nothing = contradiction reify≡ (λ ())
  ... | just n = is-var
  reifyAt-code-value {Vᵒ = ƛ T ˙ M} ()
  reifyAt-code-value {Vᵒ = ƛ̅ ε ˙ M} ()
  reifyAt-code-value {Γᵒ = Γᵒ} {ρ = ρ} {Vᵒ = ƛ̅ ` α ˙ M} reify≡
    with lookupOwner Γᵒ α
  ... | nothing = contradiction reify≡ (λ ())
  ... | just ⟨ x , T ⟩ with reifyAt Γᵒ (x ∷ ρ) M in reify-body
  ... | nothing = contradiction reify≡ (λ ())
  ... | just Mˢ = is-lamᵒ-val (reifyAt-code-value reify-body)
  reifyAt-code-value {Γᵒ = Γᵒ} {ρ = ρ} {Vᵒ = L · M} reify≡
    with reifyAt Γᵒ ρ L in reify-L
  ... | nothing = contradiction reify≡ (λ ())
  ... | just Lˢ with reifyAt Γᵒ ρ M in reify-M
  ... | nothing = contradiction reify≡ (λ ())
  ... | just Mˢ = is-app (reifyAt-code-value reify-L) (reifyAt-code-value reify-M)
  reifyAt-code-value {Vᵒ = ~ M} ()
  reifyAt-code-value {Vᵒ = blameᵒ ℓ} ()

  reifyAt-preserves-types : ∀ {Δ Θ Γᵒ Σ ρ Γˢ Vᵒ Mˢ T e}
    → Δ ⊢ Γᵒ OCtx
    → Γᵒ .cutoff ≡ zero
    → ReifyEnvWT (Γᵒ .entries) ρ Γˢ
    → CodeValue Vᵒ
    → Δ ; ⟨ Θ , Γᵒ , [] , Σ ⟩ ; e ⊢ᵒ Vᵒ ⦂ T
    → reifyAt (Γᵒ .entries) ρ Vᵒ ≡ just Mˢ
      --------------------------------------------
    → Γˢ STLC.⊢ Mˢ ⦂ T
  reifyAt-preserves-types ⊢Γᵒ cutoff-zero env is-const (⊢constᵒ r) refl =
    STLC.⊢const r
  reifyAt-preserves-types {ρ = ρ} {Vᵒ = ` x} ⊢Γᵒ cutoff-zero env is-var (⊢varᵒ lookup α<:e) reify≡
    with index ρ x in index-x
  ... | nothing = contradiction reify≡ (λ ())
  ... | just n with reify≡
  ... | refl = STLC.⊢var (env index-x lookup)
  reifyAt-preserves-types {Δ = Δ} {Γᵒ = Γᵒ} {ρ = ρ} {Γˢ = Γˢ} ⊢Γᵒ cutoff-zero env (is-lamᵒ-val vᵒ)
      (⊢lamᵒ-val {T₁ = T₁} {T₂ = T₂} {M = M} {α = α} α∈Δ owner edge e′<:e ⊢M) reify≡
    with global-member-owner {Δ = Δ} {Γᵒ = Γᵒ} {T = T₁} {α = α} ⊢Γᵒ cutoff-zero owner
  ... | ⟨ x , owner-lookup ⟩
    rewrite owner-lookup
    with reifyAt (Γᵒ .entries) (x ∷ ρ) M in reify-body
  ... | nothing = contradiction reify≡ (λ ())
  ... | just Mˢ with reify≡
  ... | refl =
    STLC.⊢lam
      (reifyAt-preserves-types {Γᵒ = Γᵒ} {ρ = x ∷ ρ} {Γˢ = T₁ ∷ Γˢ} {Vᵒ = M} {Mˢ = Mˢ} {T = T₂} {e = ` α}
        ⊢Γᵒ cutoff-zero
        (env-ext {Γᵒ = Γᵒ .entries} {ρ = ρ} {Γˢ = Γˢ} {x = x} {S = T₁} {α = α}
          env (lookupOwner->lookup {Γᵒ = Γᵒ .entries} {α = α} {x = x} {T = T₁} owner-lookup))
        vᵒ ⊢M reify-body)
  reifyAt-preserves-types {Γᵒ = Γᵒ} {ρ = ρ} ⊢Γᵒ cutoff-zero env (is-app {L = L} {M = M} vL vM) (⊢appᵒ ⊢L ⊢M) reify≡
    with reifyAt (Γᵒ .entries) ρ L in reify-L
  ... | nothing = contradiction reify≡ (λ ())
  ... | just Lˢ with reifyAt (Γᵒ .entries) ρ M in reify-M
  ... | nothing = contradiction reify≡ (λ ())
  ... | just Mˢ with reify≡
  ... | refl =
    STLC.⊢app (reifyAt-preserves-types ⊢Γᵒ cutoff-zero env vL ⊢L reify-L)
              (reifyAt-preserves-types ⊢Γᵒ cutoff-zero env vM ⊢M reify-M)


-- | Reification preserves types for generated code terms.
reify-preserves-types : ∀ {Δ Θ Γᵒ Σ Mᵒ Mˢ T}
  → Δ ⊢ Γᵒ OCtx
  → Γᵒ .cutoff ≡ zero
  → Δ ; ⟨ Θ , Γᵒ , [] , Σ ⟩ ; ε ⊢ᵒ Mᵒ ⦂ T
  → reify (Γᵒ .entries) Mᵒ ≡ just Mˢ
    ------------------------------------------
  → [] STLC.⊢ Mˢ ⦂ T
reify-preserves-types ⊢Γᵒ cutoff-zero ⊢Mᵒ reify≡ =
  reifyAt-preserves-types ⊢Γᵒ cutoff-zero (λ ()) (reifyAt-code-value reify≡) ⊢Mᵒ reify≡
