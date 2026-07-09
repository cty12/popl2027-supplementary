module Theories.SpaceEfficiency.Proofs.PreserveHeight where

open import Data.Bool using (true; false)
open import Data.List using ([]; _∷_; _∷ʳ_)
open import Data.Nat using (zero; suc; _≤_; _⊔_; z≤n; s≤s)
open import Data.Nat.Properties using
  (≤-refl; ≤-trans; m≤m⊔n; m≤n⊔m; m≤n⇒m≤1+n; ⊔-mono-≤; ⊔-lub)
open import Data.Product using (Σ-syntax; _×_) renaming (_,_ to ⟨_,_⟩)

open Data.Nat.Properties.≤-Reasoning

import Theories.Utils as U
import Theories.Heap as H

open import Theories.SpaceEfficiency.CCAlphaRefStarSyntaxAndTypeSystem
open import Theories.SpaceEfficiency.CCAlphaRefStarSemantics
open import Theories.SpaceEfficiency.Configuration
open import Theories.SpaceEfficiency.CCAlphaRefStarSizeAndHeight
open import Theories.SpaceEfficiency.ECHypercoercions
open import Theories.SpaceEfficiency.ObjectHypercoercions
open import Theories.SpaceEfficiency.MetaHypercoercions
open import Theories.SpaceEfficiency.Proofs.LeastUpperBoundLemmas
open import Theories.SpaceEfficiency.Proofs.HypercoercionCompositionBounded
  using (compose-height-meta)

heap-lookup-height : ∀ {μ a V}
  → U._∋_⦂_ μ a V
    ------------------------------
  → c-height V ≤ heap-c-height μ
heap-lookup-height U.here = m≤m⊔n _ _
heap-lookup-height (U.there lookup) =
  ≤-trans (heap-lookup-height lookup) (m≤n⊔m _ _)

heap-extend-height : ∀ μ V
    --------------------------------------------------------
  → heap-c-height (μ ∷ʳ V) ≤ c-height V ⊔ heap-c-height μ
heap-extend-height [] V = ≤-refl
heap-extend-height (W ∷ μ) V =
  ≤-trans
    (⊔-mono-≤ ≤-refl (heap-extend-height μ V))
    (⊔-swap-middle≤ (c-height W) (c-height V) (heap-c-height μ))

heap-update-height : ∀ {μ μ′ a V}
  → H._⟦_↦_⟧=_ μ a V μ′
    ------------------------------------------------------
  → heap-c-height μ′ ≤ c-height V ⊔ heap-c-height μ
heap-update-height {μ = W ∷ μ} {V = V} H.here =
  ⊔-mono-≤ ≤-refl (m≤n⊔m (c-height W) (heap-c-height μ))
heap-update-height {μ = W ∷ μ} {V = V} (H.there μ↦μ′) =
  ≤-trans
    (⊔-mono-≤ ≤-refl (heap-update-height μ↦μ′))
    (⊔-swap-middle≤ (c-height W) (c-height V) (heap-c-height μ))

heap-update-lookup-height : ∀ {μ μ′ a b V W′}
  → H._⟦_↦_⟧=_ μ b V μ′
  → U._∋_⦂_ μ′ a W′
    ---------------------------------------------------------------------
  → Σ[ W ∈ MetaTerm ] (U._∋_⦂_ μ a W × c-height W′ ≤ c-height V ⊔ c-height W)
heap-update-lookup-height {μ = W ∷ μ} {V = V} H.here U.here =
  ⟨ W , ⟨ U.here , m≤m⊔n (c-height V) (c-height W) ⟩ ⟩
heap-update-lookup-height {μ = W ∷ μ} {V = V} H.here (U.there lookup) =
  ⟨ _ , ⟨ U.there lookup , m≤n⊔m (c-height V) _ ⟩ ⟩
heap-update-lookup-height {μ = W ∷ μ} {V = V} (H.there μ↦μ′) U.here =
  ⟨ W , ⟨ U.here , m≤n⊔m (c-height V) (c-height W) ⟩ ⟩
heap-update-lookup-height {μ = W ∷ μ} {V = V} (H.there μ↦μ′) (U.there lookup)
  with heap-update-lookup-height μ↦μ′ lookup
... | ⟨ W′ , ⟨ old-lookup , height≤ ⟩ ⟩ =
  ⟨ W′ , ⟨ U.there old-lookup , height≤ ⟩ ⟩

plugᵒ-height-lower : ∀ F Mᵒ → c-heightᵒ Mᵒ ≤ c-heightᵒ (plugᵒ F Mᵒ)
plugᵒ-height-lower (□· Mᵒ) Lᵒ = m≤m⊔n _ _
plugᵒ-height-lower ((Vᵒ ·□) _) Mᵒ = m≤n⊔m _ _

plugᵐ-height-lower : ∀ F M → c-height M ≤ c-height (plugᵐ F M)
plugᵐ-height-lower (□· M) L = m≤m⊔n _ _
plugᵐ-height-lower ((V ·□) _) M = m≤n⊔m _ _
plugᵐ-height-lower ref□ M = ≤-refl
plugᵐ-height-lower (□:= M) L = m≤m⊔n _ _
plugᵐ-height-lower ((V :=□) _) M = m≤n⊔m _ _
plugᵐ-height-lower !□ M = ≤-refl
plugᵐ-height-lower (□·[ e ]) M = ≤-refl
plugᵐ-height-lower □● M = ≤-refl
plugᵐ-height-lower (□★ ℓ) M = ≤-refl

mutual

  renᵒ-code-height : ∀ ρ Mᵒ → c-heightᵒ (renᵒ-code ρ Mᵒ) ≤ c-heightᵒ Mᵒ
  renᵒ-code-height ρ ($ k) = ≤-refl
  renᵒ-code-height ρ (` x) = ≤-refl
  renᵒ-code-height ρ (ƛ T ˙ Mᵒ) = renᵒ-code-height (extᵒ ρ) Mᵒ
  renᵒ-code-height ρ (ƛ̅ e ˙ Mᵒ) = renᵒ-code-height ρ Mᵒ
  renᵒ-code-height ρ (Lᵒ · Mᵒ) =
    ⊔-mono≤ (renᵒ-code-height ρ Lᵒ) (renᵒ-code-height ρ Mᵒ)
  renᵒ-code-height ρ (~ M) = renᵒ-meta-height ρ M
  renᵒ-code-height ρ (blameᵒ ℓ) = ≤-refl

  renᵒ-meta-height : ∀ ρ M → c-height (renᵒ-meta ρ M) ≤ c-height M
  renᵒ-meta-height ρ ($ k) = ≤-refl
  renᵒ-meta-height ρ (` x) = ≤-refl
  renᵒ-meta-height ρ (addr a) = ≤-refl
  renᵒ-meta-height ρ (ƛ M) = renᵒ-meta-height ρ M
  renᵒ-meta-height ρ (L · M) =
    ⊔-mono≤ (renᵒ-meta-height ρ L) (renᵒ-meta-height ρ M)
  renᵒ-meta-height ρ (Λ M) = renᵒ-meta-height ρ M
  renᵒ-meta-height ρ (M ·[ e ]) = renᵒ-meta-height ρ M
  renᵒ-meta-height ρ (e₁ <: e₂ => M) = renᵒ-meta-height ρ M
  renᵒ-meta-height ρ (M ●) = renᵒ-meta-height ρ M
  renᵒ-meta-height ρ (M ★ ℓ) = renᵒ-meta-height ρ M
  renᵒ-meta-height ρ (‶ Mᵒ ″ e) = renᵒ-code-height ρ Mᵒ
  renᵒ-meta-height ρ (ref M) = renᵒ-meta-height ρ M
  renᵒ-meta-height ρ (L := M) =
    ⊔-mono≤ (renᵒ-meta-height ρ L) (renᵒ-meta-height ρ M)
  renᵒ-meta-height ρ (! M) = renᵒ-meta-height ρ M
  renᵒ-meta-height ρ (M ⟨ c ⟩) =
    ⊔-mono≤ (renᵒ-meta-height ρ M) ≤-refl
  renᵒ-meta-height ρ (blame ℓ) = ≤-refl

mutual

  renᵉ-middle-height : ∀ ρ m → meta-middle-height (renᵉ-mmiddle ρ m) ≤ meta-middle-height m
  renᵉ-middle-height ρ (c ⇒ d) =
    s≤s (⊔-mono≤ (renᵉ-mhc-height ρ c) (renᵉ-mhc-height ρ d))
  renᵉ-middle-height ρ (‶ cᵒ ″ cᵉ) = ≤-refl
  renᵉ-middle-height ρ (ref c d) =
    s≤s (⊔-mono≤ (renᵉ-mhc-height ρ c) (renᵉ-mhc-height ρ d))
  renᵉ-middle-height ρ (∀̇ c) =
    s≤s (renᵉ-mhc-height (extᵉ ρ) c)
  renᵉ-middle-height ρ (e₁ <: e₂ => c) =
    s≤s (renᵉ-mhc-height ρ c)
  renᵉ-middle-height ρ (err ℓ) = ≤-refl
  renᵉ-middle-height ρ id⋆ = ≤-refl
  renᵉ-middle-height ρ (idι ι) = ≤-refl

  renᵉ-mhc-height : ∀ ρ c → meta-hc-height (renᵉ-mhc ρ c) ≤ meta-hc-height c
  renᵉ-mhc-height ρ (h ⨾ m ⨾ t) = renᵉ-middle-height ρ m

mutual

  renᵉ-code-height : ∀ ρ Mᵒ → c-heightᵒ (renᵉ-code ρ Mᵒ) ≤ c-heightᵒ Mᵒ
  renᵉ-code-height ρ ($ k) = ≤-refl
  renᵉ-code-height ρ (` x) = ≤-refl
  renᵉ-code-height ρ (ƛ T ˙ Mᵒ) = renᵉ-code-height (extᵉ ρ) Mᵒ
  renᵉ-code-height ρ (ƛ̅ e ˙ Mᵒ) = renᵉ-code-height ρ Mᵒ
  renᵉ-code-height ρ (Lᵒ · Mᵒ) =
    ⊔-mono≤ (renᵉ-code-height ρ Lᵒ) (renᵉ-code-height ρ Mᵒ)
  renᵉ-code-height ρ (~ M) = renᵉ-meta-height ρ M
  renᵉ-code-height ρ (blameᵒ ℓ) = ≤-refl

  renᵉ-meta-height : ∀ ρ M → c-height (renᵉ-meta ρ M) ≤ c-height M
  renᵉ-meta-height ρ ($ k) = ≤-refl
  renᵉ-meta-height ρ (` x) = ≤-refl
  renᵉ-meta-height ρ (addr a) = ≤-refl
  renᵉ-meta-height ρ (ƛ M) = renᵉ-meta-height ρ M
  renᵉ-meta-height ρ (L · M) =
    ⊔-mono≤ (renᵉ-meta-height ρ L) (renᵉ-meta-height ρ M)
  renᵉ-meta-height ρ (Λ M) = renᵉ-meta-height (extᵉ ρ) M
  renᵉ-meta-height ρ (M ·[ e ]) = renᵉ-meta-height ρ M
  renᵉ-meta-height ρ (e₁ <: e₂ => M) = renᵉ-meta-height ρ M
  renᵉ-meta-height ρ (M ●) = renᵉ-meta-height ρ M
  renᵉ-meta-height ρ (M ★ ℓ) = renᵉ-meta-height ρ M
  renᵉ-meta-height ρ (‶ Mᵒ ″ e) = renᵉ-code-height ρ Mᵒ
  renᵉ-meta-height ρ (ref M) = renᵉ-meta-height ρ M
  renᵉ-meta-height ρ (L := M) =
    ⊔-mono≤ (renᵉ-meta-height ρ L) (renᵉ-meta-height ρ M)
  renᵉ-meta-height ρ (! M) = renᵉ-meta-height ρ M
  renᵉ-meta-height ρ (M ⟨ c ⟩) =
    ⊔-mono≤ (renᵉ-meta-height ρ M) (renᵉ-mhc-height ρ c)
  renᵉ-meta-height ρ (blame ℓ) = ≤-refl

mutual

  renᵐ-code-height : ∀ ρ Mᵒ → c-heightᵒ (renᵐ-code ρ Mᵒ) ≤ c-heightᵒ Mᵒ
  renᵐ-code-height ρ ($ k) = ≤-refl
  renᵐ-code-height ρ (` x) = ≤-refl
  renᵐ-code-height ρ (ƛ T ˙ Mᵒ) = renᵐ-code-height ρ Mᵒ
  renᵐ-code-height ρ (ƛ̅ e ˙ Mᵒ) = renᵐ-code-height ρ Mᵒ
  renᵐ-code-height ρ (Lᵒ · Mᵒ) =
    ⊔-mono≤ (renᵐ-code-height ρ Lᵒ) (renᵐ-code-height ρ Mᵒ)
  renᵐ-code-height ρ (~ M) = renᵐ-meta-height ρ M
  renᵐ-code-height ρ (blameᵒ ℓ) = ≤-refl

  renᵐ-meta-height : ∀ ρ M → c-height (renᵐ-meta ρ M) ≤ c-height M
  renᵐ-meta-height ρ ($ k) = ≤-refl
  renᵐ-meta-height ρ (` x) = ≤-refl
  renᵐ-meta-height ρ (addr a) = ≤-refl
  renᵐ-meta-height ρ (ƛ M) = renᵐ-meta-height (extᵐ ρ) M
  renᵐ-meta-height ρ (L · M) =
    ⊔-mono≤ (renᵐ-meta-height ρ L) (renᵐ-meta-height ρ M)
  renᵐ-meta-height ρ (Λ M) = renᵐ-meta-height ρ M
  renᵐ-meta-height ρ (M ·[ e ]) = renᵐ-meta-height ρ M
  renᵐ-meta-height ρ (e₁ <: e₂ => M) = renᵐ-meta-height ρ M
  renᵐ-meta-height ρ (M ●) = renᵐ-meta-height ρ M
  renᵐ-meta-height ρ (M ★ ℓ) = renᵐ-meta-height ρ M
  renᵐ-meta-height ρ (‶ Mᵒ ″ e) = renᵐ-code-height ρ Mᵒ
  renᵐ-meta-height ρ (ref M) = renᵐ-meta-height ρ M
  renᵐ-meta-height ρ (L := M) =
    ⊔-mono≤ (renᵐ-meta-height ρ L) (renᵐ-meta-height ρ M)
  renᵐ-meta-height ρ (! M) = renᵐ-meta-height ρ M
  renᵐ-meta-height ρ (M ⟨ c ⟩) =
    ⊔-mono≤ (renᵐ-meta-height ρ M) ≤-refl
  renᵐ-meta-height ρ (blame ℓ) = ≤-refl

mutual

  substᵉ-middle-height : ∀ σ m → meta-middle-height (substᵉ-mmiddle σ m) ≤ meta-middle-height m
  substᵉ-middle-height σ (c ⇒ d) =
    s≤s (⊔-mono≤ (substᵉ-mhc-height σ c) (substᵉ-mhc-height σ d))
  substᵉ-middle-height σ (‶ cᵒ ″ cᵉ) = ≤-refl
  substᵉ-middle-height σ (ref c d) =
    s≤s (⊔-mono≤ (substᵉ-mhc-height σ c) (substᵉ-mhc-height σ d))
  substᵉ-middle-height σ (∀̇ c) =
    s≤s (substᵉ-mhc-height (extsᵉ σ) c)
  substᵉ-middle-height σ (e₁ <: e₂ => c) =
    s≤s (substᵉ-mhc-height σ c)
  substᵉ-middle-height σ (err ℓ) = ≤-refl
  substᵉ-middle-height σ id⋆ = ≤-refl
  substᵉ-middle-height σ (idι ι) = ≤-refl

  substᵉ-mhc-height : ∀ σ c → meta-hc-height (substᵉ-mhc σ c) ≤ meta-hc-height c
  substᵉ-mhc-height σ (h ⨾ m ⨾ t) = substᵉ-middle-height σ m

mutual

  substᵉ-code-height : ∀ σ Mᵒ → c-heightᵒ (substᵉ-code σ Mᵒ) ≤ c-heightᵒ Mᵒ
  substᵉ-code-height σ ($ k) = ≤-refl
  substᵉ-code-height σ (` x) = ≤-refl
  substᵉ-code-height σ (ƛ T ˙ Mᵒ) = substᵉ-code-height (extsᵉ σ) Mᵒ
  substᵉ-code-height σ (ƛ̅ e ˙ Mᵒ) = substᵉ-code-height σ Mᵒ
  substᵉ-code-height σ (Lᵒ · Mᵒ) =
    ⊔-mono≤ (substᵉ-code-height σ Lᵒ) (substᵉ-code-height σ Mᵒ)
  substᵉ-code-height σ (~ M) = substᵉ-meta-height σ M
  substᵉ-code-height σ (blameᵒ ℓ) = ≤-refl

  substᵉ-meta-height : ∀ σ M → c-height (substᵉ-meta σ M) ≤ c-height M
  substᵉ-meta-height σ ($ k) = ≤-refl
  substᵉ-meta-height σ (` x) = ≤-refl
  substᵉ-meta-height σ (addr a) = ≤-refl
  substᵉ-meta-height σ (ƛ M) = substᵉ-meta-height σ M
  substᵉ-meta-height σ (L · M) =
    ⊔-mono≤ (substᵉ-meta-height σ L) (substᵉ-meta-height σ M)
  substᵉ-meta-height σ (Λ M) = substᵉ-meta-height (extsᵉ σ) M
  substᵉ-meta-height σ (M ·[ e ]) = substᵉ-meta-height σ M
  substᵉ-meta-height σ (e₁ <: e₂ => M) = substᵉ-meta-height σ M
  substᵉ-meta-height σ (M ●) = substᵉ-meta-height σ M
  substᵉ-meta-height σ (M ★ ℓ) = substᵉ-meta-height σ M
  substᵉ-meta-height σ (‶ Mᵒ ″ e) = substᵉ-code-height σ Mᵒ
  substᵉ-meta-height σ (ref M) = substᵉ-meta-height σ M
  substᵉ-meta-height σ (L := M) =
    ⊔-mono≤ (substᵉ-meta-height σ L) (substᵉ-meta-height σ M)
  substᵉ-meta-height σ (! M) = substᵉ-meta-height σ M
  substᵉ-meta-height σ (M ⟨ c ⟩) =
    ⊔-mono≤ (substᵉ-meta-height σ M) (substᵉ-mhc-height σ c)
  substᵉ-meta-height σ (blame ℓ) = ≤-refl

subst-ec-code-height : ∀ Mᵒ e → c-heightᵒ (Mᵒ [ e ]ᵉᵒ) ≤ c-heightᵒ Mᵒ
subst-ec-code-height Mᵒ e = substᵉ-code-height (e •ᵉₛ idsᵉ) Mᵒ

subst-ec-meta-height : ∀ M e → c-height (M [ e ]ᵉᵐ) ≤ c-height M
subst-ec-meta-height M e = substᵉ-meta-height (e •ᵉₛ idsᵉ) M

subst-ec-mhc-height : ∀ c e → meta-hc-height (c [ e ]ᶜ) ≤ meta-hc-height c
subst-ec-mhc-height c e = substᵉ-mhc-height (e •ᵉₛ idsᵉ) c

extsᵒ-height-zero : ∀ {σ}
  → (∀ x → c-heightᵒ (σ x) ≤ 0)
  → ∀ x → c-heightᵒ (extsᵒ σ x) ≤ 0
extsᵒ-height-zero {σ = σ} σ≤ zero = ≤-refl
extsᵒ-height-zero {σ = σ} σ≤ (suc x) =
  ≤-trans (renᵒ-code-height suc (σ x)) (σ≤ x)

mutual

  substᵒ-code-height-zero : ∀ σ
    → (∀ x → c-heightᵒ (σ x) ≤ 0)
    → ∀ Mᵒ → c-heightᵒ (substᵒ-code σ Mᵒ) ≤ c-heightᵒ Mᵒ
  substᵒ-code-height-zero σ σ≤ ($ k) = ≤-refl
  substᵒ-code-height-zero σ σ≤ (` x) = σ≤ x
  substᵒ-code-height-zero σ σ≤ (ƛ T ˙ Mᵒ) =
    substᵒ-code-height-zero (extsᵒ σ) (extsᵒ-height-zero σ≤) Mᵒ
  substᵒ-code-height-zero σ σ≤ (ƛ̅ e ˙ Mᵒ) =
    substᵒ-code-height-zero σ σ≤ Mᵒ
  substᵒ-code-height-zero σ σ≤ (Lᵒ · Mᵒ) =
    ⊔-mono≤
      (substᵒ-code-height-zero σ σ≤ Lᵒ)
      (substᵒ-code-height-zero σ σ≤ Mᵒ)
  substᵒ-code-height-zero σ σ≤ (~ M) =
    substᵒ-meta-height-zero σ σ≤ M
  substᵒ-code-height-zero σ σ≤ (blameᵒ ℓ) = ≤-refl

  substᵒ-meta-height-zero : ∀ σ
    → (∀ x → c-heightᵒ (σ x) ≤ 0)
    → ∀ M → c-height (substᵒ-meta σ M) ≤ c-height M
  substᵒ-meta-height-zero σ σ≤ ($ k) = ≤-refl
  substᵒ-meta-height-zero σ σ≤ (` x) = ≤-refl
  substᵒ-meta-height-zero σ σ≤ (addr a) = ≤-refl
  substᵒ-meta-height-zero σ σ≤ (ƛ M) =
    substᵒ-meta-height-zero σ σ≤ M
  substᵒ-meta-height-zero σ σ≤ (L · M) =
    ⊔-mono≤
      (substᵒ-meta-height-zero σ σ≤ L)
      (substᵒ-meta-height-zero σ σ≤ M)
  substᵒ-meta-height-zero σ σ≤ (Λ M) =
    substᵒ-meta-height-zero σ σ≤ M
  substᵒ-meta-height-zero σ σ≤ (M ·[ e ]) =
    substᵒ-meta-height-zero σ σ≤ M
  substᵒ-meta-height-zero σ σ≤ (e₁ <: e₂ => M) =
    substᵒ-meta-height-zero σ σ≤ M
  substᵒ-meta-height-zero σ σ≤ (M ●) =
    substᵒ-meta-height-zero σ σ≤ M
  substᵒ-meta-height-zero σ σ≤ (M ★ ℓ) =
    substᵒ-meta-height-zero σ σ≤ M
  substᵒ-meta-height-zero σ σ≤ (‶ Mᵒ ″ e) =
    substᵒ-code-height-zero σ σ≤ Mᵒ
  substᵒ-meta-height-zero σ σ≤ (ref M) =
    substᵒ-meta-height-zero σ σ≤ M
  substᵒ-meta-height-zero σ σ≤ (L := M) =
    ⊔-mono≤
      (substᵒ-meta-height-zero σ σ≤ L)
      (substᵒ-meta-height-zero σ σ≤ M)
  substᵒ-meta-height-zero σ σ≤ (! M) =
    substᵒ-meta-height-zero σ σ≤ M
  substᵒ-meta-height-zero σ σ≤ (M ⟨ c ⟩) =
    ⊔-mono≤ (substᵒ-meta-height-zero σ σ≤ M) ≤-refl
  substᵒ-meta-height-zero σ σ≤ (blame ℓ) = ≤-refl

single-code-var-height-zero : ∀ y x → c-heightᵒ (((` y) •ᵒₛ idsᵒ) x) ≤ 0
single-code-var-height-zero y zero = ≤-refl
single-code-var-height-zero y (suc x) = ≤-refl

subst-code-var-code-height : ∀ Mᵒ y → c-heightᵒ (Mᵒ [ ` y ]ᵒ) ≤ c-heightᵒ Mᵒ
subst-code-var-code-height Mᵒ y =
  substᵒ-code-height-zero (((` y) •ᵒₛ idsᵒ)) (single-code-var-height-zero y) Mᵒ

⇑ᵉˢ-height : ∀ {h σ}
  → (∀ x → c-height (σ x) ≤ h)
  → ∀ x → c-height (⇑ᵉˢ σ x) ≤ h
⇑ᵉˢ-height {σ = σ} σ≤ x =
  ≤-trans (renᵉ-meta-height suc (σ x)) (σ≤ x)

⇑ᵒˢ-height : ∀ {h σ}
  → (∀ x → c-height (σ x) ≤ h)
  → ∀ x → c-height (⇑ᵒˢ σ x) ≤ h
⇑ᵒˢ-height {σ = σ} σ≤ x =
  ≤-trans (renᵒ-meta-height suc (σ x)) (σ≤ x)

extsᵐ-height : ∀ {h σ}
  → (∀ x → c-height (σ x) ≤ h)
  → ∀ x → c-height (extsᵐ σ x) ≤ h
extsᵐ-height {σ = σ} σ≤ zero = z≤n
extsᵐ-height {σ = σ} σ≤ (suc x) =
  ≤-trans (renᵐ-meta-height suc (σ x)) (σ≤ x)

mutual

  substᵐ-code-height : ∀ {h} σ
    → (∀ x → c-height (σ x) ≤ h)
    → ∀ Mᵒ → c-heightᵒ (substᵐ-code σ Mᵒ) ≤ c-heightᵒ Mᵒ ⊔ h
  substᵐ-code-height {h} σ σ≤ ($ k) = m≤m⊔n 0 h
  substᵐ-code-height {h} σ σ≤ (` x) = m≤m⊔n 0 h
  substᵐ-code-height {h} σ σ≤ (ƛ T ˙ Mᵒ) =
    substᵐ-code-height {h = h}
      (⇑ᵒˢ (⇑ᵉˢ σ))
      (⇑ᵒˢ-height {h = h} {σ = ⇑ᵉˢ σ}
        (⇑ᵉˢ-height {h = h} {σ = σ} σ≤))
      Mᵒ
  substᵐ-code-height σ σ≤ (ƛ̅ e ˙ Mᵒ) =
    substᵐ-code-height σ σ≤ Mᵒ
  substᵐ-code-height {h} σ σ≤ (Lᵒ · Mᵒ) =
    ⊔-combine≤ {c = c-heightᵒ Lᵒ} {d = c-heightᵒ Mᵒ} {h = h}
      (substᵐ-code-height σ σ≤ Lᵒ)
      (substᵐ-code-height σ σ≤ Mᵒ)
  substᵐ-code-height σ σ≤ (~ M) =
    substᵐ-meta-height σ σ≤ M
  substᵐ-code-height {h} σ σ≤ (blameᵒ ℓ) = m≤m⊔n 0 h

  substᵐ-meta-height : ∀ {h} σ
    → (∀ x → c-height (σ x) ≤ h)
    → ∀ M → c-height (substᵐ-meta σ M) ≤ c-height M ⊔ h
  substᵐ-meta-height {h} σ σ≤ ($ k) = m≤m⊔n 0 h
  substᵐ-meta-height {h} σ σ≤ (` x) =
    ≤-trans (σ≤ x) (m≤n⊔m 0 h)
  substᵐ-meta-height {h} σ σ≤ (addr a) = m≤m⊔n 0 h
  substᵐ-meta-height σ σ≤ (ƛ M) =
    substᵐ-meta-height (extsᵐ σ) (extsᵐ-height σ≤) M
  substᵐ-meta-height {h} σ σ≤ (L · M) =
    ⊔-combine≤ {c = c-height L} {d = c-height M} {h = h}
      (substᵐ-meta-height σ σ≤ L)
      (substᵐ-meta-height σ σ≤ M)
  substᵐ-meta-height {h} σ σ≤ (Λ M) =
    substᵐ-meta-height {h = h} (⇑ᵉˢ σ) (⇑ᵉˢ-height {h = h} {σ = σ} σ≤) M
  substᵐ-meta-height σ σ≤ (M ·[ e ]) =
    substᵐ-meta-height σ σ≤ M
  substᵐ-meta-height σ σ≤ (e₁ <: e₂ => M) =
    substᵐ-meta-height σ σ≤ M
  substᵐ-meta-height σ σ≤ (M ●) =
    substᵐ-meta-height σ σ≤ M
  substᵐ-meta-height σ σ≤ (M ★ ℓ) =
    substᵐ-meta-height σ σ≤ M
  substᵐ-meta-height σ σ≤ (‶ Mᵒ ″ e) =
    substᵐ-code-height σ σ≤ Mᵒ
  substᵐ-meta-height σ σ≤ (ref M) =
    substᵐ-meta-height σ σ≤ M
  substᵐ-meta-height {h} σ σ≤ (L := M) =
    ⊔-combine≤ {c = c-height L} {d = c-height M} {h = h}
      (substᵐ-meta-height σ σ≤ L)
      (substᵐ-meta-height σ σ≤ M)
  substᵐ-meta-height σ σ≤ (! M) =
    substᵐ-meta-height σ σ≤ M
  substᵐ-meta-height {h} σ σ≤ (M ⟨ c ⟩) =
    ⊔-combine≤ {c = c-height M} {d = meta-hc-height c} {h = h}
      (substᵐ-meta-height σ σ≤ M)
      (m≤m⊔n (meta-hc-height c) h)
  substᵐ-meta-height {h} σ σ≤ (blame ℓ) = m≤m⊔n 0 h

single-subst-meta-height : ∀ V x → c-height ((V •ᵐₛ idsᵐ) x) ≤ c-height V
single-subst-meta-height V zero = ≤-refl
single-subst-meta-height V (suc x) = z≤n

subst-meta-height : ∀ N V → c-height (N [ V ]ᵐ) ≤ c-height N ⊔ c-height V
subst-meta-height N V =
  substᵐ-meta-height (V •ᵐₛ idsᵐ) (single-subst-meta-height V) N

mutual

  step-heap-heightᵒ : ∀ {C₁ C₂ e}
    → C₁ ∣ e —→ᵒ C₂
      -----------------------------------------------------------------------
    → heap-c-height (C₂ .μ) ≤ c-heightᵒ (C₁ .M) ⊔ heap-c-height (C₁ .μ)
  step-heap-heightᵒ (ξ-code Fᵒ M—→N) =
    ≤-trans
      (step-heap-heightᵒ M—→N)
      (⊔-mono-≤ (plugᵒ-height-lower Fᵒ _) ≤-refl)
  step-heap-heightᵒ (ξ-code-blame Fᵒ) = m≤n⊔m _ _
  step-heap-heightᵒ (ξ-splice M—→N) = step-heap-heightᵐ M—→N
  step-heap-heightᵒ splice-blame = m≤n⊔m _ _
  step-heap-heightᵒ (splice-β Vᵒ) = m≤n⊔m _ _
  step-heap-heightᵒ (splice-sub Vᵒ) = m≤n⊔m _ _
  step-heap-heightᵒ code-λ = m≤n⊔m _ _
  step-heap-heightᵒ (ξ-code-λ̅ M—→N) = step-heap-heightᵒ M—→N
  step-heap-heightᵒ ξ-code-λ̅-blame = m≤n⊔m _ _

  step-heap-heightᵐ : ∀ {ctx C₁ C₂}
    → ctx / C₁ —→ᵐ C₂
      ----------------------------------------------------------------------
    → heap-c-height (C₂ .μ) ≤ c-height (C₁ .M) ⊔ heap-c-height (C₁ .μ)
  step-heap-heightᵐ (ξ-meta F M—→N) =
    ≤-trans
      (step-heap-heightᵐ M—→N)
      (⊔-mono-≤ (plugᵐ-height-lower F _) ≤-refl)
  step-heap-heightᵐ (ξ-cast {M = M} {c = c} M—→N) =
    ≤-trans
      (step-heap-heightᵐ M—→N)
      (⊔-mono-≤ (m≤m⊔n (c-height M) (meta-hc-height c)) ≤-refl)
  step-heap-heightᵐ (ξ-meta-blame F) = m≤n⊔m _ _
  step-heap-heightᵐ (ξ-quote Mᵒ—→Nᵒ) = step-heap-heightᵒ Mᵒ—→Nᵒ
  step-heap-heightᵐ quote-blame = m≤n⊔m _ _
  step-heap-heightᵐ (β V) = m≤n⊔m _ _
  step-heap-heightᵐ (β-cast U W) = m≤n⊔m _ _
  step-heap-heightᵐ Λ-β = m≤n⊔m _ _
  step-heap-heightᵐ (Λ-β-cast U) = m≤n⊔m _ _
  step-heap-heightᵐ sub-β = m≤n⊔m _ _
  step-heap-heightᵐ (sub-β-cast U) = m≤n⊔m _ _
  step-heap-heightᵐ (sub-cast-success U e₁<:e₂) = m≤n⊔m _ _
  step-heap-heightᵐ (sub-cast-sub-fail U ¬e₁<:e₂) = m≤n⊔m _ _
  step-heap-heightᵐ (sub-cast-fail U G ¬G⦊e₁<:e₂) = m≤n⊔m _ _
  step-heap-heightᵐ (ref {μ = μ} {V = V} value) = heap-extend-height μ V
  step-heap-heightᵐ (deref lookup) = m≤n⊔m _ _
  step-heap-heightᵐ (assign {μ = μ} {V = V} value μ↦μ′) = heap-update-height μ↦μ′
  step-heap-heightᵐ (assign-cast value) = m≤n⊔m _ _
  step-heap-heightᵐ deref-cast = m≤n⊔m _ _
  step-heap-heightᵐ (cast-compose U) = m≤n⊔m _ _
  step-heap-heightᵐ (cast-id⋆ U) = m≤n⊔m _ _
  step-heap-heightᵐ (cast-idι U) = m≤n⊔m _ _
  step-heap-heightᵐ (cast-blame U) = m≤n⊔m _ _

step-heap-lookup-heightᵒ : ∀ {C₁ C₂ e a V}
  → C₁ ∣ e —→ᵒ C₂
  → U._∋_⦂_ (C₂ .μ) a V
    ----------------------------------------------------------------------
  → c-height V ≤ c-heightᵒ (C₁ .M) ⊔ heap-c-height (C₁ .μ)
step-heap-lookup-heightᵒ step lookup =
  ≤-trans (heap-lookup-height lookup) (step-heap-heightᵒ step)

step-heap-lookup-heightᵐ : ∀ {ctx C₁ C₂ a V}
  → ctx / C₁ —→ᵐ C₂
  → U._∋_⦂_ (C₂ .μ) a V
    ---------------------------------------------------------------------
  → c-height V ≤ c-height (C₁ .M) ⊔ heap-c-height (C₁ .μ)
step-heap-lookup-heightᵐ step lookup =
  ≤-trans (heap-lookup-height lookup) (step-heap-heightᵐ step)


plugᵒ-height : ∀ F M N
  → c-heightᵒ N ≤ c-heightᵒ M
    -----------------------------------------------
  → c-heightᵒ (plugᵒ F N) ≤ c-heightᵒ (plugᵒ F M)
plugᵒ-height (□· Mᵒ) Lᵒ Nᵒ N≤L =
  ⊔-mono-≤ N≤L ≤-refl
plugᵒ-height ((Vᵒ ·□) value) Mᵒ Nᵒ N≤M =
  ⊔-mono-≤ ≤-refl N≤M

plugᵐ-height : ∀ F M N
  → c-height N ≤ c-height M
    ---------------------------------------------
  → c-height (plugᵐ F N) ≤ c-height (plugᵐ F M)
plugᵐ-height (□· M) L N N≤L =
  ⊔-mono-≤ N≤L ≤-refl
plugᵐ-height ((V ·□) value) M N N≤M =
  ⊔-mono-≤ ≤-refl N≤M
plugᵐ-height ref□ M N N≤M = N≤M
plugᵐ-height (□:= M) L N N≤L =
  ⊔-mono-≤ N≤L ≤-refl
plugᵐ-height ((V :=□) value) M N N≤M =
  ⊔-mono-≤ ≤-refl N≤M
plugᵐ-height !□ M N N≤M = N≤M
plugᵐ-height (□·[ e ]) M N N≤M = N≤M
plugᵐ-height □● M N N≤M = N≤M
plugᵐ-height (□★ ℓ) M N N≤M = N≤M

plugᵒ-config-height : ∀ F h₁ h₂ M N
  → h₂ ⊔ c-heightᵒ N ≤ h₁ ⊔ c-heightᵒ M
    -------------------------------------------------------------------
  → h₂ ⊔ c-heightᵒ (plugᵒ F N) ≤ h₁ ⊔ c-heightᵒ (plugᵒ F M)
plugᵒ-config-height (□· Mᵒ) h₁ h₂ Lᵒ Nᵒ N≤L =
  ⊔-add-right≤
    {a = h₂} {b = c-heightᵒ Nᵒ}
    {c = h₁} {d = c-heightᵒ Lᵒ}
    {e = c-heightᵒ Mᵒ}
    N≤L
plugᵒ-config-height ((Vᵒ ·□) value) h₁ h₂ Mᵒ Nᵒ N≤M =
  ⊔-add-middle≤
    {a = h₂} {b = c-heightᵒ Nᵒ}
    {c = h₁} {d = c-heightᵒ Mᵒ}
    {e = c-heightᵒ Vᵒ}
    N≤M

plugᵐ-config-height : ∀ F h₁ h₂ M N
  → h₂ ⊔ c-height N ≤ h₁ ⊔ c-height M
    ---------------------------------------------------------------
  → h₂ ⊔ c-height (plugᵐ F N) ≤ h₁ ⊔ c-height (plugᵐ F M)
plugᵐ-config-height (□· M) h₁ h₂ L N N≤L =
  ⊔-add-right≤
    {a = h₂} {b = c-height N}
    {c = h₁} {d = c-height L}
    {e = c-height M}
    N≤L
plugᵐ-config-height ((V ·□) value) h₁ h₂ M N N≤M =
  ⊔-add-middle≤
    {a = h₂} {b = c-height N}
    {c = h₁} {d = c-height M}
    {e = c-height V}
    N≤M
plugᵐ-config-height ref□ h₁ h₂ M N N≤M = N≤M
plugᵐ-config-height (□:= M) h₁ h₂ L N N≤L =
  ⊔-add-right≤
    {a = h₂} {b = c-height N}
    {c = h₁} {d = c-height L}
    {e = c-height M}
    N≤L
plugᵐ-config-height ((V :=□) value) h₁ h₂ M N N≤M =
  ⊔-add-middle≤
    {a = h₂} {b = c-height N}
    {c = h₁} {d = c-height M}
    {e = c-height V}
    N≤M
plugᵐ-config-height !□ h₁ h₂ M N N≤M = N≤M
plugᵐ-config-height (□·[ e ]) h₁ h₂ M N N≤M = N≤M
plugᵐ-config-height □● h₁ h₂ M N N≤M = N≤M
plugᵐ-config-height (□★ ℓ) h₁ h₂ M N N≤M = N≤M

ref-cast-left-height : ∀ {A B c d}
  → meta-hc-height c ≤ meta-hc-height (id (Ref A) ⨾ ref c d ⨾ id (Ref B))
ref-cast-left-height {c = c} {d = d} =
  m≤n⇒m≤1+n (m≤m⊔n (meta-hc-height c) (meta-hc-height d))

ref-cast-right-height : ∀ {A B c d}
  → meta-hc-height d ≤ meta-hc-height (id (Ref A) ⨾ ref c d ⨾ id (Ref B))
ref-cast-right-height {c = c} {d = d} =
  m≤n⇒m≤1+n (m≤n⊔m (meta-hc-height c) (meta-hc-height d))

ref-cast-assign-height : ∀ {A B c d} h
  → h ⊔ meta-hc-height c ≤ meta-hc-height (id (Ref A) ⨾ ref c d ⨾ id (Ref B)) ⊔ h
ref-cast-assign-height {A} {B} {c} {d} h =
  ⊔-lub
    (m≤n⊔m (meta-hc-height (id (Ref A) ⨾ ref c d ⨾ id (Ref B))) h)
    (≤-trans (ref-cast-left-height {A = A} {B = B} {c = c} {d = d})
      (m≤m⊔n (meta-hc-height (id (Ref A) ⨾ ref c d ⨾ id (Ref B))) h))

fun-cast-left-height : ∀ {A B C D c d}
  → meta-hc-height c ≤ meta-hc-height (id (C ⇒ D) ⨾ c ⇒ d ⨾ id (A ⇒ B))
fun-cast-left-height {c = c} {d = d} =
  m≤n⇒m≤1+n (m≤m⊔n (meta-hc-height c) (meta-hc-height d))

fun-cast-right-height : ∀ {A B C D c d}
  → meta-hc-height d ≤ meta-hc-height (id (C ⇒ D) ⨾ c ⇒ d ⨾ id (A ⇒ B))
fun-cast-right-height {c = c} {d = d} =
  m≤n⇒m≤1+n (m≤n⊔m (meta-hc-height c) (meta-hc-height d))

fun-cast-app-height : ∀ {A B C D c d} u w
  → (u ⊔ (w ⊔ meta-hc-height c)) ⊔ meta-hc-height d
      ≤ (u ⊔ meta-hc-height (id (C ⇒ D) ⨾ c ⇒ d ⨾ id (A ⇒ B))) ⊔ w
fun-cast-app-height {A} {B} {C} {D} {c} {d} u w =
  ⊔-lub
    (⊔-lub
      u≤src
      (⊔-lub w≤src c≤src))
    d≤src
  where
    hfun = meta-hc-height (id (C ⇒ D) ⨾ c ⇒ d ⨾ id (A ⇒ B))

    u≤src : u ≤ (u ⊔ hfun) ⊔ w
    u≤src = ≤-trans (m≤m⊔n u hfun) (m≤m⊔n (u ⊔ hfun) w)

    w≤src : w ≤ (u ⊔ hfun) ⊔ w
    w≤src = m≤n⊔m (u ⊔ hfun) w

    hfun≤src : hfun ≤ (u ⊔ hfun) ⊔ w
    hfun≤src = ≤-trans (m≤n⊔m u hfun) (m≤m⊔n (u ⊔ hfun) w)

    c≤src : meta-hc-height c ≤ (u ⊔ hfun) ⊔ w
    c≤src =
      ≤-trans (fun-cast-left-height {A = A} {B = B} {C = C} {D = D} {c = c} {d = d}) hfun≤src

    d≤src : meta-hc-height d ≤ (u ⊔ hfun) ⊔ w
    d≤src =
      ≤-trans (fun-cast-right-height {A = A} {B = B} {C = C} {D = D} {c = c} {d = d}) hfun≤src

forall-cast-height : ∀ {A B c}
  → meta-hc-height c ≤ meta-hc-height (id (∀̇ A) ⨾ ∀̇ c ⨾ id (∀̇ B))
forall-cast-height {c = c} =
  m≤n⇒m≤1+n ≤-refl

sub-cast-height : ∀ {e₁ e₂ A B c}
  → meta-hc-height c ≤ meta-hc-height (id (e₁ <: e₂ => A) ⨾ e₁ <: e₂ => c ⨾ id (e₁ <: e₂ => B))
sub-cast-height {c = c} =
  m≤n⇒m≤1+n ≤-refl

mutual

  preserve-heightᵒ : ∀ {C₁ C₂ e}
    → C₁ ∣ e —→ᵒ C₂
      ---------------------------------------------
    → code-config-height C₂ ≤ code-config-height C₁
  preserve-heightᵒ (ξ-code Fᵒ Mᵒ—→Nᵒ) =
    plugᵒ-config-height Fᵒ _ _ _ _ (preserve-heightᵒ Mᵒ—→Nᵒ)
  preserve-heightᵒ (ξ-code-blame Fᵒ) =
    ⊔-mono≤ ≤-refl z≤n
  preserve-heightᵒ (ξ-splice M—→N) =
    preserve-heightᵐ M—→N
  preserve-heightᵒ splice-blame = ≤-refl
  preserve-heightᵒ (splice-β value) = ≤-refl
  preserve-heightᵒ (splice-sub {μ = μ} {e₁ = e₁} {e₂ = e₂} {O = O} {Vᵒ = Vᵒ} value) =
    ⊔-mono≤
      {a = heap-c-height μ} {b = heap-c-height μ}
      {c = c-heightᵒ Vᵒ}
      {d = c-heightᵒ Vᵒ ⊔ meta-hc-height (code-sub-hc O e₁ e₂)}
      ≤-refl
      (m≤m⊔n (c-heightᵒ Vᵒ) (meta-hc-height (code-sub-hc O e₁ e₂)))
  preserve-heightᵒ (code-λ {Δ = Δ} {Γᵒ = Γᵒ} {μ = μ} {Nᵒ = Nᵒ}) =
    ⊔-mono≤
      {a = heap-c-height μ} {b = heap-c-height μ}
      {c = c-heightᵒ (Nᵒ [ ` freshᵉ Δ ]ᵉᵒ [ ` freshᵒ Γᵒ ]ᵒ)}
      {d = c-heightᵒ Nᵒ}
      ≤-refl
      (≤-trans
        (subst-code-var-code-height (Nᵒ [ ` freshᵉ Δ ]ᵉᵒ) (freshᵒ Γᵒ))
        (subst-ec-code-height Nᵒ (` freshᵉ Δ)))
  preserve-heightᵒ (ξ-code-λ̅ Mᵒ—→Nᵒ) =
    preserve-heightᵒ Mᵒ—→Nᵒ
  preserve-heightᵒ ξ-code-λ̅-blame = ≤-refl

  preserve-heightᵐ : ∀ {ctx} {C₁ C₂ : Config MetaTerm}
    → ctx / C₁ —→ᵐ C₂
      ---------------------------------------------
    → meta-config-height C₂ ≤ meta-config-height C₁
  preserve-heightᵐ (ξ-meta F M—→N) =
    plugᵐ-config-height F _ _ _ _ (preserve-heightᵐ M—→N)
  preserve-heightᵐ (ξ-cast {μ₁ = μ₁} {μ₂ = μ₂} {M = M} {N = N} {c = c} M—→N) =
    ⊔-add-right≤
      {a = heap-c-height μ₂} {b = c-height N}
      {c = heap-c-height μ₁} {d = c-height M}
      {e = meta-hc-height c}
      (preserve-heightᵐ M—→N)
  preserve-heightᵐ (ξ-meta-blame F) =
    ⊔-mono≤ ≤-refl z≤n
  preserve-heightᵐ (ξ-quote Mᵒ—→Nᵒ) =
    preserve-heightᵒ Mᵒ—→Nᵒ
  preserve-heightᵐ quote-blame = ≤-refl
  preserve-heightᵐ (β {μ = μ} {N = N} {V = V} value) =
    ⊔-mono≤
      {a = heap-c-height μ} {b = heap-c-height μ}
      {c = c-height (N [ V ]ᵐ)}
      {d = c-height N ⊔ c-height V}
      ≤-refl
      (subst-meta-height N V)
  preserve-heightᵐ (β-cast {μ = μ} {U = U} {W = W} {A = A} {B = B} {C = C} {D = D} {c = c} {d = d} raw value) =
    ⊔-mono≤
      {a = heap-c-height μ} {b = heap-c-height μ}
      {c = (c-height U ⊔ (c-height W ⊔ meta-hc-height c)) ⊔ meta-hc-height d}
      {d = (c-height U ⊔ meta-hc-height (id (C ⇒ D) ⨾ c ⇒ d ⨾ id (A ⇒ B))) ⊔ c-height W}
      ≤-refl
      (fun-cast-app-height {A = A} {B = B} {C = C} {D = D} {c = c} {d = d} (c-height U) (c-height W))
  preserve-heightᵐ (Λ-β {μ = μ} {e = e} {M = M}) =
    ⊔-mono≤
      {a = heap-c-height μ} {b = heap-c-height μ}
      {c = c-height (M [ e ]ᵉᵐ)}
      {d = c-height M}
      ≤-refl
      (subst-ec-meta-height M e)
  preserve-heightᵐ (Λ-β-cast {μ = μ} {e = e} {U = U} {A = A} {B = B} {c = c} raw) =
    ⊔-mono≤
      {a = heap-c-height μ} {b = heap-c-height μ}
      {c = c-height U ⊔ meta-hc-height (c [ e ]ᶜ)}
      {d = c-height U ⊔ meta-hc-height (id (∀̇ A) ⨾ ∀̇ c ⨾ id (∀̇ B))}
      ≤-refl
      (⊔-mono≤ ≤-refl
        (≤-trans
          (subst-ec-mhc-height c e)
          (forall-cast-height {A = A} {B = B} {c = c})))
  preserve-heightᵐ sub-β = ≤-refl
  preserve-heightᵐ (sub-β-cast {μ = μ} {e₁ = e₁} {e₂ = e₂} {U = U} {A = A} {B = B} {c = c} raw) =
    ⊔-mono≤
      {a = heap-c-height μ} {b = heap-c-height μ}
      {c = c-height U ⊔ meta-hc-height c}
      {d = c-height U ⊔ meta-hc-height (id (e₁ <: e₂ => A) ⨾ e₁ <: e₂ => c ⨾ id (e₁ <: e₂ => B))}
      ≤-refl
      (⊔-mono≤ ≤-refl (sub-cast-height {e₁ = e₁} {e₂ = e₂} {A = A} {B = B} {c = c}))
  preserve-heightᵐ (sub-cast-success raw e₁<:e₂) = ≤-refl
  preserve-heightᵐ (sub-cast-sub-fail raw ¬e₁<:e₂) =
    ⊔-mono≤ ≤-refl z≤n
  preserve-heightᵐ (sub-cast-fail raw ground ¬G⦊e₁<:e₂) =
    ⊔-mono≤ ≤-refl z≤n
  preserve-heightᵐ (ref {μ = μ} {V = V} value) =
    ⊔-lub
      (≤-trans (heap-extend-height μ V) (⊔-comm≤ (c-height V) (heap-c-height μ)))
      z≤n
  preserve-heightᵐ (deref {μ = μ} lookup) =
    ⊔-lub
      (m≤m⊔n (heap-c-height μ) 0)
      (≤-trans (heap-lookup-height lookup) (m≤m⊔n (heap-c-height μ) 0))
  preserve-heightᵐ (assign {μ = μ} {V = V} value μ↦μ′) =
    ⊔-lub
      (≤-trans (heap-update-height μ↦μ′) (⊔-comm≤ (c-height V) (heap-c-height μ)))
      z≤n
  preserve-heightᵐ (assign-cast {μ = μ} {V = V} {A = A} {B = B} {c = c} {d = d} value) =
    ⊔-mono≤
      {a = heap-c-height μ} {b = heap-c-height μ}
      {c = c-height V ⊔ meta-hc-height c}
      {d = meta-hc-height (id (Ref A) ⨾ ref c d ⨾ id (Ref B)) ⊔ c-height V}
      ≤-refl
      (ref-cast-assign-height {A = A} {B = B} {c = c} {d = d} (c-height V))
  preserve-heightᵐ (deref-cast {μ = μ} {A = A} {B = B} {c = c} {d = d}) =
    ⊔-mono≤
      {a = heap-c-height μ} {b = heap-c-height μ}
      {c = meta-hc-height d}
      {d = meta-hc-height (id (Ref A) ⨾ ref c d ⨾ id (Ref B))}
      ≤-refl
      (ref-cast-right-height {A = A} {B = B} {c = c} {d = d})
  preserve-heightᵐ {C₁ = config _ Θ _ μ ((U ⟨ c ⟩) ⟨ d ⟩)} (cast-compose raw) =
    ⊔-mono≤
      {a = heap-c-height μ} {b = heap-c-height μ}
      {c = c-height U ⊔ meta-hc-height (Θ ⊢ c ⨟ᵐ d)}
      {d = (c-height U ⊔ meta-hc-height c) ⊔ meta-hc-height d}
      ≤-refl
      (begin
        c-height U ⊔ meta-hc-height (Θ ⊢ c ⨟ᵐ d)
      ≤⟨ ⊔-mono-≤ ≤-refl (compose-height-meta Θ c d) ⟩
        c-height U ⊔ (meta-hc-height c ⊔ meta-hc-height d)
      ≤⟨ ⊔-assoc≤ (c-height U) (meta-hc-height c) (meta-hc-height d) ⟩
        (c-height U ⊔ meta-hc-height c) ⊔ meta-hc-height d
      ∎)
  preserve-heightᵐ {C₁ = config _ _ _ μ (U ⟨ id ⋆ ⨾ id⋆ ⨾ id ⋆ ⟩)} (cast-id⋆ raw) =
    ⊔-mono≤
      {a = heap-c-height μ} {b = heap-c-height μ}
      {c = c-height U}
      {d = c-height U ⊔ meta-hc-height (id ⋆ ⨾ id⋆ ⨾ id ⋆)}
      ≤-refl
      (m≤m⊔n (c-height U) (meta-hc-height (id ⋆ ⨾ id⋆ ⨾ id ⋆)))
  preserve-heightᵐ {C₁ = config _ _ _ μ (U ⟨ id (` ι) ⨾ idι ι ⨾ id (` ι) ⟩)} (cast-idι raw) =
    ⊔-mono≤
      {a = heap-c-height μ} {b = heap-c-height μ}
      {c = c-height U}
      {d = c-height U ⊔ meta-hc-height (id (` ι) ⨾ idι ι ⨾ id (` ι))}
      ≤-refl
      (m≤m⊔n (c-height U) (meta-hc-height (id (` ι) ⨾ idι ι ⨾ id (` ι))))
  preserve-heightᵐ {C₁ = config _ _ _ μ _} (cast-blame raw) =
    ⊔-mono≤
      {a = heap-c-height μ} {b = heap-c-height μ}
      ≤-refl
      z≤n

multi-preserve-heightᵒ : ∀ {C₁ C₂ e}
  → C₁ ∣ e —↠ᵒ C₂
    ---------------------------------------------
  → code-config-height C₂ ≤ code-config-height C₁
multi-preserve-heightᵒ (C ∣ e ∎ᵒ) = ≤-refl
multi-preserve-heightᵒ (_∣_—→ᵒ⟨_⟩_ C₁ e {C₂ = C₂} {C₃ = C₃} C₁—→C₂ C₂—↠C₃) =
  begin
    code-config-height C₃
  ≤⟨ multi-preserve-heightᵒ C₂—↠C₃ ⟩
    code-config-height C₂
  ≤⟨ preserve-heightᵒ C₁—→C₂ ⟩
    code-config-height C₁
  ∎

multi-preserve-heightᵐ : ∀ {ctx} {C₁ C₂ : Config MetaTerm}
  → ctx / C₁ —↠ᵐ C₂
    ---------------------------------------------
  → meta-config-height C₂ ≤ meta-config-height C₁
multi-preserve-heightᵐ (C ∎ᵐ) = ≤-refl
multi-preserve-heightᵐ (_/_—→ᵐ⟨_⟩_ ctx C₁ {C₂ = C₂} {C₃ = C₃} C₁—→C₂ C₂—↠C₃) =
  begin
    meta-config-height C₃
  ≤⟨ multi-preserve-heightᵐ C₂—↠C₃ ⟩
    meta-config-height C₂
  ≤⟨ preserve-heightᵐ C₁—→C₂ ⟩
    meta-config-height C₁
  ∎
