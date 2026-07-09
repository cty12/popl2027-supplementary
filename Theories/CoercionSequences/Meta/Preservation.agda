module Theories.CoercionSequences.Meta.Preservation where

open import Data.List using (_++_; [_])

import Theories.CoercionSequences.Code.Definition as OC
import Theories.CoercionSequences.Code.Preservation as OCP
import Theories.CoercionSequences.EC.Definition as ECS
import Theories.CoercionSequences.EC.Preservation as ECP
open import Theories.CoercionSequences.Meta.Definition


wf-domᵉ : ∀ {Δ Θ cᵉ ê₁ ê₂}
  → Δ ECS.; Θ ⊢ᵉ cᵉ ⦂ ê₁ ⇒ ê₂
    ------------------------------
  → Δ ⊢ᵉ⋆ ê₁
wf-domᵉ (ECS.⊢! e ⊢e) = wf-ec ⊢e
wf-domᵉ (ECS.⊢? e ⊢e ℓ) = wf-⋆
wf-domᵉ (ECS.⊢↑ ⊢ê₁ ⊢ê₂ ê₁<:ê₂) = ⊢ê₁
wf-domᵉ (ECS.⊢⊥ ⊢ê₁ ⊢ê₂ ℓ) = ⊢ê₁

wf-codᵉ : ∀ {Δ Θ cᵉ ê₁ ê₂}
  → Δ ECS.; Θ ⊢ᵉ cᵉ ⦂ ê₁ ⇒ ê₂
    ------------------------------
  → Δ ⊢ᵉ⋆ ê₂
wf-codᵉ (ECS.⊢! e ⊢e) = wf-⋆
wf-codᵉ (ECS.⊢? e ⊢e ℓ) = wf-ec ⊢e
wf-codᵉ (ECS.⊢↑ ⊢ê₁ ⊢ê₂ ê₁<:ê₂) = ⊢ê₂
wf-codᵉ (ECS.⊢⊥ ⊢ê₁ ⊢ê₂ ℓ) = ⊢ê₂

wf-domᵉ̅ : ∀ {Δ Θ c̅ᵉ ê₁ ê₂}
  → Δ ECS.; Θ ⊢ᵉ̅ c̅ᵉ ⦂ ê₁ ⇒ ê₂
    --------------------------------
  → Δ ⊢ᵉ⋆ ê₁
wf-domᵉ̅ (ECS.⊢[] ⊢ê) = ⊢ê
wf-domᵉ̅ (ECS.⊢; ⊢cᵉ ⊢c̅ᵉ) = wf-domᵉ ⊢cᵉ

wf-codᵉ̅ : ∀ {Δ Θ c̅ᵉ ê₁ ê₂}
  → Δ ECS.; Θ ⊢ᵉ̅ c̅ᵉ ⦂ ê₁ ⇒ ê₂
    --------------------------------
  → Δ ⊢ᵉ⋆ ê₂
wf-codᵉ̅ (ECS.⊢[] ⊢ê) = ⊢ê
wf-codᵉ̅ (ECS.⊢; ⊢cᵉ ⊢c̅ᵉ) = wf-codᵉ̅ ⊢c̅ᵉ

wf-domᵐ : ∀ {Δ Θ cᵐ A B}
  → Δ ; Θ ⊢ᵐ cᵐ ⦂ A ⇒ B
    ---------------------
  → Δ ⊢ᵐᵗ A
wf-codᵐ : ∀ {Δ Θ cᵐ A B}
  → Δ ; Θ ⊢ᵐ cᵐ ⦂ A ⇒ B
    ---------------------
  → Δ ⊢ᵐᵗ B
wf-domᵐ̅ : ∀ {Δ Θ c̅ᵐ A B}
  → Δ ; Θ ⊢ᵐ̅ c̅ᵐ ⦂ A ⇒ B
    ----------------------
  → Δ ⊢ᵐᵗ A
wf-codᵐ̅ : ∀ {Δ Θ c̅ᵐ A B}
  → Δ ; Θ ⊢ᵐ̅ c̅ᵐ ⦂ A ⇒ B
    ----------------------
  → Δ ⊢ᵐᵗ B

wf-domᵐ (⊢! ⊢G g) = ⊢G
wf-domᵐ (⊢? ⊢G ℓ g) = wf-⋆
wf-domᵐ (⊢fun ⊢c̅ᵐ ⊢d̅ᵐ) = wf-fun (wf-codᵐ̅ ⊢c̅ᵐ) (wf-domᵐ̅ ⊢d̅ᵐ)
wf-domᵐ (⊢code ⊢c̅ᵒ ⊢c̅ᵉ) = wf-code (wf-domᵉ̅ ⊢c̅ᵉ)
wf-domᵐ (⊢ref ⊢c̅ᵐ ⊢d̅ᵐ) = wf-ref (wf-codᵐ̅ ⊢c̅ᵐ)
wf-domᵐ (⊢forall ⊢c̅ᵐ) = wf-forall (wf-domᵐ̅ ⊢c̅ᵐ)
wf-domᵐ (⊢sub ⊢e₁ ⊢e₂ ⊢c̅ᵐ) = wf-sub ⊢e₁ ⊢e₂ (wf-domᵐ̅ ⊢c̅ᵐ)
wf-domᵐ (⊢⊥ ⊢A ⊢B ℓ) = ⊢A

wf-codᵐ (⊢! ⊢G g) = wf-⋆
wf-codᵐ (⊢? ⊢G ℓ g) = ⊢G
wf-codᵐ (⊢fun ⊢c̅ᵐ ⊢d̅ᵐ) = wf-fun (wf-domᵐ̅ ⊢c̅ᵐ) (wf-codᵐ̅ ⊢d̅ᵐ)
wf-codᵐ (⊢code ⊢c̅ᵒ ⊢c̅ᵉ) = wf-code (wf-codᵉ̅ ⊢c̅ᵉ)
wf-codᵐ (⊢ref ⊢c̅ᵐ ⊢d̅ᵐ) = wf-ref (wf-domᵐ̅ ⊢c̅ᵐ)
wf-codᵐ (⊢forall ⊢c̅ᵐ) = wf-forall (wf-codᵐ̅ ⊢c̅ᵐ)
wf-codᵐ (⊢sub ⊢e₁ ⊢e₂ ⊢c̅ᵐ) = wf-sub ⊢e₁ ⊢e₂ (wf-codᵐ̅ ⊢c̅ᵐ)
wf-codᵐ (⊢⊥ ⊢A ⊢B ℓ) = ⊢B

wf-domᵐ̅ (⊢[] ⊢A) = ⊢A
wf-domᵐ̅ (⊢; ⊢cᵐ ⊢c̅ᵐ) = wf-domᵐ ⊢cᵐ

wf-codᵐ̅ (⊢[] ⊢A) = ⊢A
wf-codᵐ̅ (⊢; ⊢cᵐ ⊢c̅ᵐ) = wf-codᵐ̅ ⊢c̅ᵐ


++ᵐ-preserve : ∀ {Δ Θ c̅ᵐ d̅ᵐ A B C}
  → Δ ; Θ ⊢ᵐ̅ c̅ᵐ ⦂ A ⇒ B
  → Δ ; Θ ⊢ᵐ̅ d̅ᵐ ⦂ B ⇒ C
    ------------------------------
  → Δ ; Θ ⊢ᵐ̅ c̅ᵐ ++ d̅ᵐ ⦂ A ⇒ C
++ᵐ-preserve (⊢[] _) ⊢d̅ᵐ = ⊢d̅ᵐ
++ᵐ-preserve (⊢; ⊢cᵐ ⊢c̅ᵐ) ⊢d̅ᵐ =
  ⊢; ⊢cᵐ (++ᵐ-preserve ⊢c̅ᵐ ⊢d̅ᵐ)


private

  ⊢singleton : ∀ {Δ Θ cᵐ A B}
    → Δ ; Θ ⊢ᵐ cᵐ ⦂ A ⇒ B
      ----------------------
    → Δ ; Θ ⊢ᵐ̅ [ cᵐ ] ⦂ A ⇒ B
  ⊢singleton ⊢cᵐ = ⊢; ⊢cᵐ (⊢[] (wf-codᵐ ⊢cᵐ))

  preserve-pair : ∀ {Δ Θ cᵐ₁ cᵐ₂ d̅ᵐ A B C}
    → Θ ⊢ᵐ cᵐ₁ ; cᵐ₂ ⟶ d̅ᵐ
    → Δ ; Θ ⊢ᵐ cᵐ₁ ⦂ A ⇒ B
    → Δ ; Θ ⊢ᵐ cᵐ₂ ⦂ B ⇒ C
      ------------------------------
    → Δ ; Θ ⊢ᵐ̅ d̅ᵐ ⦂ A ⇒ C
  preserve-pair collapse (⊢! ⊢G g) (⊢? _ ℓ h) = ⊢[] ⊢G
  preserve-pair (collide G≢H) (⊢! ⊢G g) (⊢? ⊢H ℓ h) =
    ⊢singleton (⊢⊥ ⊢G ⊢H ℓ)
  preserve-pair seq-fun (⊢fun ⊢c̅ᵐ₁ ⊢c̅ᵐ₂) (⊢fun ⊢d̅ᵐ₁ ⊢d̅ᵐ₂) =
    ⊢singleton (⊢fun (++ᵐ-preserve ⊢d̅ᵐ₁ ⊢c̅ᵐ₁) (++ᵐ-preserve ⊢c̅ᵐ₂ ⊢d̅ᵐ₂))
  preserve-pair seq-ref (⊢ref ⊢c̅ᵐ₁ ⊢c̅ᵐ₂) (⊢ref ⊢d̅ᵐ₁ ⊢d̅ᵐ₂) =
    ⊢singleton (⊢ref (++ᵐ-preserve ⊢d̅ᵐ₁ ⊢c̅ᵐ₁) (++ᵐ-preserve ⊢c̅ᵐ₂ ⊢d̅ᵐ₂))
  preserve-pair seq-code (⊢code ⊢c̅ᵒ ⊢c̅ᵉ) (⊢code ⊢d̅ᵒ ⊢d̅ᵉ) =
    ⊢singleton (⊢code (OCP.++-preserve ⊢c̅ᵒ ⊢d̅ᵒ) (ECP.++ᵉ-preserve ⊢c̅ᵉ ⊢d̅ᵉ))
  preserve-pair seq-forall (⊢forall ⊢c̅ᵐ) (⊢forall ⊢d̅ᵐ) =
    ⊢singleton (⊢forall (++ᵐ-preserve ⊢c̅ᵐ ⊢d̅ᵐ))
  preserve-pair seq-sub (⊢sub ⊢e₁ ⊢e₂ ⊢c̅ᵐ) (⊢sub _ _ ⊢d̅ᵐ) =
    ⊢singleton (⊢sub ⊢e₁ ⊢e₂ (++ᵐ-preserve ⊢c̅ᵐ ⊢d̅ᵐ))
  preserve-pair ⊥-left (⊢⊥ ⊢A ⊢B ℓ) ⊢cᵐ₂ =
    ⊢singleton (⊢⊥ ⊢A (wf-codᵐ ⊢cᵐ₂) ℓ)
  preserve-pair (⊥-right not-blame not-proj) ⊢cᵐ₁ (⊢⊥ ⊢B ⊢C ℓ) =
    ⊢singleton (⊢⊥ (wf-domᵐ ⊢cᵐ₁) ⊢C ℓ)


mutual

  preserveᵐ : ∀ {Δ Θ cᵐ d̅ᵐ A B}
    → Θ ⊢ᵐ cᵐ —→ d̅ᵐ
    → Δ ; Θ ⊢ᵐ cᵐ ⦂ A ⇒ B
      -----------------------
    → Δ ; Θ ⊢ᵐ̅ d̅ᵐ ⦂ A ⇒ B
  preserveᵐ id-fun (⊢fun (⊢[] ⊢C) (⊢[] ⊢D)) =
    ⊢[] (wf-fun ⊢C ⊢D)
  preserveᵐ id-code (⊢code OC.⊢[] (ECS.⊢[] ⊢ê)) =
    ⊢[] (wf-code ⊢ê)
  preserveᵐ id-ref (⊢ref (⊢[] ⊢A) (⊢[] ⊢B)) =
    ⊢[] (wf-ref ⊢A)
  preserveᵐ id-forall (⊢forall (⊢[] ⊢A)) =
    ⊢[] (wf-forall ⊢A)
  preserveᵐ id-sub (⊢sub ⊢e₁ ⊢e₂ (⊢[] ⊢A)) =
    ⊢[] (wf-sub ⊢e₁ ⊢e₂ ⊢A)
  preserveᵐ (ξ-fun-dom c̅ᵐ₁—→d̅ᵐ₁) (⊢fun ⊢c̅ᵐ₁ ⊢c̅ᵐ₂) =
    ⊢singleton (⊢fun (preserve c̅ᵐ₁—→d̅ᵐ₁ ⊢c̅ᵐ₁) ⊢c̅ᵐ₂)
  preserveᵐ (ξ-fun-cod nf₁ c̅ᵐ₂—→d̅ᵐ₂) (⊢fun ⊢c̅ᵐ₁ ⊢c̅ᵐ₂) =
    ⊢singleton (⊢fun ⊢c̅ᵐ₁ (preserve c̅ᵐ₂—→d̅ᵐ₂ ⊢c̅ᵐ₂))
  preserveᵐ (ξ-ref-in c̅ᵐ₁—→d̅ᵐ₁) (⊢ref ⊢c̅ᵐ₁ ⊢c̅ᵐ₂) =
    ⊢singleton (⊢ref (preserve c̅ᵐ₁—→d̅ᵐ₁ ⊢c̅ᵐ₁) ⊢c̅ᵐ₂)
  preserveᵐ (ξ-ref-out nf₁ c̅ᵐ₂—→d̅ᵐ₂) (⊢ref ⊢c̅ᵐ₁ ⊢c̅ᵐ₂) =
    ⊢singleton (⊢ref ⊢c̅ᵐ₁ (preserve c̅ᵐ₂—→d̅ᵐ₂ ⊢c̅ᵐ₂))
  preserveᵐ (ξ-forall c̅ᵐ—→d̅ᵐ) (⊢forall ⊢c̅ᵐ) =
    ⊢singleton (⊢forall (preserve c̅ᵐ—→d̅ᵐ ⊢c̅ᵐ))
  preserveᵐ (ξ-sub c̅ᵐ—→d̅ᵐ) (⊢sub ⊢e₁ ⊢e₂ ⊢c̅ᵐ) =
    ⊢singleton (⊢sub ⊢e₁ ⊢e₂ (preserve c̅ᵐ—→d̅ᵐ ⊢c̅ᵐ))
  preserveᵐ (ξ-code c̅ᵒ—→d̅ᵒ) (⊢code ⊢c̅ᵒ ⊢c̅ᵉ) =
    ⊢singleton (⊢code (OCP.preserve c̅ᵒ—→d̅ᵒ ⊢c̅ᵒ) ⊢c̅ᵉ)
  preserveᵐ (ξ-code-ec nfᵒ not-blameᵒ c̅ᵉ—→d̅ᵉ) (⊢code ⊢c̅ᵒ ⊢c̅ᵉ) =
    ⊢singleton (⊢code ⊢c̅ᵒ (ECP.preserve c̅ᵉ—→d̅ᵉ ⊢c̅ᵉ))
  preserveᵐ ξ-code-⊥ (⊢code (OC.⊢; (OC.⊢⊥ C₁ C₂ ℓ) OC.⊢[]) ⊢c̅ᵉ) =
    ⊢singleton (⊢⊥ (wf-code (wf-domᵉ̅ ⊢c̅ᵉ)) (wf-code (wf-codᵉ̅ ⊢c̅ᵉ)) ℓ)
  preserveᵐ (ξ-code-ec-⊥ nfᵒ not-blameᵒ) (⊢code ⊢c̅ᵒ (ECS.⊢; (ECS.⊢⊥ ⊢ê₁ ⊢ê₂ ℓ) (ECS.⊢[] _))) =
    ⊢singleton (⊢⊥ (wf-code ⊢ê₁) (wf-code ⊢ê₂) ℓ)

  preserve : ∀ {Δ Θ c̅ᵐ d̅ᵐ A B}
    → Θ ⊢ᵐ̅ c̅ᵐ —→ d̅ᵐ
    → Δ ; Θ ⊢ᵐ̅ c̅ᵐ ⦂ A ⇒ B
      ------------------------
    → Δ ; Θ ⊢ᵐ̅ d̅ᵐ ⦂ A ⇒ B
  preserve (reduce-head cᵐ—→dᵐ) (⊢; ⊢cᵐ ⊢c̅ᵐ) =
    ++ᵐ-preserve (preserveᵐ cᵐ—→dᵐ ⊢cᵐ) ⊢c̅ᵐ
  preserve (reduce-neighbors nf cᵐ₁;cᵐ₂⟶dᵐ) (⊢; ⊢cᵐ₁ (⊢; ⊢cᵐ₂ ⊢c̅ᵐ)) =
    ++ᵐ-preserve (preserve-pair cᵐ₁;cᵐ₂⟶dᵐ ⊢cᵐ₁ ⊢cᵐ₂) ⊢c̅ᵐ
  preserve (reduce-tail snf irred cᵐ₂;c̅ᵐ—→d̅ᵐ) (⊢; ⊢cᵐ₁ ⊢cᵐ₂;c̅ᵐ) =
    ⊢; ⊢cᵐ₁ (preserve cᵐ₂;c̅ᵐ—→d̅ᵐ ⊢cᵐ₂;c̅ᵐ)
