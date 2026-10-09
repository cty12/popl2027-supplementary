module LambdaAlphaRefStar.Theories.CoercionSequences.Meta.Determinism where

open import Data.Empty using (⊥-elim)
open import Data.List using (_++_; [_])
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import Relation.Nullary using (¬_)

import LambdaAlphaRefStar.Theories.CoercionSequences.Code.Definition as OC
import LambdaAlphaRefStar.Theories.CoercionSequences.Code.Determinism as OCD
import LambdaAlphaRefStar.Theories.CoercionSequences.EC.Definition as ECS
import LambdaAlphaRefStar.Theories.CoercionSequences.EC.Determinism as ECD
open import LambdaAlphaRefStar.Theories.CoercionSequences.Meta.Definition


private

  code-irred-no-pair-step : ∀ {cᵒ₁ cᵒ₂ d̅ᵒ}
    → OC.IrredPair cᵒ₁ cᵒ₂
      -----------------------------
    → ¬ (OC.⊢ᵒ cᵒ₁ ; cᵒ₂ ⟶ d̅ᵒ)
  code-irred-no-pair-step OC.irred-?! ()
  code-irred-no-pair-step OC.irred-?fun ()
  code-irred-no-pair-step OC.irred-fun! ()
  code-irred-no-pair-step OC.irred-?⊥ ()

  mutual

    code-single-nf-no-step : ∀ {cᵒ d̅ᵒ}
      → OC.SingleNF cᵒ
        -------------------
      → ¬ (OC.⊢ᵒ cᵒ —→ d̅ᵒ)
    code-single-nf-no-step OC.nf-! ()
    code-single-nf-no-step OC.nf-? ()
    code-single-nf-no-step OC.nf-⊥ ()
    code-single-nf-no-step (OC.nf-fun nf₁ nf₂ not-both-id not-blame₁ not-blame₂) OC.id-fun =
      not-both-id (refl , refl)
    code-single-nf-no-step (OC.nf-fun nf₁ nf₂ _ _ _) (OC.ξ-fun-dom c̅ᵒ₁—→d̅ᵒ₁) =
      code-nf-no-step nf₁ c̅ᵒ₁—→d̅ᵒ₁
    code-single-nf-no-step (OC.nf-fun nf₁ nf₂ _ _ _) (OC.ξ-fun-cod _ _ c̅ᵒ₂—→d̅ᵒ₂) =
      code-nf-no-step nf₂ c̅ᵒ₂—→d̅ᵒ₂
    code-single-nf-no-step (OC.nf-fun _ _ _ not-blame _) OC.ξ-⊥-fun-dom =
      not-blame (_ , refl)
    code-single-nf-no-step (OC.nf-fun _ _ _ _ not-blame) (OC.ξ-⊥-fun-cod _ _) =
      not-blame (_ , refl)

    code-nf-no-step : ∀ {c̅ᵒ d̅ᵒ}
      → OC.NF c̅ᵒ
        --------------------
      → ¬ (OC.⊢ᵒ̅ c̅ᵒ —→ d̅ᵒ)
    code-nf-no-step OC.nf-empty ()
    code-nf-no-step (OC.nf-singleton snf) (OC.reduce-head cᵒ—→d̅ᵒ) =
      code-single-nf-no-step snf cᵒ—→d̅ᵒ
    code-nf-no-step (OC.nf-step snf irred nf-tail) (OC.reduce-head cᵒ—→d̅ᵒ) =
      code-single-nf-no-step snf cᵒ—→d̅ᵒ
    code-nf-no-step (OC.nf-step snf irred nf-tail) (OC.reduce-neighbors nf cᵒ₁;cᵒ₂⟶d̅ᵒ) =
      code-irred-no-pair-step irred cᵒ₁;cᵒ₂⟶d̅ᵒ
    code-nf-no-step (OC.nf-step snf irred nf-tail) (OC.reduce-tail _ _ cᵒ₂;c̅ᵒ—→d̅ᵒ) =
      code-nf-no-step nf-tail cᵒ₂;c̅ᵒ—→d̅ᵒ

  ec-irred-no-pair-step : ∀ {Θ cᵉ₁ cᵉ₂ d̅ᵉ}
    → ECS.IrredPair cᵉ₁ cᵉ₂
      -----------------------------
    → ¬ (Θ ECS.⊢ᵉ cᵉ₁ ; cᵉ₂ ⟶ d̅ᵉ)
  ec-irred-no-pair-step ECS.irred-?! ()
  ec-irred-no-pair-step (ECS.irred-↑! e′≢e) ()
  ec-irred-no-pair-step ECS.irred-!↑⋆ ()
  ec-irred-no-pair-step ECS.irred-?↑ ()

  ec-single-nf-no-step : ∀ {Θ cᵉ d̅ᵉ}
    → ECS.SingleNF cᵉ
      -----------------------------
    → ¬ (Θ ECS.⊢ᵉ cᵉ —→ d̅ᵉ)
  ec-single-nf-no-step ECS.nf-! ()
  ec-single-nf-no-step ECS.nf-? ()
  ec-single-nf-no-step (ECS.nf-↑ ê₁≢ê₂) ECS.↑-id = ê₁≢ê₂ refl
  ec-single-nf-no-step ECS.nf-⊥ ()

  ec-nf-no-step : ∀ {Θ c̅ᵉ d̅ᵉ}
    → ECS.NF c̅ᵉ
      --------------------------
    → ¬ (Θ ECS.⊢ᵉ̅ c̅ᵉ —→ d̅ᵉ)
  ec-nf-no-step ECS.nf-empty ()
  ec-nf-no-step (ECS.nf-singleton snf) (ECS.reduce-head cᵉ—→d̅ᵉ) =
    ec-single-nf-no-step snf cᵉ—→d̅ᵉ
  ec-nf-no-step (ECS.nf-step snf irred nf-tail) (ECS.reduce-head cᵉ—→d̅ᵉ) =
    ec-single-nf-no-step snf cᵉ—→d̅ᵉ
  ec-nf-no-step (ECS.nf-step snf irred nf-tail) (ECS.reduce-neighbors _ cᵉ₁;cᵉ₂⟶d̅ᵉ) =
    ec-irred-no-pair-step irred cᵉ₁;cᵉ₂⟶d̅ᵉ
  ec-nf-no-step (ECS.nf-step snf irred nf-tail) (ECS.reduce-tail _ _ cᵉ₂;c̅ᵉ—→d̅ᵉ) =
    ec-nf-no-step nf-tail cᵉ₂;c̅ᵉ—→d̅ᵉ

  pair-deterministic : ∀ {Θ cᵐ₁ cᵐ₂ d̅ᵐ₁ d̅ᵐ₂}
    → Θ ⊢ᵐ cᵐ₁ ; cᵐ₂ ⟶ d̅ᵐ₁
    → Θ ⊢ᵐ cᵐ₁ ; cᵐ₂ ⟶ d̅ᵐ₂
      --------------------------
    → d̅ᵐ₁ ≡ d̅ᵐ₂
  pair-deterministic collapse collapse = refl
  pair-deterministic collapse (collide G≢G) = ⊥-elim (G≢G refl)
  pair-deterministic (collide G≢G) collapse = ⊥-elim (G≢G refl)
  pair-deterministic (collide G≢H) (collide G≢H′) = refl
  pair-deterministic seq-fun seq-fun = refl
  pair-deterministic seq-ref seq-ref = refl
  pair-deterministic seq-code seq-code = refl
  pair-deterministic seq-forall seq-forall = refl
  pair-deterministic seq-sub seq-sub = refl
  pair-deterministic ⊥-left ⊥-left = refl
  pair-deterministic ⊥-left (⊥-right not-blame not-proj) =
    ⊥-elim (not-blame (_ , refl))
  pair-deterministic (⊥-right not-blame not-proj) ⊥-left =
    ⊥-elim (not-blame (_ , refl))
  pair-deterministic (⊥-right not-blame not-proj) (⊥-right not-blame′ not-proj′) = refl

  irred-no-pair-step : ∀ {Θ cᵐ₁ cᵐ₂ d̅ᵐ}
    → IrredPair cᵐ₁ cᵐ₂
      --------------------------
    → ¬ (Θ ⊢ᵐ cᵐ₁ ; cᵐ₂ ⟶ d̅ᵐ)
  irred-no-pair-step irred-?! ()
  irred-no-pair-step irred-?⊥ (⊥-right not-blame not-proj) =
    not-proj (_ , _ , _ , refl)
  irred-no-pair-step irred-?fun ()
  irred-no-pair-step irred-fun! ()
  irred-no-pair-step irred-?code ()
  irred-no-pair-step irred-code! ()
  irred-no-pair-step irred-?ref ()
  irred-no-pair-step irred-ref! ()
  irred-no-pair-step irred-?∀ ()
  irred-no-pair-step irred-∀! ()
  irred-no-pair-step irred-?sub ()
  irred-no-pair-step irred-sub! ()

  mutual

    single-nf-no-step : ∀ {Θ cᵐ d̅ᵐ}
      → SingleNF cᵐ
        ------------------------
      → ¬ (Θ ⊢ᵐ cᵐ —→ d̅ᵐ)
    single-nf-no-step nf-! ()
    single-nf-no-step nf-? ()
    single-nf-no-step nf-⊥ ()
    single-nf-no-step (nf-fun nf₁ nf₂ not-both-id) id-fun =
      not-both-id (refl , refl)
    single-nf-no-step (nf-fun nf₁ nf₂ _) (ξ-fun-dom c̅ᵐ₁—→d̅ᵐ₁) =
      nf-no-step nf₁ c̅ᵐ₁—→d̅ᵐ₁
    single-nf-no-step (nf-fun nf₁ nf₂ _) (ξ-fun-cod _ c̅ᵐ₂—→d̅ᵐ₂) =
      nf-no-step nf₂ c̅ᵐ₂—→d̅ᵐ₂
    single-nf-no-step (nf-code nfᵒ nfᵉ not-id not-blameᵒ not-blameᵉ) id-code =
      not-id (refl , refl)
    single-nf-no-step (nf-code nfᵒ nfᵉ _ not-blameᵒ not-blameᵉ) (ξ-code c̅ᵒ—→d̅ᵒ) =
      code-nf-no-step nfᵒ c̅ᵒ—→d̅ᵒ
    single-nf-no-step (nf-code nfᵒ nfᵉ _ not-blameᵒ not-blameᵉ) (ξ-code-ec _ _ c̅ᵉ—→d̅ᵉ) =
      ec-nf-no-step nfᵉ c̅ᵉ—→d̅ᵉ
    single-nf-no-step (nf-code nfᵒ nfᵉ _ not-blameᵒ not-blameᵉ) ξ-code-⊥ =
      not-blameᵒ (_ , refl)
    single-nf-no-step (nf-code nfᵒ nfᵉ _ not-blameᵒ not-blameᵉ) (ξ-code-ec-⊥ _ _) =
      not-blameᵉ (_ , refl)
    single-nf-no-step (nf-ref nf₁ nf₂ not-both-id) id-ref =
      not-both-id (refl , refl)
    single-nf-no-step (nf-ref nf₁ nf₂ _) (ξ-ref-in c̅ᵐ₁—→d̅ᵐ₁) =
      nf-no-step nf₁ c̅ᵐ₁—→d̅ᵐ₁
    single-nf-no-step (nf-ref nf₁ nf₂ _) (ξ-ref-out _ c̅ᵐ₂—→d̅ᵐ₂) =
      nf-no-step nf₂ c̅ᵐ₂—→d̅ᵐ₂
    single-nf-no-step (nf-forall nf not-id) id-forall =
      not-id refl
    single-nf-no-step (nf-forall nf _) (ξ-forall c̅ᵐ—→d̅ᵐ) =
      nf-no-step nf c̅ᵐ—→d̅ᵐ
    single-nf-no-step (nf-sub nf not-id) id-sub =
      not-id refl
    single-nf-no-step (nf-sub nf _) (ξ-sub c̅ᵐ—→d̅ᵐ) =
      nf-no-step nf c̅ᵐ—→d̅ᵐ

    nf-no-step : ∀ {Θ c̅ᵐ d̅ᵐ}
      → NF c̅ᵐ
        ----------------------
      → ¬ (Θ ⊢ᵐ̅ c̅ᵐ —→ d̅ᵐ)
    nf-no-step nf-empty ()
    nf-no-step (nf-singleton snf) (reduce-head cᵐ—→dᵐ) =
      single-nf-no-step snf cᵐ—→dᵐ
    nf-no-step (nf-step snf irred nf-tail) (reduce-head cᵐ—→dᵐ) =
      single-nf-no-step snf cᵐ—→dᵐ
    nf-no-step (nf-step snf irred nf-tail) (reduce-neighbors nf cᵐ₁;cᵐ₂⟶dᵐ) =
      irred-no-pair-step irred cᵐ₁;cᵐ₂⟶dᵐ
    nf-no-step (nf-step snf irred nf-tail) (reduce-tail _ _ cᵐ₂;c̅ᵐ—→d̅ᵐ) =
      nf-no-step nf-tail cᵐ₂;c̅ᵐ—→d̅ᵐ


mutual

  deterministicᵐ : ∀ {Θ cᵐ d̅ᵐ₁ d̅ᵐ₂}
    → Θ ⊢ᵐ cᵐ —→ d̅ᵐ₁
    → Θ ⊢ᵐ cᵐ —→ d̅ᵐ₂
      --------------------
    → d̅ᵐ₁ ≡ d̅ᵐ₂
  deterministicᵐ id-fun id-fun = refl
  deterministicᵐ id-fun (ξ-fun-dom c̅ᵐ₁—→d̅ᵐ₁) =
    ⊥-elim (nf-no-step nf-empty c̅ᵐ₁—→d̅ᵐ₁)
  deterministicᵐ id-fun (ξ-fun-cod nf₁ c̅ᵐ₂—→d̅ᵐ₂) =
    ⊥-elim (nf-no-step nf-empty c̅ᵐ₂—→d̅ᵐ₂)
  deterministicᵐ id-code id-code = refl
  deterministicᵐ id-code (ξ-code c̅ᵒ—→d̅ᵒ) =
    ⊥-elim (code-nf-no-step OC.nf-empty c̅ᵒ—→d̅ᵒ)
  deterministicᵐ id-code (ξ-code-ec nfᵒ not-blameᵒ c̅ᵉ—→d̅ᵉ) =
    ⊥-elim (ec-nf-no-step ECS.nf-empty c̅ᵉ—→d̅ᵉ)
  deterministicᵐ id-ref id-ref = refl
  deterministicᵐ id-ref (ξ-ref-in c̅ᵐ₁—→d̅ᵐ₁) =
    ⊥-elim (nf-no-step nf-empty c̅ᵐ₁—→d̅ᵐ₁)
  deterministicᵐ id-ref (ξ-ref-out nf₁ c̅ᵐ₂—→d̅ᵐ₂) =
    ⊥-elim (nf-no-step nf-empty c̅ᵐ₂—→d̅ᵐ₂)
  deterministicᵐ id-forall id-forall = refl
  deterministicᵐ id-forall (ξ-forall c̅ᵐ—→d̅ᵐ) =
    ⊥-elim (nf-no-step nf-empty c̅ᵐ—→d̅ᵐ)
  deterministicᵐ id-sub id-sub = refl
  deterministicᵐ id-sub (ξ-sub c̅ᵐ—→d̅ᵐ) =
    ⊥-elim (nf-no-step nf-empty c̅ᵐ—→d̅ᵐ)
  deterministicᵐ (ξ-fun-dom c̅ᵐ₁—→d̅ᵐ₁) id-fun =
    ⊥-elim (nf-no-step nf-empty c̅ᵐ₁—→d̅ᵐ₁)
  deterministicᵐ (ξ-fun-dom c̅ᵐ₁—→d̅ᵐ₁) (ξ-fun-dom c̅ᵐ₁—→d̅ᵐ₂) =
    cong (λ d̅ᵐ → [ d̅ᵐ ⇒ _ ]) (deterministic c̅ᵐ₁—→d̅ᵐ₁ c̅ᵐ₁—→d̅ᵐ₂)
  deterministicᵐ (ξ-fun-dom c̅ᵐ₁—→d̅ᵐ₁) (ξ-fun-cod nf₁ c̅ᵐ₂—→d̅ᵐ₂) =
    ⊥-elim (nf-no-step nf₁ c̅ᵐ₁—→d̅ᵐ₁)
  deterministicᵐ (ξ-fun-cod nf₁ c̅ᵐ₂—→d̅ᵐ₁) id-fun =
    ⊥-elim (nf-no-step nf-empty c̅ᵐ₂—→d̅ᵐ₁)
  deterministicᵐ (ξ-fun-cod nf₁ c̅ᵐ₂—→d̅ᵐ₁) (ξ-fun-dom c̅ᵐ₁—→d̅ᵐ₂) =
    ⊥-elim (nf-no-step nf₁ c̅ᵐ₁—→d̅ᵐ₂)
  deterministicᵐ (ξ-fun-cod nf₁ c̅ᵐ₂—→d̅ᵐ₁) (ξ-fun-cod nf₁′ c̅ᵐ₂—→d̅ᵐ₂) =
    cong (λ d̅ᵐ → [ _ ⇒ d̅ᵐ ]) (deterministic c̅ᵐ₂—→d̅ᵐ₁ c̅ᵐ₂—→d̅ᵐ₂)
  deterministicᵐ (ξ-ref-in c̅ᵐ₁—→d̅ᵐ₁) id-ref =
    ⊥-elim (nf-no-step nf-empty c̅ᵐ₁—→d̅ᵐ₁)
  deterministicᵐ (ξ-ref-in c̅ᵐ₁—→d̅ᵐ₁) (ξ-ref-in c̅ᵐ₁—→d̅ᵐ₂) =
    cong (λ d̅ᵐ → [ Ref_,_ d̅ᵐ _ ]) (deterministic c̅ᵐ₁—→d̅ᵐ₁ c̅ᵐ₁—→d̅ᵐ₂)
  deterministicᵐ (ξ-ref-in c̅ᵐ₁—→d̅ᵐ₁) (ξ-ref-out nf₁ c̅ᵐ₂—→d̅ᵐ₂) =
    ⊥-elim (nf-no-step nf₁ c̅ᵐ₁—→d̅ᵐ₁)
  deterministicᵐ (ξ-ref-out nf₁ c̅ᵐ₂—→d̅ᵐ₁) id-ref =
    ⊥-elim (nf-no-step nf-empty c̅ᵐ₂—→d̅ᵐ₁)
  deterministicᵐ (ξ-ref-out nf₁ c̅ᵐ₂—→d̅ᵐ₁) (ξ-ref-in c̅ᵐ₁—→d̅ᵐ₂) =
    ⊥-elim (nf-no-step nf₁ c̅ᵐ₁—→d̅ᵐ₂)
  deterministicᵐ (ξ-ref-out nf₁ c̅ᵐ₂—→d̅ᵐ₁) (ξ-ref-out nf₁′ c̅ᵐ₂—→d̅ᵐ₂) =
    cong (λ d̅ᵐ → [ Ref_,_ _ d̅ᵐ ]) (deterministic c̅ᵐ₂—→d̅ᵐ₁ c̅ᵐ₂—→d̅ᵐ₂)
  deterministicᵐ (ξ-forall c̅ᵐ—→d̅ᵐ₁) id-forall =
    ⊥-elim (nf-no-step nf-empty c̅ᵐ—→d̅ᵐ₁)
  deterministicᵐ (ξ-forall c̅ᵐ—→d̅ᵐ₁) (ξ-forall c̅ᵐ—→d̅ᵐ₂) =
    cong (λ d̅ᵐ → [ ∀̇ d̅ᵐ ]) (deterministic c̅ᵐ—→d̅ᵐ₁ c̅ᵐ—→d̅ᵐ₂)
  deterministicᵐ (ξ-sub c̅ᵐ—→d̅ᵐ₁) id-sub =
    ⊥-elim (nf-no-step nf-empty c̅ᵐ—→d̅ᵐ₁)
  deterministicᵐ (ξ-sub {e₁ = e₁} {e₂ = e₂} c̅ᵐ—→d̅ᵐ₁) (ξ-sub c̅ᵐ—→d̅ᵐ₂) =
    cong (λ d̅ᵐ → [ e₁ <: e₂ => d̅ᵐ ]) (deterministic c̅ᵐ—→d̅ᵐ₁ c̅ᵐ—→d̅ᵐ₂)
  deterministicᵐ (ξ-code c̅ᵒ—→d̅ᵒ) id-code =
    ⊥-elim (code-nf-no-step OC.nf-empty c̅ᵒ—→d̅ᵒ)
  deterministicᵐ (ξ-code c̅ᵒ—→d̅ᵒ₁) (ξ-code c̅ᵒ—→d̅ᵒ₂) =
    cong (λ d̅ᵒ → [ ‶ d̅ᵒ ″ _ ]) (OCD.deterministic c̅ᵒ—→d̅ᵒ₁ c̅ᵒ—→d̅ᵒ₂)
  deterministicᵐ (ξ-code c̅ᵒ—→d̅ᵒ) (ξ-code-ec nfᵒ not-blameᵒ c̅ᵉ—→d̅ᵉ) =
    ⊥-elim (code-nf-no-step nfᵒ c̅ᵒ—→d̅ᵒ)
  deterministicᵐ (ξ-code c̅ᵒ—→d̅ᵒ) ξ-code-⊥ =
    ⊥-elim (code-nf-no-step (OC.nf-singleton OC.nf-⊥) c̅ᵒ—→d̅ᵒ)
  deterministicᵐ (ξ-code c̅ᵒ—→d̅ᵒ) (ξ-code-ec-⊥ nfᵒ not-blameᵒ) =
    ⊥-elim (code-nf-no-step nfᵒ c̅ᵒ—→d̅ᵒ)
  deterministicᵐ (ξ-code-ec nfᵒ not-blameᵒ c̅ᵉ—→d̅ᵉ) id-code =
    ⊥-elim (ec-nf-no-step ECS.nf-empty c̅ᵉ—→d̅ᵉ)
  deterministicᵐ (ξ-code-ec nfᵒ not-blameᵒ c̅ᵉ—→d̅ᵉ) (ξ-code c̅ᵒ—→d̅ᵒ) =
    ⊥-elim (code-nf-no-step nfᵒ c̅ᵒ—→d̅ᵒ)
  deterministicᵐ (ξ-code-ec nfᵒ not-blameᵒ c̅ᵉ—→d̅ᵉ₁) (ξ-code-ec nfᵒ′ not-blameᵒ′ c̅ᵉ—→d̅ᵉ₂) =
    cong (λ d̅ᵉ → [ ‶ _ ″ d̅ᵉ ]) (ECD.deterministic c̅ᵉ—→d̅ᵉ₁ c̅ᵉ—→d̅ᵉ₂)
  deterministicᵐ (ξ-code-ec nfᵒ not-blameᵒ c̅ᵉ—→d̅ᵉ) ξ-code-⊥ =
    ⊥-elim (not-blameᵒ (_ , refl))
  deterministicᵐ (ξ-code-ec nfᵒ not-blameᵒ c̅ᵉ—→d̅ᵉ) (ξ-code-ec-⊥ nfᵒ′ not-blameᵒ′) =
    ⊥-elim (ec-nf-no-step (ECS.nf-singleton ECS.nf-⊥) c̅ᵉ—→d̅ᵉ)
  deterministicᵐ ξ-code-⊥ (ξ-code c̅ᵒ—→d̅ᵒ) =
    ⊥-elim (code-nf-no-step (OC.nf-singleton OC.nf-⊥) c̅ᵒ—→d̅ᵒ)
  deterministicᵐ ξ-code-⊥ (ξ-code-ec nfᵒ not-blameᵒ c̅ᵉ—→d̅ᵉ) =
    ⊥-elim (not-blameᵒ (_ , refl))
  deterministicᵐ ξ-code-⊥ ξ-code-⊥ = refl
  deterministicᵐ ξ-code-⊥ (ξ-code-ec-⊥ nfᵒ not-blameᵒ) =
    ⊥-elim (not-blameᵒ (_ , refl))
  deterministicᵐ (ξ-code-ec-⊥ nfᵒ not-blameᵒ) (ξ-code c̅ᵒ—→d̅ᵒ) =
    ⊥-elim (code-nf-no-step nfᵒ c̅ᵒ—→d̅ᵒ)
  deterministicᵐ (ξ-code-ec-⊥ nfᵒ not-blameᵒ) (ξ-code-ec nfᵒ′ not-blameᵒ′ c̅ᵉ—→d̅ᵉ) =
    ⊥-elim (ec-nf-no-step (ECS.nf-singleton ECS.nf-⊥) c̅ᵉ—→d̅ᵉ)
  deterministicᵐ (ξ-code-ec-⊥ nfᵒ not-blameᵒ) ξ-code-⊥ =
    ⊥-elim (not-blameᵒ (_ , refl))
  deterministicᵐ (ξ-code-ec-⊥ nfᵒ not-blameᵒ) (ξ-code-ec-⊥ nfᵒ′ not-blameᵒ′) = refl

  deterministic : ∀ {Θ c̅ᵐ d̅ᵐ₁ d̅ᵐ₂}
    → Θ ⊢ᵐ̅ c̅ᵐ —→ d̅ᵐ₁
    → Θ ⊢ᵐ̅ c̅ᵐ —→ d̅ᵐ₂
      ---------------------
    → d̅ᵐ₁ ≡ d̅ᵐ₂
  deterministic (reduce-head cᵐ—→d̅ᵐ₁) (reduce-head cᵐ—→d̅ᵐ₂) =
    cong (λ d̅ᵐ → d̅ᵐ ++ _) (deterministicᵐ cᵐ—→d̅ᵐ₁ cᵐ—→d̅ᵐ₂)
  deterministic (reduce-head cᵐ—→dᵐ) (reduce-neighbors nf cᵐ₁;cᵐ₂⟶dᵐ) =
    ⊥-elim (single-nf-no-step nf cᵐ—→dᵐ)
  deterministic (reduce-head cᵐ—→dᵐ) (reduce-tail nf irred cᵐ₂;c̅ᵐ—→d̅ᵐ) =
    ⊥-elim (single-nf-no-step nf cᵐ—→dᵐ)
  deterministic (reduce-neighbors nf cᵐ₁;cᵐ₂⟶dᵐ) (reduce-head cᵐ—→dᵐ) =
    ⊥-elim (single-nf-no-step nf cᵐ—→dᵐ)
  deterministic (reduce-neighbors nf cᵐ₁;cᵐ₂⟶d̅ᵐ₁) (reduce-neighbors nf′ cᵐ₁;cᵐ₂⟶d̅ᵐ₂) =
    cong (λ d̅ᵐ → d̅ᵐ ++ _) (pair-deterministic cᵐ₁;cᵐ₂⟶d̅ᵐ₁ cᵐ₁;cᵐ₂⟶d̅ᵐ₂)
  deterministic (reduce-neighbors nf cᵐ₁;cᵐ₂⟶dᵐ) (reduce-tail nf′ irred cᵐ₂;c̅ᵐ—→d̅ᵐ) =
    ⊥-elim (irred-no-pair-step irred cᵐ₁;cᵐ₂⟶dᵐ)
  deterministic (reduce-tail nf irred cᵐ₂;c̅ᵐ—→d̅ᵐ) (reduce-head cᵐ—→dᵐ) =
    ⊥-elim (single-nf-no-step nf cᵐ—→dᵐ)
  deterministic (reduce-tail nf irred cᵐ₂;c̅ᵐ—→d̅ᵐ) (reduce-neighbors nf′ cᵐ₁;cᵐ₂⟶dᵐ) =
    ⊥-elim (irred-no-pair-step irred cᵐ₁;cᵐ₂⟶dᵐ)
  deterministic (reduce-tail nf irred cᵐ₂;c̅ᵐ—→d̅ᵐ₁) (reduce-tail nf′ irred′ cᵐ₂;c̅ᵐ—→d̅ᵐ₂) =
    cong (λ d̅ᵐ → _ ; d̅ᵐ) (deterministic cᵐ₂;c̅ᵐ—→d̅ᵐ₁ cᵐ₂;c̅ᵐ—→d̅ᵐ₂)
