module Theories.CoercionSequences.Code.Progress where

open import Data.List using ([])
open import Relation.Binary.PropositionalEquality using (refl)
open import Data.Product using (_,_)
open import Relation.Nullary using (yes; no; ¬_)

open import Theories.CoercionSequences.Code.Definition


data Progressᵒ (cᵒ : OSingleCoercion) : Set where

  stepᵒ : ∀ {d̅ᵒ}
    → ⊢ᵒ cᵒ —→ d̅ᵒ
      ---------------
    → Progressᵒ cᵒ

  doneᵒ
    : SingleNF cᵒ
      ---------------
    → Progressᵒ cᵒ


data PairProgress (cᵒ₁ cᵒ₂ : OSingleCoercion) : Set where

  pair-step : ∀ {d̅ᵒ}
    → ⊢ᵒ cᵒ₁ ; cᵒ₂ ⟶ d̅ᵒ
      ------------------------
    → PairProgress cᵒ₁ cᵒ₂

  pair-done
    : IrredPair cᵒ₁ cᵒ₂
      ------------------------
    → PairProgress cᵒ₁ cᵒ₂


data Progress (c̅ᵒ : OCoercionSeq) : Set where

  step : ∀ {d̅ᵒ}
    → ⊢ᵒ̅ c̅ᵒ —→ d̅ᵒ
      ---------------
    → Progress c̅ᵒ

  done
    : NF c̅ᵒ
      ---------------
    → Progress c̅ᵒ


private
  progressᵒ-fun-not-id : ∀ {c̅ᵒ₁ c̅ᵒ₂}
    → NF c̅ᵒ₁
    → ¬ (IdSeq c̅ᵒ₁)
    → ¬ (BlameSeq c̅ᵒ₁)
    → Progress c̅ᵒ₂
      ---------------------------
    → Progressᵒ (c̅ᵒ₁ ⇒ c̅ᵒ₂)
  progressᵒ-fun-not-id nf not-id not-blame (step c̅ᵒ₂—→d̅ᵒ₂) =
    stepᵒ (ξ-fun-cod nf not-blame c̅ᵒ₂—→d̅ᵒ₂)
  progressᵒ-fun-not-id nf not-id not-blame (done nf-empty) =
    doneᵒ (nf-fun nf nf-empty (λ { (id₁ , _) → not-id id₁ }) not-blame (λ ()))
  progressᵒ-fun-not-id nf not-id not-blame (done (nf-singleton nf-!)) =
    doneᵒ (nf-fun nf (nf-singleton nf-!) (λ { (_ , ()) }) not-blame (λ ()))
  progressᵒ-fun-not-id nf not-id not-blame (done (nf-singleton nf-?)) =
    doneᵒ (nf-fun nf (nf-singleton nf-?) (λ { (_ , ()) }) not-blame (λ ()))
  progressᵒ-fun-not-id nf not-id not-blame (done (nf-singleton nf-⊥)) =
    stepᵒ (ξ-⊥-fun-cod nf not-blame)
  progressᵒ-fun-not-id nf₁ not-id not-blame (done nf₂@(nf-singleton (nf-fun _ _ _ _ _))) =
    doneᵒ (nf-fun nf₁ nf₂ (λ { (_ , ()) }) not-blame (λ ()))
  progressᵒ-fun-not-id nf₁ not-id not-blame (done nf₂@(nf-step _ _ _)) =
    doneᵒ (nf-fun nf₁ nf₂ (λ { (_ , ()) }) not-blame (λ ()))

  progressᵒ-fun-empty-dom : ∀ {c̅ᵒ}
    → Progress c̅ᵒ
      -------------------
    → Progressᵒ ([] ⇒ c̅ᵒ)
  progressᵒ-fun-empty-dom (step c̅ᵒ—→d̅ᵒ) =
    stepᵒ (ξ-fun-cod nf-empty (λ ()) c̅ᵒ—→d̅ᵒ)
  progressᵒ-fun-empty-dom (done nf-empty) =
    stepᵒ id-fun
  progressᵒ-fun-empty-dom (done (nf-singleton nf-!)) =
    doneᵒ (nf-fun nf-empty (nf-singleton nf-!) (λ { (_ , ()) }) (λ ()) (λ ()))
  progressᵒ-fun-empty-dom (done (nf-singleton nf-?)) =
    doneᵒ (nf-fun nf-empty (nf-singleton nf-?) (λ { (_ , ()) }) (λ ()) (λ ()))
  progressᵒ-fun-empty-dom (done (nf-singleton nf-⊥)) =
    stepᵒ (ξ-⊥-fun-cod nf-empty (λ ()))
  progressᵒ-fun-empty-dom (done nf₂@(nf-singleton (nf-fun _ _ _ _ _))) =
    doneᵒ (nf-fun nf-empty nf₂ (λ { (_ , ()) }) (λ ()) (λ ()))
  progressᵒ-fun-empty-dom (done nf₂@(nf-step _ _ _)) =
    doneᵒ (nf-fun nf-empty nf₂ (λ { (_ , ()) }) (λ ()) (λ ()))

  progressᵒ-fun-cod : ∀ {c̅ᵒ₁ c̅ᵒ₂}
    → NF c̅ᵒ₁
    → Progress c̅ᵒ₂
      ---------------------------
    → Progressᵒ (c̅ᵒ₁ ⇒ c̅ᵒ₂)
  progressᵒ-fun-cod nf-empty p =
    progressᵒ-fun-empty-dom p
  progressᵒ-fun-cod (nf-singleton nf-!) p =
    progressᵒ-fun-not-id (nf-singleton nf-!) (λ ()) (λ ()) p
  progressᵒ-fun-cod (nf-singleton nf-?) p =
    progressᵒ-fun-not-id (nf-singleton nf-?) (λ ()) (λ ()) p
  progressᵒ-fun-cod (nf-singleton nf-⊥) _ =
    stepᵒ ξ-⊥-fun-dom
  progressᵒ-fun-cod nf₁@(nf-singleton (nf-fun _ _ _ _ _)) p =
    progressᵒ-fun-not-id nf₁ (λ ()) (λ ()) p
  progressᵒ-fun-cod nf₁@(nf-step _ _ _) p =
    progressᵒ-fun-not-id nf₁ (λ ()) (λ ()) p


pair-progress : ∀ {cᵒ₁ cᵒ₂ C₁ C₂ C₃}
  → SingleNF cᵒ₁
  → ⊢ᵒ cᵒ₁ ⦂ C₁ ⇒ C₂
  → ⊢ᵒ cᵒ₂ ⦂ C₂ ⇒ C₃
    ------------------------
  → PairProgress cᵒ₁ cᵒ₂
pair-progress nf-! (⊢! {Gᵒ = Gᵒ} g) (⊢? {Gᵒ = Hᵒ} ℓ h) with Gᵒ ≡?ᵒ Hᵒ
... | yes refl = pair-step collapse
... | no Gᵒ≢Hᵒ = pair-step (collide Gᵒ≢Hᵒ)
pair-progress nf-! (⊢! g) (⊢⊥ .⋆ C₃ ℓ) =
  pair-step ⊥-right-!
pair-progress nf-? (⊢? ℓ g) (⊢! h) =
  pair-done irred-?!
pair-progress nf-? (⊢? {Gᵒ = ⋆ ⇒ ⋆} ℓ gfun) (⊢fun ⊢c̅ᵒ₁ ⊢c̅ᵒ₂) =
  pair-done irred-?fun
pair-progress nf-? (⊢? ℓ g) (⊢⊥ _ _ ℓ′) =
  pair-done irred-?⊥
pair-progress nf-⊥ (⊢⊥ C₁ C₂ ℓ) ⊢cᵒ₂ =
  pair-step ⊥-left
pair-progress (nf-fun nf₁ nf₂ not-id not-blame₁ not-blame₂) (⊢fun ⊢c̅ᵒ₁ ⊢c̅ᵒ₂) (⊢! gfun) =
  pair-done irred-fun!
pair-progress (nf-fun nf₁ nf₂ not-id not-blame₁ not-blame₂) (⊢fun ⊢c̅ᵒ₁ ⊢c̅ᵒ₂) (⊢fun ⊢d̅ᵒ₁ ⊢d̅ᵒ₂) =
  pair-step seq-fun
pair-progress (nf-fun nf₁ nf₂ not-id not-blame₁ not-blame₂) (⊢fun ⊢c̅ᵒ₁ ⊢c̅ᵒ₂) (⊢⊥ _ _ ℓ) =
  pair-step ⊥-right-fun


mutual

  progressᵒ : ∀ {cᵒ C₁ C₂}
    → ⊢ᵒ cᵒ ⦂ C₁ ⇒ C₂
      ----------------
    → Progressᵒ cᵒ
  progressᵒ (⊢! g) = doneᵒ nf-!
  progressᵒ (⊢? ℓ g) = doneᵒ nf-?
  progressᵒ (⊢⊥ C₁ C₂ ℓ) = doneᵒ nf-⊥
  progressᵒ (⊢fun ⊢c̅ᵒ₁ ⊢c̅ᵒ₂) with progress ⊢c̅ᵒ₁
  ... | step c̅ᵒ₁—→d̅ᵒ₁ = stepᵒ (ξ-fun-dom c̅ᵒ₁—→d̅ᵒ₁)
  ... | done nf₁ = progressᵒ-fun-cod nf₁ (progress ⊢c̅ᵒ₂)

  progress : ∀ {c̅ᵒ C₁ C₂}
    → ⊢ᵒ̅ c̅ᵒ ⦂ C₁ ⇒ C₂
      ------------------------
    → Progress c̅ᵒ
  progress ⊢[] = done nf-empty
  progress (⊢; ⊢cᵒ ⊢[]) with progressᵒ ⊢cᵒ
  ... | stepᵒ cᵒ—→d̅ᵒ = step (reduce-head cᵒ—→d̅ᵒ)
  ... | doneᵒ snf = done (nf-singleton snf)
  progress (⊢; ⊢cᵒ₁ (⊢; ⊢cᵒ₂ ⊢c̅ᵒ)) with progressᵒ ⊢cᵒ₁ | progress (⊢; ⊢cᵒ₂ ⊢c̅ᵒ)
  ... | stepᵒ cᵒ₁—→d̅ᵒ | _ =
    step (reduce-head cᵒ₁—→d̅ᵒ)
  ... | doneᵒ snf₁ | tail-progress with pair-progress snf₁ ⊢cᵒ₁ ⊢cᵒ₂
  ...   | pair-step cᵒ₁;cᵒ₂⟶d̅ᵒ =
    step (reduce-neighbors snf₁ cᵒ₁;cᵒ₂⟶d̅ᵒ)
  ...   | pair-done irred with tail-progress
  ...     | step cᵒ₂;c̅ᵒ—→d̅ᵒ =
    step (reduce-tail snf₁ irred cᵒ₂;c̅ᵒ—→d̅ᵒ)
  ...     | done nf-tail =
    done (nf-step snf₁ irred nf-tail)
