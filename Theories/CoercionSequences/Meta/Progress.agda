module LambdaAlphaRefStar.Theories.CoercionSequences.Meta.Progress where

open import Data.List using ([]; _∷_; [_])
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (refl)
open import Relation.Nullary using (yes; no; ¬_)

import LambdaAlphaRefStar.Theories.CoercionSequences.Code.Definition as OC
import LambdaAlphaRefStar.Theories.CoercionSequences.Code.Progress as OCP
import LambdaAlphaRefStar.Theories.CoercionSequences.EC.Definition as ECS
import LambdaAlphaRefStar.Theories.CoercionSequences.EC.Progress as ECP
open import LambdaAlphaRefStar.Theories.CoercionSequences.Meta.Definition


data Progressᵐ (Θ : SubCtx) (cᵐ : MSingleCoercion) : Set where

  stepᵐ : ∀ {d̅ᵐ}
    → Θ ⊢ᵐ cᵐ —→ d̅ᵐ
      ------------------------
    → Progressᵐ Θ cᵐ

  doneᵐ
    : SingleNF cᵐ
      ------------------------
    → Progressᵐ Θ cᵐ


data PairProgress (Θ : SubCtx) (cᵐ₁ cᵐ₂ : MSingleCoercion) : Set where

  pair-step : ∀ {d̅ᵐ}
    → Θ ⊢ᵐ cᵐ₁ ; cᵐ₂ ⟶ d̅ᵐ
      ------------------------------
    → PairProgress Θ cᵐ₁ cᵐ₂

  pair-done
    : IrredPair cᵐ₁ cᵐ₂
      ------------------------------
    → PairProgress Θ cᵐ₁ cᵐ₂


data Progress (Θ : SubCtx) (c̅ᵐ : MCoercionSeq) : Set where

  step : ∀ {d̅ᵐ}
    → Θ ⊢ᵐ̅ c̅ᵐ —→ d̅ᵐ
      ------------------------
    → Progress Θ c̅ᵐ

  done
    : NF c̅ᵐ
      ------------------
    → Progress Θ c̅ᵐ


private

  nonempty-not-id : ∀ {cᵐ c̅ᵐ}
    → ¬ (IdSeq (cᵐ ; c̅ᵐ))
  nonempty-not-id ()

  nonempty-code-not-id : ∀ {cᵒ c̅ᵒ}
    → ¬ (OC.IdSeq (cᵒ OC.; c̅ᵒ))
  nonempty-code-not-id ()

  nonempty-ec-not-id : ∀ {cᵉ c̅ᵉ}
    → ¬ (ECS.IdSeq (cᵉ ECS.; c̅ᵉ))
  nonempty-ec-not-id ()

  not-both-id-left : ∀ {c̅ᵐ₁ c̅ᵐ₂}
    → ¬ (IdSeq c̅ᵐ₁)
      ------------------------------
    → ¬ (IdSeq c̅ᵐ₁ × IdSeq c̅ᵐ₂)
  not-both-id-left not-id (id₁ , id₂) = not-id id₁

  not-both-id-right : ∀ {c̅ᵐ₁ c̅ᵐ₂}
    → ¬ (IdSeq c̅ᵐ₂)
      ------------------------------
    → ¬ (IdSeq c̅ᵐ₁ × IdSeq c̅ᵐ₂)
  not-both-id-right not-id (id₁ , id₂) = not-id id₂

  not-both-code-id-left : ∀ {c̅ᵒ c̅ᵉ}
    → ¬ (OC.IdSeq c̅ᵒ)
      ------------------------------------
    → ¬ (OC.IdSeq c̅ᵒ × ECS.IdSeq c̅ᵉ)
  not-both-code-id-left not-id (id₁ , id₂) = not-id id₁

  not-both-code-id-right : ∀ {c̅ᵒ c̅ᵉ}
    → ¬ (ECS.IdSeq c̅ᵉ)
      ------------------------------------
    → ¬ (OC.IdSeq c̅ᵒ × ECS.IdSeq c̅ᵉ)
  not-both-code-id-right not-id (id₁ , id₂) = not-id id₂

  progress-fun-done : ∀ {Θ c̅ᵐ₁ c̅ᵐ₂}
    → NF c̅ᵐ₁
    → NF c̅ᵐ₂
      -------------------------------
    → Progressᵐ Θ (c̅ᵐ₁ ⇒ c̅ᵐ₂)
  progress-fun-done nf-empty nf-empty =
    stepᵐ id-fun
  progress-fun-done nf-empty nf₂@(nf-singleton _) =
    doneᵐ (nf-fun nf-empty nf₂ (not-both-id-right nonempty-not-id))
  progress-fun-done nf-empty nf₂@(nf-step _ _ _) =
    doneᵐ (nf-fun nf-empty nf₂ (not-both-id-right nonempty-not-id))
  progress-fun-done nf₁@(nf-singleton _) nf₂ =
    doneᵐ (nf-fun nf₁ nf₂ (not-both-id-left nonempty-not-id))
  progress-fun-done nf₁@(nf-step _ _ _) nf₂ =
    doneᵐ (nf-fun nf₁ nf₂ (not-both-id-left nonempty-not-id))

  progress-ref-done : ∀ {Θ c̅ᵐ₁ c̅ᵐ₂}
    → NF c̅ᵐ₁
    → NF c̅ᵐ₂
      -------------------------------------
    → Progressᵐ Θ (Ref_,_ c̅ᵐ₁ c̅ᵐ₂)
  progress-ref-done nf-empty nf-empty =
    stepᵐ id-ref
  progress-ref-done nf-empty nf₂@(nf-singleton _) =
    doneᵐ (nf-ref nf-empty nf₂ (not-both-id-right nonempty-not-id))
  progress-ref-done nf-empty nf₂@(nf-step _ _ _) =
    doneᵐ (nf-ref nf-empty nf₂ (not-both-id-right nonempty-not-id))
  progress-ref-done nf₁@(nf-singleton _) nf₂ =
    doneᵐ (nf-ref nf₁ nf₂ (not-both-id-left nonempty-not-id))
  progress-ref-done nf₁@(nf-step _ _ _) nf₂ =
    doneᵐ (nf-ref nf₁ nf₂ (not-both-id-left nonempty-not-id))

  progress-forall-done : ∀ {Θ c̅ᵐ}
    → NF c̅ᵐ
      -----------------------
    → Progressᵐ Θ (∀̇ c̅ᵐ)
  progress-forall-done nf-empty =
    stepᵐ id-forall
  progress-forall-done nf@(nf-singleton _) =
    doneᵐ (nf-forall nf nonempty-not-id)
  progress-forall-done nf@(nf-step _ _ _) =
    doneᵐ (nf-forall nf nonempty-not-id)

  progress-sub-done : ∀ {Θ e₁ e₂ c̅ᵐ}
    → NF c̅ᵐ
      ---------------------------------
    → Progressᵐ Θ (e₁ <: e₂ => c̅ᵐ)
  progress-sub-done nf-empty =
    stepᵐ id-sub
  progress-sub-done nf@(nf-singleton _) =
    doneᵐ (nf-sub nf nonempty-not-id)
  progress-sub-done nf@(nf-step _ _ _) =
    doneᵐ (nf-sub nf nonempty-not-id)

  progress-code-done : ∀ {Θ c̅ᵒ c̅ᵉ}
    → OC.NF c̅ᵒ
    → ECS.NF c̅ᵉ
    → ¬ (OC.BlameSeq c̅ᵒ)
    → ¬ (ECS.BlameSeq c̅ᵉ)
      ------------------------------
    → Progressᵐ Θ (‶ c̅ᵒ ″ c̅ᵉ)
  progress-code-done OC.nf-empty ECS.nf-empty not-blameᵒ not-blameᵉ =
    stepᵐ id-code
  progress-code-done OC.nf-empty nfᵉ@(ECS.nf-singleton _) not-blameᵒ not-blameᵉ =
    doneᵐ (nf-code OC.nf-empty nfᵉ (not-both-code-id-right nonempty-ec-not-id) not-blameᵒ not-blameᵉ)
  progress-code-done OC.nf-empty nfᵉ@(ECS.nf-step _ _ _) not-blameᵒ not-blameᵉ =
    doneᵐ (nf-code OC.nf-empty nfᵉ (not-both-code-id-right nonempty-ec-not-id) not-blameᵒ not-blameᵉ)
  progress-code-done nfᵒ@(OC.nf-singleton _) nfᵉ not-blameᵒ not-blameᵉ =
    doneᵐ (nf-code nfᵒ nfᵉ (not-both-code-id-left nonempty-code-not-id) not-blameᵒ not-blameᵉ)
  progress-code-done nfᵒ@(OC.nf-step _ _ _) nfᵉ not-blameᵒ not-blameᵉ =
    doneᵐ (nf-code nfᵒ nfᵉ (not-both-code-id-left nonempty-code-not-id) not-blameᵒ not-blameᵉ)

  progress-code-ec : ∀ {Θ c̅ᵒ c̅ᵉ}
    → OC.NF c̅ᵒ
    → ¬ (OC.BlameSeq c̅ᵒ)
    → ECP.Progress Θ c̅ᵉ
      ------------------------------
    → Progressᵐ Θ (‶ c̅ᵒ ″ c̅ᵉ)
  progress-code-ec nfᵒ not-blameᵒ (ECP.step c̅ᵉ—→d̅ᵉ) =
    stepᵐ (ξ-code-ec nfᵒ not-blameᵒ c̅ᵉ—→d̅ᵉ)
  progress-code-ec {c̅ᵉ = []} nfᵒ not-blameᵒ (ECP.done ECS.nf-empty) =
    progress-code-done nfᵒ ECS.nf-empty not-blameᵒ (λ ())
  progress-code-ec {c̅ᵉ = ECS._！ e ∷ []} nfᵒ not-blameᵒ (ECP.done (ECS.nf-singleton ECS.nf-!)) =
    progress-code-done nfᵒ (ECS.nf-singleton ECS.nf-!) not-blameᵒ (λ ())
  progress-code-ec {c̅ᵉ = ECS._？_ e ℓ ∷ []} nfᵒ not-blameᵒ (ECP.done (ECS.nf-singleton ECS.nf-?)) =
    progress-code-done nfᵒ (ECS.nf-singleton ECS.nf-?) not-blameᵒ (λ ())
  progress-code-ec {c̅ᵉ = ECS._↑_ ê₁ ê₂ ∷ []} nfᵒ not-blameᵒ (ECP.done (ECS.nf-singleton snf)) =
    progress-code-done nfᵒ (ECS.nf-singleton snf) not-blameᵒ (λ ())
  progress-code-ec {c̅ᵉ = ECS.⊥_ ℓ ∷ []} nfᵒ not-blameᵒ (ECP.done (ECS.nf-singleton ECS.nf-⊥)) =
    stepᵐ (ξ-code-ec-⊥ nfᵒ not-blameᵒ)
  progress-code-ec nfᵒ not-blameᵒ (ECP.done nfᵉ@(ECS.nf-step _ _ _)) =
    progress-code-done nfᵒ nfᵉ not-blameᵒ (λ ())


pair-progress : ∀ {Δ Θ cᵐ₁ cᵐ₂ A B C}
  → SingleNF cᵐ₁
  → Δ ; Θ ⊢ᵐ cᵐ₁ ⦂ A ⇒ B
  → Δ ; Θ ⊢ᵐ cᵐ₂ ⦂ B ⇒ C
    ------------------------------
  → PairProgress Θ cᵐ₁ cᵐ₂
pair-progress nf-! (⊢! {G = G} ⊢G g) (⊢? {G = H} ⊢H ℓ h) with G ≡? H
... | yes refl = pair-step collapse
... | no G≢H = pair-step (collide G≢H)
pair-progress nf-! (⊢! ⊢G g) (⊢⊥ _ _ ℓ) =
  pair-step (⊥-right (λ ()) (λ ()))
pair-progress nf-? (⊢? ⊢G ℓ g) (⊢! ⊢G′ h) = pair-done irred-?!
pair-progress nf-? (⊢? {G = .(⋆ ⇒ ⋆)} ⊢G ℓ gfun) (⊢fun ⊢c̅ᵐ₁ ⊢c̅ᵐ₂) =
  pair-done irred-?fun
pair-progress nf-? (⊢? {G = .(‶ OC.⋆ ″ ⋆)} ⊢G ℓ gcode) (⊢code ⊢c̅ᵒ ⊢c̅ᵉ) =
  pair-done irred-?code
pair-progress nf-? (⊢? {G = .(Ref ⋆)} ⊢G ℓ gref) (⊢ref ⊢c̅ᵐ₁ ⊢c̅ᵐ₂) =
  pair-done irred-?ref
pair-progress nf-? (⊢? {G = .(∀̇ ⋆)} ⊢G ℓ gforall) (⊢forall ⊢c̅ᵐ) =
  pair-done irred-?∀
pair-progress nf-? (⊢? {G = .(_ <: _ => ⋆)} ⊢G ℓ gsub) (⊢sub ⊢e₁ ⊢e₂ ⊢c̅ᵐ) =
  pair-done irred-?sub
pair-progress nf-? (⊢? ⊢G ℓ g) (⊢⊥ _ _ ℓ′) =
  pair-done irred-?⊥
pair-progress nf-⊥ (⊢⊥ ⊢A ⊢B ℓ) ⊢cᵐ₂ = pair-step ⊥-left
pair-progress (nf-fun nf₁ nf₂ _) (⊢fun ⊢c̅ᵐ₁ ⊢c̅ᵐ₂) (⊢! ⊢G gfun) =
  pair-done irred-fun!
pair-progress (nf-fun nf₁ nf₂ _) (⊢fun ⊢c̅ᵐ₁ ⊢c̅ᵐ₂) (⊢fun ⊢d̅ᵐ₁ ⊢d̅ᵐ₂) =
  pair-step seq-fun
pair-progress (nf-fun nf₁ nf₂ _) (⊢fun ⊢c̅ᵐ₁ ⊢c̅ᵐ₂) (⊢⊥ _ _ ℓ) =
  pair-step (⊥-right (λ ()) (λ ()))
pair-progress (nf-code nfᵒ nfᵉ _ not-blameᵒ not-blameᵉ) (⊢code ⊢c̅ᵒ ⊢c̅ᵉ) (⊢! ⊢G gcode) =
  pair-done irred-code!
pair-progress (nf-code nfᵒ nfᵉ _ not-blameᵒ not-blameᵉ) (⊢code ⊢c̅ᵒ ⊢c̅ᵉ) (⊢code ⊢d̅ᵒ ⊢d̅ᵉ) =
  pair-step seq-code
pair-progress (nf-code nfᵒ nfᵉ _ not-blameᵒ not-blameᵉ) (⊢code ⊢c̅ᵒ ⊢c̅ᵉ) (⊢⊥ _ _ ℓ) =
  pair-step (⊥-right (λ ()) (λ ()))
pair-progress (nf-ref nf₁ nf₂ _) (⊢ref ⊢c̅ᵐ₁ ⊢c̅ᵐ₂) (⊢! ⊢G gref) =
  pair-done irred-ref!
pair-progress (nf-ref nf₁ nf₂ _) (⊢ref ⊢c̅ᵐ₁ ⊢c̅ᵐ₂) (⊢ref ⊢d̅ᵐ₁ ⊢d̅ᵐ₂) =
  pair-step seq-ref
pair-progress (nf-ref nf₁ nf₂ _) (⊢ref ⊢c̅ᵐ₁ ⊢c̅ᵐ₂) (⊢⊥ _ _ ℓ) =
  pair-step (⊥-right (λ ()) (λ ()))
pair-progress (nf-forall nf _) (⊢forall ⊢c̅ᵐ) (⊢! ⊢G gforall) =
  pair-done irred-∀!
pair-progress (nf-forall nf _) (⊢forall ⊢c̅ᵐ) (⊢forall ⊢d̅ᵐ) =
  pair-step seq-forall
pair-progress (nf-forall nf _) (⊢forall ⊢c̅ᵐ) (⊢⊥ _ _ ℓ) =
  pair-step (⊥-right (λ ()) (λ ()))
pair-progress (nf-sub nf _) (⊢sub ⊢e₁ ⊢e₂ ⊢c̅ᵐ) (⊢! ⊢G gsub) =
  pair-done irred-sub!
pair-progress (nf-sub nf _) (⊢sub ⊢e₁ ⊢e₂ ⊢c̅ᵐ) (⊢sub ⊢e₁′ ⊢e₂′ ⊢d̅ᵐ) =
  pair-step seq-sub
pair-progress (nf-sub nf _) (⊢sub ⊢e₁ ⊢e₂ ⊢c̅ᵐ) (⊢⊥ _ _ ℓ) =
  pair-step (⊥-right (λ ()) (λ ()))


mutual

  progressᵐ : ∀ {Δ Θ cᵐ A B}
    → Δ ; Θ ⊢ᵐ cᵐ ⦂ A ⇒ B
      --------------------
    → Progressᵐ Θ cᵐ
  progressᵐ (⊢! ⊢G g) = doneᵐ nf-!
  progressᵐ (⊢? ⊢G ℓ g) = doneᵐ nf-?
  progressᵐ (⊢⊥ ⊢A ⊢B ℓ) = doneᵐ nf-⊥
  progressᵐ (⊢fun ⊢c̅ᵐ₁ ⊢c̅ᵐ₂) with progress ⊢c̅ᵐ₁
  ... | step c̅ᵐ₁—→d̅ᵐ₁ = stepᵐ (ξ-fun-dom c̅ᵐ₁—→d̅ᵐ₁)
  ... | done nf₁ with progress ⊢c̅ᵐ₂
  ...   | step c̅ᵐ₂—→d̅ᵐ₂ = stepᵐ (ξ-fun-cod nf₁ c̅ᵐ₂—→d̅ᵐ₂)
  ...   | done nf₂ = progress-fun-done nf₁ nf₂
  progressᵐ (⊢code ⊢c̅ᵒ ⊢c̅ᵉ) with OCP.progress ⊢c̅ᵒ
  ... | OCP.step c̅ᵒ—→d̅ᵒ = stepᵐ (ξ-code c̅ᵒ—→d̅ᵒ)
  ... | OCP.done OC.nf-empty =
    progress-code-ec OC.nf-empty (λ ()) (ECP.progress ⊢c̅ᵉ)
  ... | OCP.done (OC.nf-singleton OC.nf-!) =
    progress-code-ec (OC.nf-singleton OC.nf-!) (λ ()) (ECP.progress ⊢c̅ᵉ)
  ... | OCP.done (OC.nf-singleton OC.nf-?) =
    progress-code-ec (OC.nf-singleton OC.nf-?) (λ ()) (ECP.progress ⊢c̅ᵉ)
  ... | OCP.done (OC.nf-singleton OC.nf-⊥) =
    stepᵐ ξ-code-⊥
  ... | OCP.done nfᵒ@(OC.nf-singleton (OC.nf-fun _ _ _ _ _)) =
    progress-code-ec nfᵒ (λ ()) (ECP.progress ⊢c̅ᵉ)
  ... | OCP.done nfᵒ@(OC.nf-step _ _ _) =
    progress-code-ec nfᵒ (λ ()) (ECP.progress ⊢c̅ᵉ)
  progressᵐ (⊢ref ⊢c̅ᵐ₁ ⊢c̅ᵐ₂) with progress ⊢c̅ᵐ₁
  ... | step c̅ᵐ₁—→d̅ᵐ₁ = stepᵐ (ξ-ref-in c̅ᵐ₁—→d̅ᵐ₁)
  ... | done nf₁ with progress ⊢c̅ᵐ₂
  ...   | step c̅ᵐ₂—→d̅ᵐ₂ = stepᵐ (ξ-ref-out nf₁ c̅ᵐ₂—→d̅ᵐ₂)
  ...   | done nf₂ = progress-ref-done nf₁ nf₂
  progressᵐ (⊢forall ⊢c̅ᵐ) with progress ⊢c̅ᵐ
  ... | step c̅ᵐ—→d̅ᵐ = stepᵐ (ξ-forall c̅ᵐ—→d̅ᵐ)
  ... | done nf = progress-forall-done nf
  progressᵐ (⊢sub ⊢e₁ ⊢e₂ ⊢c̅ᵐ) with progress ⊢c̅ᵐ
  ... | step c̅ᵐ—→d̅ᵐ = stepᵐ (ξ-sub c̅ᵐ—→d̅ᵐ)
  ... | done nf = progress-sub-done nf

  progress : ∀ {Δ Θ c̅ᵐ A B}
    → Δ ; Θ ⊢ᵐ̅ c̅ᵐ ⦂ A ⇒ B
      ---------------------------
    → Progress Θ c̅ᵐ
  progress (⊢[] _) = done nf-empty
  progress (⊢; ⊢cᵐ (⊢[] _)) with progressᵐ ⊢cᵐ
  ... | stepᵐ cᵐ—→dᵐ = step (reduce-head cᵐ—→dᵐ)
  ... | doneᵐ snf = done (nf-singleton snf)
  progress (⊢; ⊢cᵐ₁ (⊢; ⊢cᵐ₂ ⊢c̅ᵐ)) with progressᵐ ⊢cᵐ₁ | progress (⊢; ⊢cᵐ₂ ⊢c̅ᵐ)
  ... | stepᵐ cᵐ₁—→dᵐ | _ = step (reduce-head cᵐ₁—→dᵐ)
  ... | doneᵐ snf₁ | tail-progress with pair-progress snf₁ ⊢cᵐ₁ ⊢cᵐ₂
  ...   | pair-step cᵐ₁;cᵐ₂⟶dᵐ = step (reduce-neighbors snf₁ cᵐ₁;cᵐ₂⟶dᵐ)
  ...   | pair-done irred with tail-progress
  ...     | step cᵐ₂;c̅ᵐ—→d̅ᵐ = step (reduce-tail snf₁ irred cᵐ₂;c̅ᵐ—→d̅ᵐ)
  ...     | done nf-tail = done (nf-step snf₁ irred nf-tail)
