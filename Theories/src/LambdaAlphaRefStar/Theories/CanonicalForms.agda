module LambdaAlphaRefStar.Theories.CanonicalForms where

open import Data.List using ([]; _∷_; [_]; _++_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; ∃-syntax) renaming (_,_ to ⟨_,_⟩)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary using (¬_)
open import Relation.Nullary.Negation using (contradiction)

open import Utils using (_∋_⦂_; ⟨_,_,_,_⟩)
open import LambdaAlphaRefStar.Theories.CCAlphaRefStarSyntaxAndTypeSystem
open import LambdaAlphaRefStar.Theories.Values
import LambdaAlphaRefStar.Theories.CoercionSequences.Meta.Definition as MC
open import LambdaAlphaRefStar.Theories.CoercionSequences.Meta.Definition using (Inert)
import LambdaAlphaRefStar.Theories.CoercionSequences.Code.Definition as OC
import LambdaAlphaRefStar.Theories.CoercionSequences.EC.Definition as ECS


data CanonicalFun : MetaTerm → Set where

  fun-ƛ : ∀ {M}
      ---------------------
    → CanonicalFun (ƛ M)

  fun-cast : ∀ {U c d}
    → RawValue U
    → Inert [ c MC.⇒ d ]
      ------------------------------------
    → CanonicalFun (U ⟨ [ c MC.⇒ d ] ⟩)


data CanonicalForall : MetaTerm → Set where

  forall-Λ : ∀ {M}
      ---------------------------
    → CanonicalForall (Λ M)

  forall-cast : ∀ {U c}
    → RawValue U
    → Inert [ MC.∀̇ c ]
      ---------------------------------
    → CanonicalForall (U ⟨ [ MC.∀̇ c ] ⟩)


data CanonicalSub : MetaTerm → Set where

  sub-intro : ∀ {e₁ e₂ M}
      ---------------------------------
    → CanonicalSub (e₁ <: e₂ => M)

  sub-cast : ∀ {U e₁ e₂ c}
    → RawValue U
    → Inert [ e₁ MC.<: e₂ => c ]
      ---------------------------------------
    → CanonicalSub (U ⟨ [ e₁ MC.<: e₂ => c ] ⟩)


data CanonicalRef (Σ : HeapCtx) : MetaTerm → MType → Set where

  ref-addr : ∀ {a A}
    → Σ ∋ a ⦂ A
      ------------------------------
    → CanonicalRef Σ (addr a) A

  ref-cast : ∀ {a A c d}
    → Inert [ MC.Ref c , d ]
      ---------------------------------------------
    → CanonicalRef Σ ((addr a) ⟨ [ MC.Ref c , d ] ⟩) A


data CanonicalCode : MetaTerm → EC → Set where

  code-quote : ∀ {Vᵒ e}
    → CodeValue Vᵒ
      ---------------------------------
    → CanonicalCode (‶ Vᵒ ″ e) e

  code-sub : ∀ {Vᵒ e₁ e}
    → CodeValue Vᵒ
      ------------------------------------------------------------------
    → CanonicalCode ((‶ Vᵒ ″ e₁) ⟨ [ MC.‶ [] ″ [ ECS.ec e₁ ECS.↑ ECS.ec e ] ] ⟩) e


data CanonicalStar : MetaTerm → Set where

  star-inj : ∀ {U c G} {g : Ground G}
    → RawValue U
    → Inert (c ++ [ (G MC.！) g ])
      ---------------------------------------------
    → CanonicalStar (U ⟨ c ++ [ (G MC.！) g ] ⟩)


private

  nf-⋆↑⋆-impossible : ∀ {c̅ᵉ}
    → ¬ ECS.NF ((ECS.⋆ ECS.↑ ECS.⋆) ∷ c̅ᵉ)
  nf-⋆↑⋆-impossible (ECS.nf-singleton (ECS.nf-↑ neq)) = neq refl
  nf-⋆↑⋆-impossible (ECS.nf-step (ECS.nf-↑ neq) _ _) = neq refl

  ec-up-canonical : ∀ {Δ Θ c̅ᵉ e₁ e₂}
    → ECS.NF c̅ᵉ
    → ¬ ECS.IdSeq c̅ᵉ
    → ¬ ECS.BlameSeq c̅ᵉ
    → Δ ECS.; Θ ⊢ᵉ̅ c̅ᵉ ⦂ ECS.ec e₁ ⇒ ECS.ec e₂
      -------------------------------------------------
    → c̅ᵉ ≡ [ ECS.ec e₁ ECS.↑ ECS.ec e₂ ]
  ec-up-canonical ECS.nf-empty not-id not-blame (ECS.⊢[] _) =
    contradiction refl not-id
  ec-up-canonical (ECS.nf-singleton ECS.nf-!) not-id not-blame
    (ECS.⊢; (ECS.⊢! _ _) ())
  ec-up-canonical (ECS.nf-singleton ECS.nf-?) not-id not-blame
    (ECS.⊢; () _)
  ec-up-canonical (ECS.nf-singleton (ECS.nf-↑ _)) not-id not-blame
    (ECS.⊢; (ECS.⊢↑ _ _ _) (ECS.⊢[] _)) =
    refl
  ec-up-canonical (ECS.nf-singleton ECS.nf-⊥) not-id not-blame
    (ECS.⊢; (ECS.⊢⊥ _ _ ℓ) (ECS.⊢[] _)) =
    contradiction ⟨ ℓ , refl ⟩ not-blame
  ec-up-canonical (ECS.nf-step ECS.nf-? ECS.irred-?! nf-tail)
    not-id not-blame (ECS.⊢; () _)
  ec-up-canonical (ECS.nf-step (ECS.nf-↑ _) (ECS.irred-↑! _) nf-tail)
    not-id not-blame (ECS.⊢; (ECS.⊢↑ _ _ _) ⊢tail)
    with ec-up-canonical nf-tail (λ ()) (λ { ⟨ ℓ , () ⟩ }) ⊢tail
  ... | ()
  ec-up-canonical (ECS.nf-step ECS.nf-! ECS.irred-!↑⋆ nf-tail)
    not-id not-blame (ECS.⊢; _ _) =
    contradiction nf-tail nf-⋆↑⋆-impossible
  ec-up-canonical (ECS.nf-step ECS.nf-? ECS.irred-?↑ nf-tail)
    not-id not-blame (ECS.⊢; () _)

  code-id-canonical : ∀ {c̅ᵒ C O S T}
    → OC.NF c̅ᵒ
    → ¬ OC.BlameSeq c̅ᵒ
    → C ↪ᵒ S
    → O ↪ᵒ T
    → OC.⊢ᵒ̅ c̅ᵒ ⦂ C ⇒ O
      -------------------------
    → c̅ᵒ ≡ []
  code-id-canonical OC.nf-empty not-blame C↪S O↪T OC.⊢[] =
    refl
  code-id-canonical (OC.nf-singleton OC.nf-!) not-blame C↪S () (OC.⊢; (OC.⊢! _) OC.⊢[])
  code-id-canonical (OC.nf-singleton OC.nf-?) not-blame () O↪T (OC.⊢; (OC.⊢? _ _) OC.⊢[])
  code-id-canonical (OC.nf-singleton OC.nf-⊥) not-blame C↪S O↪T (OC.⊢; (OC.⊢⊥ _ _ ℓ) OC.⊢[]) =
    contradiction ⟨ ℓ , refl ⟩ not-blame
  code-id-canonical
    (OC.nf-singleton (OC.nf-fun nfc̅ nfd̅ not-both-id not-blame-c not-blame-d))
    not-blame (C₁↪S₁ ⇒ C₂↪S₂) (O₁↪T₁ ⇒ O₂↪T₂)
    (OC.⊢; (OC.⊢fun ⊢c̅ ⊢d̅) OC.⊢[]) =
    contradiction
      ⟨ code-id-canonical nfc̅ not-blame-c O₁↪T₁ C₁↪S₁ ⊢c̅
      , code-id-canonical nfd̅ not-blame-d C₂↪S₂ O₂↪T₂ ⊢d̅
      ⟩
      not-both-id
  code-id-canonical
    (OC.nf-step (OC.nf-fun nfc̅ nfd̅ not-both-id not-blame-c not-blame-d)
      OC.irred-fun! nf-tail)
    not-blame (C₁↪S₁ ⇒ C₂↪S₂) ()
    (OC.⊢; (OC.⊢fun ⊢c̅ ⊢d̅) (OC.⊢; (OC.⊢! OC.gfun) OC.⊢[]))
  code-id-canonical
    (OC.nf-step (OC.nf-fun nfc̅ nfd̅ not-both-id not-blame-c not-blame-d)
      OC.irred-fun! (OC.nf-step OC.nf-! () nf-tail))
    not-blame (C₁↪S₁ ⇒ C₂↪S₂) O↪T
    (OC.⊢; (OC.⊢fun ⊢c̅ ⊢d̅) (OC.⊢; (OC.⊢! OC.gfun) ⊢tail))

  raw-not-star : ∀ {Δ Γ U}
    → RawValue U
      ------------------------------
    → ¬ (Δ ; Γ ⊢ᵐ U ⦂ ⋆)
  raw-not-star U-const ()
  raw-not-star U-addr ()
  raw-not-star U-ƛ ()
  raw-not-star U-Λ ()
  raw-not-star (U-quote _) ()
  raw-not-star U-sub ()

  inj-seq-target≢⋆ : ∀ {Δ Θ A G c̅} {g : Ground G}
    → ¬ (A ≡ ⋆)
    → MC.NF (MC._！ G g ∷ c̅)
      ---------------------------------------------------
    → ¬ (Δ MC.; Θ ⊢ᵐ̅ (MC._！ G g ∷ c̅) ⦂ G ⇒ A)
  inj-seq-target≢⋆ A≢⋆ (MC.nf-singleton MC.nf-!) (MC.⊢; (MC.⊢! _ _) (MC.⊢[] _)) =
    A≢⋆ refl
  inj-seq-target≢⋆ A≢⋆ (MC.nf-step MC.nf-! () _) (MC.⊢; _ _)

  multi-target≢⋆ : ∀ {Δ Θ Γᵒ Γᵐ Σ A S X U c₁ c₂ c̅}
    → RawValue U
    → Δ ; ⟨ Θ , Γᵒ , Γᵐ , Σ ⟩ ⊢ᵐ U ⦂ S
    → ¬ (A ≡ ⋆)
    → MC.SingleNF c₁
    → MC.IrredPair c₁ c₂
    → MC.NF (c₂ ∷ c̅)
    → Δ MC.; Θ ⊢ᵐ c₁ ⦂ S ⇒ X
      ---------------------------------------------------
    → ¬ (Δ MC.; Θ ⊢ᵐ̅ (c₂ ∷ c̅) ⦂ X ⇒ A)
  multi-target≢⋆ u ⊢U A≢⋆ MC.nf-? MC.irred-?! nfTail (MC.⊢? _ _ _) ⊢tail =
    contradiction ⊢U (raw-not-star u)
  multi-target≢⋆ u ⊢U A≢⋆ MC.nf-? MC.irred-?⊥ nfTail (MC.⊢? _ _ _) ⊢tail =
    contradiction ⊢U (raw-not-star u)
  multi-target≢⋆ u ⊢U A≢⋆ MC.nf-? MC.irred-?fun nfTail (MC.⊢? _ _ _) ⊢tail =
    contradiction ⊢U (raw-not-star u)
  multi-target≢⋆ u ⊢U A≢⋆ (MC.nf-fun _ _ _) MC.irred-fun! nfTail (MC.⊢fun _ _) ⊢tail@(MC.⊢; (MC.⊢! _ _) _) =
    inj-seq-target≢⋆ {G = ⋆ ⇒ ⋆} {g = MC.gfun} A≢⋆ nfTail ⊢tail
  multi-target≢⋆ u ⊢U A≢⋆ MC.nf-? MC.irred-?code nfTail (MC.⊢? _ _ _) ⊢tail =
    contradiction ⊢U (raw-not-star u)
  multi-target≢⋆ u ⊢U A≢⋆ (MC.nf-code _ _ _ _ _) MC.irred-code! nfTail (MC.⊢code _ _) ⊢tail@(MC.⊢; (MC.⊢! _ _) _) =
    inj-seq-target≢⋆ {G = ‶ ⋆ ″ ⋆} {g = MC.gcode} A≢⋆ nfTail ⊢tail
  multi-target≢⋆ u ⊢U A≢⋆ MC.nf-? MC.irred-?ref nfTail (MC.⊢? _ _ _) ⊢tail =
    contradiction ⊢U (raw-not-star u)
  multi-target≢⋆ u ⊢U A≢⋆ (MC.nf-ref _ _ _) MC.irred-ref! nfTail (MC.⊢ref _ _) ⊢tail@(MC.⊢; (MC.⊢! _ _) _) =
    inj-seq-target≢⋆ {G = Ref ⋆} {g = MC.gref} A≢⋆ nfTail ⊢tail
  multi-target≢⋆ u ⊢U A≢⋆ MC.nf-? MC.irred-?∀ nfTail (MC.⊢? _ _ _) ⊢tail =
    contradiction ⊢U (raw-not-star u)
  multi-target≢⋆ u ⊢U A≢⋆ (MC.nf-forall _ _) MC.irred-∀! nfTail (MC.⊢forall _) ⊢tail@(MC.⊢; (MC.⊢! _ _) _) =
    inj-seq-target≢⋆ {G = ∀̇ ⋆} {g = MC.gforall} A≢⋆ nfTail ⊢tail
  multi-target≢⋆ u ⊢U A≢⋆ MC.nf-? MC.irred-?sub nfTail (MC.⊢? _ _ _) ⊢tail =
    contradiction ⊢U (raw-not-star u)
  multi-target≢⋆ u ⊢U A≢⋆ (MC.nf-sub _ _) (MC.irred-sub! {e₁ = e₁} {e₂ = e₂}) nfTail (MC.⊢sub _ _ _) ⊢tail@(MC.⊢; (MC.⊢! _ _) _) =
    inj-seq-target≢⋆ {G = e₁ <: e₂ => ⋆} {g = MC.gsub} A≢⋆ nfTail ⊢tail

  canonical-fun-cast : ∀ {Δ Θ Γᵒ Γᵐ Σ A B S U c}
    → RawValue U
    → Δ ; ⟨ Θ , Γᵒ , Γᵐ , Σ ⟩ ⊢ᵐ U ⦂ S
    → MC.NF c
    → ¬ MC.IdSeq c
    → ¬ MC.BlameSeq c
    → Δ MC.; Θ ⊢ᵐ̅ c ⦂ S ⇒ (A ⇒ B)
      -----------------------------------------------------
    → CanonicalFun (U ⟨ c ⟩)
  canonical-fun-cast u ⊢U MC.nf-empty not-id not-blame (MC.⊢[] _) =
    contradiction refl not-id
  canonical-fun-cast u ⊢U (MC.nf-singleton MC.nf-!) not-id not-blame (MC.⊢; (MC.⊢! _ _) ())
  canonical-fun-cast u ⊢U (MC.nf-singleton MC.nf-?) not-id not-blame (MC.⊢; (MC.⊢? _ _ MC.gfun) (MC.⊢[] _)) =
    contradiction ⊢U (raw-not-star u)
  canonical-fun-cast u ⊢U nf@(MC.nf-singleton (MC.nf-fun _ _ _)) not-id not-blame (MC.⊢; (MC.⊢fun _ _) (MC.⊢[] _)) =
    fun-cast u ⟨ nf , ⟨ not-id , not-blame ⟩ ⟩
  canonical-fun-cast u ⊢U (MC.nf-singleton MC.nf-⊥) not-id not-blame (MC.⊢; (MC.⊢⊥ _ _ ℓ) (MC.⊢[] _)) =
    contradiction ⟨ ℓ , refl ⟩ not-blame
  canonical-fun-cast u ⊢U (MC.nf-singleton (MC.nf-code _ _ _ _ _)) not-id not-blame (MC.⊢; (MC.⊢code _ _) ())
  canonical-fun-cast u ⊢U (MC.nf-singleton (MC.nf-ref _ _ _)) not-id not-blame (MC.⊢; (MC.⊢ref _ _) ())
  canonical-fun-cast u ⊢U (MC.nf-singleton (MC.nf-forall _ _)) not-id not-blame (MC.⊢; (MC.⊢forall _) ())
  canonical-fun-cast u ⊢U (MC.nf-singleton (MC.nf-sub _ _)) not-id not-blame (MC.⊢; (MC.⊢sub _ _ _) ())
  canonical-fun-cast u ⊢U (MC.nf-step nf ir nfTail) not-id not-blame (MC.⊢; ⊢c ⊢tail) =
    contradiction ⊢tail (multi-target≢⋆ u ⊢U (λ ()) nf ir nfTail ⊢c)

  canonical-forall-cast : ∀ {Δ Θ Γᵒ Γᵐ Σ A S U c}
    → RawValue U
    → Δ ; ⟨ Θ , Γᵒ , Γᵐ , Σ ⟩ ⊢ᵐ U ⦂ S
    → MC.NF c
    → ¬ MC.IdSeq c
    → ¬ MC.BlameSeq c
    → Δ MC.; Θ ⊢ᵐ̅ c ⦂ S ⇒ ∀̇ A
      -----------------------------------------------------
    → CanonicalForall (U ⟨ c ⟩)
  canonical-forall-cast u ⊢U MC.nf-empty not-id not-blame (MC.⊢[] _) =
    contradiction refl not-id
  canonical-forall-cast u ⊢U (MC.nf-singleton MC.nf-!) not-id not-blame (MC.⊢; (MC.⊢! _ _) ())
  canonical-forall-cast u ⊢U (MC.nf-singleton MC.nf-?) not-id not-blame (MC.⊢; (MC.⊢? _ _ MC.gforall) (MC.⊢[] _)) =
    contradiction ⊢U (raw-not-star u)
  canonical-forall-cast u ⊢U nf@(MC.nf-singleton (MC.nf-forall _ _)) not-id not-blame (MC.⊢; (MC.⊢forall _) (MC.⊢[] _)) =
    forall-cast u ⟨ nf , ⟨ not-id , not-blame ⟩ ⟩
  canonical-forall-cast u ⊢U (MC.nf-singleton MC.nf-⊥) not-id not-blame (MC.⊢; (MC.⊢⊥ _ _ ℓ) (MC.⊢[] _)) =
    contradiction ⟨ ℓ , refl ⟩ not-blame
  canonical-forall-cast u ⊢U (MC.nf-singleton (MC.nf-fun _ _ _)) not-id not-blame (MC.⊢; (MC.⊢fun _ _) ())
  canonical-forall-cast u ⊢U (MC.nf-singleton (MC.nf-code _ _ _ _ _)) not-id not-blame (MC.⊢; (MC.⊢code _ _) ())
  canonical-forall-cast u ⊢U (MC.nf-singleton (MC.nf-ref _ _ _)) not-id not-blame (MC.⊢; (MC.⊢ref _ _) ())
  canonical-forall-cast u ⊢U (MC.nf-singleton (MC.nf-sub _ _)) not-id not-blame (MC.⊢; (MC.⊢sub _ _ _) ())
  canonical-forall-cast u ⊢U (MC.nf-step nf ir nfTail) not-id not-blame (MC.⊢; ⊢c ⊢tail) =
    contradiction ⊢tail (multi-target≢⋆ u ⊢U (λ ()) nf ir nfTail ⊢c)

  canonical-sub-cast : ∀ {Δ Θ Γᵒ Γᵐ Σ A S U c e₁ e₂}
    → RawValue U
    → Δ ; ⟨ Θ , Γᵒ , Γᵐ , Σ ⟩ ⊢ᵐ U ⦂ S
    → MC.NF c
    → ¬ MC.IdSeq c
    → ¬ MC.BlameSeq c
    → Δ MC.; Θ ⊢ᵐ̅ c ⦂ S ⇒ (e₁ <: e₂ => A)
      -----------------------------------------------------
    → CanonicalSub (U ⟨ c ⟩)
  canonical-sub-cast u ⊢U MC.nf-empty not-id not-blame (MC.⊢[] _) =
    contradiction refl not-id
  canonical-sub-cast u ⊢U (MC.nf-singleton MC.nf-!) not-id not-blame (MC.⊢; (MC.⊢! _ _) ())
  canonical-sub-cast u ⊢U (MC.nf-singleton MC.nf-?) not-id not-blame (MC.⊢; (MC.⊢? _ _ MC.gsub) (MC.⊢[] _)) =
    contradiction ⊢U (raw-not-star u)
  canonical-sub-cast u ⊢U nf@(MC.nf-singleton (MC.nf-sub _ _)) not-id not-blame (MC.⊢; (MC.⊢sub _ _ _) (MC.⊢[] _)) =
    sub-cast u ⟨ nf , ⟨ not-id , not-blame ⟩ ⟩
  canonical-sub-cast u ⊢U (MC.nf-singleton MC.nf-⊥) not-id not-blame (MC.⊢; (MC.⊢⊥ _ _ ℓ) (MC.⊢[] _)) =
    contradiction ⟨ ℓ , refl ⟩ not-blame
  canonical-sub-cast u ⊢U (MC.nf-singleton (MC.nf-fun _ _ _)) not-id not-blame (MC.⊢; (MC.⊢fun _ _) ())
  canonical-sub-cast u ⊢U (MC.nf-singleton (MC.nf-code _ _ _ _ _)) not-id not-blame (MC.⊢; (MC.⊢code _ _) ())
  canonical-sub-cast u ⊢U (MC.nf-singleton (MC.nf-ref _ _ _)) not-id not-blame (MC.⊢; (MC.⊢ref _ _) ())
  canonical-sub-cast u ⊢U (MC.nf-singleton (MC.nf-forall _ _)) not-id not-blame (MC.⊢; (MC.⊢forall _) ())
  canonical-sub-cast u ⊢U (MC.nf-step nf ir nfTail) not-id not-blame (MC.⊢; ⊢c ⊢tail) =
    contradiction ⊢tail (multi-target≢⋆ u ⊢U (λ ()) nf ir nfTail ⊢c)

  canonical-ref-cast : ∀ {Δ Θ Γᵒ Γᵐ Σ A S U c}
    → RawValue U
    → Δ ; ⟨ Θ , Γᵒ , Γᵐ , Σ ⟩ ⊢ᵐ U ⦂ S
    → MC.NF c
    → ¬ MC.IdSeq c
    → ¬ MC.BlameSeq c
    → Δ MC.; Θ ⊢ᵐ̅ c ⦂ S ⇒ Ref A
      -----------------------------------------------------
    → CanonicalRef Σ (U ⟨ c ⟩) A
  canonical-ref-cast u ⊢U MC.nf-empty not-id not-blame (MC.⊢[] _) =
    contradiction refl not-id
  canonical-ref-cast u ⊢U (MC.nf-singleton MC.nf-!) not-id not-blame (MC.⊢; (MC.⊢! _ _) ())
  canonical-ref-cast u ⊢U (MC.nf-singleton MC.nf-?) not-id not-blame (MC.⊢; (MC.⊢? _ _ MC.gref) (MC.⊢[] _)) =
    contradiction ⊢U (raw-not-star u)
  canonical-ref-cast U-addr (⊢addr _) nf@(MC.nf-singleton (MC.nf-ref _ _ _)) not-id not-blame (MC.⊢; (MC.⊢ref _ _) (MC.⊢[] _)) =
    ref-cast ⟨ nf , ⟨ not-id , not-blame ⟩ ⟩
  canonical-ref-cast u ⊢U (MC.nf-singleton MC.nf-⊥) not-id not-blame (MC.⊢; (MC.⊢⊥ _ _ ℓ) (MC.⊢[] _)) =
    contradiction ⟨ ℓ , refl ⟩ not-blame
  canonical-ref-cast u ⊢U (MC.nf-singleton (MC.nf-fun _ _ _)) not-id not-blame (MC.⊢; (MC.⊢fun _ _) ())
  canonical-ref-cast u ⊢U (MC.nf-singleton (MC.nf-code _ _ _ _ _)) not-id not-blame (MC.⊢; (MC.⊢code _ _) ())
  canonical-ref-cast u ⊢U (MC.nf-singleton (MC.nf-forall _ _)) not-id not-blame (MC.⊢; (MC.⊢forall _) ())
  canonical-ref-cast u ⊢U (MC.nf-singleton (MC.nf-sub _ _)) not-id not-blame (MC.⊢; (MC.⊢sub _ _ _) ())
  canonical-ref-cast u ⊢U (MC.nf-step nf ir nfTail) not-id not-blame (MC.⊢; ⊢c ⊢tail) =
    contradiction ⊢tail (multi-target≢⋆ u ⊢U (λ ()) nf ir nfTail ⊢c)

  canonical-star-cast : ∀ {Δ Θ Γᵒ Γᵐ Σ S U c}
    → RawValue U
    → Δ ; ⟨ Θ , Γᵒ , Γᵐ , Σ ⟩ ⊢ᵐ U ⦂ S
    → MC.NF c
    → ¬ MC.IdSeq c
    → ¬ MC.BlameSeq c
    → Δ MC.; Θ ⊢ᵐ̅ c ⦂ S ⇒ ⋆
      -----------------------------------------------------
    → CanonicalStar (U ⟨ c ⟩)
  canonical-star-cast u ⊢U MC.nf-empty not-id not-blame (MC.⊢[] _) =
    contradiction refl not-id
  canonical-star-cast u ⊢U nf@(MC.nf-singleton MC.nf-!) not-id not-blame (MC.⊢; (MC.⊢! _ _) (MC.⊢[] _)) =
    star-inj {c = []} u ⟨ nf , ⟨ not-id , not-blame ⟩ ⟩
  canonical-star-cast u ⊢U (MC.nf-singleton MC.nf-?) not-id not-blame (MC.⊢; (MC.⊢? _ _ _) _) =
    contradiction ⊢U (raw-not-star u)
  canonical-star-cast u ⊢U (MC.nf-singleton MC.nf-⊥) not-id not-blame (MC.⊢; (MC.⊢⊥ _ _ ℓ) (MC.⊢[] _)) =
    contradiction ⟨ ℓ , refl ⟩ not-blame
  canonical-star-cast u ⊢U (MC.nf-singleton (MC.nf-fun _ _ _)) not-id not-blame (MC.⊢; (MC.⊢fun _ _) ())
  canonical-star-cast u ⊢U (MC.nf-singleton (MC.nf-code _ _ _ _ _)) not-id not-blame (MC.⊢; (MC.⊢code _ _) ())
  canonical-star-cast u ⊢U (MC.nf-singleton (MC.nf-ref _ _ _)) not-id not-blame (MC.⊢; (MC.⊢ref _ _) ())
  canonical-star-cast u ⊢U (MC.nf-singleton (MC.nf-forall _ _)) not-id not-blame (MC.⊢; (MC.⊢forall _) ())
  canonical-star-cast u ⊢U (MC.nf-singleton (MC.nf-sub _ _)) not-id not-blame (MC.⊢; (MC.⊢sub _ _ _) ())
  canonical-star-cast u ⊢U (MC.nf-step MC.nf-? MC.irred-?! nfTail) not-id not-blame (MC.⊢; (MC.⊢? _ _ _) _) =
    contradiction ⊢U (raw-not-star u)
  canonical-star-cast u ⊢U (MC.nf-step MC.nf-? MC.irred-?⊥ nfTail) not-id not-blame (MC.⊢; (MC.⊢? _ _ _) _) =
    contradiction ⊢U (raw-not-star u)
  canonical-star-cast u ⊢U (MC.nf-step MC.nf-? MC.irred-?fun nfTail) not-id not-blame (MC.⊢; (MC.⊢? _ _ _) _) =
    contradiction ⊢U (raw-not-star u)
  canonical-star-cast u ⊢U (MC.nf-step MC.nf-? MC.irred-?code nfTail) not-id not-blame (MC.⊢; (MC.⊢? _ _ _) _) =
    contradiction ⊢U (raw-not-star u)
  canonical-star-cast u ⊢U (MC.nf-step MC.nf-? MC.irred-?ref nfTail) not-id not-blame (MC.⊢; (MC.⊢? _ _ _) _) =
    contradiction ⊢U (raw-not-star u)
  canonical-star-cast u ⊢U (MC.nf-step MC.nf-? MC.irred-?∀ nfTail) not-id not-blame (MC.⊢; (MC.⊢? _ _ _) _) =
    contradiction ⊢U (raw-not-star u)
  canonical-star-cast u ⊢U (MC.nf-step MC.nf-? MC.irred-?sub nfTail) not-id not-blame (MC.⊢; (MC.⊢? _ _ _) _) =
    contradiction ⊢U (raw-not-star u)
  canonical-star-cast u ⊢U nf@(MC.nf-step (MC.nf-fun _ _ _) MC.irred-fun! (MC.nf-singleton MC.nf-!))
    not-id not-blame (MC.⊢; (MC.⊢fun _ _) (MC.⊢; (MC.⊢! _ MC.gfun) (MC.⊢[] _))) =
    star-inj {c = [ _ ]} {g = MC.gfun} u ⟨ nf , ⟨ not-id , not-blame ⟩ ⟩
  canonical-star-cast u ⊢U nf@(MC.nf-step (MC.nf-code _ _ _ _ _) MC.irred-code! (MC.nf-singleton MC.nf-!))
    not-id not-blame (MC.⊢; (MC.⊢code _ _) (MC.⊢; (MC.⊢! _ MC.gcode) (MC.⊢[] _))) =
    star-inj {c = [ _ ]} {g = MC.gcode} u ⟨ nf , ⟨ not-id , not-blame ⟩ ⟩
  canonical-star-cast u ⊢U nf@(MC.nf-step (MC.nf-ref _ _ _) MC.irred-ref! (MC.nf-singleton MC.nf-!))
    not-id not-blame (MC.⊢; (MC.⊢ref _ _) (MC.⊢; (MC.⊢! _ MC.gref) (MC.⊢[] _))) =
    star-inj {c = [ _ ]} {g = MC.gref} u ⟨ nf , ⟨ not-id , not-blame ⟩ ⟩
  canonical-star-cast u ⊢U nf@(MC.nf-step (MC.nf-forall _ _) MC.irred-∀! (MC.nf-singleton MC.nf-!))
    not-id not-blame (MC.⊢; (MC.⊢forall _) (MC.⊢; (MC.⊢! _ MC.gforall) (MC.⊢[] _))) =
    star-inj {c = [ _ ]} {g = MC.gforall} u ⟨ nf , ⟨ not-id , not-blame ⟩ ⟩
  canonical-star-cast u ⊢U nf@(MC.nf-step (MC.nf-sub _ _) MC.irred-sub! (MC.nf-singleton MC.nf-!))
    not-id not-blame (MC.⊢; (MC.⊢sub _ _ _) (MC.⊢; (MC.⊢! _ MC.gsub) (MC.⊢[] _))) =
    star-inj {c = [ _ ]} {g = MC.gsub} u ⟨ nf , ⟨ not-id , not-blame ⟩ ⟩

  canonical-code-cast : ∀ {Δ Θ Γᵒ Γᵐ Σ S O T e U c}
    → RawValue U
    → Δ ; ⟨ Θ , Γᵒ , Γᵐ , Σ ⟩ ⊢ᵐ U ⦂ S
    → MC.NF c
    → ¬ MC.IdSeq c
    → ¬ MC.BlameSeq c
    → Δ MC.; Θ ⊢ᵐ̅ c ⦂ S ⇒ (‶ O ″ ec e)
    → O ↪ᵒ T
      -----------------------------------------------------
    → CanonicalCode (U ⟨ c ⟩) e
  canonical-code-cast u ⊢U MC.nf-empty not-id not-blame (MC.⊢[] _) O↪T =
    contradiction refl not-id
  canonical-code-cast u ⊢U (MC.nf-singleton MC.nf-!) not-id not-blame (MC.⊢; (MC.⊢! _ _) ()) O↪T
  canonical-code-cast u ⊢U (MC.nf-singleton MC.nf-?) not-id not-blame (MC.⊢; (MC.⊢? _ _ MC.gcode) ()) O↪T
  canonical-code-cast u ⊢U (MC.nf-singleton MC.nf-⊥) not-id not-blame (MC.⊢; (MC.⊢⊥ _ _ ℓ) (MC.⊢[] _)) O↪T =
    contradiction ⟨ ℓ , refl ⟩ not-blame
  canonical-code-cast u ⊢U (MC.nf-singleton (MC.nf-fun _ _ _)) not-id not-blame (MC.⊢; (MC.⊢fun _ _) ()) O↪T
  canonical-code-cast U-const () (MC.nf-singleton (MC.nf-code _ _ _ _ _)) not-id not-blame (MC.⊢; (MC.⊢code _ _) (MC.⊢[] _)) O↪T
  canonical-code-cast U-addr () (MC.nf-singleton (MC.nf-code _ _ _ _ _)) not-id not-blame (MC.⊢; (MC.⊢code _ _) (MC.⊢[] _)) O↪T
  canonical-code-cast U-ƛ () (MC.nf-singleton (MC.nf-code _ _ _ _ _)) not-id not-blame (MC.⊢; (MC.⊢code _ _) (MC.⊢[] _)) O↪T
  canonical-code-cast U-Λ () (MC.nf-singleton (MC.nf-code _ _ _ _ _)) not-id not-blame (MC.⊢; (MC.⊢code _ _) (MC.⊢[] _)) O↪T
  canonical-code-cast (U-quote vᵒ) (⊢quote ⊢Vᵒ ⊢e C↪S)
    (MC.nf-singleton (MC.nf-code nfᵒ nfᵉ not-both-id not-blameᵒ not-blameᵉ))
    not-id not-blame (MC.⊢; (MC.⊢code ⊢c̅ᵒ ⊢c̅ᵉ) (MC.⊢[] _)) O↪T
    with code-id-canonical nfᵒ not-blameᵒ C↪S O↪T ⊢c̅ᵒ
  ... | refl
    with ec-up-canonical nfᵉ (λ cᵉ-id → not-both-id ⟨ refl , cᵉ-id ⟩) not-blameᵉ ⊢c̅ᵉ
  ...   | refl = code-sub vᵒ
  canonical-code-cast U-sub () (MC.nf-singleton (MC.nf-code _ _ _ _ _)) not-id not-blame (MC.⊢; (MC.⊢code _ _) (MC.⊢[] _)) O↪T
  canonical-code-cast u ⊢U (MC.nf-singleton (MC.nf-ref _ _ _)) not-id not-blame (MC.⊢; (MC.⊢ref _ _) ()) O↪T
  canonical-code-cast u ⊢U (MC.nf-singleton (MC.nf-forall _ _)) not-id not-blame (MC.⊢; (MC.⊢forall _) ()) O↪T
  canonical-code-cast u ⊢U (MC.nf-singleton (MC.nf-sub _ _)) not-id not-blame (MC.⊢; (MC.⊢sub _ _ _) ()) O↪T
  canonical-code-cast u ⊢U (MC.nf-step nf ir nfTail) not-id not-blame (MC.⊢; ⊢c ⊢tail) O↪T =
    contradiction ⊢tail (multi-target≢⋆ u ⊢U (λ ()) nf ir nfTail ⊢c)


canonical-fun : ∀ {Δ Γ A B V}
  → Value V
  → Δ ; Γ ⊢ᵐ V ⦂ A ⇒ B
    --------------------
  → CanonicalFun V
canonical-fun (V-raw U-ƛ) (⊢lamᵐ _ _) = fun-ƛ
canonical-fun (V-cast u ⟨ nf , ⟨ not-id , not-blame ⟩ ⟩) (⊢cast ⊢U ⊢c) =
  canonical-fun-cast u ⊢U nf not-id not-blame ⊢c

canonical-forall : ∀ {Δ Γ A V}
  → Value V
  → Δ ; Γ ⊢ᵐ V ⦂ ∀̇ A
    --------------------
  → CanonicalForall V
canonical-forall (V-raw U-Λ) (⊢eclam _) = forall-Λ
canonical-forall (V-cast u ⟨ nf , ⟨ not-id , not-blame ⟩ ⟩) (⊢cast ⊢U ⊢c) =
  canonical-forall-cast u ⊢U nf not-id not-blame ⊢c

canonical-sub : ∀ {Δ Γ e₁ e₂ A V}
  → Value V
  → Δ ; Γ ⊢ᵐ V ⦂ e₁ <: e₂ => A
    --------------------
  → CanonicalSub V
canonical-sub (V-raw U-sub) (⊢subintro _ _ _) = sub-intro
canonical-sub (V-cast u ⟨ nf , ⟨ not-id , not-blame ⟩ ⟩) (⊢cast ⊢U ⊢c) =
  canonical-sub-cast u ⊢U nf not-id not-blame ⊢c

canonical-ref : ∀ {Δ Θ Γᵒ Γᵐ Σ A V}
  → Value V
  → Δ ; ⟨ Θ , Γᵒ , Γᵐ , Σ ⟩ ⊢ᵐ V ⦂ Ref A
    --------------------
  → CanonicalRef Σ V A
canonical-ref (V-raw U-addr) (⊢addr lookup) = ref-addr lookup
canonical-ref (V-cast u ⟨ nf , ⟨ not-id , not-blame ⟩ ⟩) (⊢cast ⊢U ⊢c) =
  canonical-ref-cast u ⊢U nf not-id not-blame ⊢c

canonical-code : ∀ {Δ Γ O T e V}
  → Value V
  → Δ ; Γ ⊢ᵐ V ⦂ (‶ O ″ ec e)
  → O ↪ᵒ T
    ---------------------------
  → CanonicalCode V e
canonical-code (V-raw (U-quote vᵒ)) (⊢quote _ _ _) O↪T =
  code-quote vᵒ
canonical-code (V-cast u ⟨ nf , ⟨ not-id , not-blame ⟩ ⟩) (⊢cast ⊢U ⊢c) O↪T =
  canonical-code-cast u ⊢U nf not-id not-blame ⊢c O↪T

obs : MetaTerm → Maybe CodeTerm
obs (‶ Vᵒ ″ e)         = just Vᵒ
obs ((‶ Vᵒ ″ e) ⟨ c ⟩) = just Vᵒ
obs                  _ = nothing

private
  obs-code-canonical : ∀ {Δ Θ Γᵒ Σ V O T}
    → CanonicalCode V ε
    → Δ ; ⟨ Θ , Γᵒ , [] , Σ ⟩ ⊢ᵐ V ⦂ ‶ O ″ ec ε
    → O ↪ᵒ T
      ------------------------------------------------------------------------------------
    → ∃[ Vᵒ ] obs V ≡ just Vᵒ × CodeValue Vᵒ × Δ ; ⟨ Θ , Γᵒ , [] , Σ ⟩ ; ε ⊢ᵒ Vᵒ ⦂ T
  obs-code-canonical (code-quote vᵒ) (⊢quote ⊢Vᵒ ⊢e O↪T₁) O↪T₂
    rewrite ↪ᵒ-unique O↪T₁ O↪T₂ =
    ⟨ _ , refl , vᵒ , ⊢Vᵒ ⟩
  obs-code-canonical (code-sub vᵒ)
    (⊢cast (⊢quote ⊢Vᵒ ⊢e O↪T₁)
      (MC.⊢;
        (MC.⊢code
          OC.⊢[]
          (ECS.⊢; (ECS.⊢↑ _ _ (<:-ec e₁<:ε)) (ECS.⊢[] _)))
        (MC.⊢[] _)))
    O↪T₂
    rewrite ↪ᵒ-unique O↪T₁ O↪T₂ =
    ⟨ _ , refl , vᵒ , codevalue-weaken-ec ⊢Vᵒ vᵒ e₁<:ε ⟩

obs-code : ∀ {Δ Θ Γᵒ Σ V O T}
  → Value V
  → Δ ; ⟨ Θ , Γᵒ , [] , Σ ⟩ ⊢ᵐ V ⦂ ‶ O ″ ec ε
  → O ↪ᵒ T
    ------------------------------------------------------------------------------------
  → ∃[ Vᵒ ] obs V ≡ just Vᵒ × CodeValue Vᵒ × Δ ; ⟨ Θ , Γᵒ , [] , Σ ⟩ ; ε ⊢ᵒ Vᵒ ⦂ T
obs-code v ⊢V O↪T = obs-code-canonical (canonical-code v ⊢V O↪T) ⊢V O↪T

canonical-star : ∀ {Δ Γ V}
  → Value V
  → Δ ; Γ ⊢ᵐ V ⦂ ⋆
    --------------------
  → CanonicalStar V
canonical-star (V-raw u) ⊢U =
  contradiction ⊢U (raw-not-star u)
canonical-star (V-cast u ⟨ nf , ⟨ not-id , not-blame ⟩ ⟩) (⊢cast ⊢U ⊢c) =
  canonical-star-cast u ⊢U nf not-id not-blame ⊢c
