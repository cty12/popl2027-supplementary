module Theories.ErrorFree where

open import Data.List.Relation.Unary.All using (All)

open import Theories.CCAlphaRefStarSyntaxAndTypeSystem
import Theories.CoercionSequences.EC.Definition as EC
import Theories.CoercionSequences.Code.Definition as OC
import Theories.CoercionSequences.Meta.Definition as MC


data ErrorFreeECSingle : EC.ECSingleCoercion → Set where

  ef-!ᵉ : ∀ {e}
      ---------------------------
    → ErrorFreeECSingle (e EC.！)

  ef-↑ᵉ : ∀ {ê₁ ê₂}
      ---------------------------------
    → ErrorFreeECSingle (ê₁ EC.↑ ê₂)

ErrorFreeECSeq : EC.ECCoercionSeq → Set
ErrorFreeECSeq = All ErrorFreeECSingle

ErrorFreeECCoercion : EC.ECCoercionSeq → Set
ErrorFreeECCoercion = ErrorFreeECSeq


data ErrorFreeCodeSingle : OC.OSingleCoercion → Set

ErrorFreeCodeSeq : OC.OCoercionSeq → Set
ErrorFreeCodeSeq = All ErrorFreeCodeSingle

data ErrorFreeCodeSingle where

  ef-!ᵒ : ∀ {Gᵒ} {g : OC.OGround Gᵒ}
      -------------------------------------
    → ErrorFreeCodeSingle ((Gᵒ OC.！) g)

  ef-funᵒ : ∀ {c̅ d̅}
    → ErrorFreeCodeSeq c̅
    → ErrorFreeCodeSeq d̅
      ---------------------------------
    → ErrorFreeCodeSingle (c̅ OC.⇒ d̅)

ErrorFreeCodeCoercion : OC.OCoercionSeq → Set
ErrorFreeCodeCoercion = ErrorFreeCodeSeq


data ErrorFreeMetaSingle : MC.MSingleCoercion → Set

ErrorFreeMetaSeq : MC.MCoercionSeq → Set
ErrorFreeMetaSeq = All ErrorFreeMetaSingle

data ErrorFreeMetaSingle where

  ef-!ᵐ : ∀ {G} {g : MC.Ground G}
      ---------------------------------
    → ErrorFreeMetaSingle ((G MC.！) g)

  ef-funᵐ : ∀ {c̅ d̅}
    → ErrorFreeMetaSeq c̅
    → ErrorFreeMetaSeq d̅
      ---------------------------------
    → ErrorFreeMetaSingle (c̅ MC.⇒ d̅)

  ef-codeᵐ : ∀ {c̅ᵒ c̅ᵉ}
    → ErrorFreeCodeSeq c̅ᵒ
    → ErrorFreeECSeq c̅ᵉ
      ------------------------------------
    → ErrorFreeMetaSingle (MC.‶ c̅ᵒ ″ c̅ᵉ)

  ef-refᵐ : ∀ {c̅ d̅}
    → ErrorFreeMetaSeq c̅
    → ErrorFreeMetaSeq d̅
      ------------------------------------
    → ErrorFreeMetaSingle (MC.Ref c̅ , d̅)

  ef-forallᵐ : ∀ {c̅}
    → ErrorFreeMetaSeq c̅
      ------------------------------
    → ErrorFreeMetaSingle (MC.∀̇ c̅)

  ef-subᵐ : ∀ {e₁ e₂ c̅}
    → ErrorFreeMetaSeq c̅
      ---------------------------------------
    → ErrorFreeMetaSingle (e₁ MC.<: e₂ => c̅)

ErrorFreeMetaCoercion : MC.MCoercionSeq → Set
ErrorFreeMetaCoercion = ErrorFreeMetaSeq


mutual

  data ErrorFreeCodeTerm : CodeTerm → Set where

    ef-constᵒ : ∀ {ι} {k : base-rep ι}
        ---------------------------------
      → ErrorFreeCodeTerm ($ k)

    ef-varᵒ : ∀ {x}
        ------------------------
      → ErrorFreeCodeTerm (` x)

    ef-lamᵒ : ∀ {T M}
      → ErrorFreeCodeTerm M
        ---------------------------
      → ErrorFreeCodeTerm (ƛ T ˙ M)

    ef-lamᵒ-val : ∀ {e M}
      → ErrorFreeCodeTerm M
        ---------------------------
      → ErrorFreeCodeTerm (ƛ̅ e ˙ M)

    ef-appᵒ : ∀ {L M}
      → ErrorFreeCodeTerm L
      → ErrorFreeCodeTerm M
        ---------------------------
      → ErrorFreeCodeTerm (L · M)

    ef-splice : ∀ {M}
      → ErrorFreeMetaTerm M
        ------------------------
      → ErrorFreeCodeTerm (~ M)

  data ErrorFreeMetaTerm : MetaTerm → Set where

    ef-constᵐ : ∀ {ι} {k : base-rep ι}
        ------------------------------
      → ErrorFreeMetaTerm ($ k)

    ef-varᵐ : ∀ {x}
        ------------------------
      → ErrorFreeMetaTerm (` x)

    ef-addr : ∀ {a}
        ------------------------------
      → ErrorFreeMetaTerm (addr a)

    ef-lamᵐ : ∀ {M}
      → ErrorFreeMetaTerm M
        ---------------------------
      → ErrorFreeMetaTerm (ƛ M)

    ef-appᵐ : ∀ {L M}
      → ErrorFreeMetaTerm L
      → ErrorFreeMetaTerm M
        ---------------------------
      → ErrorFreeMetaTerm (L · M)

    ef-eclam : ∀ {M}
      → ErrorFreeMetaTerm M
        ---------------------------
      → ErrorFreeMetaTerm (Λ M)

    ef-ecapp : ∀ {M e}
      → ErrorFreeMetaTerm M
        ---------------------------------
      → ErrorFreeMetaTerm (M ·[ e ])

    ef-subintro : ∀ {M e₁ e₂}
      → ErrorFreeMetaTerm M
        ------------------------------------
      → ErrorFreeMetaTerm (e₁ <: e₂ => M)

    ef-subelim : ∀ {M}
      → ErrorFreeMetaTerm M
        ---------------------------
      → ErrorFreeMetaTerm (M ●)

    ef-quote : ∀ {M e}
      → ErrorFreeCodeTerm M
        ------------------------------
      → ErrorFreeMetaTerm (‶ M ″ e)

    ef-ref : ∀ {M}
      → ErrorFreeMetaTerm M
        ---------------------------
      → ErrorFreeMetaTerm (ref M)

    ef-assign : ∀ {L M}
      → ErrorFreeMetaTerm L
      → ErrorFreeMetaTerm M
        ------------------------------
      → ErrorFreeMetaTerm (L := M)

    ef-deref : ∀ {M}
      → ErrorFreeMetaTerm M
        ---------------------------
      → ErrorFreeMetaTerm (! M)

    ef-cast : ∀ {M c}
      → ErrorFreeMetaTerm M
      → ErrorFreeMetaCoercion c
        ------------------------------
      → ErrorFreeMetaTerm (M ⟨ c ⟩)
