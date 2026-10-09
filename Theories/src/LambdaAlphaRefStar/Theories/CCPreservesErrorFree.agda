module LambdaAlphaRefStar.Theories.CCPreservesErrorFree where

open import Data.Empty using (⊥)
open import Data.List using ([]; _∷_; _∷ʳ_; _++_)
open import Data.List.Relation.Unary.All using (All) renaming ([] to []ᴬ; _∷_ to _∷ᴬ_)
open import Data.List.Relation.Unary.All.Properties using (∷ʳ⁺)
open import Data.Nat using (zero; suc)
open import Data.Product renaming (_,_ to ⟨_,_⟩)
open import Relation.Binary.PropositionalEquality using (_≢_)

open import Utils using (_∋_⦂_; here; there)
open import LambdaAlphaRefStar.Theories.CCAlphaRefStarSyntaxAndTypeSystem hiding (idᵉ)
open import LambdaAlphaRefStar.Theories.CCAlphaRefStarSemantics
open import LambdaAlphaRefStar.Theories.CodeSubst
  using (SubstCode; _[_]ᵒ; renᵒ-code; renᵒ-meta; substᵒ-code; substᵒ-meta; idsᵒ; _•ᵒₛ_)
open import LambdaAlphaRefStar.Theories.ECSubst
  using (_[_]ᵉᵐ; renᵉ-code; renᵉ-meta; renᵉ-ecoercion; renᵉ-ecoercionSeq
       ; renᵉ-mcoercion; renᵉ-mcoercionSeq; renᵉ-metacoercion
       ; substᵉ-code; substᵉ-meta; substᵉ-ecoercion; substᵉ-ecoercionSeq
       ; substᵉ-mcoercion; substᵉ-mcoercionSeq)
open import LambdaAlphaRefStar.Theories.EnvClassifiers using (SubstEC; idsᵉ; _•ᵉₛ_; freshᵉ)
open import LambdaAlphaRefStar.Theories.Heap using (Heap; _⟦_↦_⟧=_)
import LambdaAlphaRefStar.Theories.Heap as H
open import LambdaAlphaRefStar.Theories.MetaSubst
  using (SubstMeta; _[_]ᵐ; renᵐ-code; renᵐ-meta; substᵐ-code; substᵐ-meta)
open import LambdaAlphaRefStar.Theories.ErrorFree
open import LambdaAlphaRefStar.Theories.Values
import LambdaAlphaRefStar.Theories.CoercionSequences.EC.Definition as EC
import LambdaAlphaRefStar.Theories.CoercionSequences.Code.Definition as OC
import LambdaAlphaRefStar.Theories.CoercionSequences.Meta.Definition as MC


ErrorFreeHeap : Heap → Set
ErrorFreeHeap = All ErrorFreeMetaTerm


heap-lookup-error-free : ∀ {μ a V}
  → ErrorFreeHeap μ
  → μ ∋ a ⦂ V
    ------------------
  → ErrorFreeMetaTerm V
heap-lookup-error-free (npV ∷ᴬ _) here = npV
heap-lookup-error-free (_ ∷ᴬ npμ) (there lookup) =
  heap-lookup-error-free npμ lookup


meta-error-free-not-blame : ∀ {M ℓ}
  → ErrorFreeMetaTerm M
    ------------------
  → M ≢ blame ℓ
meta-error-free-not-blame ef-constᵐ ()
meta-error-free-not-blame ef-varᵐ ()
meta-error-free-not-blame ef-addr ()
meta-error-free-not-blame (ef-lamᵐ npM) ()
meta-error-free-not-blame (ef-appᵐ npL npM) ()
meta-error-free-not-blame (ef-eclam npM) ()
meta-error-free-not-blame (ef-ecapp npM) ()
meta-error-free-not-blame (ef-subintro npM) ()
meta-error-free-not-blame (ef-subelim npM) ()
meta-error-free-not-blame (ef-quote npM) ()
meta-error-free-not-blame (ef-ref npM) ()
meta-error-free-not-blame (ef-assign npL npM) ()
meta-error-free-not-blame (ef-deref npM) ()
meta-error-free-not-blame (ef-cast npM npc) ()


mutual

  substᵒ-code-error-free : ∀ {σ Mᵒ}
    → (∀ x → ErrorFreeCodeTerm (σ x))
    → ErrorFreeCodeTerm Mᵒ
      ------------------------------------
    → ErrorFreeCodeTerm (substᵒ-code σ Mᵒ)
  substᵒ-code-error-free σ-np ef-constᵒ = ef-constᵒ
  substᵒ-code-error-free σ-np ef-varᵒ = σ-np _
  substᵒ-code-error-free σ-np (ef-lamᵒ npM) =
    ef-lamᵒ (substᵒ-code-error-free (λ where zero → ef-varᵒ ; (suc x) → renᵒ-code-error-free (σ-np x)) npM)
  substᵒ-code-error-free σ-np (ef-lamᵒ-val npM) =
    ef-lamᵒ-val (substᵒ-code-error-free σ-np npM)
  substᵒ-code-error-free σ-np (ef-appᵒ npL npM) =
    ef-appᵒ (substᵒ-code-error-free σ-np npL) (substᵒ-code-error-free σ-np npM)
  substᵒ-code-error-free σ-np (ef-splice npM) =
    ef-splice (substᵒ-meta-error-free σ-np npM)

  substᵒ-meta-error-free : ∀ {σ M}
    → (∀ x → ErrorFreeCodeTerm (σ x))
    → ErrorFreeMetaTerm M
      ------------------------------------
    → ErrorFreeMetaTerm (substᵒ-meta σ M)
  substᵒ-meta-error-free σ-np ef-constᵐ = ef-constᵐ
  substᵒ-meta-error-free σ-np ef-varᵐ = ef-varᵐ
  substᵒ-meta-error-free σ-np ef-addr = ef-addr
  substᵒ-meta-error-free σ-np (ef-lamᵐ npM) =
    ef-lamᵐ (substᵒ-meta-error-free σ-np npM)
  substᵒ-meta-error-free σ-np (ef-appᵐ npL npM) =
    ef-appᵐ (substᵒ-meta-error-free σ-np npL) (substᵒ-meta-error-free σ-np npM)
  substᵒ-meta-error-free σ-np (ef-eclam npM) =
    ef-eclam (substᵒ-meta-error-free σ-np npM)
  substᵒ-meta-error-free σ-np (ef-ecapp npM) =
    ef-ecapp (substᵒ-meta-error-free σ-np npM)
  substᵒ-meta-error-free σ-np (ef-subintro npM) =
    ef-subintro (substᵒ-meta-error-free σ-np npM)
  substᵒ-meta-error-free σ-np (ef-subelim npM) =
    ef-subelim (substᵒ-meta-error-free σ-np npM)
  substᵒ-meta-error-free σ-np (ef-quote npM) =
    ef-quote (substᵒ-code-error-free σ-np npM)
  substᵒ-meta-error-free σ-np (ef-ref npM) =
    ef-ref (substᵒ-meta-error-free σ-np npM)
  substᵒ-meta-error-free σ-np (ef-assign npL npM) =
    ef-assign (substᵒ-meta-error-free σ-np npL) (substᵒ-meta-error-free σ-np npM)
  substᵒ-meta-error-free σ-np (ef-deref npM) =
    ef-deref (substᵒ-meta-error-free σ-np npM)
  substᵒ-meta-error-free σ-np (ef-cast npM npc) =
    ef-cast (substᵒ-meta-error-free σ-np npM) npc

  renᵒ-code-error-free : ∀ {ρ Mᵒ}
    → ErrorFreeCodeTerm Mᵒ
      -------------------------------
    → ErrorFreeCodeTerm (renᵒ-code ρ Mᵒ)
  renᵒ-code-error-free ef-constᵒ = ef-constᵒ
  renᵒ-code-error-free ef-varᵒ = ef-varᵒ
  renᵒ-code-error-free (ef-lamᵒ npM) = ef-lamᵒ (renᵒ-code-error-free npM)
  renᵒ-code-error-free (ef-lamᵒ-val npM) = ef-lamᵒ-val (renᵒ-code-error-free npM)
  renᵒ-code-error-free (ef-appᵒ npL npM) =
    ef-appᵒ (renᵒ-code-error-free npL) (renᵒ-code-error-free npM)
  renᵒ-code-error-free (ef-splice npM) = ef-splice (renᵒ-meta-error-free npM)

  renᵒ-meta-error-free : ∀ {ρ M}
    → ErrorFreeMetaTerm M
      -------------------------------
    → ErrorFreeMetaTerm (renᵒ-meta ρ M)
  renᵒ-meta-error-free ef-constᵐ = ef-constᵐ
  renᵒ-meta-error-free ef-varᵐ = ef-varᵐ
  renᵒ-meta-error-free ef-addr = ef-addr
  renᵒ-meta-error-free (ef-lamᵐ npM) = ef-lamᵐ (renᵒ-meta-error-free npM)
  renᵒ-meta-error-free (ef-appᵐ npL npM) =
    ef-appᵐ (renᵒ-meta-error-free npL) (renᵒ-meta-error-free npM)
  renᵒ-meta-error-free (ef-eclam npM) = ef-eclam (renᵒ-meta-error-free npM)
  renᵒ-meta-error-free (ef-ecapp npM) = ef-ecapp (renᵒ-meta-error-free npM)
  renᵒ-meta-error-free (ef-subintro npM) = ef-subintro (renᵒ-meta-error-free npM)
  renᵒ-meta-error-free (ef-subelim npM) = ef-subelim (renᵒ-meta-error-free npM)
  renᵒ-meta-error-free (ef-quote npM) = ef-quote (renᵒ-code-error-free npM)
  renᵒ-meta-error-free (ef-ref npM) = ef-ref (renᵒ-meta-error-free npM)
  renᵒ-meta-error-free (ef-assign npL npM) =
    ef-assign (renᵒ-meta-error-free npL) (renᵒ-meta-error-free npM)
  renᵒ-meta-error-free (ef-deref npM) = ef-deref (renᵒ-meta-error-free npM)
  renᵒ-meta-error-free (ef-cast npM npc) = ef-cast (renᵒ-meta-error-free npM) npc


mutual

  renᵉ-ecsingle-error-free : ∀ ρ {c}
    → ErrorFreeECSingle c
      --------------------------------------
    → ErrorFreeECSingle (renᵉ-ecoercion ρ c)
  renᵉ-ecsingle-error-free ρ {EC._！ e} ef-!ᵉ = ef-!ᵉ
  renᵉ-ecsingle-error-free ρ {EC._？_ e ℓ} ()
  renᵉ-ecsingle-error-free ρ {EC._↑_ ê₁ ê₂} ef-↑ᵉ = ef-↑ᵉ
  renᵉ-ecsingle-error-free ρ {EC.⊥ ℓ} ()

  renᵉ-ecseq-error-free : ∀ ρ {c̅}
    → ErrorFreeECSeq c̅
      -----------------------------------------
    → ErrorFreeECSeq (renᵉ-ecoercionSeq ρ c̅)
  renᵉ-ecseq-error-free ρ {[]} []ᴬ = []ᴬ
  renᵉ-ecseq-error-free ρ {c ∷ c̅} (npc ∷ᴬ npc̅) =
    renᵉ-ecsingle-error-free ρ npc ∷ᴬ renᵉ-ecseq-error-free ρ npc̅

  renᵉ-msingle-error-free : ∀ ρ {c}
    → ErrorFreeMetaSingle c
      --------------------------------------
    → ErrorFreeMetaSingle (renᵉ-mcoercion ρ c)
  renᵉ-msingle-error-free ρ {MC._！ G g} ef-!ᵐ = ef-!ᵐ
  renᵉ-msingle-error-free ρ {MC._？_ G ℓ g} ()
  renᵉ-msingle-error-free ρ {MC._⇒_ c̅ d̅} (ef-funᵐ npc̅ npd̅) =
    ef-funᵐ (renᵉ-mseq-error-free ρ npc̅) (renᵉ-mseq-error-free ρ npd̅)
  renᵉ-msingle-error-free ρ {MC.‶ c̅ᵒ ″ c̅ᵉ} (ef-codeᵐ npc̅ᵒ npc̅ᵉ) =
    ef-codeᵐ npc̅ᵒ (renᵉ-ecseq-error-free ρ npc̅ᵉ)
  renᵉ-msingle-error-free ρ {MC.Ref_,_ c̅ d̅} (ef-refᵐ npc̅ npd̅) =
    ef-refᵐ (renᵉ-mseq-error-free ρ npc̅) (renᵉ-mseq-error-free ρ npd̅)
  renᵉ-msingle-error-free ρ {MC.∀̇ c̅} (ef-forallᵐ npc̅) =
    ef-forallᵐ (renᵉ-mseq-error-free _ npc̅)
  renᵉ-msingle-error-free ρ {MC._<:_=>_ e₁ e₂ c̅} (ef-subᵐ npc̅) =
    ef-subᵐ (renᵉ-mseq-error-free ρ npc̅)
  renᵉ-msingle-error-free ρ {MC.⊥ ℓ} ()

  renᵉ-mseq-error-free : ∀ ρ {c̅}
    → ErrorFreeMetaSeq c̅
      -----------------------------------------
    → ErrorFreeMetaSeq (renᵉ-mcoercionSeq ρ c̅)
  renᵉ-mseq-error-free ρ {[]} []ᴬ = []ᴬ
  renᵉ-mseq-error-free ρ {c ∷ c̅} (npc ∷ᴬ npc̅) =
    renᵉ-msingle-error-free ρ {c = c} npc ∷ᴬ renᵉ-mseq-error-free ρ npc̅

  renᵉ-metacoercion-error-free : ∀ ρ {c}
    → ErrorFreeMetaCoercion c
      -----------------------------------------
    → ErrorFreeMetaCoercion (renᵉ-metacoercion ρ c)
  renᵉ-metacoercion-error-free ρ npc =
    renᵉ-mseq-error-free ρ npc


mutual

  renᵉ-code-error-free : ∀ {ρ Mᵒ}
    → ErrorFreeCodeTerm Mᵒ
      -------------------------------
    → ErrorFreeCodeTerm (renᵉ-code ρ Mᵒ)
  renᵉ-code-error-free ef-constᵒ = ef-constᵒ
  renᵉ-code-error-free ef-varᵒ = ef-varᵒ
  renᵉ-code-error-free (ef-lamᵒ npM) = ef-lamᵒ (renᵉ-code-error-free npM)
  renᵉ-code-error-free (ef-lamᵒ-val npM) = ef-lamᵒ-val (renᵉ-code-error-free npM)
  renᵉ-code-error-free (ef-appᵒ npL npM) =
    ef-appᵒ (renᵉ-code-error-free npL) (renᵉ-code-error-free npM)
  renᵉ-code-error-free (ef-splice npM) = ef-splice (renᵉ-meta-error-free npM)

  renᵉ-meta-error-free : ∀ {ρ M}
    → ErrorFreeMetaTerm M
      -------------------------------
    → ErrorFreeMetaTerm (renᵉ-meta ρ M)
  renᵉ-meta-error-free ef-constᵐ = ef-constᵐ
  renᵉ-meta-error-free ef-varᵐ = ef-varᵐ
  renᵉ-meta-error-free ef-addr = ef-addr
  renᵉ-meta-error-free (ef-lamᵐ npM) = ef-lamᵐ (renᵉ-meta-error-free npM)
  renᵉ-meta-error-free (ef-appᵐ npL npM) =
    ef-appᵐ (renᵉ-meta-error-free npL) (renᵉ-meta-error-free npM)
  renᵉ-meta-error-free (ef-eclam npM) = ef-eclam (renᵉ-meta-error-free npM)
  renᵉ-meta-error-free (ef-ecapp npM) = ef-ecapp (renᵉ-meta-error-free npM)
  renᵉ-meta-error-free (ef-subintro npM) = ef-subintro (renᵉ-meta-error-free npM)
  renᵉ-meta-error-free (ef-subelim npM) = ef-subelim (renᵉ-meta-error-free npM)
  renᵉ-meta-error-free (ef-quote npM) = ef-quote (renᵉ-code-error-free npM)
  renᵉ-meta-error-free (ef-ref npM) = ef-ref (renᵉ-meta-error-free npM)
  renᵉ-meta-error-free (ef-assign npL npM) =
    ef-assign (renᵉ-meta-error-free npL) (renᵉ-meta-error-free npM)
  renᵉ-meta-error-free (ef-deref npM) = ef-deref (renᵉ-meta-error-free npM)
  renᵉ-meta-error-free {ρ = ρ} (ef-cast {c = c} npM npc) =
    ef-cast (renᵉ-meta-error-free {ρ = ρ} npM) (renᵉ-metacoercion-error-free ρ {c = c} npc)


mutual

  substᵐ-code-error-free : ∀ {σ Mᵒ}
    → (∀ x → ErrorFreeMetaTerm (σ x))
    → ErrorFreeCodeTerm Mᵒ
      ------------------------------------
    → ErrorFreeCodeTerm (substᵐ-code σ Mᵒ)
  substᵐ-code-error-free σ-np ef-constᵒ = ef-constᵒ
  substᵐ-code-error-free σ-np ef-varᵒ = ef-varᵒ
  substᵐ-code-error-free σ-np (ef-lamᵒ npM) =
    ef-lamᵒ (substᵐ-code-error-free (λ x → renᵒ-meta-error-free (renᵉ-meta-error-free (σ-np x))) npM)
  substᵐ-code-error-free σ-np (ef-lamᵒ-val npM) =
    ef-lamᵒ-val (substᵐ-code-error-free σ-np npM)
  substᵐ-code-error-free σ-np (ef-appᵒ npL npM) =
    ef-appᵒ (substᵐ-code-error-free σ-np npL) (substᵐ-code-error-free σ-np npM)
  substᵐ-code-error-free σ-np (ef-splice npM) =
    ef-splice (substᵐ-meta-error-free σ-np npM)

  substᵐ-meta-error-free : ∀ {σ M}
    → (∀ x → ErrorFreeMetaTerm (σ x))
    → ErrorFreeMetaTerm M
      ------------------------------------
    → ErrorFreeMetaTerm (substᵐ-meta σ M)
  substᵐ-meta-error-free σ-np ef-constᵐ = ef-constᵐ
  substᵐ-meta-error-free σ-np ef-varᵐ = σ-np _
  substᵐ-meta-error-free σ-np ef-addr = ef-addr
  substᵐ-meta-error-free σ-np (ef-lamᵐ npM) =
    ef-lamᵐ (substᵐ-meta-error-free (λ where zero → ef-varᵐ ; (suc x) → renᵐ-meta-error-free (σ-np x)) npM)
  substᵐ-meta-error-free σ-np (ef-appᵐ npL npM) =
    ef-appᵐ (substᵐ-meta-error-free σ-np npL) (substᵐ-meta-error-free σ-np npM)
  substᵐ-meta-error-free σ-np (ef-eclam npM) =
    ef-eclam (substᵐ-meta-error-free (λ x → renᵉ-meta-error-free (σ-np x)) npM)
  substᵐ-meta-error-free σ-np (ef-ecapp npM) =
    ef-ecapp (substᵐ-meta-error-free σ-np npM)
  substᵐ-meta-error-free σ-np (ef-subintro npM) =
    ef-subintro (substᵐ-meta-error-free σ-np npM)
  substᵐ-meta-error-free σ-np (ef-subelim npM) =
    ef-subelim (substᵐ-meta-error-free σ-np npM)
  substᵐ-meta-error-free σ-np (ef-quote npM) =
    ef-quote (substᵐ-code-error-free σ-np npM)
  substᵐ-meta-error-free σ-np (ef-ref npM) =
    ef-ref (substᵐ-meta-error-free σ-np npM)
  substᵐ-meta-error-free σ-np (ef-assign npL npM) =
    ef-assign (substᵐ-meta-error-free σ-np npL) (substᵐ-meta-error-free σ-np npM)
  substᵐ-meta-error-free σ-np (ef-deref npM) =
    ef-deref (substᵐ-meta-error-free σ-np npM)
  substᵐ-meta-error-free σ-np (ef-cast npM npc) =
    ef-cast (substᵐ-meta-error-free σ-np npM) npc

  renᵐ-code-error-free : ∀ {ρ Mᵒ}
    → ErrorFreeCodeTerm Mᵒ
      -------------------------------
    → ErrorFreeCodeTerm (renᵐ-code ρ Mᵒ)
  renᵐ-code-error-free ef-constᵒ = ef-constᵒ
  renᵐ-code-error-free ef-varᵒ = ef-varᵒ
  renᵐ-code-error-free (ef-lamᵒ npM) = ef-lamᵒ (renᵐ-code-error-free npM)
  renᵐ-code-error-free (ef-lamᵒ-val npM) = ef-lamᵒ-val (renᵐ-code-error-free npM)
  renᵐ-code-error-free (ef-appᵒ npL npM) =
    ef-appᵒ (renᵐ-code-error-free npL) (renᵐ-code-error-free npM)
  renᵐ-code-error-free (ef-splice npM) = ef-splice (renᵐ-meta-error-free npM)

  renᵐ-meta-error-free : ∀ {ρ M}
    → ErrorFreeMetaTerm M
      -------------------------------
    → ErrorFreeMetaTerm (renᵐ-meta ρ M)
  renᵐ-meta-error-free ef-constᵐ = ef-constᵐ
  renᵐ-meta-error-free ef-varᵐ = ef-varᵐ
  renᵐ-meta-error-free ef-addr = ef-addr
  renᵐ-meta-error-free (ef-lamᵐ npM) = ef-lamᵐ (renᵐ-meta-error-free npM)
  renᵐ-meta-error-free (ef-appᵐ npL npM) =
    ef-appᵐ (renᵐ-meta-error-free npL) (renᵐ-meta-error-free npM)
  renᵐ-meta-error-free (ef-eclam npM) = ef-eclam (renᵐ-meta-error-free npM)
  renᵐ-meta-error-free (ef-ecapp npM) = ef-ecapp (renᵐ-meta-error-free npM)
  renᵐ-meta-error-free (ef-subintro npM) = ef-subintro (renᵐ-meta-error-free npM)
  renᵐ-meta-error-free (ef-subelim npM) = ef-subelim (renᵐ-meta-error-free npM)
  renᵐ-meta-error-free (ef-quote npM) = ef-quote (renᵐ-code-error-free npM)
  renᵐ-meta-error-free (ef-ref npM) = ef-ref (renᵐ-meta-error-free npM)
  renᵐ-meta-error-free (ef-assign npL npM) =
    ef-assign (renᵐ-meta-error-free npL) (renᵐ-meta-error-free npM)
  renᵐ-meta-error-free (ef-deref npM) = ef-deref (renᵐ-meta-error-free npM)
  renᵐ-meta-error-free (ef-cast npM npc) = ef-cast (renᵐ-meta-error-free npM) npc


mutual

  substᵉ-ecsingle-error-free : ∀ σ {c}
    → ErrorFreeECSingle c
      ----------------------------------------
    → ErrorFreeECSingle (substᵉ-ecoercion σ c)
  substᵉ-ecsingle-error-free σ {EC._！ e} ef-!ᵉ = ef-!ᵉ
  substᵉ-ecsingle-error-free σ {EC._？_ e ℓ} ()
  substᵉ-ecsingle-error-free σ {EC._↑_ ê₁ ê₂} ef-↑ᵉ = ef-↑ᵉ
  substᵉ-ecsingle-error-free σ {EC.⊥ ℓ} ()

  substᵉ-ecseq-error-free : ∀ σ {c̅}
    → ErrorFreeECSeq c̅
      -------------------------------------------
    → ErrorFreeECSeq (substᵉ-ecoercionSeq σ c̅)
  substᵉ-ecseq-error-free σ {[]} []ᴬ = []ᴬ
  substᵉ-ecseq-error-free σ {c ∷ c̅} (npc ∷ᴬ npc̅) =
    substᵉ-ecsingle-error-free σ npc ∷ᴬ substᵉ-ecseq-error-free σ npc̅

  substᵉ-msingle-error-free : ∀ σ {c}
    → ErrorFreeMetaSingle c
      ----------------------------------------
    → ErrorFreeMetaSingle (substᵉ-mcoercion σ c)
  substᵉ-msingle-error-free σ {MC._！ G g} ef-!ᵐ = ef-!ᵐ
  substᵉ-msingle-error-free σ {MC._？_ G ℓ g} ()
  substᵉ-msingle-error-free σ {MC._⇒_ c̅ d̅} (ef-funᵐ npc̅ npd̅) =
    ef-funᵐ (substᵉ-mseq-error-free σ npc̅) (substᵉ-mseq-error-free σ npd̅)
  substᵉ-msingle-error-free σ {MC.‶ c̅ᵒ ″ c̅ᵉ} (ef-codeᵐ npc̅ᵒ npc̅ᵉ) =
    ef-codeᵐ npc̅ᵒ (substᵉ-ecseq-error-free σ npc̅ᵉ)
  substᵉ-msingle-error-free σ {MC.Ref_,_ c̅ d̅} (ef-refᵐ npc̅ npd̅) =
    ef-refᵐ (substᵉ-mseq-error-free σ npc̅) (substᵉ-mseq-error-free σ npd̅)
  substᵉ-msingle-error-free σ {MC.∀̇ c̅} (ef-forallᵐ npc̅) =
    ef-forallᵐ (substᵉ-mseq-error-free _ npc̅)
  substᵉ-msingle-error-free σ {MC._<:_=>_ e₁ e₂ c̅} (ef-subᵐ npc̅) =
    ef-subᵐ (substᵉ-mseq-error-free σ npc̅)
  substᵉ-msingle-error-free σ {MC.⊥ ℓ} ()

  substᵉ-mseq-error-free : ∀ σ {c̅}
    → ErrorFreeMetaSeq c̅
      -------------------------------------------
    → ErrorFreeMetaSeq (substᵉ-mcoercionSeq σ c̅)
  substᵉ-mseq-error-free σ {[]} []ᴬ = []ᴬ
  substᵉ-mseq-error-free σ {c ∷ c̅} (npc ∷ᴬ npc̅) =
    substᵉ-msingle-error-free σ {c = c} npc ∷ᴬ substᵉ-mseq-error-free σ npc̅

mutual

  substᵉ-code-error-free : ∀ {σ Mᵒ}
    → ErrorFreeCodeTerm Mᵒ
      ------------------------------------
    → ErrorFreeCodeTerm (substᵉ-code σ Mᵒ)
  substᵉ-code-error-free ef-constᵒ = ef-constᵒ
  substᵉ-code-error-free ef-varᵒ = ef-varᵒ
  substᵉ-code-error-free (ef-lamᵒ npM) = ef-lamᵒ (substᵉ-code-error-free npM)
  substᵉ-code-error-free (ef-lamᵒ-val npM) = ef-lamᵒ-val (substᵉ-code-error-free npM)
  substᵉ-code-error-free (ef-appᵒ npL npM) =
    ef-appᵒ (substᵉ-code-error-free npL) (substᵉ-code-error-free npM)
  substᵉ-code-error-free (ef-splice npM) = ef-splice (substᵉ-meta-error-free npM)

  substᵉ-meta-error-free : ∀ {σ M}
    → ErrorFreeMetaTerm M
      ------------------------------------
    → ErrorFreeMetaTerm (substᵉ-meta σ M)
  substᵉ-meta-error-free ef-constᵐ = ef-constᵐ
  substᵉ-meta-error-free ef-varᵐ = ef-varᵐ
  substᵉ-meta-error-free ef-addr = ef-addr
  substᵉ-meta-error-free (ef-lamᵐ npM) = ef-lamᵐ (substᵉ-meta-error-free npM)
  substᵉ-meta-error-free (ef-appᵐ npL npM) =
    ef-appᵐ (substᵉ-meta-error-free npL) (substᵉ-meta-error-free npM)
  substᵉ-meta-error-free (ef-eclam npM) = ef-eclam (substᵉ-meta-error-free npM)
  substᵉ-meta-error-free (ef-ecapp npM) = ef-ecapp (substᵉ-meta-error-free npM)
  substᵉ-meta-error-free (ef-subintro npM) = ef-subintro (substᵉ-meta-error-free npM)
  substᵉ-meta-error-free (ef-subelim npM) = ef-subelim (substᵉ-meta-error-free npM)
  substᵉ-meta-error-free (ef-quote npM) = ef-quote (substᵉ-code-error-free npM)
  substᵉ-meta-error-free (ef-ref npM) = ef-ref (substᵉ-meta-error-free npM)
  substᵉ-meta-error-free (ef-assign npL npM) =
    ef-assign (substᵉ-meta-error-free npL) (substᵉ-meta-error-free npM)
  substᵉ-meta-error-free (ef-deref npM) = ef-deref (substᵉ-meta-error-free npM)
  substᵉ-meta-error-free {σ = σ} (ef-cast {c = c} npM npc) =
    ef-cast (substᵉ-meta-error-free {σ = σ} npM) (substᵉ-mseq-error-free σ {c̅ = c} npc)


ErrorFreeConfig : Config MetaTerm → Set
ErrorFreeConfig C = ErrorFreeHeap (C .μ) × ErrorFreeMetaTerm (C .M)


code-seq-++-error-free : ∀ {c̅ᵒ d̅ᵒ}
  → ErrorFreeCodeSeq c̅ᵒ
  → ErrorFreeCodeSeq d̅ᵒ
    -----------------------------
  → ErrorFreeCodeSeq (c̅ᵒ ++ d̅ᵒ)
code-seq-++-error-free {[]} npc̅ npd̅ = npd̅
code-seq-++-error-free {cᵒ ∷ c̅ᵒ} (npc ∷ᴬ npc̅) npd̅ =
  npc ∷ᴬ code-seq-++-error-free npc̅ npd̅


mutual

  code-pair-step-error-free : ∀ {cᵒ dᵒ eᵒ}
    → OC.⊢ᵒ cᵒ ; dᵒ ⟶ eᵒ
    → ErrorFreeCodeSingle cᵒ
    → ErrorFreeCodeSingle dᵒ
      ---------------------
    → ErrorFreeCodeSeq eᵒ
  code-pair-step-error-free OC.collapse npc npd = []ᴬ
  code-pair-step-error-free (OC.collide Gᵒ≢Hᵒ) npc ()
  code-pair-step-error-free OC.seq-fun (ef-funᵒ npc̅₁ npc̅₂) (ef-funᵒ npd̅₁ npd̅₂) =
    ef-funᵒ (code-seq-++-error-free npd̅₁ npc̅₁) (code-seq-++-error-free npc̅₂ npd̅₂) ∷ᴬ []ᴬ
  code-pair-step-error-free OC.⊥-left () npd
  code-pair-step-error-free OC.⊥-right-! npc ()
  code-pair-step-error-free OC.⊥-right-fun npc ()

  code-single-step-error-free : ∀ {cᵒ dᵒ}
    → OC.⊢ᵒ cᵒ —→ dᵒ
    → ErrorFreeCodeSingle cᵒ
      ---------------------
    → ErrorFreeCodeSeq dᵒ
  code-single-step-error-free OC.id-fun npc = []ᴬ
  code-single-step-error-free (OC.ξ-fun-dom c̅ᵒ₁→d̅ᵒ₁) (ef-funᵒ npc̅₁ npc̅₂) =
    ef-funᵒ (code-seq-step-error-free c̅ᵒ₁→d̅ᵒ₁ npc̅₁) npc̅₂ ∷ᴬ []ᴬ
  code-single-step-error-free (OC.ξ-fun-cod nf not-blame c̅ᵒ₂→d̅ᵒ₂) (ef-funᵒ npc̅₁ npc̅₂) =
    ef-funᵒ npc̅₁ (code-seq-step-error-free c̅ᵒ₂→d̅ᵒ₂ npc̅₂) ∷ᴬ []ᴬ
  code-single-step-error-free OC.ξ-⊥-fun-dom (ef-funᵒ (() ∷ᴬ _) _)
  code-single-step-error-free (OC.ξ-⊥-fun-cod nf not-blame) (ef-funᵒ _ (() ∷ᴬ _))

  code-seq-step-error-free : ∀ {c̅ᵒ d̅ᵒ}
    → OC.⊢ᵒ̅ c̅ᵒ —→ d̅ᵒ
    → ErrorFreeCodeSeq c̅ᵒ
      -------------------
    → ErrorFreeCodeSeq d̅ᵒ
  code-seq-step-error-free (OC.reduce-head cᵒ→dᵒ) (npc ∷ᴬ npc̅) =
    code-seq-++-error-free (code-single-step-error-free cᵒ→dᵒ npc) npc̅
  code-seq-step-error-free (OC.reduce-neighbors nf cᵒ;dᵒ→eᵒ) (npc ∷ᴬ npd ∷ᴬ npc̅) =
    code-seq-++-error-free (code-pair-step-error-free cᵒ;dᵒ→eᵒ npc npd) npc̅
  code-seq-step-error-free (OC.reduce-tail nf irred c̅ᵒ→d̅ᵒ) (npc ∷ᴬ npc̅) =
    npc ∷ᴬ code-seq-step-error-free c̅ᵒ→d̅ᵒ npc̅


ec-seq-++-error-free : ∀ {c̅ᵉ d̅ᵉ}
  → ErrorFreeECSeq c̅ᵉ
  → ErrorFreeECSeq d̅ᵉ
    ---------------------------
  → ErrorFreeECSeq (c̅ᵉ ++ d̅ᵉ)
ec-seq-++-error-free {[]} npc̅ npd̅ = npd̅
ec-seq-++-error-free {cᵉ ∷ c̅ᵉ} (npc ∷ᴬ npc̅) npd̅ =
  npc ∷ᴬ ec-seq-++-error-free npc̅ npd̅


ec-pair-step-error-free : ∀ {Θ cᵉ dᵉ e̅ᵉ}
  → Θ EC.⊢ᵉ cᵉ ; dᵉ ⟶ e̅ᵉ
  → ErrorFreeECSingle cᵉ
  → ErrorFreeECSingle dᵉ
    -------------------
  → ErrorFreeECSeq e̅ᵉ
ec-pair-step-error-free (EC.collapse e₁<:e₂) npc npd = ef-↑ᵉ ∷ᴬ []ᴬ
ec-pair-step-error-free (EC.collide e₁≮:e₂) npc ()
ec-pair-step-error-free EC.↑-collapse npc npd = ef-↑ᵉ ∷ᴬ []ᴬ
ec-pair-step-error-free EC.⊥-left () npd
ec-pair-step-error-free (EC.⊥-right not-blame) npc ()


mutual

  ec-single-step-error-free : ∀ {Θ cᵉ d̅ᵉ}
    → Θ EC.⊢ᵉ cᵉ —→ d̅ᵉ
    → ErrorFreeECSingle cᵉ
      -------------------
    → ErrorFreeECSeq d̅ᵉ
  ec-single-step-error-free EC.↑-id ef-↑ᵉ = []ᴬ

  ec-seq-step-error-free : ∀ {Θ c̅ᵉ d̅ᵉ}
    → Θ EC.⊢ᵉ̅ c̅ᵉ —→ d̅ᵉ
    → ErrorFreeECSeq c̅ᵉ
      -----------------
    → ErrorFreeECSeq d̅ᵉ
  ec-seq-step-error-free (EC.reduce-head cᵉ→d̅ᵉ) (npc ∷ᴬ npc̅) =
    ec-seq-++-error-free (ec-single-step-error-free cᵉ→d̅ᵉ npc) npc̅
  ec-seq-step-error-free (EC.reduce-neighbors nf cᵉ;dᵉ→e̅ᵉ) (npc ∷ᴬ npd ∷ᴬ npc̅) =
    ec-seq-++-error-free (ec-pair-step-error-free cᵉ;dᵉ→e̅ᵉ npc npd) npc̅
  ec-seq-step-error-free (EC.reduce-tail nf irred c̅ᵉ→d̅ᵉ) (npc ∷ᴬ npc̅) =
    npc ∷ᴬ ec-seq-step-error-free c̅ᵉ→d̅ᵉ npc̅


meta-seq-++-error-free : ∀ {c̅ᵐ d̅ᵐ}
  → ErrorFreeMetaSeq c̅ᵐ
  → ErrorFreeMetaSeq d̅ᵐ
    -----------------------------
  → ErrorFreeMetaSeq (c̅ᵐ ++ d̅ᵐ)
meta-seq-++-error-free {[]} npc̅ npd̅ = npd̅
meta-seq-++-error-free {cᵐ ∷ c̅ᵐ} (npc ∷ᴬ npc̅) npd̅ =
  npc ∷ᴬ meta-seq-++-error-free npc̅ npd̅


mutual

  meta-pair-step-error-free : ∀ {Θ cᵐ dᵐ e̅ᵐ}
    → Θ MC.⊢ᵐ cᵐ ; dᵐ ⟶ e̅ᵐ
    → ErrorFreeMetaSingle cᵐ
    → ErrorFreeMetaSingle dᵐ
      ---------------------
    → ErrorFreeMetaSeq e̅ᵐ
  meta-pair-step-error-free MC.collapse npc npd = []ᴬ
  meta-pair-step-error-free (MC.collide G≢H) npc ()
  meta-pair-step-error-free MC.seq-fun (ef-funᵐ npc̅₁ npc̅₂) (ef-funᵐ npd̅₁ npd̅₂) =
    ef-funᵐ (meta-seq-++-error-free npd̅₁ npc̅₁) (meta-seq-++-error-free npc̅₂ npd̅₂) ∷ᴬ []ᴬ
  meta-pair-step-error-free MC.seq-ref (ef-refᵐ npc̅₁ npc̅₂) (ef-refᵐ npd̅₁ npd̅₂) =
    ef-refᵐ (meta-seq-++-error-free npd̅₁ npc̅₁) (meta-seq-++-error-free npc̅₂ npd̅₂) ∷ᴬ []ᴬ
  meta-pair-step-error-free MC.seq-code (ef-codeᵐ npc̅ᵒ npc̅ᵉ) (ef-codeᵐ npd̅ᵒ npd̅ᵉ) =
    ef-codeᵐ (code-seq-++-error-free npc̅ᵒ npd̅ᵒ) (ec-seq-++-error-free npc̅ᵉ npd̅ᵉ) ∷ᴬ []ᴬ
  meta-pair-step-error-free MC.seq-forall (ef-forallᵐ npc̅) (ef-forallᵐ npd̅) =
    ef-forallᵐ (meta-seq-++-error-free npc̅ npd̅) ∷ᴬ []ᴬ
  meta-pair-step-error-free MC.seq-sub (ef-subᵐ npc̅) (ef-subᵐ npd̅) =
    ef-subᵐ (meta-seq-++-error-free npc̅ npd̅) ∷ᴬ []ᴬ
  meta-pair-step-error-free MC.⊥-left () npd
  meta-pair-step-error-free (MC.⊥-right not-blame not-proj) npc ()

  meta-single-step-error-free : ∀ {Θ cᵐ d̅ᵐ}
    → Θ MC.⊢ᵐ cᵐ —→ d̅ᵐ
    → ErrorFreeMetaSingle cᵐ
      ---------------------
    → ErrorFreeMetaSeq d̅ᵐ
  meta-single-step-error-free MC.id-fun (ef-funᵐ []ᴬ []ᴬ) = []ᴬ
  meta-single-step-error-free MC.id-code (ef-codeᵐ []ᴬ []ᴬ) = []ᴬ
  meta-single-step-error-free MC.id-ref (ef-refᵐ []ᴬ []ᴬ) = []ᴬ
  meta-single-step-error-free MC.id-forall (ef-forallᵐ []ᴬ) = []ᴬ
  meta-single-step-error-free MC.id-sub (ef-subᵐ []ᴬ) = []ᴬ
  meta-single-step-error-free (MC.ξ-fun-dom c̅ᵐ₁→d̅ᵐ₁) (ef-funᵐ npc̅₁ npc̅₂) =
    ef-funᵐ (meta-seq-step-error-free c̅ᵐ₁→d̅ᵐ₁ npc̅₁) npc̅₂ ∷ᴬ []ᴬ
  meta-single-step-error-free (MC.ξ-fun-cod nf c̅ᵐ₂→d̅ᵐ₂) (ef-funᵐ npc̅₁ npc̅₂) =
    ef-funᵐ npc̅₁ (meta-seq-step-error-free c̅ᵐ₂→d̅ᵐ₂ npc̅₂) ∷ᴬ []ᴬ
  meta-single-step-error-free (MC.ξ-ref-in c̅ᵐ₁→d̅ᵐ₁) (ef-refᵐ npc̅₁ npc̅₂) =
    ef-refᵐ (meta-seq-step-error-free c̅ᵐ₁→d̅ᵐ₁ npc̅₁) npc̅₂ ∷ᴬ []ᴬ
  meta-single-step-error-free (MC.ξ-ref-out nf c̅ᵐ₂→d̅ᵐ₂) (ef-refᵐ npc̅₁ npc̅₂) =
    ef-refᵐ npc̅₁ (meta-seq-step-error-free c̅ᵐ₂→d̅ᵐ₂ npc̅₂) ∷ᴬ []ᴬ
  meta-single-step-error-free (MC.ξ-forall c̅ᵐ→d̅ᵐ) (ef-forallᵐ npc̅) =
    ef-forallᵐ (meta-seq-step-error-free c̅ᵐ→d̅ᵐ npc̅) ∷ᴬ []ᴬ
  meta-single-step-error-free (MC.ξ-sub c̅ᵐ→d̅ᵐ) (ef-subᵐ npc̅) =
    ef-subᵐ (meta-seq-step-error-free c̅ᵐ→d̅ᵐ npc̅) ∷ᴬ []ᴬ
  meta-single-step-error-free (MC.ξ-code c̅ᵒ→d̅ᵒ) (ef-codeᵐ npc̅ᵒ npc̅ᵉ) =
    ef-codeᵐ (code-seq-step-error-free c̅ᵒ→d̅ᵒ npc̅ᵒ) npc̅ᵉ ∷ᴬ []ᴬ
  meta-single-step-error-free (MC.ξ-code-ec nf not-blame c̅ᵉ→d̅ᵉ) (ef-codeᵐ npc̅ᵒ npc̅ᵉ) =
    ef-codeᵐ npc̅ᵒ (ec-seq-step-error-free c̅ᵉ→d̅ᵉ npc̅ᵉ) ∷ᴬ []ᴬ
  meta-single-step-error-free MC.ξ-code-⊥ (ef-codeᵐ (() ∷ᴬ _) npc̅ᵉ)
  meta-single-step-error-free (MC.ξ-code-ec-⊥ nf not-blame) (ef-codeᵐ npc̅ᵒ (() ∷ᴬ _))

  meta-seq-step-error-free : ∀ {Θ c̅ᵐ d̅ᵐ}
    → Θ MC.⊢ᵐ̅ c̅ᵐ —→ d̅ᵐ
    → ErrorFreeMetaSeq c̅ᵐ
      -------------------
    → ErrorFreeMetaSeq d̅ᵐ
  meta-seq-step-error-free (MC.reduce-head cᵐ→dᵐ) (npc ∷ᴬ npc̅) =
    meta-seq-++-error-free (meta-single-step-error-free cᵐ→dᵐ npc) npc̅
  meta-seq-step-error-free (MC.reduce-neighbors nf cᵐ;dᵐ→eᵐ) (npc ∷ᴬ npd ∷ᴬ npc̅) =
    meta-seq-++-error-free (meta-pair-step-error-free cᵐ;dᵐ→eᵐ npc npd) npc̅
  meta-seq-step-error-free (MC.reduce-tail nf irred c̅ᵐ→d̅ᵐ) (npc ∷ᴬ npc̅) =
    npc ∷ᴬ meta-seq-step-error-free c̅ᵐ→d̅ᵐ npc̅


meta-coercion-step-error-free : ∀ {Θ c d}
  → Θ MC.⊢ᵐ̅ c —→ d
  → ErrorFreeMetaCoercion c
    ---------------------
  → ErrorFreeMetaCoercion d
meta-coercion-step-error-free = meta-seq-step-error-free


heap-snoc-error-free : ∀ {μ V}
  → ErrorFreeHeap μ
  → ErrorFreeMetaTerm V
    -------------------------
  → ErrorFreeHeap (μ ∷ʳ V)
heap-snoc-error-free = ∷ʳ⁺


heap-update-error-free : ∀ {μ μ′ a V}
  → ErrorFreeHeap μ
  → μ ⟦ a ↦ V ⟧= μ′
  → ErrorFreeMetaTerm V
    -----------------
  → ErrorFreeHeap μ′
heap-update-error-free (npW ∷ᴬ npμ) H.here npV =
  npV ∷ᴬ npμ
heap-update-error-free (npW ∷ᴬ npμ) (H.there write) npV =
  npW ∷ᴬ heap-update-error-free npμ write npV


mutual

  code-step-error-free : ∀ {C₁ C₂ e}
    → C₁ ∣ e —→ᵒ C₂
    → ErrorFreeHeap (C₁ .μ)
    → ErrorFreeCodeTerm (C₁ .M)
      -------------------------------------------
    → ErrorFreeHeap (C₂ .μ) × ErrorFreeCodeTerm (C₂ .M)
  code-step-error-free (ξ-code (□· Mᵒ) step) npμ (ef-appᵒ npL npM)
    with code-step-error-free step npμ npL
  ... | ⟨ npμ′ , npL′ ⟩ =
    ⟨ npμ′ , ef-appᵒ npL′ npM ⟩
  code-step-error-free (ξ-code ((Vᵒ ·□) vᵒ) step) npμ (ef-appᵒ npV npM)
    with code-step-error-free step npμ npM
  ... | ⟨ npμ′ , npM′ ⟩ =
    ⟨ npμ′ , ef-appᵒ npV npM′ ⟩
  code-step-error-free (ξ-code-blame (□· Mᵒ)) npμ (ef-appᵒ () npM)
  code-step-error-free (ξ-code-blame ((Vᵒ ·□) vᵒ)) npμ (ef-appᵒ npV ())
  code-step-error-free (ξ-splice step) npμ (ef-splice npM)
    with meta-step-error-free-pres step npμ npM
  ... | ⟨ npμ′ , npM′ ⟩ =
    ⟨ npμ′ , ef-splice npM′ ⟩
  code-step-error-free splice-blame npμ (ef-splice ())
  code-step-error-free (splice-β vᵒ) npμ (ef-splice (ef-quote npVᵒ)) =
    ⟨ npμ , npVᵒ ⟩
  code-step-error-free (splice-sub vᵒ) npμ (ef-splice (ef-cast (ef-quote npVᵒ) npc)) =
    ⟨ npμ , npVᵒ ⟩
  code-step-error-free (code-λ {Δ = Δ} {Γᵒ = Γᵒ}) npμ (ef-lamᵒ npNᵒ) =
    ⟨ npμ
    , ef-lamᵒ-val
        (substᵒ-code-error-free {σ = (` freshᵒ Γᵒ) •ᵒₛ idsᵒ}
          (λ where zero → ef-varᵒ ; (suc x) → ef-varᵒ)
          (substᵉ-code-error-free {σ = (` freshᵉ Δ) •ᵉₛ idsᵉ} npNᵒ))
    ⟩
  code-step-error-free (ξ-code-λ̅ step) npμ (ef-lamᵒ-val npNᵒ)
    with code-step-error-free step npμ npNᵒ
  ... | ⟨ npμ′ , npNᵒ′ ⟩ =
    ⟨ npμ′ , ef-lamᵒ-val npNᵒ′ ⟩
  code-step-error-free ξ-code-λ̅-blame npμ (ef-lamᵒ-val ())

  meta-step-error-free-pres : ∀ {C₁ C₂}
    → C₁ —→ᵐ C₂
    → ErrorFreeHeap (C₁ .μ)
    → ErrorFreeMetaTerm (C₁ .M)
      -------------------------------------------
    → ErrorFreeHeap (C₂ .μ) × ErrorFreeMetaTerm (C₂ .M)
  meta-step-error-free-pres (ξ-meta (□· M) step) npμ (ef-appᵐ npL npM)
    with meta-step-error-free-pres step npμ npL
  ... | ⟨ npμ′ , npL′ ⟩ =
    ⟨ npμ′ , ef-appᵐ npL′ npM ⟩
  meta-step-error-free-pres (ξ-meta ((V ·□) v) step) npμ (ef-appᵐ npV npM)
    with meta-step-error-free-pres step npμ npM
  ... | ⟨ npμ′ , npM′ ⟩ =
    ⟨ npμ′ , ef-appᵐ npV npM′ ⟩
  meta-step-error-free-pres (ξ-meta ref□ step) npμ (ef-ref npM)
    with meta-step-error-free-pres step npμ npM
  ... | ⟨ npμ′ , npM′ ⟩ =
    ⟨ npμ′ , ef-ref npM′ ⟩
  meta-step-error-free-pres (ξ-meta (□:= M) step) npμ (ef-assign npL npM)
    with meta-step-error-free-pres step npμ npL
  ... | ⟨ npμ′ , npL′ ⟩ =
    ⟨ npμ′ , ef-assign npL′ npM ⟩
  meta-step-error-free-pres (ξ-meta ((V :=□) v) step) npμ (ef-assign npV npM)
    with meta-step-error-free-pres step npμ npM
  ... | ⟨ npμ′ , npM′ ⟩ =
    ⟨ npμ′ , ef-assign npV npM′ ⟩
  meta-step-error-free-pres (ξ-meta !□ step) npμ (ef-deref npM)
    with meta-step-error-free-pres step npμ npM
  ... | ⟨ npμ′ , npM′ ⟩ =
    ⟨ npμ′ , ef-deref npM′ ⟩
  meta-step-error-free-pres (ξ-meta (□·[ e ]) step) npμ (ef-ecapp npM)
    with meta-step-error-free-pres step npμ npM
  ... | ⟨ npμ′ , npM′ ⟩ =
    ⟨ npμ′ , ef-ecapp npM′ ⟩
  meta-step-error-free-pres (ξ-meta □● step) npμ (ef-subelim npM)
    with meta-step-error-free-pres step npμ npM
  ... | ⟨ npμ′ , npM′ ⟩ =
    ⟨ npμ′ , ef-subelim npM′ ⟩
  meta-step-error-free-pres (ξ-meta (□★ ℓ) step) npμ ()
  meta-step-error-free-pres (ξ-meta (□⟨ c ⟩) step) npμ (ef-cast npM npc)
    with meta-step-error-free-pres step npμ npM
  ... | ⟨ npμ′ , npM′ ⟩ =
    ⟨ npμ′ , ef-cast npM′ npc ⟩
  meta-step-error-free-pres (ξ-meta-blame (□· M)) npμ (ef-appᵐ () npM)
  meta-step-error-free-pres (ξ-meta-blame ((V ·□) v)) npμ (ef-appᵐ npV ())
  meta-step-error-free-pres (ξ-meta-blame ref□) npμ (ef-ref ())
  meta-step-error-free-pres (ξ-meta-blame (□:= M)) npμ (ef-assign () npM)
  meta-step-error-free-pres (ξ-meta-blame ((V :=□) v)) npμ (ef-assign npV ())
  meta-step-error-free-pres (ξ-meta-blame !□) npμ (ef-deref ())
  meta-step-error-free-pres (ξ-meta-blame (□·[ e ])) npμ (ef-ecapp ())
  meta-step-error-free-pres (ξ-meta-blame □●) npμ (ef-subelim ())
  meta-step-error-free-pres (ξ-meta-blame (□★ ℓ)) npμ ()
  meta-step-error-free-pres (ξ-meta-blame (□⟨ c ⟩)) npμ (ef-cast () npc)
  meta-step-error-free-pres (ξ-quote step) npμ (ef-quote npMᵒ)
    with code-step-error-free step npμ npMᵒ
  ... | ⟨ npμ′ , npMᵒ′ ⟩ =
    ⟨ npμ′ , ef-quote npMᵒ′ ⟩
  meta-step-error-free-pres quote-blame npμ (ef-quote ())
  meta-step-error-free-pres (β v) npμ (ef-appᵐ (ef-lamᵐ npN) npV) =
    ⟨ npμ , substᵐ-meta-error-free (λ where zero → npV ; (suc x) → ef-varᵐ) npN ⟩
  meta-step-error-free-pres (β-cast u v inert) npμ (ef-appᵐ (ef-cast npU (ef-funᵐ npc npd ∷ᴬ _)) npW) =
    ⟨ npμ , ef-cast (ef-appᵐ npU (ef-cast npW npc)) npd ⟩
  meta-step-error-free-pres Λ-β npμ (ef-ecapp (ef-eclam npM)) =
    ⟨ npμ , substᵉ-meta-error-free npM ⟩
  meta-step-error-free-pres (Λ-β-cast {e = e} {c = c} u) npμ (ef-ecapp (ef-cast npU (ef-forallᵐ npc ∷ᴬ _))) =
    ⟨ npμ , ef-cast (ef-ecapp npU) (substᵉ-mseq-error-free (e •ᵉₛ idsᵉ) {c̅ = c} npc) ⟩
  meta-step-error-free-pres sub-β npμ (ef-subelim (ef-subintro npM)) =
    ⟨ npμ , npM ⟩
  meta-step-error-free-pres (sub-β-cast u) npμ (ef-subelim (ef-cast npU (ef-subᵐ npc ∷ᴬ _))) =
    ⟨ npμ , ef-cast (ef-subelim npU) npc ⟩
  meta-step-error-free-pres (sub-cast-success u e₁<:e₂ inert) npμ ()
  meta-step-error-free-pres (sub-cast-sub-fail u e₁≮:e₂ inert) npμ ()
  meta-step-error-free-pres (sub-cast-fail u inert mismatch) npμ ()
  meta-step-error-free-pres (ref v) npμ (ef-ref npV) =
    ⟨ heap-snoc-error-free npμ npV , ef-addr ⟩
  meta-step-error-free-pres (deref lookup) npμ (ef-deref npAddr) =
    ⟨ npμ , heap-lookup-error-free npμ lookup ⟩
  meta-step-error-free-pres (assign v write) npμ (ef-assign npAddr npV) =
    ⟨ heap-update-error-free npμ write npV , ef-constᵐ ⟩
  meta-step-error-free-pres (assign-cast v inert) npμ (ef-assign (ef-cast npAddr (ef-refᵐ npc npd ∷ᴬ _)) npV) =
    ⟨ npμ , ef-assign npAddr (ef-cast npV npc) ⟩
  meta-step-error-free-pres (deref-cast inert) npμ (ef-deref (ef-cast npAddr (ef-refᵐ npc npd ∷ᴬ _))) =
    ⟨ npμ , ef-cast (ef-deref npAddr) npd ⟩
  meta-step-error-free-pres (cast-reduce u c⟼d) npμ (ef-cast npU npc) =
    ⟨ npμ , ef-cast npU (meta-coercion-step-error-free c⟼d npc) ⟩
  meta-step-error-free-pres (cast-compose u) npμ (ef-cast (ef-cast npU npc) npd) =
    ⟨ npμ , ef-cast npU (meta-seq-++-error-free npc npd) ⟩
  meta-step-error-free-pres (cast-id u) npμ (ef-cast npU npc) =
    ⟨ npμ , npU ⟩
  meta-step-error-free-pres (cast-blame u) npμ (ef-cast npU (() ∷ᴬ _))
