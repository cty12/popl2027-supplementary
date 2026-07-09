module LambdaAlphaRefStar.Theories.CCAlphaRefStarProgress where

open import Data.List using ([]; [_]; _++_)
open import Data.Product using (∃-syntax) renaming (_,_ to ⟨_,_⟩)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary using (yes; no)

open import Utils using (_∋_⦂_; ∅; here; there; ⟨_,_,_,_⟩)
open import LambdaAlphaRefStar.Theories.CCAlphaRefStarSyntaxAndTypeSystem hiding (idᵉ)
open import LambdaAlphaRefStar.Theories.CCAlphaRefStarSemantics
open import LambdaAlphaRefStar.Theories.CanonicalForms
open import LambdaAlphaRefStar.Theories.Configurations
open import LambdaAlphaRefStar.Theories.ECSubtypeDecidable using (ec-<:?)
open import LambdaAlphaRefStar.Theories.Heap
import LambdaAlphaRefStar.Theories.Heap as H
open import LambdaAlphaRefStar.Theories.Values
import LambdaAlphaRefStar.Theories.CoercionSequences.Meta.Definition as MC
open import LambdaAlphaRefStar.Theories.CoercionSequences.Meta.Definition using (Inert)
import LambdaAlphaRefStar.Theories.CoercionSequences.Meta.Progress as MCP

data CodeProgress (C : Config CodeTerm) (e : EC) : Set where
  stepᵒ : ∀ {C′}
    → C ∣ e —→ᵒ C′
      ---------------------
    → CodeProgress C e

  doneᵒ :
       CodeValue (C .M)
      ---------------------
    → CodeProgress C e

  blameᵒ : ∀ {ℓ}
    → C .M ≡ blameᵒ ℓ
      ---------------------
    → CodeProgress C e

data MetaProgress (C : Config MetaTerm) : Set where
  stepᵐ : ∀ {C′}
    → C —→ᵐ C′
      ------------------
    → MetaProgress C

  doneᵐ :
    Value (C .M)
      ---------------------
    → MetaProgress C

  blameᵐ : ∀ {ℓ}
    → C .M ≡ blame ℓ
      ---------------------
    → MetaProgress C

private
  heap-lookup-progress : ∀ {Δ Θ Γᵒ Σ μ Σ′ a A}
    → HeapTyping Δ Θ Γᵒ Σ μ Σ′
    → Σ′ ∋ a ⦂ A
      -----------------------------------------
    → ∃[ V ] μ ∋ a ⦂ V
  heap-lookup-progress ht-∅ ()
  heap-lookup-progress (ht-, ⊢V ⊢μ) here = ⟨ _ , here ⟩
  heap-lookup-progress (ht-, ⊢V ⊢μ) (there lookup)
    with heap-lookup-progress ⊢μ lookup
  ... | ⟨ V , μ∋V ⟩ = ⟨ V , there μ∋V ⟩

  heap-write-progress : ∀ {Δ Θ Γᵒ Σ μ Σ′ a A V}
    → HeapTyping Δ Θ Γᵒ Σ μ Σ′
    → Σ′ ∋ a ⦂ A
      -----------------------------------------
    → ∃[ μ′ ] μ ⟦ a ↦ V ⟧= μ′
  heap-write-progress ht-∅ ()
  heap-write-progress (ht-, ⊢W ⊢μ) here = ⟨ _ , H.here ⟩
  heap-write-progress (ht-, ⊢W ⊢μ) (there lookup)
    with heap-write-progress ⊢μ lookup
  ... | ⟨ μ′ , μ↦μ′ ⟩ = ⟨ _ , H.there μ↦μ′ ⟩

  progress-star-cast : ∀ {Δ Θ Γᵒ μ U c G ℓ} {g : Ground G}
    → RawValue U
    → Inert (c ++ [ (G MC.！) g ])
      ----------------------------------------------------------------
    → MetaProgress (config Δ Θ Γᵒ μ ((U ⟨ c ++ [ (G MC.！) g ] ⟩) ★ ℓ))
  progress-star-cast {G = ` _} {g = gbase} u inert =
    stepᵐ (sub-cast-fail {e₁ = ε} {e₂ = ε} u inert (λ ()))
  progress-star-cast {G = .(⋆ ⇒ ⋆)} {g = gfun} u inert =
    stepᵐ (sub-cast-fail {e₁ = ε} {e₂ = ε} u inert (λ ()))
  progress-star-cast {G = .(Ref ⋆)} {g = gref} u inert =
    stepᵐ (sub-cast-fail {e₁ = ε} {e₂ = ε} u inert (λ ()))
  progress-star-cast {G = .(‶ ⋆ ″ ⋆)} {g = gcode} u inert =
    stepᵐ (sub-cast-fail {e₁ = ε} {e₂ = ε} u inert (λ ()))
  progress-star-cast {G = .(∀̇ ⋆)} {g = gforall} u inert =
    stepᵐ (sub-cast-fail {e₁ = ε} {e₂ = ε} u inert (λ ()))
  progress-star-cast {Θ = Θ} {G = e₁ <: e₂ => ⋆} {g = gsub} u inert
    with ec-<:? Θ e₁ e₂
  ... | yes e₁<:e₂ = stepᵐ (sub-cast-success u e₁<:e₂ inert)
  ... | no  e₁≮:e₂ = stepᵐ (sub-cast-sub-fail u (λ e₁<:e₂ → e₁≮:e₂ e₁<:e₂) inert)

  progress-assign-ref : ∀ {Δ Θ Γᵒ Σ μ M N A}
    → Value M
    → Value N
    → Δ ; ⟨ Θ , Γᵒ , ∅ , Σ ⟩ ⊢ᵐ M ⦂ Ref A
    → Δ ; Θ ; Γᵒ ; Σ ⊢ᴴ μ
      --------------------------------------
    → MetaProgress (config Δ Θ Γᵒ μ (M := N))
  progress-assign-ref vM vN ⊢M ⊢μ
    with canonical-ref vM ⊢M
  ... | ref-cast {a = a} {c = c} {d = d} inert =
    stepᵐ (assign-cast {a = a} {c = c} {d = d} vN inert)
  ... | ref-addr lookup
    with heap-write-progress ⊢μ lookup
  ...   | ⟨ μ′ , μ↦μ′ ⟩ =
    stepᵐ (assign vN μ↦μ′)

  progress-deref-ref : ∀ {Δ Θ Γᵒ Σ μ M A}
    → Value M
    → Δ ; ⟨ Θ , Γᵒ , ∅ , Σ ⟩ ⊢ᵐ M ⦂ Ref A
    → Δ ; Θ ; Γᵒ ; Σ ⊢ᴴ μ
      --------------------------------------
    → MetaProgress (config Δ Θ Γᵒ μ (! M))
  progress-deref-ref v ⊢M ⊢μ
    with canonical-ref v ⊢M
  ... | ref-cast {a = a} {c = c} {d = d} inert =
    stepᵐ (deref-cast {a = a} {c = c} {d = d} inert)
  ... | ref-addr lookup
    with heap-lookup-progress ⊢μ lookup
  ...   | ⟨ V , μ∋V ⟩ =
    stepᵐ (deref μ∋V)

mutual
  progressᵒ-⊢ : ∀ {Δ Θ Γᵒ Σ μ e M T}
    → Δ ⊢ Θ SubCtx
    → Δ ⊢ Γᵒ OCtx
    → Δ ⊢ Σ HeapCtx
    → Δ ; Θ ; Γᵒ ; Σ ⊢ᴴ μ
    → Δ ; ⟨ Θ , Γᵒ , ∅ , Σ ⟩ ; e ⊢ᵒ M ⦂ T
      --------------------------------------------
    → CodeProgress (config Δ Θ Γᵒ μ M) e
  progressᵒ-⊢ ⊢Θ ⊢Γᵒ ⊢Σ ⊢μ (⊢constᵒ r) =
    doneᵒ is-const
  progressᵒ-⊢ ⊢Θ ⊢Γᵒ ⊢Σ ⊢μ (⊢varᵒ lookup α<:e) =
    doneᵒ is-var
  progressᵒ-⊢ ⊢Θ ⊢Γᵒ ⊢Σ ⊢μ (⊢lamᵒ ⊢M) =
    stepᵒ code-λ
  progressᵒ-⊢ ⊢Θ ⊢Γᵒ ⊢Σ ⊢μ (⊢lamᵒ-val α∈Δ owner edge e₁<:e₂ ⊢M)
    with progressᵒ-⊢ ⊢Θ ⊢Γᵒ ⊢Σ ⊢μ ⊢M
  ... | stepᵒ M—→N = stepᵒ (ξ-code-λ̅ M—→N)
  ... | doneᵒ vᵒ = doneᵒ (is-lamᵒ-val vᵒ)
  ... | blameᵒ refl = stepᵒ ξ-code-λ̅-blame
  progressᵒ-⊢ ⊢Θ ⊢Γᵒ ⊢Σ ⊢μ (⊢appᵒ {L = L} {M = M} ⊢L ⊢M)
    with progressᵒ-⊢ ⊢Θ ⊢Γᵒ ⊢Σ ⊢μ ⊢L
  ... | stepᵒ L—→L′ = stepᵒ (ξ-code (□· M) L—→L′)
  ... | blameᵒ refl = stepᵒ (ξ-code-blame (□· M))
  ... | doneᵒ vL
    with progressᵒ-⊢ ⊢Θ ⊢Γᵒ ⊢Σ ⊢μ ⊢M
  ...   | stepᵒ M—→M′ = stepᵒ (ξ-code ((L ·□) vL) M—→M′)
  ...   | blameᵒ refl = stepᵒ (ξ-code-blame ((L ·□) vL))
  ...   | doneᵒ vM = doneᵒ (is-app vL vM)
  progressᵒ-⊢ ⊢Θ ⊢Γᵒ ⊢Σ ⊢μ (⊢splice ⊢M O↪T)
    with progressᵐ-⊢ ⊢Θ ⊢Γᵒ ⊢Σ ⊢μ ⊢M
  ... | stepᵐ M—→N = stepᵒ (ξ-splice M—→N)
  ... | blameᵐ refl = stepᵒ splice-blame
  ... | doneᵐ v
    with canonical-code v ⊢M O↪T
  ...   | code-quote vᵒ = stepᵒ (splice-β vᵒ)
  ...   | code-sub vᵒ = stepᵒ (splice-sub vᵒ)
  progressᵒ-⊢ ⊢Θ ⊢Γᵒ ⊢Σ ⊢μ (⊢blameᵒ ℓ) =
    blameᵒ refl

  progressᵐ-⊢ : ∀ {Δ Θ Γᵒ Σ μ M A}
    → Δ ⊢ Θ SubCtx
    → Δ ⊢ Γᵒ OCtx
    → Δ ⊢ Σ HeapCtx
    → Δ ; Θ ; Γᵒ ; Σ ⊢ᴴ μ
    → Δ ; ⟨ Θ , Γᵒ , ∅ , Σ ⟩ ⊢ᵐ M ⦂ A
      --------------------------------------------
    → MetaProgress (config Δ Θ Γᵒ μ M)
  progressᵐ-⊢ ⊢Θ ⊢Γᵒ ⊢Σ ⊢μ (⊢constᵐ r) =
    doneᵐ (V-raw U-const)
  progressᵐ-⊢ ⊢Θ ⊢Γᵒ ⊢Σ ⊢μ (⊢varᵐ ())
  progressᵐ-⊢ ⊢Θ ⊢Γᵒ ⊢Σ ⊢μ (⊢addr lookup) =
    doneᵐ (V-raw U-addr)
  progressᵐ-⊢ ⊢Θ ⊢Γᵒ ⊢Σ ⊢μ (⊢lamᵐ ⊢A ⊢M) =
    doneᵐ (V-raw U-ƛ)
  progressᵐ-⊢ ⊢Θ ⊢Γᵒ ⊢Σ ⊢μ (⊢appᵐ {L = L} {M = M} ⊢L ⊢M)
    with progressᵐ-⊢ ⊢Θ ⊢Γᵒ ⊢Σ ⊢μ ⊢L
  ... | stepᵐ L—→L′ = stepᵐ (ξ-meta (□· M) L—→L′)
  ... | blameᵐ refl = stepᵐ (ξ-meta-blame (□· M))
  ... | doneᵐ vL
    with progressᵐ-⊢ ⊢Θ ⊢Γᵒ ⊢Σ ⊢μ ⊢M
  ...   | stepᵐ M—→M′ = stepᵐ (ξ-meta ((L ·□) vL) M—→M′)
  ...   | blameᵐ refl =
    stepᵐ (ξ-meta-blame ((L ·□) vL))
  ...   | doneᵐ vM
    with canonical-fun vL ⊢L
  ...     | fun-ƛ =
    stepᵐ (β vM)
  ...     | fun-cast {U = U} {c = c} {d = d} u inert =
    stepᵐ (β-cast {U = U} {c = c} {d = d} u vM inert)
  progressᵐ-⊢ ⊢Θ ⊢Γᵒ ⊢Σ ⊢μ (⊢eclam ⊢M) =
    doneᵐ (V-raw U-Λ)
  progressᵐ-⊢ ⊢Θ ⊢Γᵒ ⊢Σ ⊢μ (⊢ecapp {e = e} ⊢M ⊢e)
    with progressᵐ-⊢ ⊢Θ ⊢Γᵒ ⊢Σ ⊢μ ⊢M
  ... | stepᵐ M—→N = stepᵐ (ξ-meta (□·[ e ]) M—→N)
  ... | blameᵐ refl = stepᵐ (ξ-meta-blame (□·[ e ]))
  ... | doneᵐ v
    with canonical-forall v ⊢M
  ...   | forall-Λ = stepᵐ Λ-β
  ...   | forall-cast {U = U} {c = c} u inert = stepᵐ (Λ-β-cast {U = U} {c = c} u)
  progressᵐ-⊢ ⊢Θ ⊢Γᵒ ⊢Σ ⊢μ (⊢subintro ⊢e₁ ⊢e₂ ⊢M) =
    doneᵐ (V-raw U-sub)
  progressᵐ-⊢ ⊢Θ ⊢Γᵒ ⊢Σ ⊢μ (⊢subelim ⊢M e₁<:e₂)
    with progressᵐ-⊢ ⊢Θ ⊢Γᵒ ⊢Σ ⊢μ ⊢M
  ... | stepᵐ M—→N = stepᵐ (ξ-meta □● M—→N)
  ... | blameᵐ refl = stepᵐ (ξ-meta-blame □●)
  ... | doneᵐ v
    with canonical-sub v ⊢M
  ...   | sub-intro = stepᵐ sub-β
  ...   | sub-cast {c = c} u inert = stepᵐ (sub-β-cast {c = c} u)
  progressᵐ-⊢ ⊢Θ ⊢Γᵒ ⊢Σ ⊢μ (⊢subelim⋆ ⊢M ℓ)
    with progressᵐ-⊢ ⊢Θ ⊢Γᵒ ⊢Σ ⊢μ ⊢M
  ... | stepᵐ M—→N = stepᵐ (ξ-meta (□★ ℓ) M—→N)
  ... | blameᵐ refl = stepᵐ (ξ-meta-blame (□★ ℓ))
  ... | doneᵐ v
    with canonical-star v ⊢M
  ...   | star-inj u inert = progress-star-cast u inert
  progressᵐ-⊢ ⊢Θ ⊢Γᵒ ⊢Σ ⊢μ (⊢quote {e = e} ⊢M ⊢e O↪T)
    with progressᵒ-⊢ ⊢Θ ⊢Γᵒ ⊢Σ ⊢μ ⊢M
  ... | stepᵒ M—→N = stepᵐ (ξ-quote M—→N)
  ... | blameᵒ refl = stepᵐ quote-blame
  ... | doneᵒ vᵒ = doneᵐ (V-raw (U-quote vᵒ))
  progressᵐ-⊢ ⊢Θ ⊢Γᵒ ⊢Σ ⊢μ (⊢ref ⊢M)
    with progressᵐ-⊢ ⊢Θ ⊢Γᵒ ⊢Σ ⊢μ ⊢M
  ... | stepᵐ M—→N = stepᵐ (ξ-meta ref□ M—→N)
  ... | blameᵐ refl = stepᵐ (ξ-meta-blame ref□)
  ... | doneᵐ v = stepᵐ (ref v)
  progressᵐ-⊢ ⊢Θ ⊢Γᵒ ⊢Σ ⊢μ (⊢assign {M = M} {N = N} ⊢M ⊢N)
    with progressᵐ-⊢ ⊢Θ ⊢Γᵒ ⊢Σ ⊢μ ⊢M
  ... | stepᵐ M—→M′ = stepᵐ (ξ-meta (□:= N) M—→M′)
  ... | blameᵐ refl = stepᵐ (ξ-meta-blame (□:= N))
  ... | doneᵐ vM
    with progressᵐ-⊢ ⊢Θ ⊢Γᵒ ⊢Σ ⊢μ ⊢N
  ...   | stepᵐ N—→N′ = stepᵐ (ξ-meta ((M :=□) vM) N—→N′)
  ...   | blameᵐ refl = stepᵐ (ξ-meta-blame ((M :=□) vM))
  ...   | doneᵐ vN = progress-assign-ref vM vN ⊢M ⊢μ
  progressᵐ-⊢ ⊢Θ ⊢Γᵒ ⊢Σ ⊢μ (⊢deref ⊢M)
    with progressᵐ-⊢ ⊢Θ ⊢Γᵒ ⊢Σ ⊢μ ⊢M
  ... | stepᵐ M—→N = stepᵐ (ξ-meta !□ M—→N)
  ... | blameᵐ refl = stepᵐ (ξ-meta-blame !□)
  ... | doneᵐ v = progress-deref-ref v ⊢M ⊢μ
  progressᵐ-⊢ ⊢Θ ⊢Γᵒ ⊢Σ ⊢μ (⊢cast {c = c} ⊢M ⊢c)
    with progressᵐ-⊢ ⊢Θ ⊢Γᵒ ⊢Σ ⊢μ ⊢M
  ... | stepᵐ M—→N = stepᵐ (ξ-meta (□⟨ c ⟩) M—→N)
  ... | blameᵐ refl = stepᵐ (ξ-meta-blame (□⟨ c ⟩))
  ... | doneᵐ (V-cast u inert) = stepᵐ (cast-compose u)
  ... | doneᵐ (V-raw u)
    with MCP.progress ⊢c
  ...   | MCP.step c→d = stepᵐ (cast-reduce u c→d)
  ...   | MCP.done MC.nf-empty = stepᵐ (cast-id u)
  ...   | MCP.done (MC.nf-singleton MC.nf-⊥) = stepᵐ (cast-blame u)
  ...   | MCP.done nf@(MC.nf-singleton MC.nf-!) =
    doneᵐ (V-cast u ⟨ nf , ⟨ (λ ()) , (λ { ⟨ _ , () ⟩ }) ⟩ ⟩)
  ...   | MCP.done nf@(MC.nf-singleton MC.nf-?) =
    doneᵐ (V-cast u ⟨ nf , ⟨ (λ ()) , (λ { ⟨ _ , () ⟩ }) ⟩ ⟩)
  ...   | MCP.done nf@(MC.nf-singleton (MC.nf-fun _ _ _)) =
    doneᵐ (V-cast u ⟨ nf , ⟨ (λ ()) , (λ { ⟨ _ , () ⟩ }) ⟩ ⟩)
  ...   | MCP.done nf@(MC.nf-singleton (MC.nf-code _ _ _ _ _)) =
    doneᵐ (V-cast u ⟨ nf , ⟨ (λ ()) , (λ { ⟨ _ , () ⟩ }) ⟩ ⟩)
  ...   | MCP.done nf@(MC.nf-singleton (MC.nf-ref _ _ _)) =
    doneᵐ (V-cast u ⟨ nf , ⟨ (λ ()) , (λ { ⟨ _ , () ⟩ }) ⟩ ⟩)
  ...   | MCP.done nf@(MC.nf-singleton (MC.nf-forall _ _)) =
    doneᵐ (V-cast u ⟨ nf , ⟨ (λ ()) , (λ { ⟨ _ , () ⟩ }) ⟩ ⟩)
  ...   | MCP.done nf@(MC.nf-singleton (MC.nf-sub _ _)) =
    doneᵐ (V-cast u ⟨ nf , ⟨ (λ ()) , (λ { ⟨ _ , () ⟩ }) ⟩ ⟩)
  ...   | MCP.done nf@(MC.nf-step _ _ _) =
    doneᵐ (V-cast u ⟨ nf , ⟨ (λ ()) , (λ { ⟨ _ , () ⟩ }) ⟩ ⟩)
  progressᵐ-⊢ ⊢Θ ⊢Γᵒ ⊢Σ ⊢μ (⊢blame ⊢A ℓ) = blameᵐ refl

progressᵒ : ∀ {C Σ e T}
  → WTCodeConfig C Σ e T
    ---------------------------
  → CodeProgress C e
progressᵒ (wtCodeConfig ⊢Θ ⊢Γᵒ ⊢Σ ⊢μ ⊢M) = progressᵒ-⊢ ⊢Θ ⊢Γᵒ ⊢Σ ⊢μ ⊢M

progressᵐ : ∀ {C Σ A}
  → WTMetaConfig C Σ A
    ---------------------------
  → MetaProgress C
progressᵐ (wtMetaConfig ⊢Θ ⊢Γᵒ ⊢Σ ⊢μ ⊢M) = progressᵐ-⊢ ⊢Θ ⊢Γᵒ ⊢Σ ⊢μ ⊢M
