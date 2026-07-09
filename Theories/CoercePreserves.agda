module Theories.CoercePreserves where

open import Theories.BlameLabels
open import Theories.EnvClassifiers
open import Theories.CodeTypes
open import Theories.MetaTypes
open import Theories.ConsistentSubtyping
open import Theories.Coerce
open import Theories.CoercionSequences.EC.Definition using (_;_⊢ᵉ̅_⦂_⇒_)
open import Theories.CoercionSequences.Code.Definition using (⊢ᵒ̅_⦂_⇒_)
open import Theories.CoercionSequences.Meta.Definition using (_;_⊢ᵐ̅_⦂_⇒_)
import Theories.CoercionSequences.EC.Definition as EC
import Theories.CoercionSequences.Code.Definition as OC
import Theories.CoercionSequences.Meta.Definition as MC
import Theories.CoercionSequences.Code.Preservation as OCP
import Theories.CoercionSequences.Meta.Preservation as MCP


coerceᵉ-preserves : ∀ {Δ Θ ê ê′ ℓ}
  → Δ ⊢ᵉ⋆ ê
  → Δ ⊢ᵉ⋆ ê′
  → (ê≲ê′ : Θ ⊢ᵉ ê ≲ ê′)
    ---------------------------------------------
  → Δ ; Θ ⊢ᵉ̅ coerceᵉ ê≲ê′ ℓ ⦂ ê ⇒ ê′
coerceᵉ-preserves wf-⋆ wf-⋆ csubᵉ-⋆-left =
  EC.⊢; (EC.⊢↑ wf-⋆ wf-⋆ <:-⋆) (EC.⊢[] wf-⋆)
coerceᵉ-preserves wf-⋆ wf-⋆ csubᵉ-⋆-right =
  EC.⊢; (EC.⊢↑ wf-⋆ wf-⋆ <:-⋆) (EC.⊢[] wf-⋆)
coerceᵉ-preserves {ℓ = ℓ} wf-⋆ (wf-ec ⊢e) csubᵉ-⋆-left =
  EC.⊢; (EC.⊢? _ ⊢e ℓ) (EC.⊢[] (EC.wf-ec ⊢e))
coerceᵉ-preserves (wf-ec ⊢e) wf-⋆ csubᵉ-⋆-right =
  EC.⊢; (EC.⊢! _ ⊢e) (EC.⊢[] EC.wf-⋆)
coerceᵉ-preserves (wf-ec ⊢e) (wf-ec ⊢e′) (csubᵉ-ec e<:e′) =
  EC.⊢; (EC.⊢↑ (wf-ec ⊢e) (wf-ec ⊢e′) (<:-ec e<:e′)) (EC.⊢[] (wf-ec ⊢e′))

coerceᵒ-preserves : ∀ {O O′ ℓ}
  → (O≲O′ : O ≲ᵒ O′)
    ---------------------------------------
  → ⊢ᵒ̅ coerceᵒ O≲O′ ℓ ⦂ O ⇒ O′
coerceᵒ-preserves {⋆} {⋆} csubᵒ-⋆-left = OC.⊢[]
coerceᵒ-preserves {⋆} {⋆} csubᵒ-⋆-right = OC.⊢[]
coerceᵒ-preserves {⋆} {` ι} {ℓ = ℓ} csubᵒ-⋆-left =
  OC.⊢; (OC.⊢? ℓ gbase) OC.⊢[]
coerceᵒ-preserves {` ι} {⋆} csubᵒ-⋆-right =
  OC.⊢; (OC.⊢! gbase) OC.⊢[]
coerceᵒ-preserves {` ι} {` .ι} csubᵒ-base = OC.⊢[]
coerceᵒ-preserves {⋆} {O₁ ⇒ O₂} {ℓ = ℓ} csubᵒ-⋆-left =
  OCP.++-preserve
    (OC.⊢; (OC.⊢? ℓ gfun) OC.⊢[])
    (OC.⊢;
      (OC.⊢fun (coerceᵒ-preserves (csubᵒ-⋆-right {O₁}))
               (coerceᵒ-preserves (csubᵒ-⋆-left {O₂})))
      OC.⊢[])
coerceᵒ-preserves {O₁ ⇒ O₂} {⋆} csubᵒ-⋆-right =
  OCP.++-preserve
    (OC.⊢;
      (OC.⊢fun (coerceᵒ-preserves (csubᵒ-⋆-left {O₁}))
               (coerceᵒ-preserves (csubᵒ-⋆-right {O₂})))
      OC.⊢[])
    (OC.⊢; (OC.⊢! gfun) OC.⊢[])
coerceᵒ-preserves {O₁ ⇒ O₂} {O₁′ ⇒ O₂′} (csubᵒ-fun O₁′≲O₁ O₂≲O₂′) =
  OC.⊢; (OC.⊢fun (coerceᵒ-preserves O₁′≲O₁) (coerceᵒ-preserves O₂≲O₂′)) OC.⊢[]


mutual
  coerce-from⋆-preserves : ∀ {Δ ℓ}
    → (Θ : SubCtx)
    → (B : MType)
    → Δ ⊢ᵐᵗ B
      -----------------------------------------------
    → Δ ; Θ ⊢ᵐ̅ coerce-from⋆ Θ B ℓ ⦂ ⋆ ⇒ B
  coerce-from⋆-preserves Θ ⋆ wf-⋆ = MC.⊢[] wf-⋆
  coerce-from⋆-preserves {ℓ = ℓ} Θ (` ι) wf-base =
    MC.⊢; (MC.⊢? wf-base ℓ gbase) (MC.⊢[] wf-base)
  coerce-from⋆-preserves {ℓ = ℓ} Θ (A ⇒ B) (wf-fun ⊢A ⊢B) =
    MCP.++ᵐ-preserve
      (MC.⊢; (MC.⊢? (wf-fun wf-⋆ wf-⋆) ℓ gfun)
             (MC.⊢[] (wf-fun wf-⋆ wf-⋆)))
      (MC.⊢;
        (MC.⊢fun (coerce-to⋆-preserves Θ A ⊢A)
                 (coerce-from⋆-preserves Θ B ⊢B))
        (MC.⊢[] (wf-fun ⊢A ⊢B)))
  coerce-from⋆-preserves {ℓ = ℓ} Θ (Ref A) (wf-ref ⊢A) =
    MCP.++ᵐ-preserve
      (MC.⊢; (MC.⊢? (wf-ref wf-⋆) ℓ gref)
             (MC.⊢[] (wf-ref wf-⋆)))
      (MC.⊢;
        (MC.⊢ref (coerce-to⋆-preserves Θ A ⊢A)
                 (coerce-from⋆-preserves Θ A ⊢A))
        (MC.⊢[] (wf-ref ⊢A)))
  coerce-from⋆-preserves {ℓ = ℓ} Θ (‶ O ″ ê) (wf-code ⊢ê) =
    MCP.++ᵐ-preserve
      (MC.⊢; (MC.⊢? (wf-code wf-⋆) ℓ gcode)
             (MC.⊢[] (wf-code wf-⋆)))
      (MC.⊢;
        (MC.⊢code (coerceᵒ-preserves (csubᵒ-⋆-left {O}))
                  (coerceᵉ-preserves wf-⋆ ⊢ê (csubᵉ-⋆-left {Θ} {ê})))
        (MC.⊢[] (MC.wf-code ⊢ê)))
  coerce-from⋆-preserves {ℓ = ℓ} Θ (∀̇ A) (wf-forall ⊢A) =
    MCP.++ᵐ-preserve
      (MC.⊢; (MC.⊢? (wf-forall wf-⋆) ℓ gforall)
             (MC.⊢[] (wf-forall wf-⋆)))
      (MC.⊢;
        (MC.⊢forall (coerce-from⋆-preserves (⇑ᵉ-subctx Θ) A ⊢A))
        (MC.⊢[] (wf-forall ⊢A)))
  coerce-from⋆-preserves {ℓ = ℓ} Θ (e₁ <: e₂ => A) (wf-sub ⊢e₁ ⊢e₂ ⊢A) =
    MCP.++ᵐ-preserve
      (MC.⊢; (MC.⊢? (wf-sub ⊢e₁ ⊢e₂ wf-⋆) ℓ gsub)
             (MC.⊢[] (wf-sub ⊢e₁ ⊢e₂ wf-⋆)))
      (MC.⊢;
        (MC.⊢sub ⊢e₁ ⊢e₂ (coerce-from⋆-preserves (Θ , e₁ <: e₂) A ⊢A))
        (MC.⊢[] (wf-sub ⊢e₁ ⊢e₂ ⊢A)))

  coerce-to⋆-preserves : ∀ {Δ ℓ}
    → (Θ : SubCtx)
    → (A : MType)
    → Δ ⊢ᵐᵗ A
      -----------------------------------------------
    → Δ ; Θ ⊢ᵐ̅ coerce-to⋆ Θ A ℓ ⦂ A ⇒ ⋆
  coerce-to⋆-preserves Θ ⋆ wf-⋆ = MC.⊢[] wf-⋆
  coerce-to⋆-preserves Θ (` ι) wf-base =
    MC.⊢; (MC.⊢! wf-base gbase) (MC.⊢[] MC.wf-⋆)
  coerce-to⋆-preserves Θ (A ⇒ B) (wf-fun ⊢A ⊢B) =
    MCP.++ᵐ-preserve
      (MC.⊢;
        (MC.⊢fun (coerce-from⋆-preserves Θ A ⊢A)
                 (coerce-to⋆-preserves Θ B ⊢B))
        (MC.⊢[] (wf-fun wf-⋆ wf-⋆)))
      (MC.⊢; (MC.⊢! (wf-fun wf-⋆ wf-⋆) gfun) (MC.⊢[] MC.wf-⋆))
  coerce-to⋆-preserves Θ (Ref A) (wf-ref ⊢A) =
    MCP.++ᵐ-preserve
      (MC.⊢;
        (MC.⊢ref (coerce-from⋆-preserves Θ A ⊢A)
                 (coerce-to⋆-preserves Θ A ⊢A))
        (MC.⊢[] (wf-ref wf-⋆)))
      (MC.⊢; (MC.⊢! (wf-ref wf-⋆) gref) (MC.⊢[] MC.wf-⋆))
  coerce-to⋆-preserves Θ (‶ O ″ ê) (wf-code ⊢ê) =
    MCP.++ᵐ-preserve
      (MC.⊢;
        (MC.⊢code (coerceᵒ-preserves (csubᵒ-⋆-right {O}))
                  (coerceᵉ-preserves ⊢ê wf-⋆ (csubᵉ-⋆-right {Θ} {ê})))
        (MC.⊢[] (MC.wf-code wf-⋆)))
      (MC.⊢; (MC.⊢! (wf-code wf-⋆) gcode) (MC.⊢[] MC.wf-⋆))
  coerce-to⋆-preserves Θ (∀̇ A) (wf-forall ⊢A) =
    MCP.++ᵐ-preserve
      (MC.⊢;
        (MC.⊢forall (coerce-to⋆-preserves (⇑ᵉ-subctx Θ) A ⊢A))
        (MC.⊢[] (wf-forall wf-⋆)))
      (MC.⊢; (MC.⊢! (wf-forall wf-⋆) gforall) (MC.⊢[] MC.wf-⋆))
  coerce-to⋆-preserves Θ (e₁ <: e₂ => A) (wf-sub ⊢e₁ ⊢e₂ ⊢A) =
    MCP.++ᵐ-preserve
      (MC.⊢;
        (MC.⊢sub ⊢e₁ ⊢e₂ (coerce-to⋆-preserves (Θ , e₁ <: e₂) A ⊢A))
        (MC.⊢[] (wf-sub ⊢e₁ ⊢e₂ wf-⋆)))
      (MC.⊢; (MC.⊢! (wf-sub ⊢e₁ ⊢e₂ wf-⋆) gsub) (MC.⊢[] MC.wf-⋆))

  coerceᵐ-preserves : ∀ {Δ Θ A B ℓ}
    → Δ ⊢ᵐᵗ A
    → Δ ⊢ᵐᵗ B
    → (A≲B : Θ ⊢ A ≲ B)
      ---------------------------------------------
    → Δ ; Θ ⊢ᵐ̅ coerceᵐ A≲B ℓ ⦂ A ⇒ B
  coerceᵐ-preserves wf-⋆ ⊢B csub-⋆-left =
    coerce-from⋆-preserves _ _ ⊢B
  coerceᵐ-preserves ⊢A wf-⋆ csub-⋆-right =
    coerce-to⋆-preserves _ _ ⊢A
  coerceᵐ-preserves wf-base wf-base csub-base =
    MC.⊢[] wf-base
  coerceᵐ-preserves (wf-fun ⊢A ⊢B) (wf-fun ⊢A′ ⊢B′) (csub-fun A′≲A B≲B′) =
    MC.⊢;
      (MC.⊢fun (coerceᵐ-preserves ⊢A′ ⊢A A′≲A)
               (coerceᵐ-preserves ⊢B ⊢B′ B≲B′))
      (MC.⊢[] (wf-fun ⊢A′ ⊢B′))
  coerceᵐ-preserves (wf-ref ⊢A) (wf-ref ⊢B) (csub-ref A≲B B≲A) =
    MC.⊢;
      (MC.⊢ref (coerceᵐ-preserves ⊢B ⊢A B≲A)
               (coerceᵐ-preserves ⊢A ⊢B A≲B))
      (MC.⊢[] (wf-ref ⊢B))
  coerceᵐ-preserves (wf-code ⊢ê) (wf-code ⊢ê′) (csub-code O≲O′ ê≲ê′) =
    MC.⊢;
      (MC.⊢code (coerceᵒ-preserves O≲O′)
                (coerceᵉ-preserves ⊢ê ⊢ê′ ê≲ê′))
      (MC.⊢[] (MC.wf-code ⊢ê′))
  coerceᵐ-preserves (wf-forall ⊢A) (wf-forall ⊢B) (csub-univ A≲B) =
    MC.⊢;
      (MC.⊢forall (coerceᵐ-preserves ⊢A ⊢B A≲B))
      (MC.⊢[] (wf-forall ⊢B))
  coerceᵐ-preserves (wf-sub ⊢e₁ ⊢e₂ ⊢A) (wf-sub _ _ ⊢B) (csub-sub A≲B) =
    MC.⊢;
      (MC.⊢sub ⊢e₁ ⊢e₂ (coerceᵐ-preserves ⊢A ⊢B A≲B))
      (MC.⊢[] (wf-sub ⊢e₁ ⊢e₂ ⊢B))
