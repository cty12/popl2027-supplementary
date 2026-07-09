module LambdaAlphaRefStar.Theories.Coerce where

open import Data.List using ([]; [_]; _++_)

open import LambdaAlphaRefStar.Theories.BlameLabels
open import LambdaAlphaRefStar.Theories.EnvClassifiers
open import LambdaAlphaRefStar.Theories.CodeTypes
open import LambdaAlphaRefStar.Theories.MetaTypes
open import LambdaAlphaRefStar.Theories.ConsistentSubtyping
import LambdaAlphaRefStar.Theories.CoercionSequences.EC.Definition as ECS
import LambdaAlphaRefStar.Theories.CoercionSequences.Code.Definition as OC
import LambdaAlphaRefStar.Theories.CoercionSequences.Meta.Definition as MC


-- | Generate an EC coercion sequence from consistent subtyping for EC.
coerceᵉ : ∀ {Θ ê ê′}
  → Θ ⊢ᵉ ê ≲ ê′
  → BlameLabel
    ---------------------
  → ECS.ECCoercionSeq
coerceᵉ {Θ} {⋆}    {⋆}     _                ℓ = [ ECS.⋆ ECS.↑ ECS.⋆ ]
coerceᵉ {Θ} {⋆}    {ec e}  csubᵉ-⋆-left     ℓ = [ e ECS.？ ℓ ]
coerceᵉ {Θ} {ec e} {⋆}     csubᵉ-⋆-right    ℓ = [ e ECS.！ ]
coerceᵉ {Θ} {ec e} {ec e′} (csubᵉ-ec e<:e′) ℓ = [ ECS.ec e ECS.↑ ECS.ec e′ ]


-- | Generate a code coercion sequence from consistent subtyping for code.
coerceᵒ : ∀ {O O′}
  → O ≲ᵒ O′
  → BlameLabel
    ---------------------
  → OC.OCoercionSeq
coerceᵒ {⋆} {⋆}      _ _             = []
coerceᵒ {⋆} {` ι}    csubᵒ-⋆-left  ℓ = [ ((` ι OC.？ ℓ) OC.gbase) ]
coerceᵒ {` ι} {⋆}    csubᵒ-⋆-right ℓ = [ ((` ι OC.！) OC.gbase) ]
coerceᵒ {` ι} {` .ι} csubᵒ-base    ℓ = []
coerceᵒ {⋆} {O₁ ⇒ O₂} csubᵒ-⋆-left ℓ =
  let O₁≲⋆ = csubᵒ-⋆-right {O₁}
      ⋆≲O₂ = csubᵒ-⋆-left  {O₂} in
  [ (((⋆ ⇒ ⋆) OC.？ ℓ) OC.gfun) ] ++ [ coerceᵒ O₁≲⋆ ℓ OC.⇒ coerceᵒ ⋆≲O₂ ℓ ]
coerceᵒ {O₁ ⇒ O₂} {⋆} csubᵒ-⋆-right ℓ =
  let ⋆≲O₁ = csubᵒ-⋆-left  {O₁}
      O₂≲⋆ = csubᵒ-⋆-right {O₂} in
  [ coerceᵒ ⋆≲O₁ ℓ OC.⇒ coerceᵒ O₂≲⋆ ℓ ] ++ [ (((⋆ ⇒ ⋆) OC.！) OC.gfun) ]
coerceᵒ {O₁ ⇒ O₂} {O₁′ ⇒ O₂′} (csubᵒ-fun O₁′≲O₁ O₂≲O₂′) ℓ =
  [ coerceᵒ O₁′≲O₁ ℓ OC.⇒ coerceᵒ O₂≲O₂′ ℓ ]


mutual

  coerce-from⋆ : ∀ Θ
    → (B : MType)
    → BlameLabel
      ---------------------
    → MC.MCoercionSeq
  coerce-from⋆ Θ ⋆     _ = []
  coerce-from⋆ Θ (` ι) ℓ = [ ((` ι MC.？ ℓ) MC.gbase) ]
  coerce-from⋆ Θ (A ⇒ B) ℓ =
    [ (((⋆ ⇒ ⋆) MC.？ ℓ) MC.gfun) ] ++ [ coerce-to⋆ Θ A ℓ MC.⇒ coerce-from⋆ Θ B ℓ ]
  coerce-from⋆ Θ (Ref A) ℓ =
    [ (((Ref ⋆) MC.？ ℓ) MC.gref) ] ++ [ MC.Ref (coerce-to⋆ Θ A ℓ) , (coerce-from⋆ Θ A ℓ) ]
  coerce-from⋆ Θ (‶ O ″ ê) ℓ =
    let ⋆≲O = csubᵒ-⋆-left {O}
        ⋆≲ê = csubᵉ-⋆-left {Θ} {ê} in
    [ (((‶ ⋆ ″ ⋆) MC.？ ℓ) MC.gcode) ] ++ [ MC.‶ coerceᵒ ⋆≲O ℓ ″ coerceᵉ ⋆≲ê ℓ ]
  coerce-from⋆ Θ (∀̇ A) ℓ =
    [ (((∀̇ ⋆) MC.？ ℓ) MC.gforall) ] ++ [ MC.∀̇ (coerce-from⋆ (⇑ᵉ-subctx Θ) A ℓ) ]
  coerce-from⋆ Θ (e₁ <: e₂ => A) ℓ =
    [ (((e₁ <: e₂ => ⋆) MC.？ ℓ) MC.gsub) ] ++ [ e₁ MC.<: e₂ => coerce-from⋆ (Θ , e₁ <: e₂) A ℓ ]


  coerce-to⋆ : ∀ Θ
    → (A : MType)
    → BlameLabel
      ---------------------
    → MC.MCoercionSeq
  coerce-to⋆ Θ ⋆     _ = []
  coerce-to⋆ Θ (` ι) ℓ = [ ((` ι MC.！) MC.gbase) ]
  coerce-to⋆ Θ (A ⇒ B) ℓ =
    [ coerce-from⋆ Θ A ℓ MC.⇒ coerce-to⋆ Θ B ℓ ] ++ [ (((⋆ ⇒ ⋆) MC.！) MC.gfun) ]
  coerce-to⋆ Θ (Ref A) ℓ =
    [ MC.Ref (coerce-from⋆ Θ A ℓ) , (coerce-to⋆ Θ A ℓ) ] ++ [ (((Ref ⋆) MC.！) MC.gref) ]
  coerce-to⋆ Θ (‶ O ″ ê) ℓ =
    let O≲⋆ = csubᵒ-⋆-right {O}
        ê≲⋆ = csubᵉ-⋆-right {Θ} {ê} in
    [ MC.‶ coerceᵒ O≲⋆ ℓ ″ coerceᵉ ê≲⋆ ℓ ] ++ [ (((‶ ⋆ ″ ⋆) MC.！) MC.gcode) ]
  coerce-to⋆ Θ (∀̇ A) ℓ =
    [ MC.∀̇ (coerce-to⋆ (⇑ᵉ-subctx Θ) A ℓ) ] ++ [ (((∀̇ ⋆) MC.！) MC.gforall) ]
  coerce-to⋆ Θ (e₁ <: e₂ => A) ℓ =
    [ e₁ MC.<: e₂ => coerce-to⋆ (Θ , e₁ <: e₂) A ℓ ] ++ [ (((e₁ <: e₂ => ⋆) MC.！) MC.gsub) ]

  -- | Generate a meta coercion sequence from consistent subtyping for meta.
  coerceᵐ : ∀ {Θ A B}
    → Θ ⊢ A ≲ B
    → BlameLabel
      ---------------------
    → MC.MCoercionSeq
  coerceᵐ {Θ} {.⋆}  {B}     csub-⋆-left  ℓ = coerce-from⋆ Θ B ℓ
  coerceᵐ {Θ} {A}   {.⋆}    csub-⋆-right ℓ = coerce-to⋆ Θ A ℓ
  coerceᵐ {Θ} {` ι} {` .ι}  csub-base    _ = []
  coerceᵐ {A = A ⇒ B} {B = A′ ⇒ B′} (csub-fun A′≲A B≲B′) ℓ =
    [ coerceᵐ A′≲A ℓ MC.⇒ coerceᵐ B≲B′ ℓ ]
  coerceᵐ {A = Ref A} {B = Ref B} (csub-ref A≲B B≲A) ℓ =
    [ MC.Ref (coerceᵐ B≲A ℓ) , (coerceᵐ A≲B ℓ) ]
  coerceᵐ {A = ‶ O ″ ê} {B = ‶ O′ ″ ê′} (csub-code O≲O′ ê≲ê′) ℓ =
    [ MC.‶ coerceᵒ O≲O′ ℓ ″ coerceᵉ ê≲ê′ ℓ ]
  coerceᵐ {A = ∀̇ A} {B = ∀̇ B} (csub-univ A≲B) ℓ =
    [ MC.∀̇ (coerceᵐ A≲B ℓ) ]
  coerceᵐ {A = e₁ <: e₂ => A} {B = .e₁ <: .e₂ => B} (csub-sub A≲B) ℓ =
    [ e₁ MC.<: e₂ => coerceᵐ A≲B ℓ ]
