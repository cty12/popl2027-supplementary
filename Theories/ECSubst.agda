module Theories.ECSubst where

open import Data.List using ([]; _∷_)

open import Theories.CCAlphaRefStarSyntaxAndTypeSystem
open import Theories.CoercionSequences.EC.Definition
open import Theories.CoercionSequences.Meta.Definition hiding (_;_)


-- +-----------------------------+ --
-- | EC-variable renaming        | --
-- +-----------------------------+ --

mutual

  renᵉ-code : RenameEC → CodeTerm → CodeTerm
  renᵉ-code ρ ($ r) = $ r
  renᵉ-code ρ (` x) = ` x
  renᵉ-code ρ (ƛ T ˙ M) = ƛ T ˙ renᵉ-code (extᵉ ρ) M
  renᵉ-code ρ (ƛ̅ e ˙ M) = ƛ̅ renᵉ-ec ρ e ˙ renᵉ-code ρ M
  renᵉ-code ρ (L · M) = renᵉ-code ρ L · renᵉ-code ρ M
  renᵉ-code ρ (~ M) = ~ renᵉ-meta ρ M
  renᵉ-code ρ (blameᵒ ℓ) = blameᵒ ℓ

  renᵉ-meta : RenameEC → MetaTerm → MetaTerm
  renᵉ-meta ρ ($ r) = $ r
  renᵉ-meta ρ (` x) = ` x
  renᵉ-meta ρ (addr a) = addr a
  renᵉ-meta ρ (ƛ M) = ƛ renᵉ-meta ρ M
  renᵉ-meta ρ (L · M) = renᵉ-meta ρ L · renᵉ-meta ρ M
  renᵉ-meta ρ (Λ M) = Λ renᵉ-meta (extᵉ ρ) M
  renᵉ-meta ρ (M ·[ e ]) = renᵉ-meta ρ M ·[ renᵉ-ec ρ e ]
  renᵉ-meta ρ (e₁ <: e₂ => M) =
    renᵉ-ec ρ e₁ <: renᵉ-ec ρ e₂ => renᵉ-meta ρ M
  renᵉ-meta ρ (M ●) = renᵉ-meta ρ M ●
  renᵉ-meta ρ (M ★ ℓ) = renᵉ-meta ρ M ★ ℓ
  renᵉ-meta ρ (‶ M ″ e) = ‶ renᵉ-code ρ M ″ renᵉ-ec ρ e
  renᵉ-meta ρ (ref M) = ref (renᵉ-meta ρ M)
  renᵉ-meta ρ (M := N) = renᵉ-meta ρ M := renᵉ-meta ρ N
  renᵉ-meta ρ (! M) = ! renᵉ-meta ρ M
  renᵉ-meta ρ (M ⟨ c ⟩) = renᵉ-meta ρ M ⟨ renᵉ-metacoercion ρ c ⟩
  renᵉ-meta ρ (blame ℓ) = blame ℓ

  renᵉ-ecoercion : RenameEC → ECSingleCoercion → ECSingleCoercion
  renᵉ-ecoercion ρ (e ！) = renᵉ-ec ρ e ！
  renᵉ-ecoercion ρ (e ？ ℓ) = renᵉ-ec ρ e ？ ℓ
  renᵉ-ecoercion ρ (ê₁ ↑ ê₂) = renᵉ-ec⋆ ρ ê₁ ↑ renᵉ-ec⋆ ρ ê₂
  renᵉ-ecoercion ρ (⊥ ℓ) = ⊥ ℓ

  renᵉ-ecoercionSeq : RenameEC → ECCoercionSeq → ECCoercionSeq
  renᵉ-ecoercionSeq ρ [] = []
  renᵉ-ecoercionSeq ρ (cᵉ ∷ c̅ᵉ) = renᵉ-ecoercion ρ cᵉ ∷ renᵉ-ecoercionSeq ρ c̅ᵉ

  renᵉ-mcoercion : RenameEC → MSingleCoercion → MSingleCoercion
  renᵉ-mcoercion ρ ((G ！) g) = (renᵉ ρ G ！) (renᵉ-ground ρ g)
  renᵉ-mcoercion ρ ((G ？ ℓ) g) = (renᵉ ρ G ？ ℓ) (renᵉ-ground ρ g)
  renᵉ-mcoercion ρ (c̅ ⇒ d̅) = renᵉ-mcoercionSeq ρ c̅ ⇒ renᵉ-mcoercionSeq ρ d̅
  renᵉ-mcoercion ρ (‶ c̅ᵒ ″ c̅ᵉ) = ‶ c̅ᵒ ″ renᵉ-ecoercionSeq ρ c̅ᵉ
  renᵉ-mcoercion ρ (Ref c̅ , d̅) = Ref renᵉ-mcoercionSeq ρ c̅ , renᵉ-mcoercionSeq ρ d̅
  renᵉ-mcoercion ρ (∀̇ c̅) = ∀̇ renᵉ-mcoercionSeq (extᵉ ρ) c̅
  renᵉ-mcoercion ρ (e₁ <: e₂ => c) =
    renᵉ-ec ρ e₁ <: renᵉ-ec ρ e₂ => renᵉ-mcoercionSeq ρ c
  renᵉ-mcoercion ρ (⊥ ℓ) = ⊥ ℓ

  renᵉ-mcoercionSeq : RenameEC → MCoercionSeq → MCoercionSeq
  renᵉ-mcoercionSeq ρ [] = []
  renᵉ-mcoercionSeq ρ (c ∷ cs) = renᵉ-mcoercion ρ c ∷ renᵉ-mcoercionSeq ρ cs

  renᵉ-metacoercion : RenameEC → MCoercionSeq → MCoercionSeq
  renᵉ-metacoercion = renᵉ-mcoercionSeq


-- +----------------------------------+ --
-- | EC-variable parallel substitution | --
-- +----------------------------------+ --

subᵉ-ground : ∀ {G}
  → (σ : SubstEC)
  → Ground G
    -------------------
  → Ground (subᵉ σ G)
subᵉ-ground σ gbase = gbase
subᵉ-ground σ gfun = gfun
subᵉ-ground σ gref = gref
subᵉ-ground σ gcode = gcode
subᵉ-ground σ gforall = gforall
subᵉ-ground σ gsub = gsub

mutual

  substᵉ-code : SubstEC → CodeTerm → CodeTerm
  substᵉ-code σ ($ r) = $ r
  substᵉ-code σ (` x) = ` x
  substᵉ-code σ (ƛ T ˙ M) = ƛ T ˙ substᵉ-code (extsᵉ σ) M
  substᵉ-code σ (ƛ̅ e ˙ M) = ƛ̅ subᵉ-ec σ e ˙ substᵉ-code σ M
  substᵉ-code σ (L · M) = substᵉ-code σ L · substᵉ-code σ M
  substᵉ-code σ (~ M) = ~ substᵉ-meta σ M
  substᵉ-code σ (blameᵒ ℓ) = blameᵒ ℓ

  substᵉ-meta : SubstEC → MetaTerm → MetaTerm
  substᵉ-meta σ ($ r) = $ r
  substᵉ-meta σ (` x) = ` x
  substᵉ-meta σ (addr a) = addr a
  substᵉ-meta σ (ƛ M) = ƛ substᵉ-meta σ M
  substᵉ-meta σ (L · M) = substᵉ-meta σ L · substᵉ-meta σ M
  substᵉ-meta σ (Λ M) = Λ substᵉ-meta (extsᵉ σ) M
  substᵉ-meta σ (M ·[ e ]) = substᵉ-meta σ M ·[ subᵉ-ec σ e ]
  substᵉ-meta σ (e₁ <: e₂ => M) =
    subᵉ-ec σ e₁ <: subᵉ-ec σ e₂ => substᵉ-meta σ M
  substᵉ-meta σ (M ●) = substᵉ-meta σ M ●
  substᵉ-meta σ (M ★ ℓ) = substᵉ-meta σ M ★ ℓ
  substᵉ-meta σ (‶ M ″ e) = ‶ substᵉ-code σ M ″ subᵉ-ec σ e
  substᵉ-meta σ (ref M) = ref (substᵉ-meta σ M)
  substᵉ-meta σ (M := N) = substᵉ-meta σ M := substᵉ-meta σ N
  substᵉ-meta σ (! M) = ! substᵉ-meta σ M
  substᵉ-meta σ (M ⟨ c ⟩) = substᵉ-meta σ M ⟨ substᵉ-mcoercionSeq σ c ⟩
  substᵉ-meta σ (blame ℓ) = blame ℓ

  substᵉ-ecoercion : SubstEC → ECSingleCoercion → ECSingleCoercion
  substᵉ-ecoercion σ (e ！) = subᵉ-ec σ e ！
  substᵉ-ecoercion σ (e ？ ℓ) = subᵉ-ec σ e ？ ℓ
  substᵉ-ecoercion σ (ê₁ ↑ ê₂) = subᵉ-ec⋆ σ ê₁ ↑ subᵉ-ec⋆ σ ê₂
  substᵉ-ecoercion σ (⊥ ℓ) = ⊥ ℓ

  substᵉ-ecoercionSeq : SubstEC → ECCoercionSeq → ECCoercionSeq
  substᵉ-ecoercionSeq σ [] = []
  substᵉ-ecoercionSeq σ (cᵉ ∷ c̅ᵉ) = substᵉ-ecoercion σ cᵉ ∷ substᵉ-ecoercionSeq σ c̅ᵉ

  substᵉ-mcoercion : SubstEC → MSingleCoercion → MSingleCoercion
  substᵉ-mcoercion σ ((G ！) g) = (subᵉ σ G ！) (subᵉ-ground σ g)
  substᵉ-mcoercion σ ((G ？ ℓ) g) = (subᵉ σ G ？ ℓ) (subᵉ-ground σ g)
  substᵉ-mcoercion σ (c̅ ⇒ d̅) = substᵉ-mcoercionSeq σ c̅ ⇒ substᵉ-mcoercionSeq σ d̅
  substᵉ-mcoercion σ (‶ c̅ᵒ ″ c̅ᵉ) = ‶ c̅ᵒ ″ substᵉ-ecoercionSeq σ c̅ᵉ
  substᵉ-mcoercion σ (Ref c̅ , d̅) = Ref substᵉ-mcoercionSeq σ c̅ , substᵉ-mcoercionSeq σ d̅
  substᵉ-mcoercion σ (∀̇ c̅) = ∀̇ substᵉ-mcoercionSeq (extsᵉ σ) c̅
  substᵉ-mcoercion σ (e₁ <: e₂ => c) =
    subᵉ-ec σ e₁ <: subᵉ-ec σ e₂ => substᵉ-mcoercionSeq σ c
  substᵉ-mcoercion σ (⊥ ℓ) = ⊥ ℓ

  substᵉ-mcoercionSeq : SubstEC → MCoercionSeq → MCoercionSeq
  substᵉ-mcoercionSeq σ [] = []
  substᵉ-mcoercionSeq σ (c ∷ cs) = substᵉ-mcoercion σ c ∷ substᵉ-mcoercionSeq σ cs

-- +-----------------------------+ --
-- | EC-variable substitution    | --
-- +-----------------------------+ --

infix 8 _[_]ᵉᵒ
infix 8 _[_]ᵉᵐ
infix 8 _[_]ᶜ

_[_]ᵉᵒ : CodeTerm → EC → CodeTerm
Mᵒ [ e ]ᵉᵒ = substᵉ-code (e •ᵉₛ idsᵉ) Mᵒ

_[_]ᵉᵐ : MetaTerm → EC → MetaTerm
M [ e ]ᵉᵐ = substᵉ-meta (e •ᵉₛ idsᵉ) M

_[_]ᶜ : MCoercionSeq → EC → MCoercionSeq
c [ e ]ᶜ = substᵉ-mcoercionSeq (e •ᵉₛ idsᵉ) c
