{-

  Small-step semantics for the cast calculus of λαRef⋆ with
  space-efficient hypercoercions.

  This mirrors Theories.CCAlphaRefStarSemantics, but the
  raw term syntax comes from the space-efficient extrinsic type-system module
  and casts carry meta hypercoercions.

-}

module Theories.SpaceEfficiency.CCAlphaRefStarSemantics where

open import Data.List using (_∷ʳ_; length)
open import Data.Nat using (zero; suc)
open import Data.Unit using (tt)
open import Relation.Nullary using (¬_)

open import Theories.Utils using (_∋_⦂_)
open import Theories.SpaceEfficiency.CCAlphaRefStarSyntaxAndTypeSystem
open import Theories.SpaceEfficiency.Configuration public
open import Theories.Heap using (_⟦_↦_⟧=_) public

open import Theories.SpaceEfficiency.ECHypercoercions
open import Theories.SpaceEfficiency.ObjectHypercoercions
open import Theories.SpaceEfficiency.MetaHypercoercions


-- +-----------------------------+ --
-- | Code-variable substitution  | --
-- +-----------------------------+ --

RenameCode : Set
RenameCode = Var → Var

idᵒ : RenameCode
idᵒ x = x

extᵒ : RenameCode → RenameCode
extᵒ ρ zero = zero
extᵒ ρ (suc x) = suc (ρ x)

_•ᵒ_ : Var → RenameCode → RenameCode
(y •ᵒ _) zero = y
(_ •ᵒ ρ) (suc x) = ρ x

mutual

  renᵒ-code : RenameCode → CodeTerm → CodeTerm
  renᵒ-code ρ ($ r) = $ r
  renᵒ-code ρ (` x) = ` ρ x
  renᵒ-code ρ (ƛ T ˙ M) = ƛ T ˙ renᵒ-code (extᵒ ρ) M
  renᵒ-code ρ (ƛ̅ e ˙ M) = ƛ̅ e ˙ renᵒ-code ρ M
  renᵒ-code ρ (L · M) = renᵒ-code ρ L · renᵒ-code ρ M
  renᵒ-code ρ (~ M) = ~ renᵒ-meta ρ M
  renᵒ-code ρ (blameᵒ ℓ) = blameᵒ ℓ

  renᵒ-meta : RenameCode → MetaTerm → MetaTerm
  renᵒ-meta ρ ($ r) = $ r
  renᵒ-meta ρ (` x) = ` x
  renᵒ-meta ρ (addr a) = addr a
  renᵒ-meta ρ (ƛ M) = ƛ renᵒ-meta ρ M
  renᵒ-meta ρ (L · M) = renᵒ-meta ρ L · renᵒ-meta ρ M
  renᵒ-meta ρ (Λ M) = Λ renᵒ-meta ρ M
  renᵒ-meta ρ (M ·[ e ]) = renᵒ-meta ρ M ·[ e ]
  renᵒ-meta ρ (e₁ <: e₂ => M) = e₁ <: e₂ => renᵒ-meta ρ M
  renᵒ-meta ρ (M ●) = renᵒ-meta ρ M ●
  renᵒ-meta ρ (M ★ ℓ) = renᵒ-meta ρ M ★ ℓ
  renᵒ-meta ρ (‶ M ″ e) = ‶ renᵒ-code ρ M ″ e
  renᵒ-meta ρ (ref M) = ref (renᵒ-meta ρ M)
  renᵒ-meta ρ (M := N) = renᵒ-meta ρ M := renᵒ-meta ρ N
  renᵒ-meta ρ (! M) = ! renᵒ-meta ρ M
  renᵒ-meta ρ (M ⟨ c ⟩) = renᵒ-meta ρ M ⟨ c ⟩
  renᵒ-meta ρ (blame ℓ) = blame ℓ

SubstCode : Set
SubstCode = Var → CodeTerm

idsᵒ : SubstCode
idsᵒ x = ` x

extsᵒ : SubstCode → SubstCode
extsᵒ σ zero = ` zero
extsᵒ σ (suc x) = renᵒ-code suc (σ x)

_•ᵒₛ_ : CodeTerm → SubstCode → SubstCode
(Mᵒ •ᵒₛ σ) zero = Mᵒ
(_ •ᵒₛ σ) (suc x) = σ x

mutual

  substᵒ-code : SubstCode → CodeTerm → CodeTerm
  substᵒ-code σ ($ r) = $ r
  substᵒ-code σ (` x) = σ x
  substᵒ-code σ (ƛ T ˙ M) = ƛ T ˙ substᵒ-code (extsᵒ σ) M
  substᵒ-code σ (ƛ̅ e ˙ M) = ƛ̅ e ˙ substᵒ-code σ M
  substᵒ-code σ (L · M) = substᵒ-code σ L · substᵒ-code σ M
  substᵒ-code σ (~ M) = ~ substᵒ-meta σ M
  substᵒ-code σ (blameᵒ ℓ) = blameᵒ ℓ

  substᵒ-meta : SubstCode → MetaTerm → MetaTerm
  substᵒ-meta σ ($ r) = $ r
  substᵒ-meta σ (` x) = ` x
  substᵒ-meta σ (addr a) = addr a
  substᵒ-meta σ (ƛ M) = ƛ substᵒ-meta σ M
  substᵒ-meta σ (L · M) = substᵒ-meta σ L · substᵒ-meta σ M
  substᵒ-meta σ (Λ M) = Λ substᵒ-meta σ M
  substᵒ-meta σ (M ·[ e ]) = substᵒ-meta σ M ·[ e ]
  substᵒ-meta σ (e₁ <: e₂ => M) = e₁ <: e₂ => substᵒ-meta σ M
  substᵒ-meta σ (M ●) = substᵒ-meta σ M ●
  substᵒ-meta σ (M ★ ℓ) = substᵒ-meta σ M ★ ℓ
  substᵒ-meta σ (‶ M ″ e) = ‶ substᵒ-code σ M ″ e
  substᵒ-meta σ (ref M) = ref (substᵒ-meta σ M)
  substᵒ-meta σ (M := N) = substᵒ-meta σ M := substᵒ-meta σ N
  substᵒ-meta σ (! M) = ! substᵒ-meta σ M
  substᵒ-meta σ (M ⟨ c ⟩) = substᵒ-meta σ M ⟨ c ⟩
  substᵒ-meta σ (blame ℓ) = blame ℓ

infix 8 _[_]ᵒ

_[_]ᵒ : CodeTerm → CodeTerm → CodeTerm
Nᵒ [ Mᵒ ]ᵒ = substᵒ-code (Mᵒ •ᵒₛ idsᵒ) Nᵒ


-- +--------------------------+ --
-- | EC-variable substitution | --
-- +--------------------------+ --

renᵉ-ehead : RenameEC → ECHead → ECHead
renᵉ-ehead ρ (e ？ ℓ) = renᵉ-ec ρ e ？ ℓ
renᵉ-ehead ρ (id ê) = id (renᵉ-ec⋆ ρ ê)

renᵉ-emiddle : RenameEC → ECMiddle → ECMiddle
renᵉ-emiddle ρ (ê₁ ↑ ê₂) = renᵉ-ec⋆ ρ ê₁ ↑ renᵉ-ec⋆ ρ ê₂
renᵉ-emiddle ρ (err ℓ) = err ℓ

renᵉ-etail : RenameEC → ECTail → ECTail
renᵉ-etail ρ (e ！) = renᵉ-ec ρ e ！
renᵉ-etail ρ (id ê) = id (renᵉ-ec⋆ ρ ê)

renᵉ-ehc : RenameEC → ECHypercoercion → ECHypercoercion
renᵉ-ehc ρ (h ⨾ m ⨾ t) = renᵉ-ehead ρ h ⨾ renᵉ-emiddle ρ m ⨾ renᵉ-etail ρ t

mutual

  renᵉ-mhead : RenameEC → MHead → MHead
  renᵉ-mhead ρ (G ？ ℓ) = renᵉ ρ G ？ ℓ
  renᵉ-mhead ρ (id A) = id (renᵉ ρ A)

  renᵉ-mmiddle : RenameEC → MMiddle → MMiddle
  renᵉ-mmiddle ρ (c ⇒ d) = renᵉ-mhc ρ c ⇒ renᵉ-mhc ρ d
  renᵉ-mmiddle ρ (‶ cᵒ ″ cᵉ) = ‶ cᵒ ″ renᵉ-ehc ρ cᵉ
  renᵉ-mmiddle ρ (ref c d) = ref (renᵉ-mhc ρ c) (renᵉ-mhc ρ d)
  renᵉ-mmiddle ρ (∀̇ c) = ∀̇ renᵉ-mhc (extᵉ ρ) c
  renᵉ-mmiddle ρ (e₁ <: e₂ => c) =
    renᵉ-ec ρ e₁ <: renᵉ-ec ρ e₂ => renᵉ-mhc ρ c
  renᵉ-mmiddle ρ (err ℓ) = err ℓ
  renᵉ-mmiddle ρ id⋆ = id⋆
  renᵉ-mmiddle ρ (idι ι) = idι ι

  renᵉ-mtail : RenameEC → MTail → MTail
  renᵉ-mtail ρ (G ！) = renᵉ ρ G ！
  renᵉ-mtail ρ (id A) = id (renᵉ ρ A)

  renᵉ-mhc : RenameEC → MHypercoercion → MHypercoercion
  renᵉ-mhc ρ (h ⨾ m ⨾ t) = renᵉ-mhead ρ h ⨾ renᵉ-mmiddle ρ m ⨾ renᵉ-mtail ρ t

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
  renᵉ-meta ρ (M ⟨ c ⟩) = renᵉ-meta ρ M ⟨ renᵉ-mhc ρ c ⟩
  renᵉ-meta ρ (blame ℓ) = blame ℓ

substᵉ-ehead : SubstEC → ECHead → ECHead
substᵉ-ehead σ (e ？ ℓ) = subᵉ-ec σ e ？ ℓ
substᵉ-ehead σ (id ê) = id (subᵉ-ec⋆ σ ê)

substᵉ-emiddle : SubstEC → ECMiddle → ECMiddle
substᵉ-emiddle σ (ê₁ ↑ ê₂) = subᵉ-ec⋆ σ ê₁ ↑ subᵉ-ec⋆ σ ê₂
substᵉ-emiddle σ (err ℓ) = err ℓ

substᵉ-etail : SubstEC → ECTail → ECTail
substᵉ-etail σ (e ！) = subᵉ-ec σ e ！
substᵉ-etail σ (id ê) = id (subᵉ-ec⋆ σ ê)

substᵉ-ehc : SubstEC → ECHypercoercion → ECHypercoercion
substᵉ-ehc σ (h ⨾ m ⨾ t) =
  substᵉ-ehead σ h ⨾ substᵉ-emiddle σ m ⨾ substᵉ-etail σ t

mutual

  substᵉ-mhead : SubstEC → MHead → MHead
  substᵉ-mhead σ (G ？ ℓ) = subᵉ σ G ？ ℓ
  substᵉ-mhead σ (id A) = id (subᵉ σ A)

  substᵉ-mmiddle : SubstEC → MMiddle → MMiddle
  substᵉ-mmiddle σ (c ⇒ d) = substᵉ-mhc σ c ⇒ substᵉ-mhc σ d
  substᵉ-mmiddle σ (‶ cᵒ ″ cᵉ) = ‶ cᵒ ″ substᵉ-ehc σ cᵉ
  substᵉ-mmiddle σ (ref c d) = ref (substᵉ-mhc σ c) (substᵉ-mhc σ d)
  substᵉ-mmiddle σ (∀̇ c) = ∀̇ substᵉ-mhc (extsᵉ σ) c
  substᵉ-mmiddle σ (e₁ <: e₂ => c) =
    subᵉ-ec σ e₁ <: subᵉ-ec σ e₂ => substᵉ-mhc σ c
  substᵉ-mmiddle σ (err ℓ) = err ℓ
  substᵉ-mmiddle σ id⋆ = id⋆
  substᵉ-mmiddle σ (idι ι) = idι ι

  substᵉ-mtail : SubstEC → MTail → MTail
  substᵉ-mtail σ (G ！) = subᵉ σ G ！
  substᵉ-mtail σ (id A) = id (subᵉ σ A)

  substᵉ-mhc : SubstEC → MHypercoercion → MHypercoercion
  substᵉ-mhc σ (h ⨾ m ⨾ t) =
    substᵉ-mhead σ h ⨾ substᵉ-mmiddle σ m ⨾ substᵉ-mtail σ t

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
  substᵉ-meta σ (M ⟨ c ⟩) = substᵉ-meta σ M ⟨ substᵉ-mhc σ c ⟩
  substᵉ-meta σ (blame ℓ) = blame ℓ

infix 8 _[_]ᵉᵒ
infix 8 _[_]ᵉᵐ
infix 8 _[_]ᶜ

_[_]ᵉᵒ : CodeTerm → EC → CodeTerm
Mᵒ [ e ]ᵉᵒ = substᵉ-code (e •ᵉₛ idsᵉ) Mᵒ

_[_]ᵉᵐ : MetaTerm → EC → MetaTerm
M [ e ]ᵉᵐ = substᵉ-meta (e •ᵉₛ idsᵉ) M

_[_]ᶜ : MHypercoercion → EC → MHypercoercion
c [ e ]ᶜ = substᵉ-mhc (e •ᵉₛ idsᵉ) c


-- +-----------------------------+ --
-- | Meta-variable substitution  | --
-- +-----------------------------+ --

RenameMeta : Set
RenameMeta = Var → Var

idᵐ : RenameMeta
idᵐ x = x

extᵐ : RenameMeta → RenameMeta
extᵐ ρ zero = zero
extᵐ ρ (suc x) = suc (ρ x)

_•ᵐ_ : Var → RenameMeta → RenameMeta
(y •ᵐ _) zero = y
(_ •ᵐ ρ) (suc x) = ρ x

mutual

  renᵐ-code : RenameMeta → CodeTerm → CodeTerm
  renᵐ-code ρ ($ r) = $ r
  renᵐ-code ρ (` x) = ` x
  renᵐ-code ρ (ƛ T ˙ M) = ƛ T ˙ renᵐ-code ρ M
  renᵐ-code ρ (ƛ̅ e ˙ M) = ƛ̅ e ˙ renᵐ-code ρ M
  renᵐ-code ρ (L · M) = renᵐ-code ρ L · renᵐ-code ρ M
  renᵐ-code ρ (~ M) = ~ renᵐ-meta ρ M
  renᵐ-code ρ (blameᵒ ℓ) = blameᵒ ℓ

  renᵐ-meta : RenameMeta → MetaTerm → MetaTerm
  renᵐ-meta ρ ($ r) = $ r
  renᵐ-meta ρ (` x) = ` ρ x
  renᵐ-meta ρ (addr a) = addr a
  renᵐ-meta ρ (ƛ M) = ƛ renᵐ-meta (extᵐ ρ) M
  renᵐ-meta ρ (L · M) = renᵐ-meta ρ L · renᵐ-meta ρ M
  renᵐ-meta ρ (Λ M) = Λ renᵐ-meta ρ M
  renᵐ-meta ρ (M ·[ e ]) = renᵐ-meta ρ M ·[ e ]
  renᵐ-meta ρ (e₁ <: e₂ => M) = e₁ <: e₂ => renᵐ-meta ρ M
  renᵐ-meta ρ (M ●) = renᵐ-meta ρ M ●
  renᵐ-meta ρ (M ★ ℓ) = renᵐ-meta ρ M ★ ℓ
  renᵐ-meta ρ (‶ M ″ e) = ‶ renᵐ-code ρ M ″ e
  renᵐ-meta ρ (ref M) = ref (renᵐ-meta ρ M)
  renᵐ-meta ρ (M := N) = renᵐ-meta ρ M := renᵐ-meta ρ N
  renᵐ-meta ρ (! M) = ! renᵐ-meta ρ M
  renᵐ-meta ρ (M ⟨ c ⟩) = renᵐ-meta ρ M ⟨ c ⟩
  renᵐ-meta ρ (blame ℓ) = blame ℓ

SubstMeta : Set
SubstMeta = Var → MetaTerm

idsᵐ : SubstMeta
idsᵐ x = ` x

extsᵐ : SubstMeta → SubstMeta
extsᵐ σ zero = ` zero
extsᵐ σ (suc x) = renᵐ-meta suc (σ x)

⇑ᵉˢ : SubstMeta → SubstMeta
⇑ᵉˢ σ x = renᵉ-meta suc (σ x)

⇑ᵒˢ : SubstMeta → SubstMeta
⇑ᵒˢ σ x = renᵒ-meta suc (σ x)

_•ᵐₛ_ : MetaTerm → SubstMeta → SubstMeta
(M •ᵐₛ σ) zero = M
(_ •ᵐₛ σ) (suc x) = σ x

mutual

  substᵐ-code : SubstMeta → CodeTerm → CodeTerm
  substᵐ-code σ ($ r) = $ r
  substᵐ-code σ (` x) = ` x
  substᵐ-code σ (ƛ T ˙ M) = ƛ T ˙ substᵐ-code (⇑ᵒˢ (⇑ᵉˢ σ)) M
  substᵐ-code σ (ƛ̅ e ˙ M) = ƛ̅ e ˙ substᵐ-code σ M
  substᵐ-code σ (L · M) = substᵐ-code σ L · substᵐ-code σ M
  substᵐ-code σ (~ M) = ~ substᵐ-meta σ M
  substᵐ-code σ (blameᵒ ℓ) = blameᵒ ℓ

  substᵐ-meta : SubstMeta → MetaTerm → MetaTerm
  substᵐ-meta σ ($ r) = $ r
  substᵐ-meta σ (` x) = σ x
  substᵐ-meta σ (addr a) = addr a
  substᵐ-meta σ (ƛ M) = ƛ substᵐ-meta (extsᵐ σ) M
  substᵐ-meta σ (L · M) = substᵐ-meta σ L · substᵐ-meta σ M
  substᵐ-meta σ (Λ M) = Λ substᵐ-meta (⇑ᵉˢ σ) M
  substᵐ-meta σ (M ·[ e ]) = substᵐ-meta σ M ·[ e ]
  substᵐ-meta σ (e₁ <: e₂ => M) = e₁ <: e₂ => substᵐ-meta σ M
  substᵐ-meta σ (M ●) = substᵐ-meta σ M ●
  substᵐ-meta σ (M ★ ℓ) = substᵐ-meta σ M ★ ℓ
  substᵐ-meta σ (‶ M ″ e) = ‶ substᵐ-code σ M ″ e
  substᵐ-meta σ (ref M) = ref (substᵐ-meta σ M)
  substᵐ-meta σ (M := N) = substᵐ-meta σ M := substᵐ-meta σ N
  substᵐ-meta σ (! M) = ! substᵐ-meta σ M
  substᵐ-meta σ (M ⟨ c ⟩) = substᵐ-meta σ M ⟨ c ⟩
  substᵐ-meta σ (blame ℓ) = blame ℓ

infix 8 _[_]ᵐ

_[_]ᵐ : MetaTerm → MetaTerm → MetaTerm
M [ N ]ᵐ = substᵐ-meta (N •ᵐₛ idsᵐ) M


-- +------------------------------+ --
-- | Values and inert coercions   | --
-- +------------------------------+ --

data CodeValue : CodeTerm → Set where

  is-const : ∀ {ι} {r : base-rep ι}
      ---------------------------------
    → CodeValue ($ r)

  is-var : ∀ {x}
      ------------------------------
    → CodeValue (` x)

  is-lamᵒ-val : ∀ {α M}
    → CodeValue M
      ---------------------------------
    → CodeValue (ƛ̅ ` α ˙ M)

  is-app : ∀ {L M}
    → CodeValue L
    → CodeValue M
      ------------------------------
    → CodeValue (L · M)


data InertInjMid : ∀ {G} → Ground G → MMiddle → Set where

  inj-idι : ∀ {ι}
      ------------------------------
    → InertInjMid (gbase {ι = ι}) (idι ι)

  inj-fun : ∀ {c d}
      ------------------------------
    → InertInjMid gfun (c ⇒ d)

  inj-code : ∀ {cᵒ cᵉ}
      ------------------------------
    → InertInjMid gcode (‶ cᵒ ″ cᵉ)

  inj-ref : ∀ {c d}
      ------------------------------
    → InertInjMid gref (ref c d)

  inj-∀̇ : ∀ {c}
      ------------------------------
    → InertInjMid gforall (∀̇ c)

  inj-sub : ∀ {e₁ e₂ c}
      ------------------------------
    → InertInjMid (gsub {e₁ = e₁} {e₂ = e₂}) (e₁ <: e₂ => c)


data InertIdMid : MMiddle → Set where

  id-fun : ∀ {c d}
      ---------------------
    → InertIdMid (c ⇒ d)

  id-code : ∀ {cᵒ cᵉ}
      ---------------------
    → InertIdMid (‶ cᵒ ″ cᵉ)

  id-ref : ∀ {c d}
      ---------------------
    → InertIdMid (ref c d)

  id-∀̇ : ∀ {c}
      ---------------------
    → InertIdMid (∀̇ c)

  id-sub : ∀ {e₁ e₂ c}
      ---------------------
    → InertIdMid (e₁ <: e₂ => c)


data Inert : MHypercoercion → Set where

  inj-tail : ∀ {A G m} {g : Ground G}
    → InertInjMid g m
      ----------------------------------------
    → Inert (id A ⨾ m ⨾ G ！)

  id-tail : ∀ {A B m}
    → InertIdMid m
      ----------------------------------------
    → Inert (id A ⨾ m ⨾ id B)


data RawValue : MetaTerm → Set where

  U-const : ∀ {ι} {r : base-rep ι}
      ---------------------
    → RawValue ($ r)

  U-addr : ∀ {a}
      ---------------------
    → RawValue (addr a)

  U-ƛ : ∀ {M}
      ---------------------
    → RawValue (ƛ M)

  U-Λ : ∀ {M}
      ---------------------
    → RawValue (Λ M)

  U-quote : ∀ {e Vᵒ}
    → CodeValue Vᵒ
      ---------------------
    → RawValue (‶ Vᵒ ″ e)

  U-sub : ∀ {e₁ e₂ M}
      ---------------------------
    → RawValue (e₁ <: e₂ => M)


data Value : MetaTerm → Set where

  V-raw : ∀ {M}
    → RawValue M
      ------------------
    → Value M

  V-cast : ∀ {U c}
    → RawValue U
    → Inert c
      ---------------------
    → Value (U ⟨ c ⟩)


-- +-----------------------------+ --
-- | Hypercoercion constructors  | --
-- +-----------------------------+ --

id-hcᵒ : OType⋆ → OHypercoercion
id-hcᵒ ⋆ = id ⋆ ⨾ id⋆ ⨾ id ⋆
id-hcᵒ (` ι) = id (` ι) ⨾ idι ι ⨾ id (` ι)
id-hcᵒ (O₁ ⇒ O₂) =
  id (O₁ ⇒ O₂) ⨾ (id-hcᵒ O₁ ⇒ id-hcᵒ O₂) ⨾ id (O₁ ⇒ O₂)

id-hcᵉ : EC⋆ → ECHypercoercion
id-hcᵉ ê = id ê ⨾ ê ↑ ê ⨾ id ê

sub-hcᵉ : EC → EC → ECHypercoercion
sub-hcᵉ e₁ e₂ = id (ec e₁) ⨾ ec e₁ ↑ ec e₂ ⨾ id (ec e₂)

code-sub-hc : OType⋆ → EC → EC → MHypercoercion
code-sub-hc O e₁ e₂ =
  id (‶ O ″ ec e₁) ⨾ ‶ id-hcᵒ O ″ sub-hcᵉ e₁ e₂ ⨾ id (‶ O ″ ec e₂)


-- +------------------------------+ --
-- | Frames and plug              | --
-- +------------------------------+ --

data CodeFrame : Set where

  □·_ : CodeTerm → CodeFrame

  _·□ : (Vᵒ : CodeTerm) → CodeValue Vᵒ → CodeFrame

plugᵒ : CodeFrame → CodeTerm → CodeTerm
plugᵒ (□· Mᵒ) Lᵒ = Lᵒ · Mᵒ
plugᵒ ((Vᵒ ·□) _) Mᵒ = Vᵒ · Mᵒ


data MetaFrame : Set where

  □·_ : MetaTerm → MetaFrame

  _·□ : (V : MetaTerm) → Value V → MetaFrame

  ref□ : MetaFrame

  □:=_ : MetaTerm → MetaFrame

  _:=□ : (V : MetaTerm) → Value V → MetaFrame

  !□ : MetaFrame

  □·[_] : EC → MetaFrame

  □● : MetaFrame

  □★_ : BlameLabel → MetaFrame


plugᵐ : MetaFrame → MetaTerm → MetaTerm
plugᵐ (□· M) L = L · M
plugᵐ ((V ·□) _) M = V · M
plugᵐ ref□ M = ref M
plugᵐ (□:= M) L = L := M
plugᵐ ((V :=□) _) M = V := M
plugᵐ !□ M = ! M
plugᵐ (□·[ e ]) M = M ·[ e ]
plugᵐ □● M = M ●
plugᵐ (□★ ℓ) M = M ★ ℓ


-- +------------------------------------------------------+ --
-- | Raw reduction semantics for space-efficient CCαRef⋆  | --
-- +------------------------------------------------------+ --

data ReductionCtx : Set where
  Any : ReductionCtx
  NonCast : ReductionCtx


infix 0 _/_—→ᵐ_
infix 0 _∣_—→ᵒ_

data _/_—→ᵐ_ : ReductionCtx → Config MetaTerm → Config MetaTerm → Set

data _∣_—→ᵒ_ : Config CodeTerm → EC → Config CodeTerm → Set

data _∣_—→ᵒ_ where

  ξ-code : ∀ {Δ₁ Δ₂ Θ₁ Θ₂ Γᵒ₁ Γᵒ₂ μ₁ μ₂ e Mᵒ Nᵒ}
    → (Fᵒ : CodeFrame)
    → config Δ₁ Θ₁ Γᵒ₁ μ₁ Mᵒ ∣ e —→ᵒ config Δ₂ Θ₂ Γᵒ₂ μ₂ Nᵒ
      ---------------------------------------------------------------------------------------
    → config Δ₁ Θ₁ Γᵒ₁ μ₁ (plugᵒ Fᵒ Mᵒ) ∣ e —→ᵒ config Δ₂ Θ₂ Γᵒ₂ μ₂ (plugᵒ Fᵒ Nᵒ)

  ξ-code-blame : ∀ {Δ Θ Γᵒ μ e ℓ}
    → (Fᵒ : CodeFrame)
      ----------------------------------------------------------------------------------
    → config Δ Θ Γᵒ μ (plugᵒ Fᵒ (blameᵒ ℓ)) ∣ e —→ᵒ config Δ Θ Γᵒ μ (blameᵒ ℓ)

  ξ-splice : ∀ {Δ₁ Δ₂ Θ₁ Θ₂ Γᵒ₁ Γᵒ₂ μ₁ μ₂ e M N}
    → ∀ {ctx}
    → ctx / config Δ₁ Θ₁ Γᵒ₁ μ₁ M —→ᵐ config Δ₂ Θ₂ Γᵒ₂ μ₂ N
      ------------------------------------------------------------------
    → config Δ₁ Θ₁ Γᵒ₁ μ₁ (~ M) ∣ e —→ᵒ config Δ₂ Θ₂ Γᵒ₂ μ₂ (~ N)

  splice-blame : ∀ {Δ Θ Γᵒ μ e ℓ}
      ---------------------------------------------------------------------------
    → config Δ Θ Γᵒ μ (~ (blame ℓ)) ∣ e —→ᵒ config Δ Θ Γᵒ μ (blameᵒ ℓ)

  splice-β : ∀ {Δ Θ Γᵒ μ e₁ e₂ Vᵒ}
    → CodeValue Vᵒ
      ---------------------------------------------------------------------
    → config Δ Θ Γᵒ μ (~ (‶ Vᵒ ″ e₁)) ∣ e₂ —→ᵒ config Δ Θ Γᵒ μ Vᵒ

  splice-sub : ∀ {Δ Θ Γᵒ μ e₁ e₂ O Vᵒ}
    → CodeValue Vᵒ
      ------------------------------------------------------------------------------------------------
    → config Δ Θ Γᵒ μ (~ ((‶ Vᵒ ″ e₁) ⟨ code-sub-hc O e₁ e₂ ⟩)) ∣ e₂ —→ᵒ
       config Δ Θ Γᵒ μ Vᵒ

  code-λ : ∀ {Δ Θ Γᵒ μ e T Nᵒ}
      ------------------------------------------------------------------------------------------
    → let β = freshᵉ Δ in
       let y = freshᵒ Γᵒ in
       config Δ Θ Γᵒ μ (ƛ T ˙ Nᵒ) ∣ e —→ᵒ
       config (Δ ,ᵍα) (Θ ,ᵍ e <: ` β) (Γᵒ ,ᵍ T ＠ β) μ (ƛ̅ ` β ˙ (Nᵒ [ ` β ]ᵉᵒ [ ` y ]ᵒ))

  ξ-code-λ̅ : ∀ {Δ₁ Δ₂ Θ₁ Θ₂ Γᵒ₁ Γᵒ₂ μ₁ μ₂ e₁ e₂ Nᵒ₁ Nᵒ₂}
    → config Δ₁ Θ₁ Γᵒ₁ μ₁ Nᵒ₁ ∣ e₂ —→ᵒ config Δ₂ Θ₂ Γᵒ₂ μ₂ Nᵒ₂
      ------------------------------------------------------------------------------------
    → config Δ₁ Θ₁ Γᵒ₁ μ₁ (ƛ̅ e₂ ˙ Nᵒ₁) ∣ e₁ —→ᵒ config Δ₂ Θ₂ Γᵒ₂ μ₂ (ƛ̅ e₂ ˙ Nᵒ₂)

  ξ-code-λ̅-blame : ∀ {Δ Θ Γᵒ μ e₁ e₂ ℓ}
      ---------------------------------------------------------------------------------
    → config Δ Θ Γᵒ μ (ƛ̅ e₂ ˙ blameᵒ ℓ) ∣ e₁ —→ᵒ config Δ Θ Γᵒ μ (blameᵒ ℓ)

data _/_—→ᵐ_ where

  ξ-meta : ∀ {Δ₁ Δ₂ Θ₁ Θ₂ Γᵒ₁ Γᵒ₂ μ₁ μ₂ M N}
    → (F : MetaFrame)
    → ∀ {ctx}
    → ctx / config Δ₁ Θ₁ Γᵒ₁ μ₁ M —→ᵐ config Δ₂ Θ₂ Γᵒ₂ μ₂ N
      ---------------------------------------------------------------------------
    → Any / config Δ₁ Θ₁ Γᵒ₁ μ₁ (plugᵐ F M) —→ᵐ config Δ₂ Θ₂ Γᵒ₂ μ₂ (plugᵐ F N)

  ξ-cast : ∀ {Δ₁ Δ₂ Θ₁ Θ₂ Γᵒ₁ Γᵒ₂ μ₁ μ₂ M N c}
    → Any / config Δ₁ Θ₁ Γᵒ₁ μ₁ M —→ᵐ config Δ₂ Θ₂ Γᵒ₂ μ₂ N
      ------------------------------------------------------------------------------------
    → NonCast / config Δ₁ Θ₁ Γᵒ₁ μ₁ (M ⟨ c ⟩) —→ᵐ config Δ₂ Θ₂ Γᵒ₂ μ₂ (N ⟨ c ⟩)

  ξ-meta-blame : ∀ {Δ Θ Γᵒ μ ℓ}
    → (F : MetaFrame)
      ---------------------------------------------------------------------
    → Any / config Δ Θ Γᵒ μ (plugᵐ F (blame ℓ)) —→ᵐ config Δ Θ Γᵒ μ (blame ℓ)

  ξ-quote : ∀ {Δ₁ Δ₂ Θ₁ Θ₂ Γᵒ₁ Γᵒ₂ μ₁ μ₂ e Mᵒ Nᵒ}
    → config Δ₁ Θ₁ Γᵒ₁ μ₁ Mᵒ ∣ e —→ᵒ config Δ₂ Θ₂ Γᵒ₂ μ₂ Nᵒ
      ------------------------------------------------------------------------
    → Any / config Δ₁ Θ₁ Γᵒ₁ μ₁ (‶ Mᵒ ″ e) —→ᵐ config Δ₂ Θ₂ Γᵒ₂ μ₂ (‶ Nᵒ ″ e)

  quote-blame : ∀ {Δ Θ Γᵒ μ e ℓ}
      ------------------------------------------------------------------------
    → Any / config Δ Θ Γᵒ μ (‶ blameᵒ ℓ ″ e) —→ᵐ config Δ Θ Γᵒ μ (blame ℓ)

  β : ∀ {Δ Θ Γᵒ μ N V}
    → Value V
      ------------------------------------------------------------------
    → Any / config Δ Θ Γᵒ μ ((ƛ N) · V) —→ᵐ config Δ Θ Γᵒ μ (N [ V ]ᵐ)

  β-cast : ∀ {Δ Θ Γᵒ μ U W A B C D c d}
    → RawValue U
    → Value W
      ----------------------------------------------------------------------------------------------------------------
    → Any / config Δ Θ Γᵒ μ ((U ⟨ id (C ⇒ D) ⨾ c ⇒ d ⨾ id (A ⇒ B) ⟩) · W) —→ᵐ
       config Δ Θ Γᵒ μ ((U · (W ⟨ c ⟩)) ⟨ d ⟩)

  Λ-β : ∀ {Δ Θ Γᵒ μ e M}
      ---------------------------------------------------------------------
    → Any / config Δ Θ Γᵒ μ ((Λ M) ·[ e ]) —→ᵐ config Δ Θ Γᵒ μ (M [ e ]ᵉᵐ)

  Λ-β-cast : ∀ {Δ Θ Γᵒ μ e U A B c}
    → RawValue U
      ----------------------------------------------------------------------------------------------------------
    → Any / config Δ Θ Γᵒ μ ((U ⟨ id (∀̇ A) ⨾ ∀̇ c ⨾ id (∀̇ B) ⟩) ·[ e ]) —→ᵐ
       config Δ Θ Γᵒ μ ((U ·[ e ]) ⟨ c [ e ]ᶜ ⟩)

  sub-β : ∀ {Δ Θ Γᵒ μ e₁ e₂ M}
      ------------------------------------------------------------------
    → Any / config Δ Θ Γᵒ μ ((e₁ <: e₂ => M) ●) —→ᵐ config Δ Θ Γᵒ μ M

  sub-β-cast : ∀ {Δ Θ Γᵒ μ e₁ e₂ U A B c}
    → RawValue U
      -------------------------------------------------------------------------------------------------------------------
    → Any / config Δ Θ Γᵒ μ ((U ⟨ id (e₁ <: e₂ => A) ⨾ e₁ <: e₂ => c ⨾ id (e₁ <: e₂ => B) ⟩) ●) —→ᵐ
       config Δ Θ Γᵒ μ ((U ●) ⟨ c ⟩)

  sub-cast-success : ∀ {Δ Θ Γᵒ μ e₁ e₂ U A m ℓ}
    → RawValue U
    → Θ ⊢ᵉ e₁ <: e₂
      --------------------------------------------------------------------------------------------------------------------------------
    → Any / config Δ Θ Γᵒ μ ((U ⟨ id (e₁ <: e₂ => A) ⨾ m ⨾ (e₁ <: e₂ => ⋆) ！ ⟩) ★ ℓ) —→ᵐ
       config Δ Θ Γᵒ μ ((U ⟨ id (e₁ <: e₂ => A) ⨾ m ⨾ id (e₁ <: e₂ => ⋆) ⟩) ●)

  sub-cast-sub-fail : ∀ {Δ Θ Γᵒ μ e₁ e₂ U A m ℓ}
    → RawValue U
    → ¬ Θ ⊢ᵉ e₁ <: e₂
      --------------------------------------------------------------------------------------------------------------------------
    → Any / config Δ Θ Γᵒ μ ((U ⟨ id (e₁ <: e₂ => A) ⨾ m ⨾ (e₁ <: e₂ => ⋆) ！ ⟩) ★ ℓ) —→ᵐ
       config Δ Θ Γᵒ μ (blame ℓ)

  sub-cast-fail : ∀ {Δ Θ Γᵒ μ e₁ e₂ U A G m ℓ}
    → RawValue U
    → Ground G
    → ¬ G ⦊ e₁ <: e₂ => ⋆
      -------------------------------------------------------------------------------------------------------
    → Any / config Δ Θ Γᵒ μ ((U ⟨ id (e₁ <: e₂ => A) ⨾ m ⨾ G ！ ⟩) ★ ℓ) —→ᵐ
       config Δ Θ Γᵒ μ (blame ℓ)

  ref : ∀ {Δ Θ Γᵒ μ V}
    → Value V
      ------------------------------------------------------------------------------
    → Any / config Δ Θ Γᵒ μ (ref V) —→ᵐ config Δ Θ Γᵒ (μ ∷ʳ V) (addr (length μ))

  deref : ∀ {Δ Θ Γᵒ μ a V}
    → μ ∋ a ⦂ V
      ------------------------------------------------------------
    → Any / config Δ Θ Γᵒ μ (! (addr a)) —→ᵐ config Δ Θ Γᵒ μ V

  assign : ∀ {Δ Θ Γᵒ μ μ′ a V}
    → Value V
    → μ ⟦ a ↦ V ⟧= μ′
      ---------------------------------------------------------------------
    → Any / config Δ Θ Γᵒ μ ((addr a) := V) —→ᵐ config Δ Θ Γᵒ μ′ ($ tt)

  assign-cast : ∀ {Δ Θ Γᵒ μ a V A B c d}
    → Value V
      --------------------------------------------------------------------------------------------------------------
    → Any / config Δ Θ Γᵒ μ (((addr a) ⟨ id (Ref A) ⨾ ref c d ⨾ id (Ref B) ⟩) := V) —→ᵐ
       config Δ Θ Γᵒ μ ((addr a) := (V ⟨ c ⟩))

  deref-cast : ∀ {Δ Θ Γᵒ μ a A B c d}
      --------------------------------------------------------------------------------------------------------
    → Any / config Δ Θ Γᵒ μ (! ((addr a) ⟨ id (Ref A) ⨾ ref c d ⨾ id (Ref B) ⟩)) —→ᵐ
       config Δ Θ Γᵒ μ ((! (addr a)) ⟨ d ⟩)

  cast-compose : ∀ {Δ Θ Γᵒ μ U c d}
    → RawValue U
      -------------------------------------------------------------------------------------
    → NonCast / config Δ Θ Γᵒ μ ((U ⟨ c ⟩) ⟨ d ⟩) —→ᵐ
       config Δ Θ Γᵒ μ (U ⟨ Θ ⊢ c ⨟ᵐ d ⟩)

  cast-id⋆ : ∀ {Δ Θ Γᵒ μ U}
    → RawValue U
      -----------------------------------------------------------------------------------
    → NonCast / config Δ Θ Γᵒ μ (U ⟨ id ⋆ ⨾ id⋆ ⨾ id ⋆ ⟩) —→ᵐ config Δ Θ Γᵒ μ U

  cast-idι : ∀ {Δ Θ Γᵒ μ U ι}
    → RawValue U
      ------------------------------------------------------------------------------------------------
    → NonCast / config Δ Θ Γᵒ μ (U ⟨ id (` ι) ⨾ idι ι ⨾ id (` ι) ⟩) —→ᵐ config Δ Θ Γᵒ μ U

  cast-blame : ∀ {Δ Θ Γᵒ μ U A t ℓ}
    → RawValue U
      ---------------------------------------------------------------------------------------------
    → NonCast / config Δ Θ Γᵒ μ (U ⟨ id A ⨾ err ℓ ⨾ t ⟩) —→ᵐ config Δ Θ Γᵒ μ (blame ℓ)


-- +-------------------------------------+ --
-- | Reflexive-transitive closure        | --
-- +-------------------------------------+ --

infix 0 _/_—↠ᵐ_
infix 0 _∣_—↠ᵒ_
infixr 2 _/_—→ᵐ⟨_⟩_
infixr 2 _∣_—→ᵒ⟨_⟩_
infix 3 _∎ᵐ
infix 3 _∣_∎ᵒ

data _∣_—↠ᵒ_ : Config CodeTerm → EC → Config CodeTerm → Set where

  _∣_∎ᵒ :
      (C : Config CodeTerm)
    → (e : EC)
      ---------------------
    → C ∣ e —↠ᵒ C

  _∣_—→ᵒ⟨_⟩_ :
      (C₁ : Config CodeTerm)
    → (e : EC)
    → {C₂ C₃ : Config CodeTerm}
    → C₁ ∣ e —→ᵒ C₂
    → C₂ ∣ e —↠ᵒ C₃
      ---------------------
    → C₁ ∣ e —↠ᵒ C₃


data _/_—↠ᵐ_ : ReductionCtx → Config MetaTerm → Config MetaTerm → Set where

  _∎ᵐ :
      {ctx : ReductionCtx}
    → (C : Config MetaTerm)
      ---------------------
    → ctx / C —↠ᵐ C

  _/_—→ᵐ⟨_⟩_ :
       (ctx : ReductionCtx) (C₁ : Config MetaTerm)
    → {C₂ C₃ : Config MetaTerm}
    → ctx / C₁ —→ᵐ C₂
    → ctx / C₂ —↠ᵐ C₃
      ---------------------
    → ctx / C₁ —↠ᵐ C₃
