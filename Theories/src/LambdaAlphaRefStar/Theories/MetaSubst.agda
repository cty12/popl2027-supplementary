module LambdaAlphaRefStar.Theories.MetaSubst where

open import LambdaAlphaRefStar.Theories.CCAlphaRefStarSyntaxAndTypeSystem
open import LambdaAlphaRefStar.Theories.CodeSubst using (renᵒ-meta)
open import LambdaAlphaRefStar.Theories.ECSubst using (renᵉ-meta)


-- +-----------------------------+ --
-- | Meta-variable renaming      | --
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


-- +--------------------------------------+ --
-- | Meta-variable parallel substitution  | --
-- +--------------------------------------+ --

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


-- +-----------------------------+ --
-- | Meta-variable substitution  | --
-- +-----------------------------+ --

infix 8 _[_]ᵐ

_[_]ᵐ : MetaTerm → MetaTerm → MetaTerm
M [ N ]ᵐ = substᵐ-meta (N •ᵐₛ idsᵐ) M
