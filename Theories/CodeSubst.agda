module Theories.CodeSubst where

open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)

open import Theories.CCAlphaRefStarSyntaxAndTypeSystem


-- +-----------------------------+ --
-- | Code-variable renaming      | --
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


-- +--------------------------------------+ --
-- | Code-variable parallel substitution  | --
-- +--------------------------------------+ --

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


-- +-----------------------------+ --
-- | Code-variable substitution  | --
-- +-----------------------------+ --

infix 8 _[_]ᵒ

_[_]ᵒ : CodeTerm → CodeTerm → CodeTerm
Nᵒ [ Mᵒ ]ᵒ = substᵒ-code (Mᵒ •ᵒₛ idsᵒ) Nᵒ


-- +-----------------------------------------------+ --
-- | Code-variable substitution as code renaming   | --
-- +-----------------------------------------------+ --

private

  mutual

    subst-code-ren : ∀ {σ ρ} Mᵒ
      → (∀ x → σ x ≡ ` ρ x)
        ---------------------------------------
      → substᵒ-code σ Mᵒ ≡ renᵒ-code ρ Mᵒ
    subst-code-ren ($ r) σ≡ρ = refl
    subst-code-ren (` x) σ≡ρ = σ≡ρ x
    subst-code-ren {σ = σ} {ρ = ρ} (ƛ T ˙ Mᵒ) σ≡ρ
      rewrite subst-code-ren {σ = extsᵒ σ} {ρ = extᵒ ρ} Mᵒ
        (λ where
          zero → refl
          (suc x) → cong (renᵒ-code suc) (σ≡ρ x)) = refl
    subst-code-ren (ƛ̅ e ˙ Mᵒ) σ≡ρ rewrite subst-code-ren Mᵒ σ≡ρ = refl
    subst-code-ren (L · M) σ≡ρ rewrite subst-code-ren L σ≡ρ | subst-code-ren M σ≡ρ = refl
    subst-code-ren (~ M) σ≡ρ rewrite subst-meta-ren M σ≡ρ = refl
    subst-code-ren (blameᵒ ℓ) σ≡ρ = refl

    subst-meta-ren : ∀ {σ ρ} M
      → (∀ x → σ x ≡ ` ρ x)
        ------------------------------------
      → substᵒ-meta σ M ≡ renᵒ-meta ρ M
    subst-meta-ren ($ r) σ≡ρ = refl
    subst-meta-ren (` x) σ≡ρ = refl
    subst-meta-ren (addr a) σ≡ρ = refl
    subst-meta-ren (ƛ M) σ≡ρ rewrite subst-meta-ren M σ≡ρ = refl
    subst-meta-ren (L · M) σ≡ρ rewrite subst-meta-ren L σ≡ρ | subst-meta-ren M σ≡ρ = refl
    subst-meta-ren (Λ M) σ≡ρ rewrite subst-meta-ren M σ≡ρ = refl
    subst-meta-ren (M ·[ e ]) σ≡ρ rewrite subst-meta-ren M σ≡ρ = refl
    subst-meta-ren (e₁ <: e₂ => M) σ≡ρ rewrite subst-meta-ren M σ≡ρ = refl
    subst-meta-ren (M ●) σ≡ρ rewrite subst-meta-ren M σ≡ρ = refl
    subst-meta-ren (M ★ ℓ) σ≡ρ rewrite subst-meta-ren M σ≡ρ = refl
    subst-meta-ren (‶ M ″ e) σ≡ρ rewrite subst-code-ren M σ≡ρ = refl
    subst-meta-ren (ref M) σ≡ρ rewrite subst-meta-ren M σ≡ρ = refl
    subst-meta-ren (M := N) σ≡ρ rewrite subst-meta-ren M σ≡ρ | subst-meta-ren N σ≡ρ = refl
    subst-meta-ren (! M) σ≡ρ rewrite subst-meta-ren M σ≡ρ = refl
    subst-meta-ren (M ⟨ c ⟩) σ≡ρ rewrite subst-meta-ren M σ≡ρ = refl
    subst-meta-ren (blame ℓ) σ≡ρ = refl

subst-code-var-ren : ∀ y Mᵒ
    ------------------------------------------
  → Mᵒ [ ` y ]ᵒ ≡ renᵒ-code (y •ᵒ idᵒ) Mᵒ
subst-code-var-ren y Mᵒ =
  subst-code-ren Mᵒ λ where
    zero → refl
    (suc x) → refl
