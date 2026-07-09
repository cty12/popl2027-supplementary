module Theories.MetaTypes where

open import Data.List using (List; []; _∷_; _∷ʳ_; map) public
open import Data.List.Relation.Unary.All using (All)
open import Data.Product using (∃-syntax; _×_) renaming (_,_ to ⟨_,_⟩)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary using (Dec; yes; no)

open import Theories.Utils using (_∋_⦂_; here; there; ⟨_,_,_⟩)
open import Theories.EnvClassifiers
open import Theories.BaseTypes
open import Theories.CodeTypes

infixr 6 _⇒_

-- | Syntax of metalanguage types.
data MType : Set where
  ⋆        : MType
  `_       : Base → MType
  _⇒_      : MType → MType → MType
  Ref_     : MType → MType
  ‶_″_     : OType⋆ → EC⋆ → MType
  ∀̇_       : MType → MType
  _<:_=>_  : EC → EC → MType → MType

-- | EC variable renaming in meta types
renᵉ : RenameEC → MType → MType
renᵉ ρ ⋆ = ⋆
renᵉ ρ (` ι) = ` ι
renᵉ ρ (A ⇒ B) = renᵉ ρ A ⇒ renᵉ ρ B
renᵉ ρ (Ref A) = Ref (renᵉ ρ A)
renᵉ ρ (‶ O ″ ê) = ‶ O ″ renᵉ-ec⋆ ρ ê
renᵉ ρ (∀̇ A) = ∀̇ (renᵉ (extᵉ ρ) A)
renᵉ ρ (e₁ <: e₂ => A) = renᵉ-ec ρ e₁ <: renᵉ-ec ρ e₂ => renᵉ ρ A

-- | EC variable substitution in meta types
subᵉ : SubstEC → MType → MType
subᵉ σ ⋆ = ⋆
subᵉ σ (` ι) = ` ι
subᵉ σ (A ⇒ B) = subᵉ σ A ⇒ subᵉ σ B
subᵉ σ (Ref A) = Ref (subᵉ σ A)
subᵉ σ (‶ O ″ ê) = ‶ O ″ subᵉ-ec⋆ σ ê
subᵉ σ (∀̇ A) = ∀̇ (subᵉ (extsᵉ σ) A)
subᵉ σ (e₁ <: e₂ => A) = subᵉ-ec σ e₁ <: subᵉ-ec σ e₂ => subᵉ σ A

-- | EC single substitution in meta types
infix 6 _[_]ᵉ

_[_]ᵉ : MType → EC → MType
A [ e ]ᵉ = subᵉ (e •ᵉₛ idsᵉ) A

-- | Type matching for subtype constrained type.
data _⦊_<:_=>_ : MType → EC → EC → MType → Set where

  ⦊-sub : ∀ {e₁ e₂ A} → (e₁ <: e₂ => A) ⦊ e₁ <: e₂ => A

data Ground : MType → Set where
  gbase   : ∀ {ι} → Ground (` ι)
  gfun    : Ground (⋆ ⇒ ⋆)
  gref    : Ground (Ref ⋆)
  gcode   : Ground (‶ ⋆ ″ ⋆)
  gforall : Ground (∀̇ ⋆)
  gsub    : ∀ {e₁ e₂} → Ground (e₁ <: e₂ => ⋆)

renᵉ-ground : ∀ {G} → (ρ : RenameEC) → Ground G → Ground (renᵉ ρ G)
renᵉ-ground ρ gbase = gbase
renᵉ-ground ρ gfun = gfun
renᵉ-ground ρ gref = gref
renᵉ-ground ρ gcode = gcode
renᵉ-ground ρ gforall = gforall
renᵉ-ground ρ gsub = gsub

-- | Metalanguage typing context.
infixl 5 _⸴_

MCtx = List MType

pattern _⸴_ Γᵐ A = A ∷ Γᵐ

renᵉ-mctx : RenameEC → MCtx → MCtx
renᵉ-mctx ρ = map (renᵉ ρ)

⇑ᵉ-mctx : MCtx → MCtx
⇑ᵉ-mctx = renᵉ-mctx suc

subᵉ-mctx : SubstEC → MCtx → MCtx
subᵉ-mctx σ = map (subᵉ σ)

lookup-⇑ᵉ-mctx : ∀ {Γᵐ x A}
  → Γᵐ ∋ x ⦂ A
    ---------------------------------
  → ⇑ᵉ-mctx Γᵐ ∋ x ⦂ renᵉ suc A
lookup-⇑ᵉ-mctx here = here
lookup-⇑ᵉ-mctx (there lookup) = there (lookup-⇑ᵉ-mctx lookup)

lookup-⇑ᵉ-mctx-inv : ∀ {Γᵐ x A′}
  → ⇑ᵉ-mctx Γᵐ ∋ x ⦂ A′
    ------------------------------------------
  → ∃[ A ] (A′ ≡ renᵉ suc A × Γᵐ ∋ x ⦂ A)
lookup-⇑ᵉ-mctx-inv {Γᵐ = []} ()
lookup-⇑ᵉ-mctx-inv {Γᵐ = _ ∷ _} here = ⟨ _ , refl , here ⟩
lookup-⇑ᵉ-mctx-inv {Γᵐ = _ ∷ _} (there lookup) with lookup-⇑ᵉ-mctx-inv lookup
... | ⟨ A , refl , lookup′ ⟩ = ⟨ A , refl , there lookup′ ⟩

-- | Type well-formedness
infix 4 _⊢ᵐᵗ_

data _⊢ᵐᵗ_ : ECCtx → MType → Set where
  wf-⋆      : ∀ {Δ} → Δ ⊢ᵐᵗ ⋆
  wf-base   : ∀ {Δ ι} → Δ ⊢ᵐᵗ ` ι
  wf-fun    : ∀ {Δ A B} → Δ ⊢ᵐᵗ A → Δ ⊢ᵐᵗ B → Δ ⊢ᵐᵗ A ⇒ B
  wf-ref    : ∀ {Δ A} → Δ ⊢ᵐᵗ A → Δ ⊢ᵐᵗ Ref A
  wf-code   : ∀ {Δ O ê} → Δ ⊢ᵉ⋆ ê → Δ ⊢ᵐᵗ ‶ O ″ ê
  wf-forall : ∀ {Δ A} → Δ ,α ⊢ᵐᵗ A → Δ ⊢ᵐᵗ ∀̇ A
  wf-sub    : ∀ {Δ e₁ e₂ A} → Δ ⊢ᵉ e₁ → Δ ⊢ᵉ e₂ → Δ ⊢ᵐᵗ A → Δ ⊢ᵐᵗ e₁ <: e₂ => A

-- | Well-formed metalanguage contexts.
infix 4 _⊢_MCtx

_⊢_MCtx : ECCtx → MCtx → Set
Δ ⊢ Γᵐ MCtx = All (λ A → Δ ⊢ᵐᵗ A) Γᵐ

_≡?_ : ∀ (A B : MType) → Dec (A ≡ B)
⋆ ≡? ⋆ = yes refl
⋆ ≡? (` _) = no λ ()
⋆ ≡? (_ ⇒ _) = no λ ()
⋆ ≡? (Ref _) = no λ ()
⋆ ≡? (‶ _ ″ _) = no λ ()
⋆ ≡? (∀̇ _) = no λ ()
⋆ ≡? (_ <: _ => _) = no λ ()
(` _) ≡? ⋆ = no λ ()
(` ι) ≡? (` ι′) with base-eq? ι ι′
... | yes refl = yes refl
... | no ι≢ι′ = no λ { refl → ι≢ι′ refl }
(` _) ≡? (_ ⇒ _) = no λ ()
(` _) ≡? (Ref _) = no λ ()
(` _) ≡? (‶ _ ″ _) = no λ ()
(` _) ≡? (∀̇ _) = no λ ()
(` _) ≡? (_ <: _ => _) = no λ ()
(_ ⇒ _) ≡? ⋆ = no λ ()
(_ ⇒ _) ≡? (` _) = no λ ()
(A ⇒ B) ≡? (C ⇒ D) with A ≡? C | B ≡? D
... | yes refl | yes refl = yes refl
... | no A≢C | _ = no λ { refl → A≢C refl }
... | yes refl | no B≢D = no λ { refl → B≢D refl }
(_ ⇒ _) ≡? (Ref _) = no λ ()
(_ ⇒ _) ≡? (‶ _ ″ _) = no λ ()
(_ ⇒ _) ≡? (∀̇ _) = no λ ()
(_ ⇒ _) ≡? (_ <: _ => _) = no λ ()
(Ref _) ≡? ⋆ = no λ ()
(Ref _) ≡? (` _) = no λ ()
(Ref _) ≡? (_ ⇒ _) = no λ ()
(Ref A) ≡? (Ref B) with A ≡? B
... | yes refl = yes refl
... | no A≢B = no λ { refl → A≢B refl }
(Ref _) ≡? (‶ _ ″ _) = no λ ()
(Ref _) ≡? (∀̇ _) = no λ ()
(Ref _) ≡? (_ <: _ => _) = no λ ()
(‶ _ ″ _) ≡? ⋆ = no λ ()
(‶ _ ″ _) ≡? (` _) = no λ ()
(‶ _ ″ _) ≡? (_ ⇒ _) = no λ ()
(‶ _ ″ _) ≡? (Ref _) = no λ ()
(‶ O ″ ê) ≡? (‶ O′ ″ ê′) with O ≡?ᵒ O′ | ê ≡?ᵉ⋆ ê′
... | yes refl | yes refl = yes refl
... | no O≢O′ | _ = no λ { refl → O≢O′ refl }
... | yes refl | no ê≢ê′ = no λ { refl → ê≢ê′ refl }
(‶ _ ″ _) ≡? (∀̇ _) = no λ ()
(‶ _ ″ _) ≡? (_ <: _ => _) = no λ ()
(∀̇ _) ≡? ⋆ = no λ ()
(∀̇ _) ≡? (` _) = no λ ()
(∀̇ _) ≡? (_ ⇒ _) = no λ ()
(∀̇ _) ≡? (Ref _) = no λ ()
(∀̇ _) ≡? (‶ _ ″ _) = no λ ()
(∀̇ A) ≡? (∀̇ B) with A ≡? B
... | yes refl = yes refl
... | no A≢B = no λ { refl → A≢B refl }
(∀̇ _) ≡? (_ <: _ => _) = no λ ()
(_ <: _ => _) ≡? ⋆ = no λ ()
(_ <: _ => _) ≡? (` _) = no λ ()
(_ <: _ => _) ≡? (_ ⇒ _) = no λ ()
(_ <: _ => _) ≡? (Ref _) = no λ ()
(_ <: _ => _) ≡? (‶ _ ″ _) = no λ ()
(_ <: _ => _) ≡? (∀̇ _) = no λ ()
(e₁ <: e₂ => A) ≡? (e₃ <: e₄ => B) with e₁ ≡?ᵉ e₃ | e₂ ≡?ᵉ e₄ | A ≡? B
... | yes refl | yes refl | yes refl = yes refl
... | no e₁≢e₃ | _ | _ = no λ { refl → e₁≢e₃ refl }
... | yes refl | no e₂≢e₄ | _ = no λ { refl → e₂≢e₄ refl }
... | yes refl | yes refl | no A≢B = no λ { refl → A≢B refl }
