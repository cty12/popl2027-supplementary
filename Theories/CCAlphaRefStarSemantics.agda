{-

  Small-step semantics for the cast calculus of λαRef⋆.

  The syntax is raw.  Runtime configurations carry exactly the contexts used
  by reduction: EC variables, subtyping constraints, object variables, and the
  heap.  Heap typing contexts belong to preservation, not to reduction.

-}

module Theories.CCAlphaRefStarSemantics where

open import Data.List using ([]; [_]; _++_; _∷ʳ_; length)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≢_)
open import Relation.Nullary using (¬_)

open import Theories.Utils using (_∋_⦂_)
open import Theories.CCAlphaRefStarSyntaxAndTypeSystem hiding (idᵉ)
open import Theories.Heap
open import Theories.Configurations public
open import Theories.Values
open import Theories.CodeSubst using (_[_]ᵒ) public
open import Theories.ECSubst using (_[_]ᵉᵒ; _[_]ᵉᵐ; _[_]ᶜ) public
open import Theories.MetaSubst using (_[_]ᵐ) public

import Theories.CoercionSequences.EC.Definition as ECS
import Theories.CoercionSequences.Meta.Definition as MC
open import Theories.CoercionSequences.Meta.Definition using (Inert)


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

  □⟨_⟩ : MC.MCoercionSeq → MetaFrame


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
plugᵐ (□⟨ c ⟩) M = M ⟨ c ⟩


-- +------------------------------------------------------+ --
-- |  Raw reduction semantics for CCαRef⋆                 | --
-- +------------------------------------------------------+ --

infix 0 _—→ᵐ_
infix 0 _∣_—→ᵒ_

data _—→ᵐ_ : Config MetaTerm → Config MetaTerm → Set

data _∣_—→ᵒ_ : Config CodeTerm → EC → Config CodeTerm → Set

-- | a config is irreducible if it can't take a step
Irreducible : Config MetaTerm → Set
Irreducible C = ∀ {C′} → ¬ (C —→ᵐ C′)

NotBlame : Config MetaTerm → Set
NotBlame C = ∀ ℓ → C .M ≢ blame ℓ

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
    → config Δ₁ Θ₁ Γᵒ₁ μ₁ M —→ᵐ config Δ₂ Θ₂ Γᵒ₂ μ₂ N
      ------------------------------------------------------------------
    → config Δ₁ Θ₁ Γᵒ₁ μ₁ (~ M) ∣ e —→ᵒ config Δ₂ Θ₂ Γᵒ₂ μ₂ (~ N)

  splice-blame : ∀ {Δ Θ Γᵒ μ e ℓ}
      ---------------------------------------------------------------------------
    → config Δ Θ Γᵒ μ (~ (blame ℓ)) ∣ e —→ᵒ config Δ Θ Γᵒ μ (blameᵒ ℓ)

  splice-β : ∀ {Δ Θ Γᵒ μ e₁ e₂ Vᵒ}
    → CodeValue Vᵒ
      ---------------------------------------------------------------------
    → config Δ Θ Γᵒ μ (~ (‶ Vᵒ ″ e₁)) ∣ e₂ —→ᵒ config Δ Θ Γᵒ μ Vᵒ

  splice-sub : ∀ {Δ Θ Γᵒ μ e₁ e₂ Vᵒ}
    → CodeValue Vᵒ
      ---------------------------------------------------------------------------------------------------------------
    → config Δ Θ Γᵒ μ (~ ((‶ Vᵒ ″ e₁) ⟨ [ MC.‶ [] ″ [ ec e₁ ECS.↑ ec e₂ ] ] ⟩)) ∣ e₂ —→ᵒ config Δ Θ Γᵒ μ Vᵒ

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


data _—→ᵐ_ where

  ξ-meta : ∀ {Δ₁ Δ₂ Θ₁ Θ₂ Γᵒ₁ Γᵒ₂ μ₁ μ₂ M N}
    → (F : MetaFrame)
    → config Δ₁ Θ₁ Γᵒ₁ μ₁ M —→ᵐ config Δ₂ Θ₂ Γᵒ₂ μ₂ N
      ---------------------------------------------------------------------------
    → config Δ₁ Θ₁ Γᵒ₁ μ₁ (plugᵐ F M) —→ᵐ config Δ₂ Θ₂ Γᵒ₂ μ₂ (plugᵐ F N)

  ξ-meta-blame : ∀ {Δ Θ Γᵒ μ ℓ}
    → (F : MetaFrame)
      ---------------------------------------------------------------------
    → config Δ Θ Γᵒ μ (plugᵐ F (blame ℓ)) —→ᵐ config Δ Θ Γᵒ μ (blame ℓ)

  ξ-quote : ∀ {Δ₁ Δ₂ Θ₁ Θ₂ Γᵒ₁ Γᵒ₂ μ₁ μ₂ e Mᵒ Nᵒ}
    → config Δ₁ Θ₁ Γᵒ₁ μ₁ Mᵒ ∣ e —→ᵒ config Δ₂ Θ₂ Γᵒ₂ μ₂ Nᵒ
      ------------------------------------------------------------------------
    → config Δ₁ Θ₁ Γᵒ₁ μ₁ (‶ Mᵒ ″ e) —→ᵐ config Δ₂ Θ₂ Γᵒ₂ μ₂ (‶ Nᵒ ″ e)

  quote-blame : ∀ {Δ Θ Γᵒ μ e ℓ}
      ------------------------------------------------------------------------
    → config Δ Θ Γᵒ μ (‶ blameᵒ ℓ ″ e) —→ᵐ config Δ Θ Γᵒ μ (blame ℓ)

  β : ∀ {Δ Θ Γᵒ μ N V}
    → Value V
      ------------------------------------------------------------------
    → config Δ Θ Γᵒ μ ((ƛ N) · V) —→ᵐ config Δ Θ Γᵒ μ (N [ V ]ᵐ)

  β-cast : ∀ {Δ Θ Γᵒ μ U W c d}
    → RawValue U
    → Value W
    → Inert [ c MC.⇒ d ]
      ------------------------------------------------------------------------------------------------
    → config Δ Θ Γᵒ μ ((U ⟨ [ c MC.⇒ d ] ⟩) · W) —→ᵐ config Δ Θ Γᵒ μ ((U · (W ⟨ c ⟩)) ⟨ d ⟩)

  Λ-β : ∀ {Δ Θ Γᵒ μ e M}
      ---------------------------------------------------------------------
    → config Δ Θ Γᵒ μ ((Λ M) ·[ e ]) —→ᵐ config Δ Θ Γᵒ μ (M [ e ]ᵉᵐ)

  Λ-β-cast : ∀ {Δ Θ Γᵒ μ e U c}
    → RawValue U
      ---------------------------------------------------------------------------------------------------
    → config Δ Θ Γᵒ μ ((U ⟨ [ MC.∀̇ c ] ⟩) ·[ e ]) —→ᵐ config Δ Θ Γᵒ μ ((U ·[ e ]) ⟨ c [ e ]ᶜ ⟩)

  sub-β : ∀ {Δ Θ Γᵒ μ e₁ e₂ M}
      ------------------------------------------------------------------
    → config Δ Θ Γᵒ μ ((e₁ <: e₂ => M) ●) —→ᵐ config Δ Θ Γᵒ μ M

  sub-β-cast : ∀ {Δ Θ Γᵒ μ e₁ e₂ U c}
    → RawValue U
      ------------------------------------------------------------------------------------
    → config Δ Θ Γᵒ μ ((U ⟨ [ e₁ MC.<: e₂ => c ] ⟩) ●) —→ᵐ config Δ Θ Γᵒ μ ((U ●) ⟨ c ⟩)

  sub-cast-success : ∀ {Δ Θ Γᵒ μ e₁ e₂ U c ℓ}
    → RawValue U
    → Θ ⊢ᵉ e₁ <: e₂
    → Inert (c ++ [ ((e₁ <: e₂ => ⋆) MC.！) gsub ])
      ---------------------------------------------------------------------------------------------------------------
    → config Δ Θ Γᵒ μ ((U ⟨ c ++ [ ((e₁ <: e₂ => ⋆) MC.！) gsub ] ⟩) ★ ℓ) —→ᵐ config Δ Θ Γᵒ μ ((U ⟨ c ⟩) ●)

  sub-cast-sub-fail : ∀ {Δ Θ Γᵒ μ e₁ e₂ U c ℓ}
    → RawValue U
    → ¬ Θ ⊢ᵉ e₁ <: e₂
    → Inert (c ++ [ ((e₁ <: e₂ => ⋆) MC.！) gsub ])
      ------------------------------------------------------------------------------------------------------------
    → config Δ Θ Γᵒ μ ((U ⟨ c ++ [ ((e₁ <: e₂ => ⋆) MC.！) gsub ] ⟩) ★ ℓ) —→ᵐ config Δ Θ Γᵒ μ (blame ℓ)

  sub-cast-fail : ∀ {Δ Θ Γᵒ μ e₁ e₂ U c G g ℓ}
    → RawValue U
    → Inert (c ++ [ (G MC.！) g ])
    → ¬ G ⦊ e₁ <: e₂ => ⋆
      ------------------------------------------------------------------------------------------
    → config Δ Θ Γᵒ μ ((U ⟨ c ++ [ (G MC.！) g ] ⟩) ★ ℓ) —→ᵐ config Δ Θ Γᵒ μ (blame ℓ)

  ref : ∀ {Δ Θ Γᵒ μ V}
    → Value V
      ------------------------------------------------------------------------------
    → config Δ Θ Γᵒ μ (ref V) —→ᵐ config Δ Θ Γᵒ (μ ∷ʳ V) (addr (length μ))

  deref : ∀ {Δ Θ Γᵒ μ a V}
    → μ ∋ a ⦂ V
      ------------------------------------------------------------
    → config Δ Θ Γᵒ μ (! (addr a)) —→ᵐ config Δ Θ Γᵒ μ V

  assign : ∀ {Δ Θ Γᵒ μ μ′ a V}
    → Value V
    → μ ⟦ a ↦ V ⟧= μ′
      ---------------------------------------------------------------------
    → config Δ Θ Γᵒ μ ((addr a) := V) —→ᵐ config Δ Θ Γᵒ μ′ ($ tt)

  assign-cast : ∀ {Δ Θ Γᵒ μ a V c d}
    → Value V
    → Inert [ MC.Ref c , d ]
      ------------------------------------------------------------------------------------------------------------
    → config Δ Θ Γᵒ μ (((addr a) ⟨ [ MC.Ref c , d ] ⟩) := V) —→ᵐ config Δ Θ Γᵒ μ ((addr a) := (V ⟨ c ⟩))

  deref-cast : ∀ {Δ Θ Γᵒ μ a c d}
    → Inert [ MC.Ref c , d ]
      ------------------------------------------------------------------------------------------------------
    → config Δ Θ Γᵒ μ (! ((addr a) ⟨ [ MC.Ref c , d ] ⟩)) —→ᵐ config Δ Θ Γᵒ μ ((! (addr a)) ⟨ d ⟩)

  cast-reduce : ∀ {Δ Θ Γᵒ μ U c d}
    → RawValue U
    → Θ MC.⊢ᵐ̅ c —→ d
      ---------------------------------------------------------------
    → config Δ Θ Γᵒ μ (U ⟨ c ⟩) —→ᵐ config Δ Θ Γᵒ μ (U ⟨ d ⟩)

  cast-compose : ∀ {Δ Θ Γᵒ μ U c d}
    → RawValue U
      ------------------------------------------------------------------------------
    → config Δ Θ Γᵒ μ ((U ⟨ c ⟩) ⟨ d ⟩) —→ᵐ config Δ Θ Γᵒ μ (U ⟨ c ++ d ⟩)

  cast-id : ∀ {Δ Θ Γᵒ μ U}
    → RawValue U
      ---------------------------------------------------------
    → config Δ Θ Γᵒ μ (U ⟨ [] ⟩) —→ᵐ config Δ Θ Γᵒ μ U

  cast-blame : ∀ {Δ Θ Γᵒ μ U ℓ}
    → RawValue U
      ------------------------------------------------------------------------------
    → config Δ Θ Γᵒ μ (U ⟨ [ MC.⊥ ℓ ] ⟩) —→ᵐ config Δ Θ Γᵒ μ (blame ℓ)
