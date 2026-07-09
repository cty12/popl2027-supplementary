module Theories.Reify where

open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing; _>>=_)
open import Data.Nat using (zero; suc)
open import Data.Product using (_×_) renaming (_,_ to ⟨_,_⟩)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Theories.CCAlphaRefStarSyntaxAndTypeSystem as CC
  using (CodeTerm; OType; ECVar; Var; `_ ; ε; lookupOwner)
open import Theories.BaseTypes using (Nat; Unit; Int)
open import Theories.STLC as STLC
  using (STLCTerm)
open import Theories.Utils using (index)


-- | The reification environment stores the globally-allocated code variables
-- | corresponding to the lexical binders currently in scope, innermost first.
ReifyEnv : Set
ReifyEnv = List Var

reifyAt : List (OType × ECVar) → ReifyEnv → CodeTerm → Maybe STLCTerm
reifyAt Γᵒ ρ (CC.$ r) = just (STLC.$ r)
reifyAt Γᵒ ρ (CC.` x) = do
  x′ ← index ρ x
  just (STLC.` x′)
reifyAt Γᵒ ρ (CC.ƛ T ˙ M) = nothing
reifyAt Γᵒ ρ (CC.ƛ̅ ε ˙ M) = nothing
reifyAt Γᵒ ρ (CC.ƛ̅ ` α ˙ M) = do
  ⟨ x , T ⟩ ← lookupOwner Γᵒ α
  M′ ← reifyAt Γᵒ (x ∷ ρ) M
  just (STLC.ƛ T ˙ M′)
reifyAt Γᵒ ρ (L CC.· M) = do
  L′ ← reifyAt Γᵒ ρ L
  M′ ← reifyAt Γᵒ ρ M
  just (L′ STLC.· M′)
reifyAt Γᵒ ρ (CC.~ M) = nothing
reifyAt Γᵒ ρ (CC.blameᵒ ℓ) = nothing

reify : List (OType × ECVar) → CodeTerm → Maybe STLCTerm
reify Γᵒ M = reifyAt Γᵒ [] M


reify-example :
  reify (⟨ ` Nat , 41 ⟩ ∷ ⟨ ` Unit , 43 ⟩ ∷ ⟨ ` Int , 42 ⟩ ∷ [])
        (CC.ƛ̅ ` 41 ˙ CC.ƛ̅ ` 42 ˙ CC.ƛ̅ ` 43 ˙ CC.` 0)
    ≡ just (STLC.ƛ ` Nat ˙ STLC.ƛ ` Int ˙ STLC.ƛ ` Unit ˙ STLC.` 2)
reify-example = refl
