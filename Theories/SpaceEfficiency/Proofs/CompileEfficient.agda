module Theories.SpaceEfficiency.Proofs.CompileEfficient where

open import Data.Bool using (Bool; true)
open import Data.Nat using (ℕ; zero; suc; _≤_; z≤n; s≤s)
open import Data.Product using (Σ-syntax; _×_) renaming (_,_ to ⟨_,_⟩)

open import Theories.SurfaceSyntaxAndTypeSystem
open import Theories.SpaceEfficiency.Compilation
  using (compileᵒ⇒; compileᵒ⇐; compile)
open import Theories.SpaceEfficiency.AdjacentCastOK
  using
    (_⊢ᵒ_ok; _∣_⊢ᵐ_ok;
     spliceOK; constᵒOK; varᵒOK; absᵒOK; appᵒOK;
     constᵐOK; varᵐOK; absᵐOK; appᵐOK; ecAbsOK; ecAppOK; subIntroOK; subElimOK; subElimDynOK;
     quoteOK; refOK; assignOK; derefOK)
open import Theories.SpaceEfficiency.Proofs.PreserveOK
  using (cast-pres-ok)


mutual

  compileᵒ⇒-efficient : ∀ {Δ Θ Γᵐ Γᵒ e T delayed M}
    → (d : Δ ; Θ ; Γᵐ ; Γᵒ ; e ⊢ M ⭆ T)
    → delayed ⊢ᵒ compileᵒ⇒ d ok
  compileᵒ⇒-efficient code-constˢ =
    constᵒOK
  compileᵒ⇒-efficient (code-varˢ lookup sub) =
    varᵒOK
  compileᵒ⇒-efficient (code-absˢ d) =
    absᵒOK (compileᵒ⇒-efficient d)
  compileᵒ⇒-efficient (code-appˢ dL dM) =
    appᵒOK (compileᵒ⇒-efficient dL) (compileᵒ⇐-efficient dM)

  compileᵒ⇐-efficient : ∀ {Δ Θ Γᵐ Γᵒ e T delayed M}
    → (d : Δ ; Θ ; Γᵐ ; Γᵒ ; e ⊢ M ⭅ T)
    → delayed ⊢ᵒ compileᵒ⇐ d ok
  compileᵒ⇐-efficient (spliceˢ d A≲T)
    with compile-efficient d
  ... | ⟨ n , ⟨ n≤1 , Mok ⟩ ⟩ =
    spliceOK (cast-pres-ok Mok n≤1)
  compileᵒ⇐-efficient (checkˢ d) =
    compileᵒ⇒-efficient d

  compile-efficient : ∀ {Δ Θ Γᵐ Γᵒ A delayed M}
    → (d : Δ ; Θ ; Γᵐ ; Γᵒ ⊢ M ⦂ A)
    → Σ[ n ∈ ℕ ] (n ≤ 1 × n ∣ delayed ⊢ᵐ compile d ok)
  compile-efficient meta-constˢ =
    ⟨ zero , ⟨ z≤n , constᵐOK ⟩ ⟩
  compile-efficient (meta-varˢ lookup) =
    ⟨ suc zero , ⟨ s≤s z≤n , varᵐOK ⟩ ⟩
  compile-efficient (meta-absˢ ⊢A dM)
    with compile-efficient {delayed = true} dM
  ... | ⟨ n , ⟨ n≤1 , Mok ⟩ ⟩ =
    ⟨ zero , ⟨ z≤n , absᵐOK Mok ⟩ ⟩
  compile-efficient (meta-appˢ dL dM B≲A₁)
    with compile-efficient dL | compile-efficient dM
  ... | ⟨ n , ⟨ n≤1 , Lok ⟩ ⟩ | ⟨ m , ⟨ m≤1 , Mok ⟩ ⟩ =
    ⟨ zero , ⟨ z≤n , appᵐOK Lok (cast-pres-ok Mok m≤1) ⟩ ⟩
  compile-efficient (meta-app⋆ˢ dL dM)
    with compile-efficient dL | compile-efficient dM
  ... | ⟨ n , ⟨ n≤1 , Lok ⟩ ⟩ | ⟨ m , ⟨ m≤1 , Mok ⟩ ⟩ =
    ⟨ zero , ⟨ z≤n , appᵐOK (cast-pres-ok Lok n≤1) (cast-pres-ok Mok m≤1) ⟩ ⟩
  compile-efficient (meta-ecabsˢ dM)
    with compile-efficient {delayed = true} dM
  ... | ⟨ n , ⟨ n≤1 , Mok ⟩ ⟩ =
    ⟨ zero , ⟨ z≤n , ecAbsOK Mok ⟩ ⟩
  compile-efficient (meta-ecappˢ ⊢e dM)
    with compile-efficient dM
  ... | ⟨ n , ⟨ n≤1 , Mok ⟩ ⟩ =
    ⟨ zero , ⟨ z≤n , ecAppOK Mok ⟩ ⟩
  compile-efficient (meta-ecapp⋆ˢ ⊢e dM)
    with compile-efficient dM
  ... | ⟨ n , ⟨ n≤1 , Mok ⟩ ⟩ =
    ⟨ zero , ⟨ z≤n , ecAppOK (cast-pres-ok Mok n≤1) ⟩ ⟩
  compile-efficient (meta-subintroˢ ⊢e₁ ⊢e₂ dM)
    with compile-efficient {delayed = true} dM
  ... | ⟨ n , ⟨ n≤1 , Mok ⟩ ⟩ =
    ⟨ zero , ⟨ z≤n , subIntroOK Mok ⟩ ⟩
  compile-efficient (meta-subelimˢ sub dM)
    with compile-efficient dM
  ... | ⟨ n , ⟨ n≤1 , Mok ⟩ ⟩ =
    ⟨ zero , ⟨ z≤n , subElimOK Mok ⟩ ⟩
  compile-efficient (meta-subelim⋆ˢ dM)
    with compile-efficient dM
  ... | ⟨ n , ⟨ n≤1 , Mok ⟩ ⟩ =
    ⟨ zero , ⟨ z≤n , subElimDynOK Mok ⟩ ⟩
  compile-efficient (meta-quoteˢ ⊢e dM) =
    ⟨ zero , ⟨ z≤n , quoteOK (compileᵒ⇒-efficient dM) ⟩ ⟩
  compile-efficient (meta-refˢ dM)
    with compile-efficient dM
  ... | ⟨ n , ⟨ n≤1 , Mok ⟩ ⟩ =
    ⟨ zero , ⟨ z≤n , refOK Mok ⟩ ⟩
  compile-efficient (meta-assignˢ dL dM B≲A)
    with compile-efficient dL | compile-efficient dM
  ... | ⟨ n , ⟨ n≤1 , Lok ⟩ ⟩ | ⟨ m , ⟨ m≤1 , Mok ⟩ ⟩ =
    ⟨ zero , ⟨ z≤n , assignOK Lok (cast-pres-ok Mok m≤1) ⟩ ⟩
  compile-efficient (meta-assign⋆ˢ dL dM)
    with compile-efficient dL | compile-efficient dM
  ... | ⟨ n , ⟨ n≤1 , Lok ⟩ ⟩ | ⟨ m , ⟨ m≤1 , Mok ⟩ ⟩ =
    ⟨ zero , ⟨ z≤n , assignOK (cast-pres-ok Lok n≤1) (cast-pres-ok Mok m≤1) ⟩ ⟩
  compile-efficient (meta-derefˢ dM)
    with compile-efficient dM
  ... | ⟨ n , ⟨ n≤1 , Mok ⟩ ⟩ =
    ⟨ zero , ⟨ z≤n , derefOK Mok ⟩ ⟩
  compile-efficient (meta-deref⋆ˢ dM)
    with compile-efficient dM
  ... | ⟨ n , ⟨ n≤1 , Mok ⟩ ⟩ =
    ⟨ zero , ⟨ z≤n , derefOK (cast-pres-ok Mok n≤1) ⟩ ⟩
