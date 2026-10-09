module LambdaAlphaRefStar.Theories.SpaceEfficiency.Proofs.ElaborationEfficient where

open import Data.Bool using (Bool; true)
open import Data.Nat using (ℕ; zero; suc; _≤_; z≤n; s≤s)
open import Data.Product using (∃-syntax; _×_) renaming (_,_ to ⟨_,_⟩)

open import LambdaAlphaRefStar.Theories.SpaceEfficiency.CCAlphaRefStarSyntaxAndTypeSystem
open import LambdaAlphaRefStar.Theories.SpaceEfficiency.Elaboration
open import LambdaAlphaRefStar.Theories.SpaceEfficiency.Proofs.PreserveOK
  using
    (_⊢ᵒ_ok; _∣_⊢ᵐ_ok; cast-pres-ok;
     spliceOK; constᵒOK; varᵒOK; absᵒOK; appᵒOK;
     constᵐOK; varᵐOK; absᵐOK; appᵐOK; ecAbsOK; ecAppOK; subIntroOK; subElimOK; subElimDynOK;
     quoteOK; refOK; assignOK; derefOK)


mutual

  elab-efficientᵒ⇒ : ∀ {Δ Θ Γᵐ Γᵒ e T d M M′}
    → Δ ; Θ ; Γᵐ ; Γᵒ ; e ⊢ M ↝ M′ ⭆ T
    → d ⊢ᵒ M′ ok
  elab-efficientᵒ⇒ code-const = constᵒOK
  elab-efficientᵒ⇒ (code-var lookup sub) = varᵒOK
  elab-efficientᵒ⇒ (code-abs N↝N′) = absᵒOK (elab-efficientᵒ⇒ N↝N′)
  elab-efficientᵒ⇒ (code-app L↝L′ M↝M′) =
    appᵒOK (elab-efficientᵒ⇒ L↝L′) (elab-efficientᵒ⇐ M↝M′)

  elab-efficientᵒ⇐ : ∀ {Δ Θ Γᵐ Γᵒ e T d M M′}
    → Δ ; Θ ; Γᵐ ; Γᵒ ; e ⊢ M ↝ M′ ⭅ T
    → d ⊢ᵒ M′ ok
  elab-efficientᵒ⇐ (splice M↝M′ A≲T)
    with elab-efficient M↝M′
  ... | ⟨ n , ⟨ n≤1 , Mok ⟩ ⟩ =
    spliceOK (cast-pres-ok Mok n≤1)
  elab-efficientᵒ⇐ (check M↝M′) = elab-efficientᵒ⇒ M↝M′

  elab-efficient : ∀ {Δ Θ Γᵐ Γᵒ A d M M′}
    → Δ ; Θ ; Γᵐ ; Γᵒ ⊢ M ↝ M′ ⦂ A
    → ∃[ n ] (n ≤ 1 × n ∣ d ⊢ᵐ M′ ok)
  elab-efficient meta-const = ⟨ zero , ⟨ z≤n , constᵐOK ⟩ ⟩
  elab-efficient (meta-var lookup) = ⟨ suc zero , ⟨ s≤s z≤n , varᵐOK ⟩ ⟩
  elab-efficient {d = d} (meta-abs ⊢A M↝M′)
    with elab-efficient {d = true} M↝M′
  ... | ⟨ n , ⟨ n≤1 , Mok ⟩ ⟩ =
    ⟨ zero , ⟨ z≤n , absᵐOK Mok ⟩ ⟩
  elab-efficient {d = d} (meta-app L↝L′ M↝M′ B≲A₁)
    with elab-efficient {d = d} L↝L′ | elab-efficient {d = d} M↝M′
  ... | ⟨ n , ⟨ n≤1 , Lok ⟩ ⟩ | ⟨ m , ⟨ m≤1 , Mok ⟩ ⟩ =
    ⟨ zero , ⟨ z≤n , appᵐOK Lok (cast-pres-ok Mok m≤1) ⟩ ⟩
  elab-efficient {d = d} (meta-app⋆ L↝L′ M↝M′)
    with elab-efficient {d = d} L↝L′ | elab-efficient {d = d} M↝M′
  ... | ⟨ n , ⟨ n≤1 , Lok ⟩ ⟩ | ⟨ m , ⟨ m≤1 , Mok ⟩ ⟩ =
    ⟨ zero , ⟨ z≤n , appᵐOK (cast-pres-ok Lok n≤1) (cast-pres-ok Mok m≤1) ⟩ ⟩
  elab-efficient {d = d} (meta-ecabs M↝M′)
    with elab-efficient {d = true} M↝M′
  ... | ⟨ n , ⟨ n≤1 , Mok ⟩ ⟩ =
    ⟨ zero , ⟨ z≤n , ecAbsOK Mok ⟩ ⟩
  elab-efficient {d = d} (meta-ecapp ⊢e M↝M′)
    with elab-efficient {d = d} M↝M′
  ... | ⟨ n , ⟨ n≤1 , Mok ⟩ ⟩ =
    ⟨ zero , ⟨ z≤n , ecAppOK Mok ⟩ ⟩
  elab-efficient {d = d} (meta-ecapp⋆ ⊢e M↝M′)
    with elab-efficient {d = d} M↝M′
  ... | ⟨ n , ⟨ n≤1 , Mok ⟩ ⟩ =
    ⟨ zero , ⟨ z≤n , ecAppOK (cast-pres-ok Mok n≤1) ⟩ ⟩
  elab-efficient {d = d} (meta-subintro ⊢e₁ ⊢e₂ M↝M′)
    with elab-efficient {d = true} M↝M′
  ... | ⟨ n , ⟨ n≤1 , Mok ⟩ ⟩ =
    ⟨ zero , ⟨ z≤n , subIntroOK Mok ⟩ ⟩
  elab-efficient {d = d} (meta-subelim pf M↝M′)
    with elab-efficient {d = d} M↝M′
  ... | ⟨ n , ⟨ n≤1 , Mok ⟩ ⟩ =
    ⟨ zero , ⟨ z≤n , subElimOK Mok ⟩ ⟩
  elab-efficient {d = d} (meta-subelim⋆ M↝M′)
    with elab-efficient {d = d} M↝M′
  ... | ⟨ n , ⟨ n≤1 , Mok ⟩ ⟩ =
    ⟨ zero , ⟨ z≤n , subElimDynOK Mok ⟩ ⟩
  elab-efficient {d = d} (meta-quote ⊢e M↝M′) =
    ⟨ zero , ⟨ z≤n , quoteOK (elab-efficientᵒ⇒ M↝M′) ⟩ ⟩
  elab-efficient {d = d} (meta-ref M↝M′)
    with elab-efficient {d = d} M↝M′
  ... | ⟨ n , ⟨ n≤1 , Mok ⟩ ⟩ =
    ⟨ zero , ⟨ z≤n , refOK Mok ⟩ ⟩
  elab-efficient {d = d} (meta-assign L↝L′ M↝M′ B≲A)
    with elab-efficient {d = d} L↝L′ | elab-efficient {d = d} M↝M′
  ... | ⟨ n , ⟨ n≤1 , Lok ⟩ ⟩ | ⟨ m , ⟨ m≤1 , Mok ⟩ ⟩ =
    ⟨ zero , ⟨ z≤n , assignOK Lok (cast-pres-ok Mok m≤1) ⟩ ⟩
  elab-efficient {d = d} (meta-assign⋆ L↝L′ M↝M′)
    with elab-efficient {d = d} L↝L′ | elab-efficient {d = d} M↝M′
  ... | ⟨ n , ⟨ n≤1 , Lok ⟩ ⟩ | ⟨ m , ⟨ m≤1 , Mok ⟩ ⟩ =
    ⟨ zero , ⟨ z≤n , assignOK (cast-pres-ok Lok n≤1) (cast-pres-ok Mok m≤1) ⟩ ⟩
  elab-efficient {d = d} (meta-deref M↝M′)
    with elab-efficient {d = d} M↝M′
  ... | ⟨ n , ⟨ n≤1 , Mok ⟩ ⟩ =
    ⟨ zero , ⟨ z≤n , derefOK Mok ⟩ ⟩
  elab-efficient {d = d} (meta-deref⋆ M↝M′)
    with elab-efficient {d = d} M↝M′
  ... | ⟨ n , ⟨ n≤1 , Mok ⟩ ⟩ =
    ⟨ zero , ⟨ z≤n , derefOK (cast-pres-ok Mok n≤1) ⟩ ⟩
