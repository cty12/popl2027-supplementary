module LambdaAlphaRefStar.Theories.ConsistentSubtypingProperties where

open import Data.Product using (∃-syntax; _×_) renaming (_,_ to ⟨_,_⟩)
open import Function using (_⇔_; mk⇔)

open import Utils using (⟨_,_,_⟩; ⟨_,_,_,_⟩)
open import LambdaAlphaRefStar.Theories.EnvClassifiers
open import LambdaAlphaRefStar.Theories.CodeTypes
open import LambdaAlphaRefStar.Theories.MetaTypes
open import LambdaAlphaRefStar.Theories.ConsistentSubtyping

{-
  Consistent subtyping is the composition of consistency and subtyping, in
  either order:

    Θ ⊢ A ≲ B   iff   ∃ C. A ~ C  and  Θ ⊢ C <: B        (≲⇔~<:)
    Θ ⊢ A ≲ B   iff   ∃ C. Θ ⊢ A <: C  and  C ~ B        (≲⇔<:~)

  Consistency (_~ᵉ_, _~ᵒ_, _~_) relates ECs and types that are equal
  wherever neither is ⋆. Subtyping (_⊢_<:_) is neutral with ⋆: ⋆ is
  related only to itself.
-}

------------------------------------------------------------------------
-- Decomposition on code types

-- Code types have no subtyping of their own, so consistent subtyping on
-- them is just consistency.
≲ᵒ→~ᵒ : ∀ {O O′} → O ≲ᵒ O′ → O ~ᵒ O′
≲ᵒ→~ᵒ csubᵒ-⋆-left          = ~ᵒ-⋆-left
≲ᵒ→~ᵒ csubᵒ-⋆-right         = ~ᵒ-⋆-right
≲ᵒ→~ᵒ csubᵒ-base            = ~ᵒ-base
≲ᵒ→~ᵒ (csubᵒ-fun O₁′≲O₁ O₂≲O₂′) = ~ᵒ-fun (~ᵒ-sym (≲ᵒ→~ᵒ O₁′≲O₁)) (≲ᵒ→~ᵒ O₂≲O₂′)


------------------------------------------------------------------------
-- Decomposition on ECs

≲ᵉ→~<: : ∀ {Θ ê ê′}
  → Θ ⊢ᵉ ê ≲ ê′
    ---------------------------------------------
  → ∃[ ê″ ] (ê ~ᵉ ê″ × Θ ⊢ᵉ ê″ <:⋆ ê′)
≲ᵉ→~<: csubᵉ-⋆-left      = ⟨ _ , ~ᵉ-⋆-left , <:⋆-refl ⟩
≲ᵉ→~<: csubᵉ-⋆-right     = ⟨ ⋆ , ~ᵉ-⋆-right , <:-⋆ ⟩
≲ᵉ→~<: (csubᵉ-ec e<:e′)  = ⟨ _ , ~ᵉ-ec , <:-ec e<:e′ ⟩

≲ᵉ→<:~ : ∀ {Θ ê ê′}
  → Θ ⊢ᵉ ê ≲ ê′
    ---------------------------------------------
  → ∃[ ê″ ] (Θ ⊢ᵉ ê <:⋆ ê″ × ê″ ~ᵉ ê′)
≲ᵉ→<:~ csubᵉ-⋆-left      = ⟨ ⋆ , <:-⋆ , ~ᵉ-⋆-left ⟩
≲ᵉ→<:~ csubᵉ-⋆-right     = ⟨ _ , <:⋆-refl , ~ᵉ-⋆-right ⟩
≲ᵉ→<:~ (csubᵉ-ec e<:e′)  = ⟨ _ , <:-ec e<:e′ , ~ᵉ-ec ⟩

-- When consistent subtyping holds in both directions, one middle EC serves
-- both static directions.  This is what the invariant reference case needs.
≲ᵉ-both : ∀ {Θ ê ê′}
  → Θ ⊢ᵉ ê  ≲ ê′
  → Θ ⊢ᵉ ê′ ≲ ê
    -----------------------------------------------------------------
  → ∃[ ê″ ] (ê ~ᵉ ê″ × Θ ⊢ᵉ ê″ <:⋆ ê′ × Θ ⊢ᵉ ê′ <:⋆ ê″)
≲ᵉ-both csubᵉ-⋆-left  _                = ⟨ _ , ~ᵉ-⋆-left , <:⋆-refl , <:⋆-refl ⟩
≲ᵉ-both csubᵉ-⋆-right _                = ⟨ ⋆ , ~ᵉ-⋆-right , <:-⋆ , <:-⋆ ⟩
≲ᵉ-both (csubᵉ-ec e<:e′) (csubᵉ-ec e′<:e) = ⟨ _ , ~ᵉ-ec , <:-ec e<:e′ , <:-ec e′<:e ⟩


------------------------------------------------------------------------
-- Decomposition on meta types

-- Two-sided version, used for the invariant reference case: the middle type
-- is consistent with A and mutually a subtype of B.
≲-both : ∀ {Θ A B}
  → Θ ⊢ A ≲ B
  → Θ ⊢ B ≲ A
    -----------------------------------------------------
  → ∃[ C ] (A ~ C × Θ ⊢ C <: B × Θ ⊢ B <: C)
≲-both csub-⋆-left  _ = ⟨ _ , ~-⋆-left , sub-refl , sub-refl ⟩
≲-both csub-⋆-right _ = ⟨ ⋆ , ~-⋆-right , sub-⋆ , sub-⋆ ⟩
≲-both csub-base    _ = ⟨ _ , ~-base , sub-base , sub-base ⟩
≲-both (csub-fun A′≲A B≲B′) (csub-fun A≲A′ B′≲B)
  with ≲-both A≲A′ A′≲A | ≲-both B≲B′ B′≲B
... | ⟨ C₁ , A~C₁ , C₁<:A′ , A′<:C₁ ⟩ | ⟨ C₂ , B~C₂ , C₂<:B′ , B′<:C₂ ⟩ =
  ⟨ C₁ ⇒ C₂ , ~-fun A~C₁ B~C₂ , sub-fun A′<:C₁ C₂<:B′ , sub-fun C₁<:A′ B′<:C₂ ⟩
≲-both (csub-ref A≲B B≲A) _
  with ≲-both A≲B B≲A
... | ⟨ C , A~C , C<:B , B<:C ⟩ =
  ⟨ Ref C , ~-ref A~C , sub-ref C<:B B<:C , sub-ref B<:C C<:B ⟩
≲-both (csub-code O≲O′ ê≲ê′) (csub-code _ ê′≲ê)
  with ≲ᵉ-both ê≲ê′ ê′≲ê
... | ⟨ ê″ , ê~ê″ , ê″<:ê′ , ê′<:ê″ ⟩ =
  ⟨ _ , ~-code (≲ᵒ→~ᵒ O≲O′) ê~ê″ , sub-code ê″<:ê′ , sub-code ê′<:ê″ ⟩
≲-both (csub-univ A≲B) (csub-univ B≲A)
  with ≲-both A≲B B≲A
... | ⟨ C , A~C , C<:B , B<:C ⟩ =
  ⟨ ∀̇ C , ~-univ A~C , sub-univ C<:B , sub-univ B<:C ⟩
≲-both (csub-sub A≲B) (csub-sub B≲A)
  with ≲-both A≲B B≲A
... | ⟨ C , A~C , C<:B , B<:C ⟩ =
  ⟨ _ , ~-sub A~C , sub-sub C<:B , sub-sub B<:C ⟩

mutual

  -- (1) consistency first, then subtyping
  ≲→~<: : ∀ {Θ A B}
    → Θ ⊢ A ≲ B
      ---------------------------------------
    → ∃[ C ] (A ~ C × Θ ⊢ C <: B)
  ≲→~<: csub-⋆-left  = ⟨ _ , ~-⋆-left , sub-refl ⟩
  ≲→~<: csub-⋆-right = ⟨ ⋆ , ~-⋆-right , sub-⋆ ⟩
  ≲→~<: csub-base    = ⟨ _ , ~-base , sub-base ⟩
  ≲→~<: (csub-fun A′≲A B≲B′)
    with ≲→<:~ A′≲A | ≲→~<: B≲B′
  ... | ⟨ C₁ , A′<:C₁ , C₁~A ⟩ | ⟨ C₂ , B~C₂ , C₂<:B′ ⟩ =
    ⟨ C₁ ⇒ C₂ , ~-fun (~-sym C₁~A) B~C₂ , sub-fun A′<:C₁ C₂<:B′ ⟩
  ≲→~<: (csub-ref A≲B B≲A)
    with ≲-both A≲B B≲A
  ... | ⟨ C , A~C , C<:B , B<:C ⟩ =
    ⟨ Ref C , ~-ref A~C , sub-ref C<:B B<:C ⟩
  ≲→~<: (csub-code O≲O′ ê≲ê′)
    with ≲ᵉ→~<: ê≲ê′
  ... | ⟨ ê″ , ê~ê″ , ê″<:ê′ ⟩ =
    ⟨ _ , ~-code (≲ᵒ→~ᵒ O≲O′) ê~ê″ , sub-code ê″<:ê′ ⟩
  ≲→~<: (csub-univ A≲B)
    with ≲→~<: A≲B
  ... | ⟨ C , A~C , C<:B ⟩ = ⟨ ∀̇ C , ~-univ A~C , sub-univ C<:B ⟩
  ≲→~<: (csub-sub A≲B)
    with ≲→~<: A≲B
  ... | ⟨ C , A~C , C<:B ⟩ = ⟨ _ , ~-sub A~C , sub-sub C<:B ⟩

  -- (2) subtyping first, then consistency
  ≲→<:~ : ∀ {Θ A B}
    → Θ ⊢ A ≲ B
      ---------------------------------------
    → ∃[ C ] (Θ ⊢ A <: C × C ~ B)
  ≲→<:~ csub-⋆-left  = ⟨ ⋆ , sub-⋆ , ~-⋆-left ⟩
  ≲→<:~ csub-⋆-right = ⟨ _ , sub-refl , ~-⋆-right ⟩
  ≲→<:~ csub-base    = ⟨ _ , sub-base , ~-base ⟩
  ≲→<:~ (csub-fun A′≲A B≲B′)
    with ≲→~<: A′≲A | ≲→<:~ B≲B′
  ... | ⟨ C₁ , A′~C₁ , C₁<:A ⟩ | ⟨ C₂ , B<:C₂ , C₂~B′ ⟩ =
    ⟨ C₁ ⇒ C₂ , sub-fun C₁<:A B<:C₂ , ~-fun (~-sym A′~C₁) C₂~B′ ⟩
  ≲→<:~ (csub-ref A≲B B≲A)
    with ≲-both B≲A A≲B
  ... | ⟨ C , B~C , C<:A , A<:C ⟩ =
    ⟨ Ref C , sub-ref A<:C C<:A , ~-ref (~-sym B~C) ⟩
  ≲→<:~ (csub-code O≲O′ ê≲ê′)
    with ≲ᵉ→<:~ ê≲ê′
  ... | ⟨ ê″ , ê<:ê″ , ê″~ê′ ⟩ =
    ⟨ _ , sub-code ê<:ê″ , ~-code (≲ᵒ→~ᵒ O≲O′) ê″~ê′ ⟩
  ≲→<:~ (csub-univ A≲B)
    with ≲→<:~ A≲B
  ... | ⟨ C , A<:C , C~B ⟩ = ⟨ ∀̇ C , sub-univ A<:C , ~-univ C~B ⟩
  ≲→<:~ (csub-sub A≲B)
    with ≲→<:~ A≲B
  ... | ⟨ C , A<:C , C~B ⟩ = ⟨ _ , sub-sub A<:C , ~-sub C~B ⟩


------------------------------------------------------------------------
-- Completeness: each composition is contained in ≲

-- Object types have no subtyping of their own, so consistency is already
-- consistent subtyping.
~ᵒ→≲ᵒ : ∀ {O O′} → O ~ᵒ O′ → O ≲ᵒ O′
~ᵒ→≲ᵒ ~ᵒ-⋆-left          = csubᵒ-⋆-left
~ᵒ→≲ᵒ ~ᵒ-⋆-right         = csubᵒ-⋆-right
~ᵒ→≲ᵒ ~ᵒ-base            = csubᵒ-base
~ᵒ→≲ᵒ (~ᵒ-fun O₁~O₁′ O₂~O₂′) = csubᵒ-fun (~ᵒ→≲ᵒ (~ᵒ-sym O₁~O₁′)) (~ᵒ→≲ᵒ O₂~O₂′)

~<:→≲ᵉ : ∀ {Θ ê ê″ ê′}
  → ê ~ᵉ ê″
  → Θ ⊢ᵉ ê″ <:⋆ ê′
    ---------------------
  → Θ ⊢ᵉ ê ≲ ê′
~<:→≲ᵉ ~ᵉ-⋆-left  _             = csubᵉ-⋆-left
~<:→≲ᵉ ~ᵉ-⋆-right <:-⋆          = csubᵉ-⋆-right
~<:→≲ᵉ ~ᵉ-ec      (<:-ec e<:e′) = csubᵉ-ec e<:e′

<:~→≲ᵉ : ∀ {Θ ê ê″ ê′}
  → Θ ⊢ᵉ ê <:⋆ ê″
  → ê″ ~ᵉ ê′
    ---------------------
  → Θ ⊢ᵉ ê ≲ ê′
<:~→≲ᵉ <:-⋆          _          = csubᵉ-⋆-left
<:~→≲ᵉ (<:-ec e<:e′) ~ᵉ-⋆-right = csubᵉ-⋆-right
<:~→≲ᵉ (<:-ec e<:e′) ~ᵉ-ec      = csubᵉ-ec e<:e′

mutual

  -- (1) consistency then subtyping is contained in ≲
  ~<:→≲ : ∀ {Θ A C B}
    → A ~ C
    → Θ ⊢ C <: B
      ---------------
    → Θ ⊢ A ≲ B
  ~<:→≲ ~-⋆-left  _        = csub-⋆-left
  ~<:→≲ ~-⋆-right sub-⋆    = csub-⋆-right
  ~<:→≲ ~-base    sub-base = csub-base
  ~<:→≲ (~-fun A₁~C₁ A₂~C₂) (sub-fun B₁<:C₁ C₂<:B₂) =
    csub-fun (<:~→≲ B₁<:C₁ (~-sym A₁~C₁)) (~<:→≲ A₂~C₂ C₂<:B₂)
  ~<:→≲ (~-ref A~C) (sub-ref C<:B B<:C) =
    csub-ref (~<:→≲ A~C C<:B) (<:~→≲ B<:C (~-sym A~C))
  ~<:→≲ (~-code O~O′ ê~ê″) (sub-code ê″<:ê′) =
    csub-code (~ᵒ→≲ᵒ O~O′) (~<:→≲ᵉ ê~ê″ ê″<:ê′)
  ~<:→≲ (~-univ A~C) (sub-univ C<:B) = csub-univ (~<:→≲ A~C C<:B)
  ~<:→≲ (~-sub A~C)  (sub-sub C<:B)  = csub-sub  (~<:→≲ A~C C<:B)

  -- (2) subtyping then consistency is contained in ≲
  <:~→≲ : ∀ {Θ A C B}
    → Θ ⊢ A <: C
    → C ~ B
      ---------------
    → Θ ⊢ A ≲ B
  <:~→≲ sub-⋆    _         = csub-⋆-left
  <:~→≲ sub-base ~-⋆-right = csub-⋆-right
  <:~→≲ sub-base ~-base    = csub-base
  <:~→≲ (sub-fun C₁<:A₁ A₂<:C₂) ~-⋆-right = csub-⋆-right
  <:~→≲ (sub-fun C₁<:A₁ A₂<:C₂) (~-fun C₁~B₁ C₂~B₂) =
    csub-fun (~<:→≲ (~-sym C₁~B₁) C₁<:A₁) (<:~→≲ A₂<:C₂ C₂~B₂)
  <:~→≲ (sub-ref A<:C C<:A) ~-⋆-right = csub-⋆-right
  <:~→≲ (sub-ref A<:C C<:A) (~-ref C~B) =
    csub-ref (<:~→≲ A<:C C~B) (~<:→≲ (~-sym C~B) C<:A)
  <:~→≲ (sub-code ê<:ê″) ~-⋆-right = csub-⋆-right
  <:~→≲ (sub-code ê<:ê″) (~-code O~O′ ê″~ê′) =
    csub-code (~ᵒ→≲ᵒ O~O′) (<:~→≲ᵉ ê<:ê″ ê″~ê′)
  <:~→≲ (sub-univ A<:C) ~-⋆-right    = csub-⋆-right
  <:~→≲ (sub-univ A<:C) (~-univ C~B) = csub-univ (<:~→≲ A<:C C~B)
  <:~→≲ (sub-sub A<:C)  ~-⋆-right    = csub-⋆-right
  <:~→≲ (sub-sub A<:C)  (~-sub C~B)  = csub-sub  (<:~→≲ A<:C C~B)


------------------------------------------------------------------------
-- Consistent subtyping is the composition, in either order

≲⇔~<: : ∀ {Θ A B}
  → (Θ ⊢ A ≲ B) ⇔ (∃[ C ] (A ~ C × Θ ⊢ C <: B))
≲⇔~<: = mk⇔ ≲→~<: (λ { ⟨ C , A~C , C<:B ⟩ → ~<:→≲ A~C C<:B })

≲⇔<:~ : ∀ {Θ A B}
  → (Θ ⊢ A ≲ B) ⇔ (∃[ C ] (Θ ⊢ A <: C × C ~ B))
≲⇔<:~ = mk⇔ ≲→<:~ (λ { ⟨ C , A<:C , C~B ⟩ → <:~→≲ A<:C C~B })
