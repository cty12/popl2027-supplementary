module LambdaAlphaRefStar.Theories.SpaceEfficiency.Elaboration where

open import Data.Product renaming (_,_ to ⟨_,_⟩)

open import Utils
open import LambdaAlphaRefStar.Theories.SurfaceSyntaxAndTypeSystem public
open import LambdaAlphaRefStar.Theories.ConsistentSubtyping public
open import LambdaAlphaRefStar.Theories.SpaceEfficiency.CCAlphaRefStarSyntaxAndTypeSystem

import LambdaAlphaRefStar.Theories.SpaceEfficiency.ECHypercoercions as EHC
import LambdaAlphaRefStar.Theories.SpaceEfficiency.ObjectHypercoercions as OHC
import LambdaAlphaRefStar.Theories.SpaceEfficiency.MetaHypercoercions as MH

infix 3 _;_;_;_;_⊢_↝_⭆_
infix 3 _;_;_;_;_⊢_↝_⭅_
infix 3 _;_;_;_⊢_↝_⦂_


elab-ctx : SubCtx → MCtx → OCtx → Ctx
elab-ctx Θ Γᵐ Γᵒ = ⟨ Θ , Γᵒ , Γᵐ , ∅ ⟩


record OCast (O O′ : OType⋆) : Set where
  constructor ocast
  field
    coercionᵒ : OHC.OHypercoercion
    typedᵒ    : OHC.⊢ᵒ coercionᵒ ⦂ O ⇒ O′

open OCast public


record ECast (Δ : ECCtx) (Θ : SubCtx) (ê ê′ : EC⋆) : Set where
  constructor ecast
  field
    coercionᵉ : EHC.ECHypercoercion
    typedᵉ    : EHC._;_⊢ᵉ_⦂_⇒_ Δ Θ coercionᵉ ê ê′

open ECast public


record MCast (Δ : ECCtx) (Θ : SubCtx) (A B : MType) : Set where
  constructor mcast
  field
    coercionᵐ : MH.MHypercoercion
    typedᵐ    : MH._;_⊢ᵐ_⦂_⇒_ Δ Θ coercionᵐ A B

open MCast public


coerceᵒ : ∀ {O O′}
  → O ≲ᵒ O′
  → BlameLabel
  → OCast O O′
coerceᵒ {O = ⋆} {O′ = ⋆} _ ℓ =
  ocast (OHC.id ⋆ OHC.⨾ OHC.id⋆ ⨾ OHC.id ⋆)
        (OHC.⊢hc (OHC.⊢idʰ ⋆) OHC.⊢id⋆ᵐ (OHC.⊢idᵗ ⋆))
coerceᵒ {O = ⋆} {O′ = ` ι} csubᵒ-⋆-left ℓ =
  ocast ((` ι) OHC.？ ℓ OHC.⨾ OHC.idι ι ⨾ OHC.id (` ι))
        (OHC.⊢hc (OHC.⊢projʰ gbase ℓ) (OHC.⊢idιᵐ ι) (OHC.⊢idᵗ (` ι)))
coerceᵒ {O = ⋆} {O′ = O₁ ⇒ O₂} csubᵒ-⋆-left ℓ
    with coerceᵒ (csubᵒ-⋆-right {O = O₁}) ℓ
       | coerceᵒ (csubᵒ-⋆-left {O = O₂}) ℓ
... | ocast c₁ ⊢c₁ | ocast c₂ ⊢c₂ =
  ocast ((⋆ ⇒ ⋆) OHC.？ ℓ OHC.⨾ c₁ OHC.⇒ c₂ ⨾ OHC.id (O₁ ⇒ O₂))
        (OHC.⊢hc (OHC.⊢projʰ gfun ℓ) (OHC.⊢funᵐ ⊢c₁ ⊢c₂) (OHC.⊢idᵗ (O₁ ⇒ O₂)))
coerceᵒ {O = ` ι} {O′ = ⋆} csubᵒ-⋆-right ℓ =
  ocast (OHC.id (` ι) OHC.⨾ OHC.idι ι ⨾ (` ι) OHC.！)
        (OHC.⊢hc (OHC.⊢idʰ (` ι)) (OHC.⊢idιᵐ ι) (OHC.⊢injᵗ gbase))
coerceᵒ {O = O₁ ⇒ O₂} {O′ = ⋆} csubᵒ-⋆-right ℓ
    with coerceᵒ (csubᵒ-⋆-left {O = O₁}) ℓ
       | coerceᵒ (csubᵒ-⋆-right {O = O₂}) ℓ
... | ocast c₁ ⊢c₁ | ocast c₂ ⊢c₂ =
  ocast (OHC.id (O₁ ⇒ O₂) OHC.⨾ c₁ OHC.⇒ c₂ ⨾ (⋆ ⇒ ⋆) OHC.！)
        (OHC.⊢hc (OHC.⊢idʰ (O₁ ⇒ O₂)) (OHC.⊢funᵐ ⊢c₁ ⊢c₂) (OHC.⊢injᵗ gfun))
coerceᵒ {O = ` ι} {O′ = ` .ι} csubᵒ-base ℓ =
  ocast (OHC.id (` ι) OHC.⨾ OHC.idι ι ⨾ OHC.id (` ι))
        (OHC.⊢hc (OHC.⊢idʰ (` ι)) (OHC.⊢idιᵐ ι) (OHC.⊢idᵗ (` ι)))
coerceᵒ {O = O₁ ⇒ O₂} {O′ = O₁′ ⇒ O₂′} (csubᵒ-fun O₁′≲O₁ O₂≲O₂′) ℓ
    with coerceᵒ O₁′≲O₁ ℓ | coerceᵒ O₂≲O₂′ ℓ
... | ocast c₁ ⊢c₁ | ocast c₂ ⊢c₂ =
  ocast (OHC.id (O₁ ⇒ O₂) OHC.⨾ c₁ OHC.⇒ c₂ ⨾ OHC.id (O₁′ ⇒ O₂′))
        (OHC.⊢hc (OHC.⊢idʰ (O₁ ⇒ O₂)) (OHC.⊢funᵐ ⊢c₁ ⊢c₂) (OHC.⊢idᵗ (O₁′ ⇒ O₂′)))


coerce-ec : ∀ {Δ Θ ê ê′}
  → Θ ⊢ᵉ ê ≲ ê′
  → BlameLabel
  → ECast Δ Θ ê ê′
coerce-ec {ê = ⋆} {ê′ = ⋆} _ ℓ =
  ecast (EHC.id ⋆ EHC.⨾ ⋆ EHC.↑ ⋆ ⨾ EHC.id ⋆)
        (EHC.⊢hc (EHC.⊢idʰ ⋆) (EHC.⊢subᵐ <:-⋆) (EHC.⊢idᵗ ⋆))
coerce-ec {ê = ⋆} {ê′ = ec e} csubᵉ-⋆-left ℓ =
  ecast (e EHC.？ ℓ EHC.⨾ ec e EHC.↑ ec e ⨾ EHC.id (ec e))
        (EHC.⊢hc (EHC.⊢projʰ e ℓ) (EHC.⊢subᵐ (<:-ec <:-refl)) (EHC.⊢idᵗ (ec e)))
coerce-ec {ê = ec e} {ê′ = ⋆} csubᵉ-⋆-right ℓ =
  ecast (EHC.id (ec e) EHC.⨾ ec e EHC.↑ ec e ⨾ e EHC.！)
        (EHC.⊢hc (EHC.⊢idʰ (ec e)) (EHC.⊢subᵐ (<:-ec <:-refl)) (EHC.⊢injᵗ e))
coerce-ec {ê = ec e} {ê′ = ec e′} (csubᵉ-ec e<:e′) ℓ =
  ecast (EHC.id (ec e) EHC.⨾ ec e EHC.↑ ec e′ ⨾ EHC.id (ec e′))
        (EHC.⊢hc (EHC.⊢idʰ (ec e)) (EHC.⊢subᵐ (<:-ec e<:e′)) (EHC.⊢idᵗ (ec e′)))


mutual

  coerce-from⋆ : ∀ {Δ}
    → (Θ : SubCtx)
    → (B : MType)
    → BlameLabel
    → MCast Δ Θ ⋆ B
  coerce-from⋆ Θ ⋆ ℓ =
    mcast (MH.id ⋆ MH.⨾ MH.id⋆ ⨾ MH.id ⋆)
          (MH.⊢hc (MH.⊢idʰ ⋆) MH.⊢id⋆ᵐ (MH.⊢idᵗ ⋆))
  coerce-from⋆ Θ (` ι) ℓ =
    mcast ((` ι) MH.？ ℓ MH.⨾ MH.idι ι ⨾ MH.id (` ι))
          (MH.⊢hc (MH.⊢projʰ gbase ℓ) (MH.⊢idιᵐ ι) (MH.⊢idᵗ (` ι)))
  coerce-from⋆ Θ (A ⇒ B) ℓ
      with coerce-to⋆ Θ A ℓ | coerce-from⋆ Θ B ℓ
  ... | mcast c₁ ⊢c₁ | mcast c₂ ⊢c₂ =
    mcast ((⋆ ⇒ ⋆) MH.？ ℓ MH.⨾ c₁ MH.⇒ c₂ ⨾ MH.id (A ⇒ B))
          (MH.⊢hc (MH.⊢projʰ gfun ℓ) (MH.⊢funᵐ ⊢c₁ ⊢c₂) (MH.⊢idᵗ (A ⇒ B)))
  coerce-from⋆ Θ (Ref A) ℓ
      with coerce-to⋆ Θ A ℓ | coerce-from⋆ Θ A ℓ
  ... | mcast c₁ ⊢c₁ | mcast c₂ ⊢c₂ =
    mcast ((Ref ⋆) MH.？ ℓ MH.⨾ MH.ref c₁ c₂ ⨾ MH.id (Ref A))
          (MH.⊢hc (MH.⊢projʰ gref ℓ) (MH.⊢refᵐ ⊢c₁ ⊢c₂) (MH.⊢idᵗ (Ref A)))
  coerce-from⋆ Θ (‶ O ″ ê) ℓ
      with coerceᵒ (csubᵒ-⋆-left {O = O}) ℓ
         | coerce-ec (csubᵉ-⋆-left {ê = ê}) ℓ
  ... | ocast cᵒ ⊢cᵒ | ecast cᵉ ⊢cᵉ =
    mcast ((‶ ⋆ ″ ⋆) MH.？ ℓ MH.⨾ MH.‶ cᵒ ″ cᵉ ⨾ MH.id (‶ O ″ ê))
          (MH.⊢hc (MH.⊢projʰ gcode ℓ) (MH.⊢codeᵐ ⊢cᵒ ⊢cᵉ) (MH.⊢idᵗ (‶ O ″ ê)))
  coerce-from⋆ Θ (∀̇ A) ℓ
      with coerce-from⋆ (⇑ᵉ-subctx Θ) A ℓ
  ... | mcast c ⊢c =
    mcast ((∀̇ ⋆) MH.？ ℓ MH.⨾ MH.∀̇ c ⨾ MH.id (∀̇ A))
          (MH.⊢hc (MH.⊢projʰ gforall ℓ) (MH.⊢forallᵐ ⊢c) (MH.⊢idᵗ (∀̇ A)))
  coerce-from⋆ Θ (e₁ <: e₂ => A) ℓ
      with coerce-from⋆ (Θ , e₁ <: e₂) A ℓ
  ... | mcast c ⊢c =
    mcast ((e₁ <: e₂ => ⋆) MH.？ ℓ MH.⨾ e₁ MH.<: e₂ => c ⨾ MH.id (e₁ <: e₂ => A))
          (MH.⊢hc (MH.⊢projʰ gsub ℓ) (MH.⊢subᵐ e₁ e₂ ⊢c) (MH.⊢idᵗ (e₁ <: e₂ => A)))

  coerce-to⋆ : ∀ {Δ}
    → (Θ : SubCtx)
    → (A : MType)
    → BlameLabel
    → MCast Δ Θ A ⋆
  coerce-to⋆ Θ ⋆ ℓ =
    mcast (MH.id ⋆ MH.⨾ MH.id⋆ ⨾ MH.id ⋆)
          (MH.⊢hc (MH.⊢idʰ ⋆) MH.⊢id⋆ᵐ (MH.⊢idᵗ ⋆))
  coerce-to⋆ Θ (` ι) ℓ =
    mcast (MH.id (` ι) MH.⨾ MH.idι ι ⨾ (` ι) MH.！)
          (MH.⊢hc (MH.⊢idʰ (` ι)) (MH.⊢idιᵐ ι) (MH.⊢injᵗ gbase))
  coerce-to⋆ Θ (A ⇒ B) ℓ
      with coerce-from⋆ Θ A ℓ | coerce-to⋆ Θ B ℓ
  ... | mcast c₁ ⊢c₁ | mcast c₂ ⊢c₂ =
    mcast (MH.id (A ⇒ B) MH.⨾ c₁ MH.⇒ c₂ ⨾ (⋆ ⇒ ⋆) MH.！)
          (MH.⊢hc (MH.⊢idʰ (A ⇒ B)) (MH.⊢funᵐ ⊢c₁ ⊢c₂) (MH.⊢injᵗ gfun))
  coerce-to⋆ Θ (Ref A) ℓ
      with coerce-from⋆ Θ A ℓ | coerce-to⋆ Θ A ℓ
  ... | mcast c₁ ⊢c₁ | mcast c₂ ⊢c₂ =
    mcast (MH.id (Ref A) MH.⨾ MH.ref c₁ c₂ ⨾ (Ref ⋆) MH.！)
          (MH.⊢hc (MH.⊢idʰ (Ref A)) (MH.⊢refᵐ ⊢c₁ ⊢c₂) (MH.⊢injᵗ gref))
  coerce-to⋆ Θ (‶ O ″ ê) ℓ
      with coerceᵒ (csubᵒ-⋆-right {O = O}) ℓ
         | coerce-ec (csubᵉ-⋆-right {ê = ê}) ℓ
  ... | ocast cᵒ ⊢cᵒ | ecast cᵉ ⊢cᵉ =
    mcast (MH.id (‶ O ″ ê) MH.⨾ MH.‶ cᵒ ″ cᵉ ⨾ (‶ ⋆ ″ ⋆) MH.！)
          (MH.⊢hc (MH.⊢idʰ (‶ O ″ ê)) (MH.⊢codeᵐ ⊢cᵒ ⊢cᵉ) (MH.⊢injᵗ gcode))
  coerce-to⋆ Θ (∀̇ A) ℓ
      with coerce-to⋆ (⇑ᵉ-subctx Θ) A ℓ
  ... | mcast c ⊢c =
    mcast (MH.id (∀̇ A) MH.⨾ MH.∀̇ c ⨾ (∀̇ ⋆) MH.！)
          (MH.⊢hc (MH.⊢idʰ (∀̇ A)) (MH.⊢forallᵐ ⊢c) (MH.⊢injᵗ gforall))
  coerce-to⋆ Θ (e₁ <: e₂ => A) ℓ
      with coerce-to⋆ (Θ , e₁ <: e₂) A ℓ
  ... | mcast c ⊢c =
    mcast (MH.id (e₁ <: e₂ => A) MH.⨾ e₁ MH.<: e₂ => c ⨾ (e₁ <: e₂ => ⋆) MH.！)
          (MH.⊢hc (MH.⊢idʰ (e₁ <: e₂ => A)) (MH.⊢subᵐ e₁ e₂ ⊢c) (MH.⊢injᵗ gsub))

  coerce : ∀ {Δ Θ A B}
    → Θ ⊢ A ≲ B
    → BlameLabel
    → MCast Δ Θ A B
  coerce {Θ = Θ} {A = .⋆} {B = B} csub-⋆-left ℓ = coerce-from⋆ Θ B ℓ
  coerce {Θ = Θ} {A = A} {B = .⋆} csub-⋆-right ℓ = coerce-to⋆ Θ A ℓ
  coerce {A = ` ι} {B = ` .ι} csub-base ℓ =
    mcast (MH.id (` ι) MH.⨾ MH.idι ι ⨾ MH.id (` ι))
          (MH.⊢hc (MH.⊢idʰ (` ι)) (MH.⊢idιᵐ ι) (MH.⊢idᵗ (` ι)))
  coerce {Θ = Θ} {A = A ⇒ B} {B = A′ ⇒ B′} (csub-fun A′≲A B≲B′) ℓ
      with coerce A′≲A ℓ | coerce B≲B′ ℓ
  ... | mcast c₁ ⊢c₁ | mcast c₂ ⊢c₂ =
    mcast (MH.id (A ⇒ B) MH.⨾ c₁ MH.⇒ c₂ ⨾ MH.id (A′ ⇒ B′))
          (MH.⊢hc (MH.⊢idʰ (A ⇒ B)) (MH.⊢funᵐ ⊢c₁ ⊢c₂) (MH.⊢idᵗ (A′ ⇒ B′)))
  coerce {A = Ref A} {B = Ref B} (csub-ref A≲B B≲A) ℓ
      with coerce B≲A ℓ | coerce A≲B ℓ
  ... | mcast c₁ ⊢c₁ | mcast c₂ ⊢c₂ =
    mcast (MH.id (Ref A) MH.⨾ MH.ref c₁ c₂ ⨾ MH.id (Ref B))
          (MH.⊢hc (MH.⊢idʰ (Ref A)) (MH.⊢refᵐ ⊢c₁ ⊢c₂) (MH.⊢idᵗ (Ref B)))
  coerce {A = ‶ O ″ ê} {B = ‶ O′ ″ ê′} (csub-code O≲O′ ê≲ê′) ℓ
      with coerceᵒ O≲O′ ℓ | coerce-ec ê≲ê′ ℓ
  ... | ocast cᵒ ⊢cᵒ | ecast cᵉ ⊢cᵉ =
    mcast (MH.id (‶ O ″ ê) MH.⨾ MH.‶ cᵒ ″ cᵉ ⨾ MH.id (‶ O′ ″ ê′))
          (MH.⊢hc (MH.⊢idʰ (‶ O ″ ê)) (MH.⊢codeᵐ ⊢cᵒ ⊢cᵉ) (MH.⊢idᵗ (‶ O′ ″ ê′)))
  coerce {Θ = Θ} {A = ∀̇ A} {B = ∀̇ B} (csub-univ A≲B) ℓ
      with coerce A≲B ℓ
  ... | mcast c ⊢c =
    mcast (MH.id (∀̇ A) MH.⨾ MH.∀̇ c ⨾ MH.id (∀̇ B))
          (MH.⊢hc (MH.⊢idʰ (∀̇ A)) (MH.⊢forallᵐ ⊢c) (MH.⊢idᵗ (∀̇ B)))
  coerce {A = e₁ <: e₂ => A} {B = .(e₁ <: e₂ => _)} (csub-sub A≲B) ℓ
      with coerce A≲B ℓ
  ... | mcast c ⊢c =
    mcast (MH.id (e₁ <: e₂ => A) MH.⨾ e₁ MH.<: e₂ => c ⨾ MH.id _)
          (MH.⊢hc (MH.⊢idʰ (e₁ <: e₂ => A)) (MH.⊢subᵐ e₁ e₂ ⊢c) (MH.⊢idᵗ _))


data _;_;_;_;_⊢_↝_⭆_
  (Δ : ECCtx) (Θ : SubCtx) (Γᵐ : MCtx) (Γᵒ : OCtx) (e : EC)
  : CodeSurfaceTerm → CodeTerm → OType → Set

data _;_;_;_;_⊢_↝_⭅_
  (Δ : ECCtx) (Θ : SubCtx) (Γᵐ : MCtx) (Γᵒ : OCtx) (e : EC)
  : CodeSurfaceTerm → CodeTerm → OType → Set

data _;_;_;_⊢_↝_⦂_
  (Δ : ECCtx) (Θ : SubCtx) (Γᵐ : MCtx) (Γᵒ : OCtx)
  : MetaSurfaceTerm → MetaTerm → MType → Set


data _;_;_;_;_⊢_↝_⭆_ Δ Θ Γᵐ Γᵒ e where

  code-const : ∀ {ι} {k : base-rep ι}
    → Δ ; Θ ; Γᵐ ; Γᵒ ; e ⊢ $ k ↝ $ k ⭆ ` ι

  code-var : ∀ {x T α}
    → Γᵒ ∋ᵒ x ⦂ ⟨ T , α ⟩
    → Θ ⊢ᵉ ` α <: e
      -----------------------------------
    → Δ ; Θ ; Γᵐ ; Γᵒ ; e ⊢ ` x ↝ ` x ⭆ T

  code-abs : ∀ {T₁ T₂ N N′}
    → Δ ,α ; (⇑ᵉ-subctx Θ , ⇑ᵉ-ec e <: ` zero) ; ⇑ᵉ-mctx Γᵐ ; (⇑ᵉ-octx Γᵒ , T₁ ＠ zero) ; ` zero
        ⊢ N ↝ N′ ⭆ T₂
      -----------------------------------------------------
    → Δ ; Θ ; Γᵐ ; Γᵒ ; e ⊢ ƛ T₁ ˙ N ↝ ƛ T₁ ˙ N′ ⭆ T₁ ⇒ T₂

  code-app : ∀ {T₁ T₂ L M L′ M′ ℓ}
    → Δ ; Θ ; Γᵐ ; Γᵒ ; e ⊢ L ↝ L′ ⭆ T₁ ⇒ T₂
    → Δ ; Θ ; Γᵐ ; Γᵒ ; e ⊢ M ↝ M′ ⭅ T₁
      --------------------------------------------------------
    → Δ ; Θ ; Γᵐ ; Γᵒ ; e ⊢ L · M ^ ℓ ↝ L′ · M′ ⭆ T₂


data _;_;_;_;_⊢_↝_⭅_ Δ Θ Γᵐ Γᵒ e where

  splice : ∀ {T A M M′ ℓ}
    → Δ ; Θ ; Γᵐ ; Γᵒ ⊢ M ↝ M′ ⦂ A
    → (A≲T : Θ ⊢ A ≲ ‶ ⌈ T ⌉ᵒ ″ ec e)
      ----------------------------------------------------------
    → Δ ; Θ ; Γᵐ ; Γᵒ ; e ⊢ ~ M ^ ℓ ↝ ~ (M′ ⟨ coercionᵐ (coerce {Δ = Δ} {Θ = Θ} A≲T ℓ) ⟩) ⭅ T

  check : ∀ {T M M′}
    → Δ ; Θ ; Γᵐ ; Γᵒ ; e ⊢ M ↝ M′ ⭆ T
      -----------------------------------
    → Δ ; Θ ; Γᵐ ; Γᵒ ; e ⊢ M ↝ M′ ⭅ T


data _;_;_;_⊢_↝_⦂_ Δ Θ Γᵐ Γᵒ where

  meta-const : ∀ {ι} {k : base-rep ι}
    → Δ ; Θ ; Γᵐ ; Γᵒ ⊢ $ k ↝ $ k ⦂ ` ι

  meta-var : ∀ {x A}
    → Γᵐ ∋ x ⦂ A
      -----------------------------
    → Δ ; Θ ; Γᵐ ; Γᵒ ⊢ ` x ↝ ` x ⦂ A

  meta-abs : ∀ {A B M M′}
    → Δ ⊢ᵐᵗ A
    → Δ ; Θ ; (Γᵐ ⸴ A) ; Γᵒ ⊢ M ↝ M′ ⦂ B
      ------------------------------------------------
    → Δ ; Θ ; Γᵐ ; Γᵒ ⊢ ƛ A ˙ M ↝ ƛ M′ ⦂ A ⇒ B

  meta-app : ∀ {A₁ A₂ B L M L′ M′ ℓ}
    → Δ ; Θ ; Γᵐ ; Γᵒ ⊢ L ↝ L′ ⦂ A₁ ⇒ A₂
    → Δ ; Θ ; Γᵐ ; Γᵒ ⊢ M ↝ M′ ⦂ B
    → (B≲A₁ : Θ ⊢ B ≲ A₁)
      ---------------------------------------------------------------------------------
    → Δ ; Θ ; Γᵐ ; Γᵒ ⊢ L · M ^ ℓ ↝ L′ · (M′ ⟨ coercionᵐ (coerce {Δ = Δ} {Θ = Θ} B≲A₁ ℓ) ⟩) ⦂ A₂

  meta-app⋆ : ∀ {A L M L′ M′ ℓ}
    → Δ ; Θ ; Γᵐ ; Γᵒ ⊢ L ↝ L′ ⦂ ⋆
    → Δ ; Θ ; Γᵐ ; Γᵒ ⊢ M ↝ M′ ⦂ A
      ------------------------------------------------------------------------------------------------------
    → Δ ; Θ ; Γᵐ ; Γᵒ ⊢ L · M ^ ℓ ↝
        (L′ ⟨ coercionᵐ (coerce {Δ = Δ} {Θ = Θ} (csub-⋆-left {A = ⋆ ⇒ ⋆}) ℓ) ⟩) ·
        (M′ ⟨ coercionᵐ (coerce {Δ = Δ} {Θ = Θ} (csub-⋆-right {A = A}) ℓ) ⟩)
        ⦂ ⋆

  meta-ecabs : ∀ {A M M′}
    → Δ ,α ; ⇑ᵉ-subctx Θ ; ⇑ᵉ-mctx Γᵐ ; ⇑ᵉ-octx Γᵒ ⊢ M ↝ M′ ⦂ A
      -----------------------------------------------------------
    → Δ ; Θ ; Γᵐ ; Γᵒ ⊢ Λ M ↝ Λ M′ ⦂ ∀̇ A

  meta-ecapp : ∀ {A M M′ e ℓ}
    → Δ ⊢ᵉ e
    → Δ ; Θ ; Γᵐ ; Γᵒ ⊢ M ↝ M′ ⦂ ∀̇ A
      ------------------------------------------------------------
    → Δ ; Θ ; Γᵐ ; Γᵒ ⊢ M ·[ e ]^ ℓ ↝ M′ ·[ e ] ⦂ A [ e ]ᵉ

  meta-ecapp⋆ : ∀ {M M′ e ℓ}
    → Δ ⊢ᵉ e
    → Δ ; Θ ; Γᵐ ; Γᵒ ⊢ M ↝ M′ ⦂ ⋆
      ---------------------------------------------------------------------------------------------------------
    → Δ ; Θ ; Γᵐ ; Γᵒ ⊢ M ·[ e ]^ ℓ ↝
        (M′ ⟨ coercionᵐ (coerce {Δ = Δ} {Θ = Θ} (csub-⋆-left {A = ∀̇ ⋆}) ℓ) ⟩) ·[ e ]
        ⦂ ⋆

  meta-subintro : ∀ {A e₁ e₂ M M′}
    → Δ ⊢ᵉ e₁
    → Δ ⊢ᵉ e₂
    → Δ ; (Θ , e₁ <: e₂) ; Γᵐ ; Γᵒ ⊢ M ↝ M′ ⦂ A
      -----------------------------------------------------------------
    → Δ ; Θ ; Γᵐ ; Γᵒ ⊢ e₁ <: e₂ => M ↝ e₁ <: e₂ => M′ ⦂ e₁ <: e₂ => A

  meta-subelim : ∀ {A e₁ e₂ M M′ ℓ}
    → Θ ⊢ᵉ e₁ <: e₂
    → Δ ; Θ ; Γᵐ ; Γᵒ ⊢ M ↝ M′ ⦂ e₁ <: e₂ => A
      --------------------------------------------------------
    → Δ ; Θ ; Γᵐ ; Γᵒ ⊢ M ●^ ℓ ↝ M′ ● ⦂ A

  meta-subelim⋆ : ∀ {M M′ ℓ}
    → Δ ; Θ ; Γᵐ ; Γᵒ ⊢ M ↝ M′ ⦂ ⋆
      -------------------------------------------
    → Δ ; Θ ; Γᵐ ; Γᵒ ⊢ M ●^ ℓ ↝ M′ ★ ℓ ⦂ ⋆

  meta-quote : ∀ {T e M M′}
    → Δ ⊢ᵉ e
    → Δ ; Θ ; Γᵐ ; Γᵒ ; e ⊢ M ↝ M′ ⭆ T
      -------------------------------------------------------------------
    → Δ ; Θ ; Γᵐ ; Γᵒ ⊢ ‶ M ″ e ↝ ‶ M′ ″ e ⦂ ‶ ⌈ T ⌉ᵒ ″ ec e

  meta-ref : ∀ {A M M′}
    → Δ ; Θ ; Γᵐ ; Γᵒ ⊢ M ↝ M′ ⦂ A
      -----------------------------------------
    → Δ ; Θ ; Γᵐ ; Γᵒ ⊢ ref M ↝ ref M′ ⦂ Ref A

  meta-assign : ∀ {A B L M L′ M′ ℓ}
    → Δ ; Θ ; Γᵐ ; Γᵒ ⊢ L ↝ L′ ⦂ Ref A
    → Δ ; Θ ; Γᵐ ; Γᵒ ⊢ M ↝ M′ ⦂ B
    → (B≲A : Θ ⊢ B ≲ A)
      ---------------------------------------------------------------------------------
    → Δ ; Θ ; Γᵐ ; Γᵒ ⊢ L := M ^ ℓ ↝ L′ := (M′ ⟨ coercionᵐ (coerce {Δ = Δ} {Θ = Θ} B≲A ℓ) ⟩) ⦂ ` Unit

  meta-assign⋆ : ∀ {A L M L′ M′ ℓ}
    → Δ ; Θ ; Γᵐ ; Γᵒ ⊢ L ↝ L′ ⦂ ⋆
    → Δ ; Θ ; Γᵐ ; Γᵒ ⊢ M ↝ M′ ⦂ A
      ------------------------------------------------------------------------------------------------------
    → Δ ; Θ ; Γᵐ ; Γᵒ ⊢ L := M ^ ℓ ↝
        (L′ ⟨ coercionᵐ (coerce {Δ = Δ} {Θ = Θ} (csub-⋆-left {A = Ref ⋆}) ℓ) ⟩) :=
        (M′ ⟨ coercionᵐ (coerce {Δ = Δ} {Θ = Θ} (csub-⋆-right {A = A}) ℓ) ⟩)
        ⦂ ` Unit

  meta-deref : ∀ {A M M′ ℓ}
    → Δ ; Θ ; Γᵐ ; Γᵒ ⊢ M ↝ M′ ⦂ Ref A
      -------------------------------------------
    → Δ ; Θ ; Γᵐ ; Γᵒ ⊢ ! M ^ ℓ ↝ ! M′ ⦂ A

  meta-deref⋆ : ∀ {M M′ ℓ}
    → Δ ; Θ ; Γᵐ ; Γᵒ ⊢ M ↝ M′ ⦂ ⋆
      ---------------------------------------------------------------------------------
    → Δ ; Θ ; Γᵐ ; Γᵒ ⊢ ! M ^ ℓ ↝
        ! (M′ ⟨ coercionᵐ (coerce {Δ = Δ} {Θ = Θ} (csub-⋆-left {A = Ref ⋆}) ℓ) ⟩)
        ⦂ ⋆
