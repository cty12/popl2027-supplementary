module LambdaAlphaRefStar.Theories.SurfaceFullyStatic where

open import LambdaAlphaRefStar.Theories.SurfaceSyntaxAndTypeSystem


-- | Fully-static gradual ECs: the unknown EC `⋆` is excluded.
data FullyStaticEC⋆ : EC⋆ → Set where

  static-ec : ∀ {e}
      ------------------------
    → FullyStaticEC⋆ (ec e)


-- | Fully-static gradual code types: the unknown code type `⋆` is excluded.
data FullyStaticOType⋆ : OType⋆ → Set where

  static-baseᵒ : ∀ {ι}
      ---------------------------
    → FullyStaticOType⋆ (` ι)

  static-funᵒ : ∀ {O₁ O₂}
    → FullyStaticOType⋆ O₁
    → FullyStaticOType⋆ O₂
      ---------------------------------
    → FullyStaticOType⋆ (O₁ ⇒ O₂)


-- | Fully-static surface meta types: every occurrence of `⋆` is excluded,
-- | including those from gradual code types and gradual ECs.
data FullyStaticMType : MType → Set where

  static-baseᵐ : ∀ {ι}
      ------------------------
    → FullyStaticMType (` ι)

  static-funᵐ : ∀ {A B}
    → FullyStaticMType A
    → FullyStaticMType B
      ---------------------------
    → FullyStaticMType (A ⇒ B)

  static-refᵐ : ∀ {A}
    → FullyStaticMType A
      ---------------------------
    → FullyStaticMType (Ref A)

  static-codeᵐ : ∀ {O ê}
    → FullyStaticOType⋆ O
    → FullyStaticEC⋆ ê
      ------------------------------
    → FullyStaticMType (‶ O ″ ê)

  static-forallᵐ : ∀ {A}
    → FullyStaticMType A
      ---------------------------
    → FullyStaticMType (∀̇ A)

  static-subᵐ : ∀ {e₁ e₂ A}
    → FullyStaticMType A
      ------------------------------------
    → FullyStaticMType (e₁ <: e₂ => A)


data FullyStaticCodeSurfaceTerm : CodeSurfaceTerm → Set
data FullyStaticMetaSurfaceTerm : MetaSurfaceTerm → Set


data FullyStaticCodeSurfaceTerm where

  static-code-const : ∀ {ι} {k : base-rep ι}
      ---------------------------------------
    → FullyStaticCodeSurfaceTerm ($ k)

  static-code-var : ∀ {x}
      ---------------------------------------
    → FullyStaticCodeSurfaceTerm (` x)

  static-code-abs : ∀ {T N}
    → FullyStaticCodeSurfaceTerm N
      ------------------------------------------
    → FullyStaticCodeSurfaceTerm (ƛ T ˙ N)

  static-code-app : ∀ {L M ℓ}
    → FullyStaticCodeSurfaceTerm L
    → FullyStaticCodeSurfaceTerm M
      ---------------------------------------------
    → FullyStaticCodeSurfaceTerm (L · M ^ ℓ)

  static-splice : ∀ {M ℓ}
    → FullyStaticMetaSurfaceTerm M
      ----------------------------------------
    → FullyStaticCodeSurfaceTerm (~ M ^ ℓ)


data FullyStaticMetaSurfaceTerm where

  static-meta-const : ∀ {ι} {k : base-rep ι}
      ---------------------------------------
    → FullyStaticMetaSurfaceTerm ($ k)

  static-meta-var : ∀ {x}
      ---------------------------------------
    → FullyStaticMetaSurfaceTerm (` x)

  static-meta-abs : ∀ {A M}
    → FullyStaticMType A
    → FullyStaticMetaSurfaceTerm M
      ------------------------------------------
    → FullyStaticMetaSurfaceTerm (ƛ A ˙ M)

  static-meta-app : ∀ {L M ℓ}
    → FullyStaticMetaSurfaceTerm L
    → FullyStaticMetaSurfaceTerm M
      ---------------------------------------------
    → FullyStaticMetaSurfaceTerm (L · M ^ ℓ)

  static-ecabs : ∀ {M}
    → FullyStaticMetaSurfaceTerm M
      ------------------------------------
    → FullyStaticMetaSurfaceTerm (Λ M)

  static-ecapp : ∀ {M e ℓ}
    → FullyStaticMetaSurfaceTerm M
      ---------------------------------------------
    → FullyStaticMetaSurfaceTerm (M ·[ e ]^ ℓ)

  static-subintro : ∀ {e₁ e₂ M}
    → FullyStaticMetaSurfaceTerm M
      ---------------------------------------------
    → FullyStaticMetaSurfaceTerm (e₁ <: e₂ => M)

  static-subelim : ∀ {M ℓ}
    → FullyStaticMetaSurfaceTerm M
      ---------------------------------------
    → FullyStaticMetaSurfaceTerm (M ●^ ℓ)

  static-quote : ∀ {M e}
    → FullyStaticCodeSurfaceTerm M
      ---------------------------------------
    → FullyStaticMetaSurfaceTerm (‶ M ″ e)

  static-ref : ∀ {M}
    → FullyStaticMetaSurfaceTerm M
      ------------------------------------
    → FullyStaticMetaSurfaceTerm (ref M)

  static-assign : ∀ {L M ℓ}
    → FullyStaticMetaSurfaceTerm L
    → FullyStaticMetaSurfaceTerm M
      ---------------------------------------------
    → FullyStaticMetaSurfaceTerm (L := M ^ ℓ)

  static-deref : ∀ {M ℓ}
    → FullyStaticMetaSurfaceTerm M
      ---------------------------------------
    → FullyStaticMetaSurfaceTerm (! M ^ ℓ)
