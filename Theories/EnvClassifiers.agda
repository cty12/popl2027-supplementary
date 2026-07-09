module Theories.EnvClassifiers where

open import Data.List using (List; []; _∷_; _∷ʳ_; drop; length; map)
open import Data.List.Relation.Unary.All using (All) renaming ([] to []ᴬ; _∷_ to _∷ᴬ_)
open import Data.List.Relation.Unary.All.Properties using (∷ʳ⁺)
open import Data.Nat using (ℕ; zero; suc; _≤_; _<_; z≤n; s≤s) public
open import Data.Nat.Properties using (_≟_; ≤-refl; <-irrefl; m≤n⇒m≤1+n; ≤-irrelevant) public
open import Data.Product using (Σ-syntax; ∃-syntax; _×_) renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; subst; sym)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Nullary.Negation using (contradiction)
open import Function using (case_of_)

open import Theories.Utils using (_∋_; _∋_⦂_; _⊆_; Z; S_; length-∷ʳ; length-map; member-snoc-inv; ⟨_,_,_⟩)


-- | Environment classifier contexts.
--
-- The first component is the number of lexical binders at the front of
-- the shared context.  Runtime allocation appends to the back without
-- changing this cutoff.  The size is the total number of lexical and
-- runtime/global EC binders currently in scope.
record ECCtx : Set where
  constructor ecctx
  field
    cutoff : ℕ
    size : ℕ
    cutoff≤size : cutoff ≤ size

{-
        cutoff
          |
          v
α, β, ..., γ,...        = Δ
|      |   |      |
+------+   +------+
EC vars    EC symbols

-}

open ECCtx public

infixl 5 _,α
infixl 5 _,ᵍα

∅ᵉ : ECCtx
∅ᵉ = ecctx zero zero z≤n

_,α : ECCtx → ECCtx
Δ ,α = ecctx (suc (Δ .cutoff)) (suc (Δ .size)) (s≤s (Δ .cutoff≤size))

_,ᵍα : ECCtx → ECCtx
Δ ,ᵍα = ecctx (Δ .cutoff) (suc (Δ .size)) (m≤n⇒m≤1+n (Δ .cutoff≤size))

freshᵉ : ECCtx → ℕ
freshᵉ Δ = Δ .size

wf-var-≢fresh : ∀ {Δ α}
  → α < Δ .size
    ------------------
  → α ≢ freshᵉ Δ
wf-var-≢fresh {Δ} α<Δ α≡fresh = <-irrefl refl (subst (_< Δ .size) α≡fresh α<Δ)


-- | EC variables represented as de Bruijn indices
ECVar = ℕ

-- | A globally allocated EC variable lives in the suffix after the lexical
-- cutoff.  The lookup proof records that the name is actually allocated.
record GlobalEC (Δ : ECCtx) (α : ECVar) : Set where
  constructor globalEC
  field
    <size : α < Δ .size
    cutoff≤ : Δ .cutoff ≤ α

open GlobalEC public

globalEC-suc : ∀ {Δ α}
  → GlobalEC Δ α
    ------------------------------
  → GlobalEC (Δ ,α) (suc α)
globalEC-suc (globalEC α<Δ cutoff≤α) = globalEC (s≤s α<Δ) (s≤s cutoff≤α)


-- | Environment classifiers
data EC : Set where
  ε  : EC
  `_ : ECVar → EC

`-injective : ∀ {α β : ECVar}
  → _≡_ {A = EC} (` α) (` β)
    ------------------------------
  → α ≡ β
`-injective refl = refl

-- | Gradual EC
data EC⋆ : Set where
  ⋆  : EC⋆
  ec : EC → EC⋆

_≡?ᵉ_ : ∀ (e₁ e₂ : EC) → Dec (e₁ ≡ e₂)
ε ≡?ᵉ ε = yes refl
ε ≡?ᵉ (` _) = no λ ()
(` _) ≡?ᵉ ε = no λ ()
(` α) ≡?ᵉ (` β) with α ≟ β
... | yes refl = yes refl
... | no α≢β = no λ { refl → α≢β refl }

_≡?ᵉ⋆_ : ∀ (ê₁ ê₂ : EC⋆) → Dec (ê₁ ≡ ê₂)
⋆ ≡?ᵉ⋆ ⋆ = yes refl
⋆ ≡?ᵉ⋆ ec _ = no λ ()
ec _ ≡?ᵉ⋆ ⋆ = no λ ()
ec e₁ ≡?ᵉ⋆ ec e₂ with e₁ ≡?ᵉ e₂
... | yes refl = yes refl
... | no e₁≢e₂ = no λ { refl → e₁≢e₂ refl }


-- | EC renaming and substitution
infixr 6 _•ᵉ_
infixr 6 _•ᵉₛ_

RenameEC = ECVar → ECVar

idᵉ : RenameEC
idᵉ α = α

extᵉ : RenameEC → RenameEC
extᵉ ρ zero = zero
extᵉ ρ (suc α) = suc (ρ α)

_•ᵉ_ : ECVar → RenameEC → RenameEC
(β •ᵉ _) zero = β
(_ •ᵉ ρ) (suc α) = ρ α

renᵉ-ec : RenameEC → EC → EC
renᵉ-ec ρ ε = ε
renᵉ-ec ρ (` α) = ` ρ α

⇑ᵉ-ec : EC → EC
⇑ᵉ-ec = renᵉ-ec suc

⇑ᵉ-injective : ∀ {e₁ e₂}
  → ⇑ᵉ-ec e₁ ≡ ⇑ᵉ-ec e₂
    ---------------------------
  → e₁ ≡ e₂
⇑ᵉ-injective {ε} {ε} refl = refl
⇑ᵉ-injective {ε} {` α} ()
⇑ᵉ-injective {` α} {ε} ()
⇑ᵉ-injective {` α} {` .α} refl = refl

renᵉ-ec⋆ : RenameEC → EC⋆ → EC⋆
renᵉ-ec⋆ ρ ⋆ = ⋆
renᵉ-ec⋆ ρ (ec e) = ec (renᵉ-ec ρ e)

⇑ᵉ-ec⋆ : EC⋆ → EC⋆
⇑ᵉ-ec⋆ = renᵉ-ec⋆ suc

SubstEC : Set
SubstEC = ECVar → EC

idsᵉ : SubstEC
idsᵉ = `_

extsᵉ : SubstEC → SubstEC
extsᵉ σ zero = ` zero
extsᵉ σ (suc α) = renᵉ-ec suc (σ α)

_•ᵉₛ_ : EC → SubstEC → SubstEC
(e •ᵉₛ σ) zero = e
(e •ᵉₛ σ) (suc α) = σ α

subᵉ-ec : SubstEC → EC → EC
subᵉ-ec σ ε = ε
subᵉ-ec σ (` α) = σ α

subᵉ-ec⋆ : SubstEC → EC⋆ → EC⋆
subᵉ-ec⋆ σ ⋆ = ⋆
subᵉ-ec⋆ σ (ec e) = ec (subᵉ-ec σ e)

-- | EC well-formedness
infix 4 _⊢ᵉ_
infix 4 _⊢ᵉ⋆_

data _⊢ᵉ_ : ECCtx → EC → Set where
  wf-ε : ∀ {Δ} → Δ ⊢ᵉ ε
  wf-` : ∀ {Δ α} → α < Δ .size → Δ ⊢ᵉ ` α

data _⊢ᵉ⋆_ : ECCtx → EC⋆ → Set where
  wf-⋆  : ∀ {Δ} → Δ ⊢ᵉ⋆ ⋆
  wf-ec : ∀ {Δ e} → Δ ⊢ᵉ e → Δ ⊢ᵉ⋆ ec e

ec-wf-weaken-global : ∀ {Δ e}
  → Δ ⊢ᵉ e
    ---------------
  → Δ ,ᵍα ⊢ᵉ e
ec-wf-weaken-global wf-ε = wf-ε
ec-wf-weaken-global (wf-` α<Δ) = wf-` (m≤n⇒m≤1+n α<Δ)

globalEC-weaken-global : ∀ {Δ α}
  → GlobalEC Δ α
    ------------------------
  → GlobalEC (Δ ,ᵍα) α
globalEC-weaken-global (globalEC α<Δ cutoff≤α) = globalEC (m≤n⇒m≤1+n α<Δ) cutoff≤α

infixl 5 _,_<:_
infixl 5 _,ᵍ_<:_
infix 4 _∋ˢ_
infix 4 _∋ˢ_⦂_

-- | EC subtyping contexts.
--
-- A SubCtx stores subtyping edges in one shared list.  The cutoff is the
-- number of lexically-bound edges at the front of that list.  Runtime scope
-- allocation appends persistent/global edges to the back without changing
-- the cutoff.
record SubCtx : Set where
  constructor subctx
  field
    cutoff : ℕ
    edges : List (EC × EC)
    cutoff≤length : cutoff ≤ length edges

open SubCtx public

subctx-cong : ∀ {cutoff xs ys p q}
  → xs ≡ ys
    ------------------------------------------
  → subctx cutoff xs p ≡ subctx cutoff ys q
subctx-cong {p = p} {q = q} refl rewrite ≤-irrelevant p q = refl

∅ˢ : SubCtx
∅ˢ = subctx zero [] z≤n

-- | Lexical subtyping binders cons a new edge and increment the cutoff.
_,_<:_ : SubCtx → EC → EC → SubCtx
Θ , e₁ <: e₂ = subctx (suc (Θ .cutoff)) (⟨ e₁ , e₂ ⟩ ∷ Θ .edges)
                      (s≤s (Θ .cutoff≤length))

-- | Runtime scope allocation appends a global edge and leaves the cutoff unchanged.
_,ᵍ_<:_ : SubCtx → EC → EC → SubCtx
Θ ,ᵍ e₁ <: e₂ = subctx (Θ .cutoff) (Θ .edges ∷ʳ ⟨ e₁ , e₂ ⟩)
  (subst (Θ .cutoff ≤_) (sym (length-∷ʳ (Θ .edges) ⟨ e₁ , e₂ ⟩)) (m≤n⇒m≤1+n (Θ .cutoff≤length)))

_∋ˢ_ : SubCtx → EC × EC → Set
Θ ∋ˢ edge = Θ .edges ∋ edge

_∋ˢ_⦂_ : SubCtx → ℕ → EC × EC → Set
Θ ∋ˢ n ⦂ edge = Θ .edges ∋ n ⦂ edge

-- | Globally-allocated subtype edges (constraints) are the ones from cutoff.
GlobalEdges : SubCtx → List (EC × EC)
GlobalEdges Θ = drop (Θ .cutoff) (Θ .edges)

-- | Global subtype edges have a unique immediate ancestor for each global EC.
UniqueGlobalAncestor : SubCtx → Set
UniqueGlobalAncestor Θ =
  ∀ {e₁ e₂ α} → GlobalEdges Θ ∋ ⟨ e₁ , ` α ⟩ → GlobalEdges Θ ∋ ⟨ e₂ , ` α ⟩ → e₁ ≡ e₂

-- | Well-formed subtype contexts.
infix 4 _⊢_SubCtx

_⊢_SubCtx : ECCtx → SubCtx → Set
Δ ⊢ Θ SubCtx =
  -- all ECs in the subtype context must be well-formed
  All (λ { ⟨ e₁ , e₂ ⟩ → Δ ⊢ᵉ e₁ × Δ ⊢ᵉ e₂ }) (Θ .edges) ×
  -- and all global edges (e <: α) must be well-formed
  (∀ {e₁ e₂} → GlobalEdges Θ ∋ ⟨ e₁ , e₂ ⟩ → ∃[ α ] (e₂ ≡ ` α) × GlobalEC Δ α) ×
  -- and each global α has a unique global ancestor
  UniqueGlobalAncestor Θ

-- | If Θ's cutoff is 0 then every edge is global
zero-cutoff→all-global : ∀ {Θ e₁ e₂}
  → Θ .cutoff ≡ zero
  → Θ ∋ˢ ⟨ e₁ , e₂ ⟩
    ------------------------------
  → GlobalEdges Θ ∋ ⟨ e₁ , e₂ ⟩
zero-cutoff→all-global refl edge = edge

-- | Adding a well-formed lexical edge preserves well-formed SubCtx
subctx-wf-lex-ext : ∀ {Δ Θ e₁ e₂}
  → Δ ⊢ Θ SubCtx
  → Δ ⊢ᵉ e₁
  → Δ ⊢ᵉ e₂
    ------------------------------
  → Δ ⊢ Θ , e₁ <: e₂ SubCtx
subctx-wf-lex-ext ⟨ ⊢edges , ⟨ ⊢global , unique ⟩ ⟩ ⊢e₁ ⊢e₂ =
  ⟨ ⟨ ⊢e₁ , ⊢e₂ ⟩ ∷ᴬ ⊢edges , ⟨ ⊢global , unique ⟩ ⟩

-- | Allocating a fresh global edge preserves well-formed SubCtx.
subctx-wf-global-ext : ∀ {Δ Θ e}
  → Δ ⊢ Θ SubCtx
  → Δ ⊢ᵉ e
    ------------------------------
  → Δ ,ᵍα ⊢ Θ ,ᵍ e <: ` freshᵉ Δ SubCtx
subctx-wf-global-ext {Δ = Δ} {Θ = Θ} {e = e} ⟨ ⊢edges , ⟨ ⊢global , unique ⟩ ⟩ ⊢e =
  ⟨ ∷ʳ⁺ (edges-wf-global-ext ⊢edges) ⟨ ec-wf-weaken-global ⊢e , wf-` (s≤s ≤-refl) ⟩ ,
    ⟨ global-snoc-wf (Θ .cutoff) (Θ .edges)
        (λ edge →
          let ⟨ α , eq , globalα ⟩ = ⊢global edge in
          ⟨ α , eq , globalEC-weaken-global globalα ⟩)
        ⟨ freshᵉ Δ , ⟨ refl , globalEC (s≤s ≤-refl) (Δ .cutoff≤size) ⟩ ⟩ ,
      unique-global-snoc (Θ .cutoff) (Θ .edges) unique
        (no-fresh-global ⟨ ⊢edges , ⟨ ⊢global , unique ⟩ ⟩)
    ⟩ ⟩
  where
  edges-wf-global-ext : ∀ {edges}
    → All (λ { ⟨ e₁ , e₂ ⟩ → Δ ⊢ᵉ e₁ × Δ ⊢ᵉ e₂ }) edges
      -----------------------------------------------------------------
    → All (λ { ⟨ e₁ , e₂ ⟩ → Δ ,ᵍα ⊢ᵉ e₁ × Δ ,ᵍα ⊢ᵉ e₂ }) edges
  edges-wf-global-ext []ᴬ = []ᴬ
  edges-wf-global-ext (⟨ ⊢e₁ , ⊢e₂ ⟩ ∷ᴬ ⊢edges) =
    ⟨ ec-wf-weaken-global ⊢e₁ , ec-wf-weaken-global ⊢e₂ ⟩ ∷ᴬ edges-wf-global-ext ⊢edges

  global-snoc-wf : ∀ {Δ} {e₃ e₄ : EC} (k : ℕ) (edges : List (EC × EC))
    → (∀ {e₁ e₂}
          → drop k edges ∋ ⟨ e₁ , e₂ ⟩
          → ∃[ α ] (e₂ ≡ ` α) × GlobalEC Δ α)
    → ∃[ α ] (e₄ ≡ ` α) × GlobalEC Δ α
    → (∀ {e₁ e₂}
          → drop k (edges ∷ʳ ⟨ e₃ , e₄ ⟩) ∋ ⟨ e₁ , e₂ ⟩
          → ∃[ α ] (e₂ ≡ ` α) × GlobalEC Δ α)
  global-snoc-wf zero [] old new Z = new
  global-snoc-wf zero [] old new (S ())
  global-snoc-wf zero (_ ∷ edges) old new Z = old Z
  global-snoc-wf zero (_ ∷ edges) old new (S edge) = global-snoc-wf zero edges (λ edge′ → old (S edge′)) new edge
  global-snoc-wf (suc zero) [] old new ()
  global-snoc-wf (suc (suc k)) [] old new ()
  global-snoc-wf (suc k) (_ ∷ edges) old new edge = global-snoc-wf k edges old new edge

  no-fresh-global : ∀ {e′}
    → Δ ⊢ Θ SubCtx
      ---------------------------------------------
    → ¬ (GlobalEdges Θ ∋ ⟨ e′ , ` freshᵉ Δ ⟩)
  no-fresh-global ⟨ _ , ⟨ ⊢global , _ ⟩ ⟩ edge
    with ⊢global edge
  ... | ⟨ .(freshᵉ Δ) , ⟨ refl , globalEC α<Δ _ ⟩ ⟩ =
    wf-var-≢fresh {Δ = Δ} α<Δ refl

  unique-global-snoc : (k : ℕ) (edges : List (EC × EC))
    → (∀ {e₁ e₂ α}
          → drop k edges ∋ ⟨ e₁ , ` α ⟩
          → drop k edges ∋ ⟨ e₂ , ` α ⟩
          → e₁ ≡ e₂)
    → (∀ {e′} → ¬ (drop k edges ∋ ⟨ e′ , ` freshᵉ Δ ⟩))
    → (∀ {e₁ e₂ α}
          → drop k (edges ∷ʳ ⟨ e , ` freshᵉ Δ ⟩) ∋ ⟨ e₁ , ` α ⟩
          → drop k (edges ∷ʳ ⟨ e , ` freshᵉ Δ ⟩) ∋ ⟨ e₂ , ` α ⟩
          → e₁ ≡ e₂)
  unique-global-snoc zero edges unique noOld edge₁ edge₂
    with member-snoc-inv edge₁ | member-snoc-inv edge₂
  ... | inj₁ old₁ | inj₁ old₂ = unique old₁ old₂
  ... | inj₁ old₁ | inj₂ refl = contradiction old₁ noOld
  ... | inj₂ refl | inj₁ old₂ = contradiction old₂ noOld
  ... | inj₂ refl | inj₂ refl = refl
  unique-global-snoc (suc zero) [] unique noOld ()
  unique-global-snoc (suc (suc k)) [] unique noOld ()
  unique-global-snoc (suc k) (_ ∷ edges) unique noOld edge₁ edge₂ =
    unique-global-snoc k edges unique noOld edge₁ edge₂



renᵉ-subctx : RenameEC → SubCtx → SubCtx
renᵉ-subctx ρ Θ =
  subctx (Θ .cutoff)
         (map (λ { ⟨ e₁ , e₂ ⟩ → ⟨ renᵉ-ec ρ e₁ , renᵉ-ec ρ e₂ ⟩ }) (Θ .edges))
         (subst (Θ .cutoff ≤_) (sym (length-map _ (Θ .edges))) (Θ .cutoff≤length))

⇑ᵉ-subctx : SubCtx → SubCtx
⇑ᵉ-subctx = renᵉ-subctx suc

subᵉ-subctx : SubstEC → SubCtx → SubCtx
subᵉ-subctx σ Θ =
  subctx (Θ .cutoff)
         (map (λ { ⟨ e₁ , e₂ ⟩ → ⟨ subᵉ-ec σ e₁ , subᵉ-ec σ e₂ ⟩ }) (Θ .edges))
         (subst (Θ .cutoff ≤_) (sym (length-map _ (Θ .edges))) (Θ .cutoff≤length))

-- | EC subtyping
infix 4 _⊢ᵉ_<:_
infix 4 _⊢ᵉ_<:⋆_

data _⊢ᵉ_<:_ : SubCtx → EC → EC → Set where

  <:-ε : ∀ {Θ e}
      ---------------------
    → Θ ⊢ᵉ ε <: e

  <:-refl : ∀ {Θ e}
      ---------------------
    → Θ ⊢ᵉ e <: e

  <:-ax : ∀ {Θ e₁ e₂}
    → Θ ∋ˢ ⟨ e₁ , e₂ ⟩
      ------------------------
    → Θ ⊢ᵉ e₁ <: e₂

  <:-trans : ∀ {Θ e₁ e₂ e₃}
    → Θ ⊢ᵉ e₁ <: e₂
    → Θ ⊢ᵉ e₂ <: e₃
      ------------------------
    → Θ ⊢ᵉ e₁ <: e₃

only-root-<:ε : ∀ {Δ Θ e}
  → Δ ⊢ Θ SubCtx
  → Θ .cutoff ≡ zero
  → Θ ⊢ᵉ e <: ε
    ---------------------
  → e ≡ ε
only-root-<:ε ⊢Θ cutoff≡0 <:-ε = refl
only-root-<:ε ⊢Θ cutoff≡0 <:-refl = refl
only-root-<:ε {Θ = Θ} ⟨ _ , ⟨ ⊢global , _ ⟩ ⟩ cutoff≡0 (<:-ax edge) =
  case ⊢global (zero-cutoff→all-global {Θ = Θ} cutoff≡0 edge) of λ where
  ⟨ _ , () , _ ⟩
only-root-<:ε ⊢Θ cutoff≡0 (<:-trans e₁<:e e<:ε) =
  case only-root-<:ε ⊢Θ cutoff≡0 e<:ε of λ where
  refl → only-root-<:ε ⊢Θ cutoff≡0 e₁<:e

ec-<:-weaken : ∀ {Θ e₁ e₂ e₃ e₄}
  → Θ            ⊢ᵉ e₁ <: e₂
    ---------------------------------
  → Θ , e₃ <: e₄ ⊢ᵉ e₁ <: e₂
ec-<:-weaken <:-ε = <:-ε
ec-<:-weaken <:-refl = <:-refl
ec-<:-weaken (<:-ax edge) = <:-ax (S edge)
ec-<:-weaken (<:-trans e₁<:e e<:e₂) = <:-trans (ec-<:-weaken e₁<:e) (ec-<:-weaken e<:e₂)

infix 4 _⊆ˢ_

record _⊆ˢ_ (Θ₁ Θ₂ : SubCtx) : Set where
  constructor subctx⊆
  field
    subtype⊆ : ∀ {e₁ e₂} → Θ₁ ⊢ᵉ e₁ <: e₂ → Θ₂ ⊢ᵉ e₁ <: e₂
    globalEdge⊆ : GlobalEdges Θ₁ ⊆ GlobalEdges Θ₂

open _⊆ˢ_ public

data _⊢ᵉ_<:⋆_ : SubCtx → EC⋆ → EC⋆ → Set where

  <:-⋆ : ∀ {Θ}
      ------------------
    → Θ ⊢ᵉ ⋆ <:⋆ ⋆

  <:-ec : ∀ {Θ e₁ e₂}
    → Θ ⊢ᵉ    e₁ <:  e₂
      ------------------------
    → Θ ⊢ᵉ ec e₁ <:⋆ ec e₂

<:⋆-trans : ∀ {Θ} {ê₁ ê₂ ê₃}
  → Θ ⊢ᵉ ê₁ <:⋆ ê₂
  → Θ ⊢ᵉ ê₂ <:⋆ ê₃
    ---------------------------
  → Θ ⊢ᵉ ê₁ <:⋆ ê₃
<:⋆-trans <:-⋆ <:-⋆ = <:-⋆
<:⋆-trans (<:-ec e₁<:e₂) (<:-ec e₂<:e₃) = <:-ec (<:-trans e₁<:e₂ e₂<:e₃)
