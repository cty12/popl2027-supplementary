module Theories.ECSubtypeDecidable where

open import Data.List using (List; []; _∷_; length)
open import Data.Nat using (ℕ; zero; suc; _≤_; s≤s)
open import Data.Product using (_×_; ∃-syntax) renaming (_,_ to ⟨_,_⟩)
open import Data.Product.Properties using (,-injectiveˡ)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (tt)
open import Relation.Binary.Construct.Closure.ReflexiveTransitive using (Star; _◅_; _◅◅_) renaming (ε to star-ε)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Nullary.Negation using (contradiction)
open import Function using (case_of_)

open import Theories.Utils using (_∋_; Z; S_; _⊆_; member?; NoDup; subset-length)
open import Theories.EnvClassifiers

{-
     Path -> "remove-cycles" -> AcyclicPath -> "acyclic->bounded" -> BoundedPath
     BoundedPath -> "bounded->path" -> Path
-}

-- | Reachability through edges in Θ.
-- | The main lemma of this file is that this reachability is decidable.
Path : SubCtx → EC → EC → Set
Path Θ e₁ e₂ = Star (λ e₃ e₄ → Θ ∋ˢ ⟨ e₃ , e₄ ⟩) e₁ e₂

path->sub : ∀ {Θ e₁ e₂}
  → Path Θ e₁ e₂
    ---------------------
  → Θ ⊢ᵉ e₁ <: e₂
path->sub star-ε = <:-refl
path->sub (edge ◅ path) = <:-trans (<:-ax edge) (path->sub path)

-- | This helper is for case analysis of EC subtyping: after normalizing
-- | transitivity, e₁ <: e₂ implies that either (1) e₁ is ε, (2) e₁ reaches ε by
-- | Θ, or (3) e₁ reaches e₂ by Θ.
subtype-cases : ∀ {Θ e₁ e₂}
  → Θ ⊢ᵉ e₁ <: e₂
    ---------------------------------------------
  → (e₁ ≡ ε) ⊎ Path Θ e₁ ε ⊎ Path Θ e₁ e₂
subtype-cases <:-ε         = inj₁ refl
subtype-cases <:-refl      = inj₂ (inj₂ star-ε)
subtype-cases (<:-ax edge) = inj₂ (inj₂ (edge ◅ star-ε))
subtype-cases {Θ} {e₁} {e₂} (<:-trans e₁<:e e<:e₂)
  with subtype-cases e₁<:e
... | inj₁ e₁≡ε = inj₁ e₁≡ε
... | inj₂ (inj₁ path) = inj₂ (inj₁ path)
... | inj₂ (inj₂ path₁) with subtype-cases e<:e₂
...   | inj₁ e≡ε = inj₂ (inj₁ (subst (Path Θ e₁) e≡ε path₁))
...   | inj₂ (inj₁ path₂) = inj₂ (inj₁ (path₁ ◅◅ path₂))
...   | inj₂ (inj₂ path₂) = inj₂ (inj₂ (path₁ ◅◅ path₂))


private

  -- | A bag of vertices in Θ. This provides the search bound.
  graphVertices : List (EC × EC) → List EC
  graphVertices [] = []
  graphVertices (⟨ e₁ , e₂ ⟩ ∷ edges) = e₁ ∷ e₂ ∷ graphVertices edges

  edge-source∈vertices : ∀ {edges e₁ e₂}
    → edges ∋ ⟨ e₁ , e₂ ⟩
      ---------------------------
    → graphVertices edges ∋ e₁
  edge-source∈vertices Z = Z
  edge-source∈vertices (S edge) = S (S (edge-source∈vertices edge))

  edge-target∈vertices : ∀ {edges e₁ e₂}
    → edges ∋ ⟨ e₁ , e₂ ⟩
      ---------------------------
    → graphVertices edges ∋ e₂
  edge-target∈vertices Z = S Z
  edge-target∈vertices (S edge) = S (S (edge-target∈vertices edge))

  mutual

    data AcyclicPath (Θ : SubCtx) : EC → EC → Set where

      ap-refl : ∀ {e}
          ---------------------
        → AcyclicPath Θ e e

      ap-step : ∀ {e₁ e e₂}
        → Θ ∋ˢ ⟨ e₁ , e ⟩
        → (path : AcyclicPath Θ e e₂)
        → ¬ (acyclicVertices path ∋ e₁)
          ------------------------------------
        → AcyclicPath Θ e₁ e₂

    -- | Collect vertices on an acyclic path
    acyclicVertices : ∀ {Θ e₁ e₂}
      → AcyclicPath Θ e₁ e₂
        ------------------------------
      → List EC
    acyclicVertices {e₁ = e₁}            ap-refl = e₁ ∷ []
    acyclicVertices {e₁ = e₁} (ap-step _ path _) = e₁ ∷ acyclicVertices path

  acyclic-nodup : ∀ {Θ e₁ e₂}
    → (path : AcyclicPath Θ e₁ e₂)
      ---------------------------------
    → NoDup (acyclicVertices path)
  acyclic-nodup                   ap-refl = ⟨ (λ ()) , tt ⟩
  acyclic-nodup (ap-step edge path fresh) = ⟨ fresh , acyclic-nodup path ⟩

  -- | Every vertex on an acyclic path appears among vertices in the graph.
  acyclic-subset : ∀ {Θ e₁ e₂}
    → (path : AcyclicPath Θ e₁ e₂)
    → graphVertices (Θ .edges) ∋ e₁
      ---------------------------------------------------
    → acyclicVertices path ⊆ graphVertices (Θ .edges)
  acyclic-subset ap-refl e₁∈vertices Z = e₁∈vertices
  acyclic-subset ap-refl e₁∈vertices (S ())
  acyclic-subset (ap-step edge path fresh) e₁∈vertices Z =
    e₁∈vertices
  acyclic-subset (ap-step edge path fresh) e₁∈vertices (S member) =
    acyclic-subset path (edge-target∈vertices edge) member

  -- | Drop an acyclic path prefix to start from a later visited vertex.
  drop-acyclic-prefix : ∀ {Θ e₁ e₂ e₃}
    → (path : AcyclicPath Θ e₁ e₂)
    → acyclicVertices path ∋ e₃
      ------------------------------------
    → AcyclicPath Θ e₃ e₂
  drop-acyclic-prefix ap-refl Z = ap-refl
  drop-acyclic-prefix ap-refl (S ())
  drop-acyclic-prefix path@(ap-step edge tail fresh) Z = path
  drop-acyclic-prefix (ap-step edge tail _) (S x) = drop-acyclic-prefix tail x

  -- | Remove cycles from an arbitrary path, yielding an acyclic path.
  remove-cycles : ∀ {Θ e₁ e₂}
    → Path Θ e₁ e₂
      ---------------------------
    → AcyclicPath Θ e₁ e₂
  remove-cycles star-ε = ap-refl
  remove-cycles {Θ} {e₁} (edge ◅ path) with remove-cycles {Θ} path
  ... | tail with member? _≡?ᵉ_ (acyclicVertices tail) e₁
  ...   | yes member = drop-acyclic-prefix tail member
  ...   | no fresh = ap-step edge tail fresh

  -- Paths with a fuel bound on the number of steps.
  data BoundedPath (Θ : SubCtx) : ℕ → EC → EC → Set where

    bp-refl : ∀ {n e}
        -----------------------
      → BoundedPath Θ n e e

    bp-step : ∀ {n e₁ e₂ e}
      → Θ ∋ˢ ⟨ e₁ , e ⟩
      → BoundedPath Θ n e e₂
        ----------------------------
      → BoundedPath Θ (suc n) e₁ e₂

  -- Forget the fuel bound from a bounded path.
  bounded->path : ∀ {Θ n e₁ e₂}
    → BoundedPath Θ n e₁ e₂
      -------------------------------
    → Path Θ e₁ e₂
  bounded->path {Θ = Θ} bp-refl = star-ε
  bounded->path {Θ = Θ} (bp-step edge path) = edge ◅ bounded->path {Θ = Θ} path

  -- Increase the fuel available to a bounded path.
  bounded-weaken : ∀ {Θ n m e₁ e₂}
    → n ≤ m
    → BoundedPath Θ n e₁ e₂
      -------------------------
    → BoundedPath Θ m e₁ e₂
  bounded-weaken n≤m bp-refl = bp-refl
  bounded-weaken (s≤s n≤m) (bp-step edge path) =
    bp-step edge (bounded-weaken n≤m path)

  -- An acyclic path is bounded by the number of vertices it visits.
  acyclic->bounded : ∀ {Θ e₁ e₂}
    → (path : AcyclicPath Θ e₁ e₂)
      ------------------------------------------------------
    → BoundedPath Θ (length (acyclicVertices path)) e₁ e₂
  acyclic->bounded                   ap-refl = bp-refl
  acyclic->bounded (ap-step edge path fresh) = bp-step edge (acyclic->bounded path)


  data ChooseOutEdge (Θ : SubCtx) (n : ℕ) (e₁ e₂ : EC) : List (EC × EC) → Set where

    choose : ∀ {edge out-edges e}
      → edge ≡ ⟨ e₁ , e ⟩
      → BoundedPath Θ n e e₂
        ------------------------------------------------
      → ChooseOutEdge Θ n e₁ e₂ (edge ∷ out-edges)

    skip : ∀ {edge out-edges}
      → ChooseOutEdge Θ n e₁ e₂ out-edges
        ------------------------------------------------
      → ChooseOutEdge Θ n e₁ e₂ (edge ∷ out-edges)

  choose-edge->bounded : ∀ {out-edges Θ n e₁ e₂}
    → (∀ {e} → out-edges ∋ ⟨ e₁ , e ⟩ → Θ ∋ˢ ⟨ e₁ , e ⟩)
    → ChooseOutEdge Θ n e₁ e₂ out-edges
      ----------------------------------------------------
    → BoundedPath Θ (suc n) e₁ e₂
  choose-edge->bounded lift (choose refl path) = bp-step (lift Z) path
  choose-edge->bounded lift (skip next)        = choose-edge->bounded (λ edge → lift (S edge)) next

  bounded->choose-edge : ∀ {out-edges Θ n e₁ e e₂}
    → out-edges ∋ ⟨ e₁ , e ⟩
    → BoundedPath Θ n e e₂
      ------------------------------------
    → ChooseOutEdge Θ n e₁ e₂ out-edges
  bounded->choose-edge        Z path = choose refl path
  bounded->choose-edge (S edge) path = skip (bounded->choose-edge edge path)

  mutual

    bounded-path? : ∀ Θ n e₁ e₂
      → Dec (BoundedPath Θ n e₁ e₂)
    bounded-path? Θ zero e₁ e₂ with e₁ ≡?ᵉ e₂
    ... | yes refl = yes bp-refl
    ... | no e₁≢e₂ = no λ { bp-refl → e₁≢e₂ refl }
    bounded-path? Θ (suc n) e₁ e₂ with e₁ ≡?ᵉ e₂
    ... | yes refl = yes bp-refl
    ... | no e₁≢e₂ with choose-edge? (Θ .edges) Θ n e₁ e₂
    ...   | yes next = yes (choose-edge->bounded (λ edge → edge) next)
    ...   | no no-step =
      no λ where
        bp-refl → e₁≢e₂ refl
        (bp-step edge path) → no-step (bounded->choose-edge edge path)

    -- | Look for an outgoing edge from e₁ that reaches e₂ with the remaining fuel.
    -- | And that's basically DFS.
    choose-edge? : ∀ out-edges Θ n e₁ e₂
      → Dec (ChooseOutEdge Θ n e₁ e₂ out-edges)
    choose-edge? [] Θ n e₁ e₂ =
      no λ ()
    choose-edge? (⟨ e , e′ ⟩ ∷ out-edges) Θ n e₁ e₂ =
      case e₁ ≡?ᵉ e of λ where
        (yes refl) →
          case bounded-path? Θ n e′ e₂ of λ where
            (yes path) → yes (choose refl path)
            (no no-path) →
              case choose-edge? out-edges Θ n e e₂ of λ where
                (yes next) → yes (skip next)
                (no no-tail) →
                  no λ where
                    (choose refl path) → no-path path
                    (skip next) → no-tail next
        (no notEq) →
          case choose-edge? out-edges Θ n e₁ e₂ of λ where
            (yes next) → yes (skip next)
            (no no-tail) →
              no λ where
                (choose eq _) → notEq (sym (,-injectiveˡ eq))
                (skip next) → no-tail next

  -- | Every path can be compressed to an acyclic path that's bounded.
  path->bounded : ∀ {Θ e₁ e₂}
    → Path Θ e₁ e₂
      ------------------------------------------------------------
    → BoundedPath Θ (length (graphVertices (Θ .edges))) e₁ e₂
  path->bounded star-ε = bp-refl
  path->bounded {Θ} path@(edge ◅ _) =
    let acyc-path = remove-cycles {Θ} path in
    bounded-weaken
      (subset-length (acyclic-nodup acyc-path)
                     (acyclic-subset acyc-path (edge-source∈vertices edge)))
      (acyclic->bounded acyc-path)

-- | It's decidable whether e₂ is reachable from e₁.
path? : ∀ Θ e₁ e₂ → Dec (Path Θ e₁ e₂)
path? Θ e₁ e₂ with bounded-path? Θ (length (graphVertices (Θ .edges))) e₁ e₂
... | yes path    = yes (bounded->path {Θ} path)
... | no  no-path = no λ path → no-path (path->bounded {Θ} path)

ec-<:? : ∀ Θ e₁ e₂ → Dec (Θ ⊢ᵉ e₁ <: e₂)
ec-<:? Θ e₁ e₂ with e₁ ≡?ᵉ ε
... | yes refl = yes <:-ε
... | no e₁≢ε with path? Θ e₁ e₂
...   | yes path = yes (path->sub path)
...   | no no-target with path? Θ e₁ ε
...     | yes path = yes (<:-trans (path->sub path) <:-ε)
...     | no no-root = no λ e₁<:e₂ →
          case subtype-cases e₁<:e₂ of λ where
            (inj₁        e₁≡ε) → contradiction e₁≡ε e₁≢ε
            (inj₂ (inj₁ path)) → no-root path
            (inj₂ (inj₂ path)) → no-target path

ec-<:⋆? : ∀ Θ ê₁ ê₂ → Dec (Θ ⊢ᵉ ê₁ <:⋆ ê₂)
ec-<:⋆? Θ ⋆ ⋆ = yes <:-⋆
ec-<:⋆? Θ ⋆ (ec e₂) = no λ ()
ec-<:⋆? Θ (ec e₁) ⋆ = no λ ()
ec-<:⋆? Θ (ec e₁) (ec e₂) with ec-<:? Θ e₁ e₂
... | yes e₁<:e₂ = yes (<:-ec e₁<:e₂)
... | no e₁≮:e₂ = no λ { (<:-ec e₁<:e₂) → e₁≮:e₂ e₁<:e₂ }
