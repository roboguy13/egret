open import Data.Sum
open import Data.Product
open import Data.Empty
open import Data.List
open import Relation.Binary.PropositionalEquality

module Syntax
  (Type-Name : Set)
  (Type-Name-eq-dec : (a b : Type-Name) → (a ≡ b) ⊎ (a ≢ b))
  where

data Type : Set where
  Ty : Type-Name → Type
  _⇒_ : Type → Type → Type

data Type-Ctx : Set where
  ∅ : Type-Ctx
  _,,_ : Type-Ctx → Type → Type-Ctx

data _∋_ : Type-Ctx → Type → Set where
  V-Here : ∀ {Γ a} → (Γ ,, a) ∋ a
  V-There : ∀ {Γ a b} →
    Γ ∋ a →
    (Γ ,, b) ∋ a

data Expr : Type-Ctx → Type → Set where
  V : ∀ {Γ a} → Γ ∋ a → Expr Γ a
  -- ƛ : ∀ {Γ a b} → Expr (Γ ,, a) b → Expr Γ (a ⇒ b)
  _·_ : ∀ {Γ a b} →
    Expr Γ (a ⇒ b) →
    Expr Γ a →
    Expr Γ b

record Equation (Γ : Type-Ctx) (a : Type) : Set where
  field
    lhs : Expr Γ a
    rhs : Expr Γ a

_≐_ : ∀ {Γ a} → Expr Γ a → Expr Γ a → Equation Γ a
_≐_ x y = record { lhs = x ; rhs = y }

Theory : ∀ (Γ : Type-Ctx) → Set
Theory Γ = List (∃[ a ] Equation Γ a)

data _∈_ : ∀ {Γ a} → Equation Γ a → Theory Γ → Set where
  Theory-here : ∀ {Γ a} {eqn : Equation Γ a} {T} →
    eqn ∈ ((a , eqn) ∷ T)
  Theory-there : ∀ {Γ a b} {eqn : Equation Γ a} {eqn′ : Equation Γ b} {T} →
    eqn ∈ T →
    eqn ∈ ((b , eqn′) ∷ T)

data _▷_≐_ : {Γ : Type-Ctx} → {a : Type} → Theory Γ → Expr Γ a → Expr Γ a → Set where
  ▷project : ∀ {Γ a} {T : Theory Γ} (e₁ e₂ : Expr Γ a) →
    (e₁ ≐ e₂) ∈ T →
    T ▷ e₁ ≐ e₂

  ▷refl : ∀ {Γ a} {T} {e : Expr Γ a} →
    T ▷ e ≐ e

  ▷sym : ∀ {Γ a} {T} {e₁ e₂ : Expr Γ a} →
    T ▷ e₁ ≐ e₂ →
    T ▷ e₂ ≐ e₁

  ▷trans : ∀ {Γ a} {T} {e₁ e₂ e₃ : Expr Γ a} →
    T ▷ e₁ ≐ e₂ →
    T ▷ e₂ ≐ e₃ →
    T ▷ e₁ ≐ e₃

  ▷app : ∀ {Γ a b} {T} {f f′ : Expr Γ (a ⇒ b)} {e e′ : Expr Γ a} →
    T ▷ f ≐ f′ →
    T ▷ e ≐ e′ →
    T ▷ (f · e) ≐ (f′ · e′)

record Rewrite (Γ : Type-Ctx) (a : Type) : Set where
  field
    lhs : Expr Γ a
    rhs : Expr Γ a

_↦_ : ∀ {Γ a} → Expr Γ a → Expr Γ a → Rewrite Γ a
x ↦ y = record { lhs = x ; rhs = y }

data _▷_↦_ : {Γ : Type-Ctx} → ∀ {a} → Theory Γ → Expr Γ a → Expr Γ a → Set where
  ▷Rewrite-eq : ∀ {Γ a} {T : Theory Γ} {lhs rhs : Expr Γ a} →
    T ▷ lhs ≐ rhs →
    T ▷ lhs ↦ rhs

data _∈⟦_⟧_ : ∀ {Γ a b} → Expr Γ a → Rewrite Γ b → Expr Γ a → Set where
  Rewrite-here-1 : ∀ {Γ a} {e₁ e₂ : Expr Γ a} →
    e₁ ∈⟦ e₁ ↦ e₂ ⟧ e₁

  Rewrite-here-2 : ∀ {Γ a} {e₁ e₂ : Expr Γ a} →
    e₂ ∈⟦ e₁ ↦ e₂ ⟧ e₁

  Rewrite-app : ∀ {Γ a b c} {e₁ e₂ : Expr Γ c} {f f′ : Expr Γ (a ⇒ b)} {e e′ : Expr Γ a} →
    f′ ∈⟦ e₁ ↦ e₂ ⟧ f →
    e′ ∈⟦ e₁ ↦ e₂ ⟧ e →
    (f′ · e′) ∈⟦ e₁ ↦ e₂ ⟧ (f · e)

data _∈Theory⟦_⟧_ : ∀ {Γ a} → Expr Γ a → Theory Γ → Expr Γ a → Set where
  Theory-Rewrite : ∀ {Γ a} {e e′ e₁ e₂ : Expr Γ a} {T} →
    T ▷ e₁ ↦ e₂ →
    e ∈⟦ e₁ ↦ e₂ ⟧ e′ →
    e ∈Theory⟦ T ⟧ e′

is-eqn′ : ∀ {Γ a b} {e₁ e₂ : Expr Γ a} {e e′ : Expr Γ b} {T} →
  e ∈⟦ e₁ ↦ e₂ ⟧ e′ →
  T ▷ e₁ ≐ e₂ →
  T ▷ e ≐ e′
is-eqn′ Rewrite-here-1 prf-2 = ▷refl
is-eqn′ Rewrite-here-2 prf-2 = ▷sym prf-2
is-eqn′ (Rewrite-app prf prf₁) prf-2 = ▷app (is-eqn′ prf prf-2) (is-eqn′ prf₁ prf-2)

is-eqn : ∀ {Γ a} {T : Theory Γ} {e e′ : Expr Γ a} →
  e ∈Theory⟦ T ⟧ e′ →
  T ▷ e ≐ e′
is-eqn {Γ} {a} {T} (Theory-Rewrite (▷Rewrite-eq x) Rewrite-here-1) = ▷refl
is-eqn {Γ} {a} {T} (Theory-Rewrite (▷Rewrite-eq x) Rewrite-here-2) = ▷sym x
is-eqn {Γ} {a} {T} (Theory-Rewrite (▷Rewrite-eq x) (Rewrite-app x₁ x₂)) = ▷app (is-eqn′ x₁ x) (is-eqn′ x₂ x)

module _ (D : Set) where
  Denotation : Set
  Denotation = ∀ {Γ a} → Expr Γ a → D

  _⊨_ : ∀ {Γ} → (𝓜 : Denotation) → Theory Γ → Set
  _⊨_ {Γ} 𝓜 T = ∀ {a} {e₁ e₂ : Expr Γ a} →
    (T ▷ e₁ ≐ e₂) → 𝓜 e₁ ≡ 𝓜 e₂

  soundness : ∀ {Γ a} {T : Theory Γ} {𝓜 : Denotation} {e e′ : Expr Γ a} →
    𝓜 ⊨ T →
    e′ ∈Theory⟦ T ⟧ e →
    𝓜 e ≡ 𝓜 e′
  soundness models (Theory-Rewrite (▷Rewrite-eq x) x₁) =
    let
        w = is-eqn′ x₁ x
        z = models w
    in
    sym z

  is-complete : ∀ {Γ} → (𝓜 : Denotation) → Theory Γ → Set
  is-complete {Γ} 𝓜 T = ∀ {a} {e₁ e₂ : Expr Γ a} →
    𝓜 e₁ ≡ 𝓜 e₂ → (T ▷ e₁ ≐ e₂)
