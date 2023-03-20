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

-- variable D-eq-dec

module _ (D : Set) where
  Denotation : Set
  Denotation = ∀ {Γ a} → Expr Γ a → D

  _⊨_ : ∀ {Γ} → (𝓜 : Denotation) → Theory Γ → Set
  _⊨_ {Γ} 𝓜 T = ∀ {a} (e₁ e₂ : Expr Γ a) →
    (T ▷ e₁ ≐ e₂) → 𝓜 e₁ ≡ 𝓜 e₂

  is-complete : ∀ {Γ} → (𝓜 : Denotation) → Theory Γ → Set
  is-complete {Γ} 𝓜 T = ∀ {a} {e₁ e₂ : Expr Γ a} →
    𝓜 e₁ ≡ 𝓜 e₂ → (T ▷ e₁ ≐ e₂)

