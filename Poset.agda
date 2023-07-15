module Poset where

open import Level
open import Relation.Binary
open import Categories.Monad
open import Categories.Category
open import Categories.Category.Construction.Thin
open import Categories.Functor renaming (id to Id)
open import Categories.NaturalTransformation
open import Data.Product renaming (_×_ to _∧_)
open import Agda.Builtin.Unit

private
    variable
        o ℓ₁ ℓ₂ e : Level


-- Definining a closure operator on a poset
record Closure (𝑃 : Poset o ℓ₁ ℓ₂) : Set (o ⊔ ℓ₁ ⊔ ℓ₂) where
    open Poset 𝑃 using (Carrier; _≤_; _≈_)
    field
        T : Carrier → Carrier
        extensiveness : ∀ {X : Carrier} → X ≤ T X
        monotonicity : ∀ {X Y : Carrier} → X ≤ Y → T X ≤ T Y
        idempotence : ∀ {X : Carrier} → T (T X) ≈ T X


--*
-- Proposition: closure operators on posets are equivalent to monads on the corresponding thin category
--* 

-- '→'
Closure→Monad : ∀ {𝑃 : Poset o ℓ₁ ℓ₂} → Closure 𝑃 → Monad {o} {ℓ₂} {e} (Thin e 𝑃)
Closure→Monad {𝑃 = 𝑃} T = record 
    { F = F
    ; η = η'
    ; μ = μ'

    ; assoc = λ {X} → lift tt
    ; sym-assoc = λ {X} → lift tt
    ; identityˡ = λ {X} → lift tt
    ; identityʳ = λ {X} → lift tt
    }
    where
        open Closure T renaming (T to T₀)
        open Poset 𝑃 using (Carrier; _≤_; _≈_; reflexive)
        F = record
            { F₀ = T₀
            ; F₁ = monotonicity
            ; identity = lift tt
            ; homomorphism = lift tt
            ; F-resp-≈ = λ {A} {B} {f} {g} _ → lift tt
            }
        η' = ntHelper {F = Id} {G = F} record
            { η = λ X → extensiveness
            ; commute = λ {X} {Y} f → lift tt
            }
        μ' = ntHelper {F = F ∘F F} {G = F} record
            { η = λ X → reflexive idempotence
            ; commute = λ {X} {Y} f → lift tt
            }
        open NaturalTransformation η'
        open NaturalTransformation μ' renaming (η to μ)


-- '←'
Monad→Closure : ∀ {𝑃 : Poset o ℓ₁ ℓ₂} → Monad {o} {ℓ₂} {e} (Thin e 𝑃) → Closure 𝑃
Monad→Closure {𝑃 = 𝑃} 𝑀 = record
    { T = F₀
    ; extensiveness = λ {X} → η.η X
    ; monotonicity = F₁
    ; idempotence = λ {X} → antisym (μ.η X) (η.η (F₀ X))
    }
    where
        open Poset 𝑃
        open Monad 𝑀
        open Functor F

-- full proof
Closure↔Monad : ∀ {𝑃 : Poset o ℓ₁ ℓ₂} → (Closure 𝑃 → Monad {o} {ℓ₂} {e} (Thin e 𝑃)) ∧ (Monad {o} {ℓ₂} {e} (Thin e 𝑃) → Closure 𝑃)
Closure↔Monad = Closure→Monad , Monad→Closure