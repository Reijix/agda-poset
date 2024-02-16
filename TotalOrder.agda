module TotalOrder where

open import Level
open import Relation.Binary using (Poset; TotalOrder)
open import Categories.Monad
open import Categories.Monad.Strong
open import Categories.Category
open import Categories.Category.Construction.Thin
open import Categories.Category.Cartesian
open import Categories.Category.BinaryProducts
open import Categories.Object.Product
open import Categories.Object.Terminal
open import Categories.Functor renaming (id to Id)
open import Categories.NaturalTransformation
open import Categories.Category.Monoidal
open import Data.Product renaming (_×_ to _∧_)
open import Agda.Builtin.Unit
open import Poset
open import Data.Sum
open import Relation.Nullary

private
    variable
        o ℓ₁ ℓ₂ e : Level

Closure→Cartesian : ∀ {𝑃 : Poset o ℓ₁ ℓ₂} → (Closure 𝑃) → Cartesian (Thin _ 𝑃)
Closure→Cartesian {𝑃} Clo = record
    { terminal = record
        { ⊤ = _
        ; ⊤-is-terminal = _
        }
    ; products = _
    }
    where
        open Closure Clo

module _ (𝑇 : TotalOrder o ℓ₁ ℓ₂) where 
    -- Closure on total order
    open TotalOrder 𝑇 renaming (poset to 𝑃)
    TClosure : Set (o ⊔ ℓ₁ ⊔ ℓ₂)
    TClosure = Closure 𝑃

    postulate
        em : ∀ {A : Set ℓ₂} → A ⊎ ¬ A

    T-Product : ∀ (Clo : Closure 𝑃) (X Y : Carrier) → Product (Thin e 𝑃) X Y
    T-Product Clo X Y with em {X ≤ Y} in eq 
    ... | inj₁ x = {!   !}
    ... | inj₂ x = {!   !}
        where
            open Closure Clo


    -- TODO remove once certain that no prove needed
    Thin-Monoidal : Monoidal (Thin e 𝑃)
    Thin-Monoidal = monoidalHelper (Thin _ 𝑃) record
        { ⊗ = record
                { F₀ = λ p → {!   !}
                ; F₁ = _
                ; identity = _
                ; homomorphism = _
                ; F-resp-≈ = _
                }
        ; unit = _
        ; unitorˡ = _
        ; unitorʳ = _
        ; associator = _
        ; unitorˡ-commute = _
        ; unitorʳ-commute = _
        ; assoc-commute = _
        ; triangle = _
        ; pentagon = _
        }
    
    module _ (c : Cartesian (Thin e 𝑃)) where 
        AllMonadsStrong : Cartesian (Thin e 𝑃) → Monad (Thin e 𝑃) → (H : Monoidal (Thin e 𝑃)) → StrongMonad {C = (Thin e 𝑃)} H
        AllMonadsStrong Cart 𝑀 Mon = record
            { M = 𝑀
            ; strength = record
                { strengthen = ntHelper record
                    { η = λ X → {!   !}
                    ; commute = _
                    }
                ; identityˡ = _
                ; η-comm = _
                ; μ-η-comm = _
                ; strength-assoc = _
                }
            }
            where
                open Cartesian Cart
                open BinaryProducts products
                open Category (Thin _ 𝑃)
                open Equiv
                open Monad 𝑀
                open Functor F
                t : ∀ X Y → F₀ X × F₀ Y ⇒ F₀ (X × Y)
                t = _
