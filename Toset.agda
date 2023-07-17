open import Level


module Toset {o ℓ₁ ℓ₂ e : Level} where

open import Relation.Binary using (TotalOrder)
open import Categories.Monad
open import Categories.Monad.Strong
open import Categories.Category
open import Categories.Category.Product
open import Categories.Category.Cartesian
open import Categories.Category.Cartesian.Monoidal
open import Categories.Category.Monoidal
open import Categories.Category.Construction.Thin
open import Categories.Functor renaming (id to Id)
open import Categories.NaturalTransformation
open import Categories.Object.Product
open import Data.Product renaming (_×_ to _∧_)
open import Data.Sum
open import Agda.Builtin.Unit
open import Poset
import Relation.Binary.PropositionalEquality as PEq

--*
-- Proof that in the category 𝐶 induced by a total order 𝑇 every monad is strong (if there exists a terminal object!)
--*

module _ (𝑇 : TotalOrder o ℓ₁ ℓ₂) where
    open TotalOrder 𝑇 renaming (poset to 𝑃)
    open Category (Thin e 𝑃) renaming (id to idC)

    --*
    -- First we identify products in thin categories then we proof that if there exists a terminal object (i.e. if the toset is bounded)
    -- the thin category is cartesian
    --*

    module _ {⊤ : Carrier} (max : ∀ {X} → X ≤ ⊤) where
        ThinCartesian : Cartesian (Thin e 𝑃)
        ThinCartesian = record 
            { terminal = record
                { ⊤ = ⊤
                ; ⊤-is-terminal = record
                    { ! = max
                    ; !-unique = λ {A} f → lift tt
                    }
                }
            ; products = record
                { product = λ {A} {B} → record
                    { A×B = get-A×B A B
                    ; π₁ = get-π₁
                    ; π₂ = get-π₂
                    ; ⟨_,_⟩ = get-⟨⟩
                    ; project₁ = lift tt
                    ; project₂ = lift tt
                    ; unique = λ {j₁} {h} {i} {j} _ _ → lift tt
                    }
                }
            }
            where
                open Equiv using () renaming (refl to Crefl)
                get-A×B : Carrier → Carrier → Carrier 
                get-A×B A B with (total A B)
                ... | inj₁ A≤B = A
                ... | inj₂ B≤A = B
                get-π₁ : ∀ {A B} → (get-A×B A B) ≤ A 
                get-π₁ {A} {B} with (total A B)
                ... | inj₁ H = refl
                ... | inj₂ H = H
                get-π₂ : ∀ {A B} → (get-A×B A B) ≤ B 
                get-π₂ {A} {B} with (total A B)
                ... | inj₁ H = H
                ... | inj₂ H = refl
                get-⟨⟩ : ∀ {A B C} (f : C ≤ A) (g : C ≤ B) → C ≤ get-A×B A B
                get-⟨⟩ {A} {B} {C} f g with (total A B)
                ... | inj₁ H = f
                ... | inj₂ H = g

        -- a cartesian category is always monoidal, we need the monoidal property for strong monad
        open CartesianMonoidal ThinCartesian using (monoidal)


        --*
        -- The actual proof that every monad is a strong monad
        -- We only need to construct the natural transformation strength, every other proof is for free
        --*
        
        module _ (T : Closure 𝑃) where
            Monad→StrongMonad : Monad (Thin e 𝑃) → StrongMonad {C = Thin e 𝑃} monoidal
            Monad→StrongMonad 𝑀 = record 
                { M = 𝑀
                ; strength = record 
                    { strengthen = ntHelper record
                        { η = λ where
                            (A , B) → helper A B
                        ; commute = λ {X} {Y} f → lift tt
                        }
                    ; identityˡ = λ {A} → lift tt
                    ; η-comm = λ {A} {B} → lift tt
                    ; μ-η-comm = λ {A} {B} → lift tt
                    ; strength-assoc = λ {A} {B} {C} → lift tt
                    }
                }
                where 
                    open Monad 𝑀
                    open Functor F
                    open Monoidal monoidal
                    open Closure (Monad→Closure {𝑃 = 𝑃} 𝑀)
                    -- The helper takes two object (of the product (A,B)) and constructs the strength morphism. 
                    -- For this we need to destruct A ≤ B and A ≤ (F₀ B)
                    helper : (A : Carrier) → (B : Carrier) → Functor.₀ (⊗ ∘F (Id ⁂ F)) (A , B) ⇒ ₀ (Functor.₀ ⊗ (A , B))
                    helper A B with (total A B) | (total A (F₀ B))
                    ... | inj₁ H | inj₁ H0 = trans refl extensiveness
                    ... | inj₂ H | inj₁ H0 = H0
                    ... | inj₁ H | inj₂ H0 = trans H0 extensiveness
                    ... | inj₂ H | inj₂ H0 = refl