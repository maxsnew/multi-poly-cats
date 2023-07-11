{-# OPTIONS --safe #-}
module Cubical.Categories.Limits.Terminal.More where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.HITs.PropositionalTruncation.Base
open import Cubical.Data.Sigma

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Isomorphism
open import Cubical.Categories.Limits.Terminal

private
  variable
    ℓ ℓ' ℓc ℓc' ℓd ℓd' : Level

preservesTerminal : ∀ (C : Category ℓc ℓc')(D : Category ℓd ℓd')
                  → Functor C D
                  → Type (ℓ-max (ℓ-max (ℓ-max ℓc ℓc') ℓd) ℓd')
preservesTerminal C D F = ∀ (One : Terminal C) → isTerminal D (F ⟅ One .fst ⟆)


preserveOnePreservesAll : ∀ (C : Category ℓc ℓc')(D : Category ℓd ℓd')
                        → (F : Functor C D)
                        → (One : Terminal C) → isTerminal D (F ⟅ One .fst ⟆)
                        → preservesTerminal C D F
preserveOnePreservesAll C D F One D-preserves-One One' =
  isoToTerminal D
                ((F ⟅ One .fst ⟆) , D-preserves-One) (F ⟅ One' .fst ⟆)
                (F-Iso {F = F} (terminalToIso C One One'))

module TerminalNotation (C : Category ℓ ℓ') (term : Terminal C) where
  𝟙 = term .fst

  !t : ∀ {a} → C [ a , 𝟙 ]
  !t = terminalArrow C term _

  𝟙η : ∀ {a} → (f : C [ a , 𝟙 ]) → f ≡ !t
  𝟙η f = sym (terminalArrowUnique C {T = term} f)

  𝟙η' : ∀ {a} → {f g : C [ a , 𝟙 ]} → f ≡ g
  𝟙η' = 𝟙η _ ∙ sym (𝟙η _)
