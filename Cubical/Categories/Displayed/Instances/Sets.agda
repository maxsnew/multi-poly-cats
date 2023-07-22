{-# OPTIONS --safe #-}
module Cubical.Categories.Displayed.Instances.Sets where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Structure
open import Cubical.Data.Sigma

open import Cubical.Categories.Category
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Category.More
open import Cubical.Categories.Displayed.Functor

private
  variable
    ℓ ℓ' ℓ'' ℓ''' : Level
    ℓC ℓC' ℓD ℓD' : Level

module _ ℓ ℓ' where
  open Categoryᴰ
  SETS : Categoryᴰ (SET ℓ) (ℓ-max ℓ (ℓ-suc ℓ')) (ℓ-max ℓ ℓ')
  SETS .ob[_] X = ⟨ X ⟩ → hSet ℓ'
  SETS .Hom[_][_,_] f P Q = ∀ x → ⟨ P x ⟩ → ⟨ Q (f x) ⟩
  SETS .idᴰ = λ x z → z
  SETS ._⋆ᴰ_ {f = f} {g} fᴰ gᴰ x p = gᴰ (f x) (fᴰ x p)
  SETS .⋆IdLᴰ fᴰ = refl
  SETS .⋆IdRᴰ fᴰ = refl
  SETS .⋆Assocᴰ fᴰ gᴰ hᴰ = refl
  SETS .isSetHomᴰ {yᴰ = Q} = isSetΠ λ x → isSetΠ λ xᴰ → Q _ .snd

open Category
open Functorᴰ
-- Displayed representable
_[-][-,_] : {C : Category ℓC ℓC'} (D : Categoryᴰ C ℓD ℓD')
          → {c : C .ob}
          → Categoryᴰ.ob[_] D c
          → Functorᴰ (C [-, c ]) (D ^opᴰ) (SETS ℓC' ℓD')
_[-][-,_] {C = C} D {c} d .F-obᴰ d' f =
  (D [ f ][ d' , d ]) , Categoryᴰ.isSetHomᴰ D
_[-][-,_] {C = C} D {c} d .F-homᴰ fᴰ g gᴰ = Categoryᴰ._⋆ᴰ_ D fᴰ gᴰ
_[-][-,_] {C = C} D {c} d .F-idᴰ i g gᴰ = Categoryᴰ.⋆IdLᴰ D gᴰ i
_[-][-,_] {C = C} D {c} d .F-seqᴰ fᴰ gᴰ i h hᴰ = Categoryᴰ.⋆Assocᴰ D gᴰ fᴰ hᴰ i

-- Displayed representable
_[-][_,-] : {C : Category ℓC ℓC'} (D : Categoryᴰ C ℓD ℓD')
          → {c : C .ob}
          → Categoryᴰ.ob[_] D c
          → Functorᴰ (C [ c ,-]) D (SETS ℓC' ℓD')
(D [-][ d ,-]) .F-obᴰ d' f = (D [ f ][ d , d' ]) , Categoryᴰ.isSetHomᴰ D
(D [-][ d ,-]) .F-homᴰ fᴰ g gᴰ = Categoryᴰ._⋆ᴰ_ D gᴰ fᴰ
(D [-][ d ,-]) .F-idᴰ i f fᴰ = Categoryᴰ.⋆IdRᴰ D fᴰ i
(D [-][ d ,-]) .F-seqᴰ fᴰ gᴰ i h hᴰ = Categoryᴰ.⋆Assocᴰ D hᴰ fᴰ gᴰ (~ i)
