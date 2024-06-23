{-# OPTIONS --safe #-}
module Cubical.Categories.Profunctor.Hom where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Profunctor.Relator
open import Cubical.Categories.Profunctor.Homomorphism.Unary
open import Cubical.Categories.Bifunctor.Redundant as Bif

private
  variable
    ℓB ℓB' ℓC ℓC' ℓD ℓD' ℓS ℓR ℓQ : Level

Hom : (C : Category ℓC ℓC') → C o-[ ℓC' ]-* C
Hom = HomBif

NatElt→NatTrans :
  {C : Category ℓC ℓC'} {D : Category ℓD ℓD'}
  {F : Functor C D}{G : Functor C D}
  → NatElt (Hom D ∘Flr (F ^opF , G)) → NatTrans F G
NatElt→NatTrans ε .NatTrans.N-ob = ε .NatElt.N-ob
NatElt→NatTrans ε .NatTrans.N-hom = NatElt.N-LR-agree ε

module _ {C : Category ℓC ℓC'} {R : C o-[ ℓR ]-* C} where
  open NatElt
  open Homomorphism
  rec : NatElt R → Homomorphism (Hom C) R
  rec n .hom = n .N-hom×
  rec n .natL f r = sym (N-hom×-fuseL n f r)
  rec n .natR r h = sym (N-hom×-fuseR n r h)
