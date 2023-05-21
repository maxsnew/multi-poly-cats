{-# OPTIONS --safe #-}
module Cubical.Categories.Constructions.Product.More where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure
open import Cubical.Categories.Category
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Functor
open import Cubical.Categories.Constructions.Product

private
  variable
    ℓA ℓC ℓC' ℓD ℓD' : Level
open Functor
module _ (A : Type ℓA) (catC : A → Category ℓC ℓC') where
  Π-intro : {D : Category ℓD ℓD'} → (∀ (a : A) → Functor D (catC a)) → Functor D (ΠC A catC)
  Π-intro Fs .Functor.F-ob d a = Fs a ⟅ d ⟆
  Π-intro Fs .Functor.F-hom f a = Fs a ⟪ f ⟫
  Π-intro Fs .Functor.F-id = funExt (λ a → Fs a .F-id)
  Π-intro Fs .Functor.F-seq f g = funExt (λ a → Fs a .F-seq f g)

-- TODO: if each of the catCs is univalent then so is the product
