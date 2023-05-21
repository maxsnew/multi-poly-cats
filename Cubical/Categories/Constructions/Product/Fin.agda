-- Finite Product of categories as flattened lists
{-# OPTIONS --safe #-}
module Cubical.Categories.Constructions.Product.Fin where


open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma
open import Cubical.Data.Nat
open import Cubical.Data.List
open import Cubical.Data.List.Dependent
open import Cubical.Data.Fin
open import Cubical.Categories.Category.Base

private
  variable
    ℓ ℓ' : Level

open Category

module _ (Cs : List (Category ℓ ℓ')) where
  FPOb : Type _
  FPOb = ListP ob Cs

  FPHom : FPOb → FPOb → Type _
  FPHom xs ys = {!!}

-- FinProduct : Category (ℓ-max (ℓ-suc ℓ) (ℓ-suc ℓ')) {!!}
-- FinProduct Cs .ob = 
-- FinProduct Cs .Hom[_,_] xs ys = {!!} where
-- FinProduct Cs .id = {!!}
-- FinProduct Cs ._⋆_ = {!!}
-- FinProduct Cs .⋆IdL = {!!}
-- FinProduct Cs .⋆IdR = {!!}
-- FinProduct Cs .⋆Assoc = {!!}
-- FinProduct Cs .isSetHom = {!!}
