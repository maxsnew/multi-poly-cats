{-# OPTIONS --safe #-}
module Cubical.Categories.Constructions.Free.CartesianCategory.ProductQuiver where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

module _ (ob : Type ℓ-zero) where
  data ProdExpr : Type (ℓ-suc ℓ-zero) where
    ↑_ : ob → ProdExpr
    _×_ : ProdExpr → ProdExpr → ProdExpr
    ⊤ : ProdExpr
  record ProductQuiver : Type (ℓ-suc ℓ-zero) where
    field
      mor : Type ℓ-zero
      dom : mor → ProdExpr
      cod : mor → ProdExpr

×Quiver : Type (ℓ-suc ℓ-zero)
×Quiver = Σ[ ob ∈ Type ℓ-zero ] ProductQuiver ob

module ×Quiver-Nice (Q : ×Quiver) where
  open ProductQuiver
  Ob = ProdExpr (Q .fst)
  Dom = Q .snd .dom
  Cod = Q .snd .cod
