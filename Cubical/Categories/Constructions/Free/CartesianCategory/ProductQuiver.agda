{-# OPTIONS --safe #-}
module Cubical.Categories.Constructions.Free.CartesianCategory.ProductQuiver
  where

open import Cubical.Foundations.Prelude

private variable ℓ ℓ' : Level

module _ (ob : Type ℓ) where
  data ProdExpr : Type ℓ where
    ↑_ : ob → ProdExpr
    _×_ : ProdExpr → ProdExpr → ProdExpr
    ⊤ : ProdExpr
  record ProductQuiver ℓ' : Type (ℓ-suc (ℓ-max ℓ ℓ')) where
    field
      mor : Type ℓ'
      dom : mor → ProdExpr
      cod : mor → ProdExpr

×Quiver : ∀ ℓ ℓ' → Type (ℓ-suc (ℓ-max ℓ ℓ'))
×Quiver ℓ ℓ' = Σ[ ob ∈ Type ℓ ] ProductQuiver ob ℓ'

module ×QuiverNotation (Q : ×Quiver ℓ ℓ') where
  open ProductQuiver
  Ob = ProdExpr (Q .fst)
  Dom = Q .snd .dom
  Cod = Q .snd .cod
