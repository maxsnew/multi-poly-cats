{-# OPTIONS --safe #-}
module Cubical.Categories.Limits.Cartesian.Functor where

open import Cubical.Foundations.Prelude
open import Cubical.Categories.Limits.Cartesian.Base
open import Cubical.Categories.Functor.Base
open import Cubical.Categories.Limits.BinProduct
open import Cubical.Categories.Category

private
  variable
    ℓC ℓC' : Level
    ℓD ℓD' : Level

module _ (C : Category ℓC ℓC')(D : Category ℓD ℓD') where
    open BinProduct
    PreservesProducts : Functor C D → Type _
    PreservesProducts F = ∀ Γ Δ → (p : BinProduct C Γ Δ) →
      isBinProduct {_} {_} D {F ⟅ Γ ⟆} {F ⟅ Δ ⟆} {F ⟅ p .binProdOb ⟆} (F ⟪ p .binProdPr₁ ⟫) (F ⟪ p .binProdPr₂ ⟫)
    --PreservesTerminal : Functor C D → Type _
    --PreservesTerminal F = Terminal (F ⟅ C .terminal ⟆)
    CartesianFunctor : Type _
    CartesianFunctor = Σ[ F ∈ Functor C D ] PreservesProducts F

--CartesianFunctor : CartesianCategory ℓC ℓC' → CartesianCategory ℓD ℓD' → Type _
--CartesianFunctor CC DD =
--  Σ[ F ∈ Functor (CC .fst) (DD .fst) ] PreservesProducts (CC .fst) (DD .fst) F
