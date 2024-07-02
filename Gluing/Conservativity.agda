{-# OPTIONS --lossy-unification #-}
module Gluing.Conservativity where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Data.Quiver.Base
open import Cubical.Data.Unit

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Yoneda
open import Cubical.Categories.Presheaf
open import Cubical.Categories.Limits.Terminal
open import Cubical.Categories.Limits.BinProduct

open import Cubical.Categories.Constructions.Free.Category.Quiver as FC
  hiding (rec)
open import Cubical.Categories.Constructions.Free.CartesianCategory.Base as FCC
  hiding (rec)
open import
  Cubical.Categories.Constructions.Free.CartesianCategory.ProductQuiver
open import Cubical.Categories.Limits.Cartesian.Base

private
  variable ℓQ ℓQ' ℓC ℓC' : Level

open Functor

Quiver→×Quiver : ∀{ℓ ℓ' : Level} → Quiver ℓ ℓ' → ×Quiver ℓ ℓ'
Quiver→×Quiver Q .fst = Q .fst
Quiver→×Quiver Q .snd .ProductQuiver.mor = Q .snd .QuiverOver.mor
Quiver→×Quiver Q .snd .ProductQuiver.dom = ↑_ ∘S Q .snd .QuiverOver.dom
Quiver→×Quiver Q .snd .ProductQuiver.cod = ↑_ ∘S Q .snd .QuiverOver.cod

module _ (Q : Quiver ℓQ ℓQ') where
  FREE : Category _ _
  FREE = FreeCat Q

  FREE-1,× : CartesianCategory _ _
  FREE-1,× = FreeCartesianCategory (Quiver→×Quiver Q)

  ı : Interp Q (FREE-1,× .fst)
  ı ._$g_ = ↑_
  ı ._<$g>_ = ↑ₑ_

  ⊆ : Functor FREE (FREE-1,× .fst)
  ⊆ = FC.rec Q ı

  -- TODO: wts ⊆* is fully faithful

  -- TODO: I think Eric Bond has these?
  -- I don't really want to bang these out when
  -- 1) someone else has already done it
  -- 2) it should follow from more general reasons (all limits)
  postulate
    presheafTerminal : (C : Category ℓC ℓC')(ℓ : Level) → Terminal (PresheafCategory C ℓ)
    presheafBinProducts : (C : Category ℓC ℓC')(ℓ : Level) → BinProducts (PresheafCategory C ℓ)

  -- the use of rec to define the functor is just to save work
  extension : Functor (FREE-1,× .fst) (PresheafCategory FREE _)
  extension = FCC.rec (Quiver→×Quiver Q)
    (PresheafCategory FREE _ , presheafTerminal _ _ , presheafBinProducts _ _)
    (λ A → YO ⟅ A ⟆)
    λ f → YO ⟪ ↑ f ⟫

  commutes : YO ≡ extension ∘F ⊆
  commutes = FreeCatFunctor≡ Q _ _
    (record { _$gᴰ_ = λ _ → refl ; _<$g>ᴰ_ = λ _ → refl })

  comp-Faithful : isFaithful (extension ∘F ⊆)
  comp-Faithful = subst isFaithful commutes isFaithfulYO

  -- TODO: move this general fact about isFaithful if it isn't already in stdlib
  module _ {ℓA ℓA' ℓB ℓB' ℓC ℓC'}
    {A : Category ℓA ℓA'}{B : Category ℓB ℓB'}{C : Category ℓC ℓC'}
    (F : Functor A B)(G : Functor B C) where
    isFaithful-GF→isFaithful-F : isFaithful (G ∘F F) → isFaithful F
    isFaithful-GF→isFaithful-F faith x y f g p = faith x y f g (congS (λ Ff → G ⟪ Ff ⟫) p)

  ⊆-Faithful : isFaithful ⊆
  ⊆-Faithful = isFaithful-GF→isFaithful-F ⊆ extension comp-Faithful

  ⊆-Full : isFull ⊆
  ⊆-Full = {!!}

  ⊆-FullyFaithful : isFullyFaithful ⊆
  ⊆-FullyFaithful = isFull+Faithful→isFullyFaithful {F = ⊆} ⊆-Full ⊆-Faithful

  ----------------------------------------
  -- graveyard
  ----------------------------------------
  --
  --module _ {C : Category ℓC ℓC'}{ℓ : Level} where
  --  terminal-presheaf : Presheaf C ℓ
  --  terminal-presheaf .F-ob _ = Unit* , isSetUnit*
  --  terminal-presheaf .F-hom _ = λ x → x
  --  terminal-presheaf .F-id = refl
  --  terminal-presheaf .F-seq _ _ = refl
  --
  --bleh : Functor (FREE-1,× .fst) (PresheafCategory FREE _)
  --bleh .F-ob (↑ A) = YO ⟅ A ⟆
  --bleh .F-ob (Γ × Δ) = terminal-presheaf
  --bleh .F-ob ⊤ = terminal-presheaf
  --bleh .F-hom {↑ x} {↑ y} (↑ₑ f) = YO ⟪ ↑ f ⟫
  --bleh .F-hom {↑ x} {↑ y} f = {!!}
  --bleh .F-hom {x} {y} f = {!!}
  --bleh .F-id = {!!}
  --bleh .F-seq = {!!}
