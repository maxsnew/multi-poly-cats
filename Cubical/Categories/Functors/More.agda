{-# OPTIONS --safe #-}

module Cubical.Categories.Functors.More where

open import Cubical.Foundations.Prelude
open import Cubical.Categories.Category
open import Cubical.Categories.Functor.Base
open import Cubical.Categories.Functors.Constant

private
  variable
    ℓC ℓC' ℓD ℓD' : Level

open Category
open Functor

ConstantComposeFunctor :
  (C : Category ℓC ℓC') (D : Category ℓD ℓD' ) (c : C .ob)
  (F : Functor C D) →
  Constant (D ^op) D (F .F-ob c) ≡ F ∘F Constant (D ^op) C c
ConstantComposeFunctor C D c F = Functor≡
  (λ c → ( refl ))
    (λ f → (
      D .id
     ≡⟨ sym (F .F-id) ⟩
       F ⟪ Constant (D ^op) C c ⟪ f ⟫ ⟫ ∎
  ))

-- The data of a functor, parameterized by the action on objects
record ActionOnMorphisms
  (C : Category ℓC ℓC')
  (D : Category ℓD ℓD')
  (F₀ : C .ob → D .ob) : Type (ℓ-max (ℓ-max ℓC ℓC') ℓD') where
  no-eta-equality

  open Category

  field
    F-hom : {x y : C .ob} → C [ x , y ] → D [ F₀ x , F₀ y ]
    F-id  : {x : C .ob} → F-hom (C .id) ≡ D .id {x = F₀ x}
    F-seq : {x y z : C .ob} (f : C [ x , y ]) (g : C [ y , z ])
          → F-hom (f ⋆⟨ C ⟩ g) ≡ (F-hom f) ⋆⟨ D ⟩ (F-hom g)

open ActionOnMorphisms

ActionOnMorphisms→Functor :
  {C : Category ℓC ℓC'} {D : Category ℓD ℓD'}{F₀ : C .ob → D .ob}
                          → ActionOnMorphisms C D F₀
                          → Functor C D
ActionOnMorphisms→Functor {F₀ = F₀} F₁ .F-ob = F₀
ActionOnMorphisms→Functor {F₀ = F₀} F₁ .F-hom = F₁ .F-hom
ActionOnMorphisms→Functor {F₀ = F₀} F₁ .F-id = F₁ .F-id
ActionOnMorphisms→Functor {F₀ = F₀} F₁ .F-seq = F₁ .F-seq
