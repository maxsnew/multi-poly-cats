{-# OPTIONS --safe #-}
module Cubical.Categories.Profunctor.Homomorphism.Unary where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Structure
open import Cubical.Categories.Category
open import Cubical.Categories.Profunctor.Relator

private
  variable
    ℓB ℓB' ℓC ℓC' ℓD ℓD' ℓS ℓR ℓQ : Level

module _ {C : Category ℓC ℓC'}
         {D : Category ℓD ℓD'} where
  record Homomorphism (R : C o-[ ℓR ]-* D)
                      (S : C o-[ ℓS ]-* D)
         : Type (ℓ-max (ℓ-max ℓC ℓC')
                (ℓ-max (ℓ-max ℓD ℓD')
                (ℓ-max ℓR ℓS))) where
    field
      hom : ∀ {c d} → R [ c , d ]R → S [ c , d ]R
      natL : ∀ {c' c d} (f : C [ c , c' ]) (r : R [ c' , d ]R)
           → hom (f ⋆l⟨ R ⟩ r ) ≡ f ⋆l⟨ S ⟩ hom r
      natR : ∀ {c d d'} (r : R [ c , d ]R) (h : D [ d , d' ])
           → hom (r ⋆r⟨ R ⟩ h) ≡ hom r ⋆r⟨ S ⟩ h

  open Homomorphism

  isIsoH : ∀ {R : C o-[ ℓR ]-* D} {S : C o-[ ℓS ]-* D}
        → Homomorphism R S → Type _
  isIsoH h = ∀ {c d} → isEquiv (h .hom {c}{d})
