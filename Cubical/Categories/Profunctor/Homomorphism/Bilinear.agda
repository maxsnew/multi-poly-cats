{-# OPTIONS --safe #-}
module Cubical.Categories.Profunctor.Homomorphism.Bilinear where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
open import Cubical.Categories.Category
open import Cubical.Categories.Profunctor.Relator

private
  variable
    ℓB ℓB' ℓC ℓC' ℓD ℓD' ℓS ℓR ℓQ : Level

module _ {B : Category ℓB ℓB'}
         {C : Category ℓC ℓC'}
         {D : Category ℓD ℓD'} where
  record Bilinear (Q : B o-[ ℓQ ]-* C)
                  (R : C o-[ ℓR ]-* D)
                  (S : B o-[ ℓS ]-* D)
         : Type (ℓ-max (ℓ-max ℓB ℓB')
                (ℓ-max (ℓ-max ℓC ℓC')
                (ℓ-max (ℓ-max ℓD ℓD')
                (ℓ-max ℓQ (ℓ-max ℓR ℓS))))) where
    field
      hom : ∀ {b c d} → Q [ b , c ]R → R [ c , d ]R → S [ b , d ]R
      natL : ∀ {b b' c d} (f : B [ b , b' ]) q (r : R [ c , d ]R)
           → hom (f ⋆l⟨ Q ⟩ q ) r ≡ f ⋆l⟨ S ⟩ hom q r
      natM : ∀ {b c c' d} (q : Q [ b , c ]R) g (r : R [ c' , d ]R)
           → hom (q ⋆r⟨ Q ⟩ g) r ≡ hom q (g ⋆l⟨ R ⟩ r)
      natR : ∀ {b c d d'} (q : Q [ b , c ]R) r (h : D [ d , d' ])
           → hom q (r ⋆r⟨ R ⟩ h) ≡ hom q r ⋆r⟨ S ⟩ h
