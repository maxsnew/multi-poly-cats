{-# OPTIONS --safe #-}
module Cubical.Categories.Yoneda.More where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Univalence using (ua)
open import Cubical.Foundations.Function renaming (_∘_ to _◍_)
open import Cubical.Data.Sigma
open import Cubical.Foundations.Equiv
open import Cubical.HITs.PropositionalTruncation

open import Cubical.Categories.Category
open import Cubical.Categories.Constructions.Lift
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Instances.Functors
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Functor
open import Cubical.Categories.Presheaf.Base

open import Cubical.Categories.Instances.Sets.More
open import Cubical.Categories.Yoneda

private
  variable
    ℓ ℓ' ℓ'' : Level

-- THE YONEDA LEMMA

open NatTrans
open NatTransP
open Functor
open Iso

-- Yoneda for contravariant functors
module _ {C : Category ℓ ℓ'} where
  open Category
  import Cubical.Categories.NaturalTransformation
  open NatTrans
  yonedaᴾ : (F : Functor (C ^op) (SET ℓ'))
          → (c : C .ob)
          → Iso ((FUNCTOR (C ^op) (SET ℓ')) [ C [-, c ] , F ]) (fst (F ⟅ c ⟆))
  yonedaᴾ F c =
    ((FUNCTOR (C ^op) (SET ℓ')) [ C [-, c ] , F ]) Iso⟨ the-iso ⟩
    FUNCTOR (C ^op) (SET ℓ') [ (C ^op) [ c ,-] , F ] Iso⟨ yoneda F c ⟩
    (fst (F ⟅ c ⟆)) ∎Iso where

    to : FUNCTOR (C ^op) (SET ℓ') [ C [-, c ] , F ] → FUNCTOR (C ^op) (SET ℓ') [ (C ^op) [ c ,-] , F ]
    to α = natTrans (α .N-ob) (α .N-hom)

    fro : FUNCTOR (C ^op) (SET ℓ') [ (C ^op) [ c ,-] , F ] → FUNCTOR (C ^op) (SET ℓ') [ C [-, c ] , F ]
    fro β = natTrans (β .N-ob) (β .N-hom)

    the-iso : Iso (FUNCTOR (C ^op) (SET ℓ') [ C [-, c ] , F ])
              (FUNCTOR (C ^op) (SET ℓ') [ (C ^op) [ c ,-] , F ])
    the-iso = iso to fro (λ b → refl) λ a → refl

-- A more universe-polymorphic Yoneda lemma
yoneda* : {C : Category ℓ ℓ'}(F : Functor C (SET ℓ''))
        → (c : Category.ob C)
        → Iso ((FUNCTOR C (SET (ℓ-max ℓ' ℓ''))) [ LiftF {ℓ'}{ℓ''} ∘F (C [ c ,-]) , LiftF {ℓ''}{ℓ'} ∘F F ]) (fst (F ⟅ c ⟆))
yoneda* {ℓ}{ℓ'}{ℓ''}{C} F c =
  ((FUNCTOR C (SET (ℓ-max ℓ' ℓ''))) [ LiftF {ℓ'}{ℓ''} ∘F (C [ c ,-]) , LiftF {ℓ''}{ℓ'} ∘F F ])
    Iso⟨ the-iso ⟩
  ((FUNCTOR (LiftHoms C ℓ'') (SET (ℓ-max ℓ' ℓ''))) [ (LiftHoms C ℓ'' [ c ,-]) , LiftF {ℓ''}{ℓ'} ∘F (F ∘F lowerHoms C ℓ'') ])
    Iso⟨ yoneda (LiftF {ℓ''}{ℓ'} ∘F (F ∘F lowerHoms C ℓ'')) c ⟩
  Lift {ℓ''}{ℓ'} (fst (F ⟅ c ⟆))
    Iso⟨ invIso LiftIso ⟩
  (fst (F ⟅ c ⟆)) ∎Iso where

  the-iso : Iso ((FUNCTOR C (SET (ℓ-max ℓ' ℓ''))) [ LiftF {ℓ'}{ℓ''} ∘F (C [ c ,-]) , LiftF {ℓ''}{ℓ'} ∘F F ]) ((FUNCTOR (LiftHoms C ℓ'') (SET (ℓ-max ℓ' ℓ''))) [ (LiftHoms C ℓ'' [ c ,-]) , LiftF {ℓ''}{ℓ'} ∘F (F ∘F lowerHoms C ℓ'') ])
  the-iso .fun α .N-ob d f = α .N-ob d f
  the-iso .fun α .N-hom g = α .N-hom (g .lower)
  the-iso .inv β .N-ob d f = β .N-ob d f
  the-iso .inv β .N-hom g = β .N-hom (lift g)
  the-iso .rightInv β = refl
  the-iso .leftInv α = refl

yonedaᴾ* : {C : Category ℓ ℓ'}(F : Functor (C ^op) (SET ℓ''))
            → (c : Category.ob C)
            → Iso (FUNCTOR (C ^op) (SET (ℓ-max ℓ' ℓ'')) [ LiftF {ℓ'}{ℓ''} ∘F (C [-, c ]) , LiftF {ℓ''}{ℓ'} ∘F F ]) (fst (F ⟅ c ⟆))
yonedaᴾ* {ℓ}{ℓ'}{ℓ''}{C} F c =
  (FUNCTOR (C ^op) (SET (ℓ-max ℓ' ℓ'')) [ LiftF {ℓ'}{ℓ''} ∘F (C [-, c ]) , LiftF {ℓ''}{ℓ'} ∘F F ]) Iso⟨ the-iso ⟩
  (FUNCTOR (C ^op) (SET (ℓ-max ℓ' ℓ'')) [ LiftF {ℓ'}{ℓ''} ∘F ((C ^op) [ c ,-]) , LiftF {ℓ''}{ℓ'} ∘F F ]) Iso⟨ yoneda* F c ⟩
  fst (F ⟅ c ⟆) ∎Iso where

  the-iso :
    Iso (FUNCTOR (C ^op) (SET (ℓ-max ℓ' ℓ'')) [ LiftF {ℓ'}{ℓ''} ∘F (C [-, c ]) , LiftF {ℓ''}{ℓ'} ∘F F ])
        (FUNCTOR (C ^op) (SET (ℓ-max ℓ' ℓ'')) [ LiftF {ℓ'}{ℓ''} ∘F ((C ^op) [ c ,-]) , LiftF {ℓ''}{ℓ'} ∘F F ])
  the-iso .fun α .N-ob = α .N-ob
  the-iso .fun α .N-hom = α .N-hom
  the-iso .inv β .N-ob = β .N-ob
  the-iso .inv β .N-hom = β .N-hom
  the-iso .rightInv = λ b → refl
  the-iso .leftInv = λ a → refl
