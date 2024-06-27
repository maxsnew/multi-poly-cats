{-# OPTIONS --safe #-}

module Cubical.Categories.Displayed.Constructions.HomPropertyOver where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Unit

open import Cubical.Categories.Category
open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Constructions.StructureOver

private
  variable
    ℓC ℓC' ℓH : Level

record HomPropertyOver (C : Category ℓC ℓC') ℓH :
  Type (ℓ-max (ℓ-max ℓC ℓC') (ℓ-suc ℓH)) where
  open Category C
  field
    Hom[_][-,-] : ∀ {x y} → Hom[ x , y ] → Type ℓH
    isPropHomᴰ : ∀ {x y} (f : Hom[ x , y ]) → isProp Hom[ f ][-,-]
    idᴰ : ∀ {x} → Hom[ id {x} ][-,-]
    _⋆ᴰ_ : ∀ {x y z} (f : Hom[ x , y ]) (g : Hom[ y , z ])
      → Hom[ f ][-,-] → Hom[ g ][-,-] → Hom[ f ⋆ g ][-,-]

module _ {C : Category ℓC ℓC'} (Pᴰ : HomPropertyOver C ℓH) where
  open Category C
  open HomPropertyOver Pᴰ
  HomPropertyOver→Catᴰ : Categoryᴰ C ℓ-zero ℓH
  HomPropertyOver→Catᴰ = StructureOver→Catᴰ struct where
    struct : StructureOver C ℓ-zero ℓH
    struct .StructureOver.ob[_] _ = Unit
    struct .StructureOver.Hom[_][_,_] f _ _ = Hom[ f ][-,-]
    struct .StructureOver.idᴰ = idᴰ
    struct .StructureOver._⋆ᴰ_ = _ ⋆ᴰ _
    struct .StructureOver.isPropHomᴰ = isPropHomᴰ _

module examples where
  open import Cubical.Categories.Constructions.TotalCategory

  open Category

  module _
    (C : Category ℓC ℓC')
    where

    open import Cubical.Categories.Isomorphism

    open Category C

    -- Given as an example of a wide subcategory on nlab:
    -- https://ncatlab.org/nlab/show/core+groupoid
    Coreᴰ : Categoryᴰ C ℓ-zero ℓC'
    Coreᴰ = HomPropertyOver→Catᴰ struct where
      open HomPropertyOver
      struct : HomPropertyOver C ℓC'
      struct .Hom[_][-,-] = isIso C
      struct .isPropHomᴰ = isPropIsIso
      struct .idᴰ = idCatIso .snd
      struct ._⋆ᴰ_ f g isIsof isIsog = compIso (g , isIsog) (f , isIsof) .snd

    Core : Category ℓC ℓC'
    Core = ∫C Coreᴰ

    private
      module Core = Category Core

    morCore→isIso : ∀ {x y} (f : Core [ x , y ]) → isIso C (f .fst)
    morCore→isIso f = f .snd

  module _ where
    open import Cubical.Data.Nat hiding (isEven ; isOdd)
    open import Cubical.Data.Bool
    open import Cubical.Data.Empty

    -- Natural numbers monoid as a one object monoid
    NatCat : Category ℓ-zero ℓ-zero
    NatCat .ob = Unit
    NatCat .Hom[_,_] _ _ = ℕ
    NatCat .id = 0
    NatCat ._⋆_ a b = a + b
    NatCat .⋆IdL _ = refl
    NatCat .⋆IdR _ = +-zero _
    NatCat .⋆Assoc f g h = sym (+-assoc f g h)
    NatCat .isSetHom = isSetℕ

    isEven : ℕ → Type
    isEven zero = Unit
    isEven (suc zero) = ⊥
    isEven (suc (suc x)) = isEven x

    isPropIsEven : (n : ℕ) → isProp (isEven n)
    isPropIsEven zero = isPropUnit
    isPropIsEven (suc zero) = isProp⊥
    isPropIsEven (suc (suc n)) = isPropIsEven n

    even-closed-under-+ :
      {x y z : Unit} (f : NatCat [ x , y ])
      (g : NatCat [ y , z ]) →
      isEven f → isEven g → isEven (f + g)
    even-closed-under-+ zero zero isEvenf isEveng = _
    even-closed-under-+ zero (suc (suc g)) isEvenf isEveng = isEveng
    even-closed-under-+ (suc (suc f)) zero isEvenf isEveng =
      transport (sym (cong isEven (+-zero f))) isEvenf
    even-closed-under-+ (suc (suc f)) (suc (suc g)) isEvenf isEveng =
      even-closed-under-+ f (suc (suc g)) isEvenf isEveng

    Evensᴰ : Categoryᴰ NatCat ℓ-zero ℓ-zero
    Evensᴰ = HomPropertyOver→Catᴰ struct where
      open HomPropertyOver
      struct : HomPropertyOver NatCat ℓ-zero
      struct .Hom[_][-,-] = isEven
      struct .isPropHomᴰ = isPropIsEven
      struct .idᴰ = _
      struct ._⋆ᴰ_ = even-closed-under-+

    -- The submonoid of even natural numbers
    Evens : Category ℓ-zero ℓ-zero
    Evens = ∫C Evensᴰ

    morEvens→Evenℕ : ∀ {a}{b} → Evens [ a , b ] → Σ[ n ∈ ℕ ] isEven n
    morEvens→Evenℕ f = f
