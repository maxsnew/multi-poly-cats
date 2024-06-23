{-

  The usual definition of a displayed category over C is *precisely*
  that of a lax functor from C to Span.

  The (equivalent) alternate definition provided here is instead
  *precisely* that of a normal lax functor from C to Prof. The main
  difference is in the lax functor definition, the fiber category over
  an object is not primitive, instead being defined as the

-}
module Cubical.Categories.Displayed.Alt where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv hiding (fiber)
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma
open import Cubical.Categories.Category.Base
open import Cubical.Categories.Constructions.Fiber
open import Cubical.Categories.Bifunctor.Redundant
open import Cubical.Categories.Functor
open import Cubical.Categories.Profunctor.Relator
open import Cubical.Categories.Profunctor.Hom
open import Cubical.Categories.Profunctor.Homomorphism.Unary
open import Cubical.Categories.Profunctor.Homomorphism.Bilinear


private
  variable
    ℓC ℓC' ℓCᴰ ℓCᴰ' ℓD ℓD' ℓDᴰ ℓDᴰ' : Level

open Bilinear
open Category
open NatElt

record Categoryᴰ (C : Category ℓC ℓC') ℓCᴰ ℓCᴰ'
  : Type (ℓ-suc (ℓ-max (ℓ-max ℓC ℓC') (ℓ-max ℓCᴰ ℓCᴰ'))) where
  no-eta-equality

  -- A displayed category consists of a *lax functor to Prof* that is
  -- *normal up to isomorphism*.

  field
    -- for each object, a fiber category over it
    fiber[_] : C .ob → Category ℓCᴰ ℓCᴰ'
    -- for each morphism, a *profunctor* of morphisms over it!
    Hom[_] : ∀ {x y} → C [ x , y ] → fiber[ x ] o-[ ℓCᴰ' ]-* fiber[ y ]
    -- this should laxly preserve the identity morphism
    idᴰh : ∀ {x} → NatElt Hom[ C .id {x} ]
    -- actually it should *strongly* preserve the identity morphism!
    idᴰh-normal : ∀ {x} → isIsoH (rec (idᴰh {x}))
    -- and it should laxly preserve the composition
    ⋆ᴰh : ∀ {x y z} → (f : C [ x , y ])(g : C [ y , z ])
        → Bilinear Hom[ f ] Hom[ g ] Hom[ f ⋆⟨ C ⟩ g ]

  ob[_] : C .ob → Type ℓCᴰ
  ob[ x ] = fiber[ x ] .ob

  Hom[_][_,_] : ∀ {x y} → C [ x , y ] → ob[ x ] → ob[ y ] → Type ℓCᴰ'
  Hom[ f ][ xᴰ , yᴰ ] = Hom[ f ] [ xᴰ , yᴰ ]R

  idᴰ : ∀ {x} {xᴰ : ob[ x ]} → Hom[ C .id ][ xᴰ , xᴰ ]
  idᴰ = idᴰh .N-ob _

  _⋆ᴰ_ : ∀ {x y z} {f : C [ x , y ]} {g : C [ y , z ]} {xᴰ yᴰ zᴰ}
       → Hom[ f ][ xᴰ , yᴰ ] → Hom[ g ][ yᴰ , zᴰ ] → Hom[ f ⋆⟨ C ⟩ g ][ xᴰ , zᴰ ]
  fᴰ ⋆ᴰ gᴰ = ⋆ᴰh _ _ .hom fᴰ gᴰ

  infixr 9 _⋆ᴰ_
  _≡[_]_ : ∀ {x y xᴰ yᴰ} {f g : C [ x , y ]} → Hom[ f ][ xᴰ , yᴰ ] → f ≡ g
         → Hom[ g ][ xᴰ , yᴰ ] → Type ℓCᴰ'
  _≡[_]_ {x} {y} {xᴰ} {yᴰ} fᴰ p gᴰ = PathP (λ i → Hom[ p i ][ xᴰ , yᴰ ]) fᴰ gᴰ

  infix 2 _≡[_]_

  field
    -- and finally the equations for the lax preservation
    ⋆IdLᴰ : ∀ {x y} {f : C [ x , y ]} {xᴰ yᴰ} (fᴰ : Hom[ f ][ xᴰ , yᴰ ])
          → idᴰ ⋆ᴰ fᴰ ≡[ C .⋆IdL f ] fᴰ
    ⋆IdRᴰ : ∀ {x y} {f : C [ x , y ]} {xᴰ yᴰ} (fᴰ : Hom[ f ][ xᴰ , yᴰ ])
          → fᴰ ⋆ᴰ idᴰ ≡[ C .⋆IdR f ] fᴰ
    ⋆Assocᴰ : ∀ {x y z w} {f : C [ x , y ]} {g : C [ y , z ]}  {h : C [ z , w ]}
            {xᴰ yᴰ zᴰ wᴰ} (fᴰ : Hom[ f ][ xᴰ , yᴰ ]) (gᴰ : Hom[ g ][ yᴰ , zᴰ ])
            (hᴰ : Hom[ h ][ zᴰ , wᴰ ])
            → (fᴰ ⋆ᴰ gᴰ) ⋆ᴰ hᴰ ≡[ C .⋆Assoc f g h ] fᴰ ⋆ᴰ (gᴰ ⋆ᴰ hᴰ)

  isSetHomᴰ : ∀ {x y} {f : C [ x , y ]} {xᴰ yᴰ} → isSet Hom[ f ][ xᴰ , yᴰ ]
  isSetHomᴰ = (Hom[ _ ] ⟅ _ , _ ⟆b) .snd


open Categoryᴰ

-- Example: Sets
open import Cubical.Foundations.Structure
open import Cubical.Categories.Instances.Sets
private
  variable
    ℓ ℓ' ℓ'' ℓ''' : Level

module _ ℓ ℓ' where
  open Categoryᴰ
  open Bifunctor
  module _ (A : hSet ℓ) where
    depSET : Category _ _
    depSET .ob = ⟨ A ⟩ → hSet ℓ'
    depSET .Hom[_,_] B C = ∀ a → ⟨ B a ⟩ → ⟨ C a ⟩
    depSET .id = λ a z → z
    depSET ._⋆_ = λ f g a z → g a (f a z)
    depSET .⋆IdL _ = refl
    depSET .⋆IdR _ = refl
    depSET .⋆Assoc _ _ _ = refl
    depSET .isSetHom {y = C} = isSetΠ λ _ → isSetΠ λ _ → C _ .snd

  module _ (A B : hSet ℓ) (f : ⟨ A ⟩ → ⟨ B ⟩) where
    ⊢f : depSET A o-[ _ ]-* depSET B
    ⊢f = mkBifunctorSep SETᶠ where
      open BifunctorSep
      SETᶠ : BifunctorSep _ _ _
      SETᶠ .Bif-ob B B' = (∀ x → ⟨ B x ⟩ → ⟨ B' (f x) ⟩)
        , isSetΠ λ x → isSetΠ λ b → B' (f x) .snd
      SETᶠ .Bif-homL = λ f d z x x₁ → z x (f x x₁)
      SETᶠ .Bif-homR = λ c g z x x₁ → g (f x) (z x x₁)
      SETᶠ .Bif-L-id = refl
      SETᶠ .Bif-L-seq _ _ = refl
      SETᶠ .Bif-R-id = refl
      SETᶠ .Bif-R-seq _ _ = refl
      SETᶠ .SepBif-RL-commute _ _ = refl

  SETᴰ : Categoryᴰ (SET ℓ) (ℓ-max ℓ (ℓ-suc ℓ')) (ℓ-max ℓ ℓ')
  SETᴰ .fiber[_] = depSET
  SETᴰ .Hom[_] {x = A}{y = B} f = ⊢f A B f
  SETᴰ .idᴰh {x = A} = NatEltUnary→NatElt _ neu where
    open NatEltUnary
    neu : NatEltUnary _
    neu .N-ob B = λ a b → b
    neu .N-nat = λ f → refl
  SETᴰ .idᴰh-normal = idEquiv _ .snd
  SETᴰ .⋆ᴰh f g = f*g where
    open Bilinear
    f*g : Bilinear _ _ _
    f*g .hom f^ g^ = λ x y → g^ (f x) (f^ x y)
    f*g .natL _ _ _ = refl
    f*g .natM _ _ _ = refl
    f*g .natR _ _ _ = refl
  SETᴰ .⋆IdLᴰ = λ _ → refl
  SETᴰ .⋆IdRᴰ = λ _ → refl
  SETᴰ .⋆Assocᴰ = λ _ _ _ → refl

-- -- TODO: finish this
-- module _ {C : Category ℓC ℓC'} where
--   import Cubical.Categories.Displayed.Base as Original
--   open Original.Categoryᴰ
--   Original→Alt : Original.Categoryᴰ C ℓCᴰ ℓCᴰ' → Categoryᴰ C ℓCᴰ ℓCᴰ'
--   Original→Alt Cᴰ .fiber[_] = fiber Cᴰ
--   Original→Alt Cᴰ .Hom[_] = Homᴰ Cᴰ
--   Original→Alt Cᴰ .idᴰh .N-ob = λ _ → Cᴰ .Original.Categoryᴰ.idᴰ
--   Original→Alt Cᴰ .idᴰh .N-hom× = λ f → f
--   Original→Alt Cᴰ .idᴰh .N-ob-hom×-agree = refl
--   Original→Alt Cᴰ .idᴰh .N-natL = {!!}
--   Original→Alt Cᴰ .idᴰh .N-natR = {!!}
--   Original→Alt Cᴰ .idᴰh-normal = idEquiv _ .snd
--   Original→Alt Cᴰ .⋆ᴰh f g .hom = Cᴰ .Original.Categoryᴰ._⋆ᴰ_
--   Original→Alt Cᴰ .⋆ᴰh f g .natL = {!!}
--   Original→Alt Cᴰ .⋆ᴰh f g .natM = {!!}
--   Original→Alt Cᴰ .⋆ᴰh f g .natR = {!!}
--   Original→Alt Cᴰ .⋆IdLᴰ = Cᴰ .⋆IdLᴰ
--   Original→Alt Cᴰ .⋆IdRᴰ = Cᴰ .⋆IdRᴰ
--   Original→Alt Cᴰ .⋆Assocᴰ = Cᴰ .⋆Assocᴰ
