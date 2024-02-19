-- Monad relative to a Relator
{-
   Monads as extension systems, i.e., in terms of unit and bind,
   deriving the rest of the structure
   https://ncatlab.org/nlab/show/extension+system
-}
{-# OPTIONS --safe --lossy-unification #-}
module Cubical.Categories.Monad.Relative where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure
open import Cubical.Data.Sigma
open import Cubical.Categories.Category hiding (isIso)
open import Cubical.Categories.Functor renaming (𝟙⟨_⟩ to funcId)
open import Cubical.Categories.NaturalTransformation.Base
open import Cubical.Categories.NaturalTransformation.Properties
open import Cubical.Categories.NaturalTransformation.More
open import Cubical.Categories.Functors.HomFunctor
open import Cubical.Categories.Constructions.BinProduct
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Monad.Base
open import Cubical.Categories.Presheaf.Representable
open import Cubical.Categories.Profunctor.Relator
open import Cubical.Categories.Profunctor.General
open import Cubical.Categories.Profunctor.FunctorComprehension
open import Cubical.Categories.Bifunctor.Redundant
open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Base.More as Disp
open import Cubical.Categories.Displayed.Properties
open import Cubical.Categories.Displayed.Preorder

open import Cubical.Foundations.Isomorphism.More

private
  variable
    ℓC ℓC' ℓD ℓD' ℓS : Level

module _ {C : Category ℓC ℓC'}{D : Category ℓD ℓD'}
         (R : C o-[ ℓS ]-* D)
         where
  open Category
  private
    module R = Bifunctor R
    variable
      a a' b b' : C .ob
      c d : D .ob
      f g h : C [ a , b ]
      ϕ ψ : D [ c , d ]
      r s : ⟨ R ⟅ a , c ⟆b ⟩

  -- This defines a profunctor Kl : C o-* C
  record ExtensionSystem : Type (ℓ-max ℓC (ℓ-max (ℓ-max ℓD ℓD') ℓS)) where
   field
     T : C .ob → D .ob
     η : ⟨ R ⟅ a , T a ⟆b ⟩
     -- 
     bind : ⟨ R ⟅ a , T b ⟆b ⟩ → D [ T a , T b ]
     -- x <- η(x); M = x. M
     bind-r : bind (η {a = a}) ≡ D .id
     -- x <- M; η(x)
     -- | TODO: we desperately need relator notation here
     bind-l : {r : ⟨ R ⟅ a , T b ⟆b ⟩} → (R ⟪ bind r ⟫r) η ≡ r
     -- bind-comp : bind f ∘⟨ C ⟩ bind g ≡ bind (bind f ∘⟨ C ⟩ g)
     bind-comp : {r : ⟨ R ⟅ a , T a' ⟆b ⟩}{s : ⟨ R ⟅ a' , T b ⟆b ⟩}
                → bind r ⋆⟨ D ⟩ bind s ≡ bind ((R ⟪ bind s ⟫r) r)

  module _ (E : ExtensionSystem) where
    private
      module E = ExtensionSystem E
    
    Kleisli : Category ℓC ℓS
    Kleisli .ob = C .ob
    Kleisli .Hom[_,_] a b = ⟨ R ⟅ a , E.T b ⟆b ⟩
    Kleisli .id = E.η
    Kleisli ._⋆_ r s = (R ⟪ E.bind s ⟫r) r
    Kleisli .⋆IdL f = E.bind-l
    Kleisli .⋆IdR r =
      (λ i → (R ⟪ E.bind-r i ⟫r) r)
      ∙ (λ i → R.Bif-R-id i r)
    Kleisli .⋆Assoc r r' r'' =
      (λ i → (R.Bif-R-seq (E.bind r') (E.bind r'') (~ i)) r)
      ∙ λ i → (R ⟪ E.bind-comp {r = r'}{s = r''} i ⟫r) r
    Kleisli .isSetHom = str (R ⟅ _ , E.T _ ⟆b)

    -- We construct the functor from C to D in two parts.
    -- First, we construct a functor from C to Kleisli by
    -- FunctorComprehension
    Fck : Functor C Kleisli
    Fck = (FunctorComprehension Fck-ues) ^opF where
      Fck-Rel : C o-[ ℓS ]-* Kleisli
      Fck-Rel = mkBifunctorSep G where
        G : BifunctorSep (C ^op) Kleisli (SET ℓS)
        G .BifunctorSep.Bif-ob c d = R ⟅ c , E.T d ⟆b
        G .BifunctorSep.Bif-homL f d = R.Bif-homL _ _
        G .BifunctorSep.Bif-L-id = R.Bif-L-id
        G .BifunctorSep.Bif-L-seq = R.Bif-L-seq
        G .BifunctorSep.Bif-homR c g = R.Bif-homR _ _
        G .BifunctorSep.Bif-R-id = funExt (Kleisli .⋆IdR)
        G .BifunctorSep.Bif-R-seq g g' = funExt λ _ → sym (Kleisli .⋆Assoc _ _ _)
        G .BifunctorSep.SepBif-RL-commute f g = Bif-RL-commute R _ _

      Fck-spec : Profunctor (C ^op) (Kleisli ^op) ℓS
      Fck-spec = CurryBifunctor Fck-Rel

      open UniversalElement
      -- every Kleisli morphism
      --   r : ⟨ R ⟅ c , E.T d ⟆b ⟩
      -- factors through
      --   η : ⟨ R ⟅ c , E.T c ⟆b ⟩
      Fck-ues : UniversalElements Fck-spec
      Fck-ues c .vertex = c
      Fck-ues c .element = E.η
      Fck-ues c .universal c' = isIsoToIsEquiv (
        (λ z → z)
        , (λ _ → E.bind-l)
        , (λ _ → E.bind-l))

    Fkd : Functor Kleisli D
    Fkd .Functor.F-ob = E.T
    Fkd .Functor.F-hom = E.bind
    Fkd .Functor.F-id = E.bind-r
    Fkd .Functor.F-seq f g = sym E.bind-comp

    F : Functor C D
    F = Fkd ∘F Fck

    private
      -- test the definitional behavior of F
      _ : F ⟪ f ⟫ ≡ E.bind ((R ⟪ f ⟫l) E.η)
      _ = refl

    record AlgebraOver (carrier : D .ob) : Type (ℓ-max (ℓ-max ℓC ℓD) (ℓ-max ℓD' ℓS)) where
      field
        bindA : ⟨ R ⟅ a , carrier ⟆b ⟩ → D [ E.T a , carrier ]
        bindA-l : {r : ⟨ R ⟅ a , carrier ⟆b ⟩}
                → (R ⟪ bindA r ⟫r) E.η ≡ r
        bindA-comp : {r : Kleisli [ a , a' ]}{s : ⟨ R ⟅ a' , carrier ⟆b ⟩}
                   → E.bind r ⋆⟨ D ⟩ bindA s ≡ bindA ((R ⟪ bindA s ⟫r) r)

    open AlgebraOver

    ALGEBRAᴰ : Categoryᴰ D _ _
    ALGEBRAᴰ = Preorderᴰ→Catᴰ A where
      A : Preorderᴰ D _ _
      A .Preorderᴰ.ob[_] = AlgebraOver
      A .Preorderᴰ.Hom[_][_,_] ϕ B1 B2 =
        ∀ {a} (r : ⟨ R ⟅ a , _ ⟆b ⟩)
         → ϕ ∘⟨ D ⟩ B1 .bindA r ≡ B2 .bindA ((R ⟪ ϕ ⟫r) r)
      A .Preorderᴰ.idᴰ {p = B} r = D .⋆IdR _
        ∙ cong (B .bindA) (sym (funExt⁻ (R.Bif-R-id) r))
      A .Preorderᴰ._⋆ᴰ_ {f = ϕ}{g = ψ}{xᴰ = B1}{yᴰ = B2}{zᴰ = B3} ϕ-homo ψ-homo r =
        sym (D .⋆Assoc _ _ _)
        ∙ cong₂ (D ._⋆_) (ϕ-homo r) refl
        ∙ ψ-homo _
        ∙ cong (B3 .bindA) (sym (funExt⁻ (R.Bif-R-seq _ _) r))
      A .Preorderᴰ.isPropHomᴰ = isPropImplicitΠ λ _ → isPropΠ λ _ →
        D .isSetHom _ _

    ALGEBRA : Category _ _
    ALGEBRA = ∫C ALGEBRAᴰ

    Carrier : Functor ALGEBRA D
    Carrier = Disp.Fst
