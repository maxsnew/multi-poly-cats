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
open import Cubical.Categories.Limits.AsRepresentable
open import Cubical.Categories.Functor renaming (𝟙⟨_⟩ to funcId)
open import Cubical.Categories.NaturalTransformation.Base
open import Cubical.Categories.NaturalTransformation.Properties
open import Cubical.Categories.NaturalTransformation.More
open import Cubical.Categories.Functors.HomFunctor
open import Cubical.Categories.Constructions.BinProduct
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Monad.Base
open import Cubical.Categories.Presheaf.Representable
open import Cubical.Categories.Presheaf.More
open import Cubical.Categories.Profunctor.Relator
open import Cubical.Categories.Profunctor.General
open import Cubical.Categories.Profunctor.FunctorComprehension
open import Cubical.Categories.Bifunctor.Redundant
open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.HLevels
open import Cubical.Categories.Displayed.HLevels.More
open import Cubical.Categories.Displayed.Limits.Limits
open import Cubical.Categories.Displayed.Section.Base
open import Cubical.Categories.Constructions.TotalCategory as TotalCat
open import Cubical.Categories.Constructions.TotalCategory.More as TotalCat
open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Displayed.Properties
open import Cubical.Categories.Displayed.Constructions.StructureOver

open import Cubical.Categories.Displayed.Presheaf
open import Cubical.Foundations.Isomorphism.More

private
  variable
    ℓC ℓC' ℓD ℓD' ℓS : Level

module _ {C : Category ℓC ℓC'}{D : Category ℓD ℓD'}
         (J : C o-[ ℓS ]-* D)
         where
  open Category
  open Section
  open Functorᴰ
  private
    module J = Bifunctor J
    variable
      a a' b b' : C .ob
      c d : D .ob
      f g h : C [ a , b ]
      ϕ ψ : D [ c , d ]
      r s : ⟨ J ⟅ a , c ⟆b ⟩

  record ExtensionSystem : Type (ℓ-max ℓC (ℓ-max (ℓ-max ℓD ℓD') ℓS)) where
   field
     T : C .ob → D .ob
     η : ⟨ J ⟅ a , T a ⟆b ⟩
     bind : ⟨ J ⟅ a , T b ⟆b ⟩ → D [ T a , T b ]
     -- x <- η(x); M = x. M
     bind-r : bind (η {a = a}) ≡ D .id
     -- x <- M; η(x)
     bind-l : {r : ⟨ J ⟅ a , T b ⟆b ⟩} → (J ⟪ bind r ⟫r) η ≡ r
     -- bind-comp : bind f ∘⟨ C ⟩ bind g ≡ bind (bind f ∘⟨ C ⟩ g)
     bind-comp : {r : ⟨ J ⟅ a , T a' ⟆b ⟩}{s : ⟨ J ⟅ a' , T b ⟆b ⟩}
                → bind r ⋆⟨ D ⟩ bind s ≡ bind ((J ⟪ bind s ⟫r) r)

  module _ (E : ExtensionSystem) where
    private
      module E = ExtensionSystem E

    Kleisli : Category ℓC ℓS
    Kleisli .ob = C .ob
    Kleisli .Hom[_,_] a b = ⟨ J ⟅ a , E.T b ⟆b ⟩
    Kleisli .id = E.η
    Kleisli ._⋆_ r s = (J ⟪ E.bind s ⟫r) r
    Kleisli .⋆IdL f = E.bind-l
    Kleisli .⋆IdR r =
      (λ i → (J ⟪ E.bind-r i ⟫r) r)
      ∙ (λ i → J.Bif-R-id i r)
    Kleisli .⋆Assoc r r' r'' =
      (λ i → (J.Bif-R-seq (E.bind r') (E.bind r'') (~ i)) r)
      ∙ λ i → (J ⟪ E.bind-comp {r = r'}{s = r''} i ⟫r) r
    Kleisli .isSetHom = str (J ⟅ _ , E.T _ ⟆b)

    -- The Kleisli category comes almost by definition with a functor to D
    Fkd : Functor Kleisli D
    Fkd .Functor.F-ob = E.T
    Fkd .Functor.F-hom = E.bind
    Fkd .Functor.F-id = E.bind-r
    Fkd .Functor.F-seq f g = sym E.bind-comp

    -- Algebras for a relative monad are *structure* over objects of D
    record AlgebraOver (carrier : D .ob)
      : Type (ℓ-max (ℓ-max ℓC ℓD) (ℓ-max ℓD' ℓS)) where
      field
        bindA : ⟨ J ⟅ a , carrier ⟆b ⟩ → D [ E.T a , carrier ]
        bindA-l : {r : ⟨ J ⟅ a , carrier ⟆b ⟩}
                → (J ⟪ bindA r ⟫r) E.η ≡ r
        bindA-comp : {r : Kleisli [ a , a' ]}{s : ⟨ J ⟅ a' , carrier ⟆b ⟩}
                   → E.bind r ⋆⟨ D ⟩ bindA s ≡ bindA ((J ⟪ bindA s ⟫r) r)

    open AlgebraOver
    private
      -- This defines what it means for a morphism in D to be a homomorphism.
      A : StructureOver D _ _
      A .StructureOver.ob[_] = AlgebraOver
      A .StructureOver.Hom[_][_,_] ϕ B1 B2 =
        ∀ {a} (r : ⟨ J ⟅ a , _ ⟆b ⟩)
         → ϕ ∘⟨ D ⟩ B1 .bindA r ≡ B2 .bindA ((J ⟪ ϕ ⟫r) r)
      A .StructureOver.idᴰ {p = B} r = D .⋆IdR _
        ∙ cong (B .bindA) (sym (funExt⁻ (J.Bif-R-id) r))
      A .StructureOver._⋆ᴰ_ {f = ϕ}{g = ψ}{xᴰ = B1}{yᴰ = B2}{zᴰ = B3}
        ϕ-homo ψ-homo r =
        sym (D .⋆Assoc _ _ _)
        ∙ cong₂ (D ._⋆_) (ϕ-homo r) refl
        ∙ ψ-homo _
        ∙ cong (B3 .bindA) (sym (funExt⁻ (J.Bif-R-seq _ _) r))
      A .StructureOver.isPropHomᴰ = isPropImplicitΠ λ _ → isPropΠ λ _ →
        D .isSetHom _ _
    ALGEBRAᴰ : Categoryᴰ D _ _
    ALGEBRAᴰ = StructureOver→Catᴰ A

    open UniversalElementᴰ
    open NatTrans
    -- TODO
    -- ALGEBRA-liftsLimits : ∀ ℓS ℓS' → liftsLimits ALGEBRAᴰ ℓS ℓS'
    -- ALGEBRA-liftsLimits _ _ S limitOfS {D = F} Fᴰ = record
    --   { vertexᴰ    = LimAlg
    --   ; elementᴰ   = {!!}
    --   ; universalᴰ = {!!}
    --   } where
    --   -- module Lim = UniversalElement (limitOfS F)
    --   module D = Category D
    --   module Lim = UniversalElementNotation (limitOfS F)

    --   LimAlg : AlgebraOver Lim.vertex
    --   LimAlg .bindA j = Lim.intro
    --     (natTrans
    --       ((λ s → Fᴰ .F-obᴰ {x = s} _ .bindA ((J ⟪ Lim.element ⟦ s ⟧ ⟫r) j)))
    --       commutes )
    --     where
    --       ps : N-ob-Type ((ΔF ^opF) ⟅ E.T _ ⟆) F
    --       ps =
    --       ((λ s → Fᴰ .F-obᴰ {x = s} _ .bindA ((J ⟪ Lim.element ⟦ s ⟧ ⟫r) j)))
    --       opaque
    --         commutes : N-hom-Type ((ΔF ^opF) ⟅ E.T _ ⟆) F ps
    --         commutes = λ f →
    --           -- Better limit notation would help a lot here.
    --           D.⋆IdL _
    --           ∙ cong (Fᴰ .F-obᴰ _ .bindA)
    --             ( cong₂ (J.Bif-homR _)
    --                     (sym (D.⋆IdL _) ∙ Lim.element .N-hom f)
    --                     refl
    --             ∙ funExt⁻ (J.Bif-R-seq _ _) _)
    --           ∙ sym (Fᴰ .F-homᴰ {f = f} _ _)

    --   LimAlg .bindA-l = {!!}
    --   LimAlg .bindA-comp = {!!}

    hasPropHomsALGEBRAᴰ = hasPropHomsStructureOver A

    ALGEBRA : Category _ _
    ALGEBRA = ∫C ALGEBRAᴰ

    Carrier : Functor ALGEBRA D
    Carrier = TotalCat.Fst

    FreeAlg : ∀ c → AlgebraOver (E.T c)
    FreeAlg c .bindA = E.bind
    FreeAlg c .bindA-l = E.bind-l
    FreeAlg c .bindA-comp = E.bind-comp

    KleisliToAlgebra : Functor Kleisli ALGEBRA
    KleisliToAlgebra = TotalCat.intro' Fkd FreeAlgS where
      FreeAlgS : Section _ _
      FreeAlgS = mkPropHomsSection hasPropHomsALGEBRAᴰ
        FreeAlg
        λ f r → E.bind-comp

    Fck : Functor C Kleisli
    Fck = (FunctorComprehension Fck-ues) ^opF where
      Fck-Rel : C o-[ ℓS ]-* Kleisli
      Fck-Rel = J ∘Fr Fkd
      Fck-spec : Profunctor (C ^op) (Kleisli ^op) ℓS
      Fck-spec = CurryBifunctor Fck-Rel

      open UniversalElement
      -- every Kleisli morphism
      --   r : ⟨ J ⟅ c , E.T d ⟆b ⟩
      -- factors through
      --   η : ⟨ J ⟅ c , E.T c ⟆b ⟩
      Fck-ues : UniversalElements Fck-spec
      Fck-ues c .vertex = c
      Fck-ues c .element = E.η
      Fck-ues c .universal c' = isIsoToIsEquiv (
        (λ z → z)
        , (λ _ → E.bind-l)
        , (λ _ → E.bind-l))

    F : Functor C D
    F = Carrier ∘F KleisliToAlgebra ∘F Fck

    private
      -- test the definitional behavior of F
      _ : F ⟪ f ⟫ ≡ E.bind ((J ⟪ f ⟫l) E.η)
      _ = refl
