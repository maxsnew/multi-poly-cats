{-

  Explicit "redundant" definition of a bifunctor F : C , D → E.
  Includes all 3 of
  1. A "parallel action" f × g
  2. Two "separate actions" f × d and c × g
  Plus axioms that say
  1. The actions are functorial
  2. and that they agree

  The full definition includes some redundant *axioms* to make it
  convenient to use, so we include two alternative formulations to
  make it easier to prove.

-}

{-# OPTIONS --safe #-}
module Cubical.Categories.Bifunctor.Redundant where

open import Cubical.Foundations.Prelude hiding (Path)

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Constructions.BinProduct hiding (Fst; Snd)
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Instances.Functors

open import Cubical.Data.Sigma
open import Cubical.Tactics.CategorySolver.Reflection

private
  variable
    ℓ ℓ' ℓc ℓc' ℓd ℓd' ℓe ℓe' : Level

open Category
open Functor
open NatTrans

-- This definition is the most convenient to use
-- But its axioms are redundant as well as its
record Bifunctor (C : Category ℓc ℓc')
                 (D : Category ℓd ℓd')
                 (E : Category ℓe ℓe')
       : Type (ℓ-max ℓc (ℓ-max ℓc' (ℓ-max ℓd (ℓ-max ℓd' (ℓ-max ℓe ℓe'))))) where
  field
    Bif-ob : C .ob → D .ob → E .ob
    Bif-homL : ∀ {c c'} → (f : C [ c , c' ]) → ∀ d
             → E [ Bif-ob c d , Bif-ob c' d ]
    Bif-homR : ∀ {d d'} c → (g : D [ d , d' ]) → E [ Bif-ob c d , Bif-ob c d' ]
    Bif-hom× : ∀ {c c' d d'} (f : C [ c , c' ])(g : D [ d , d' ])
             → E [ Bif-ob c d , Bif-ob c' d' ]
    Bif-L-id : ∀ {c d} → Bif-homL (C .id {c}) d ≡ E .id
    Bif-L-seq : ∀ {c c' c'' d} (f : C [ c , c' ])(f' : C [ c' , c'' ])
             → Bif-homL (f ⋆⟨ C ⟩ f') d ≡ Bif-homL f d ⋆⟨ E ⟩ Bif-homL f' d
    Bif-R-id : ∀ {c d} → Bif-homR c (D .id {d}) ≡ E .id
    Bif-R-seq : ∀ {c d d' d''} (g : D [ d , d' ])(g' : D [ d' , d'' ])
             → Bif-homR c (g ⋆⟨ D ⟩ g') ≡ Bif-homR c g ⋆⟨ E ⟩ Bif-homR c g'
    Bif-×-id : ∀ {c d} → Bif-hom× (C .id {c}) (D .id {d}) ≡ E .id
    Bif-×-seq : ∀ {c c' c'' d d' d''}
               (f : C [ c , c' ])(f' : C [ c' , c'' ])
               (g : D [ d , d' ])(g' : D [ d' , d'' ])
             → Bif-hom× (f ⋆⟨ C ⟩ f') (g ⋆⟨ D ⟩ g')
             ≡ Bif-hom× f g ⋆⟨ E ⟩ Bif-hom× f' g'
    Bif-L×-agree : ∀ {c c' d} → (f : C [ c , c' ])
                 → Bif-homL f d ≡ Bif-hom× f (D .id)
    Bif-R×-agree : ∀ {c d d'} → (g : D [ d , d' ])
                 → Bif-homR c g ≡ Bif-hom× (C .id) g
    Bif-LR-fuse : ∀ {c c' d d'} → (f : C [ c , c' ]) (g : D [ d , d' ])
               → Bif-homL f d ⋆⟨ E ⟩ Bif-homR c' g
               ≡ Bif-hom× f g

    Bif-RL-fuse : ∀ {c c' d d'} → (f : C [ c , c' ]) (g : D [ d , d' ])
               → Bif-homR c g ⋆⟨ E ⟩ Bif-homL f d'
               ≡ Bif-hom× f g

record BifunctorParAx (C : Category ℓc ℓc')
                  (D : Category ℓd ℓd')
                  (E : Category ℓe ℓe')
       : Type (ℓ-max ℓc (ℓ-max ℓc' (ℓ-max ℓd (ℓ-max ℓd' (ℓ-max ℓe ℓe'))))) where
  field
    Bif-ob : C .ob → D .ob → E .ob
    Bif-homL : ∀ {c c'} → (f : C [ c , c' ]) → ∀ d
             → E [ Bif-ob c d , Bif-ob c' d ]
    Bif-homR : ∀ {d d'} c → (g : D [ d , d' ]) → E [ Bif-ob c d , Bif-ob c d' ]
    Bif-hom× : ∀ {c c' d d'} (f : C [ c , c' ])(g : D [ d , d' ])
             → E [ Bif-ob c d , Bif-ob c' d' ]
    Bif-×-id : ∀ {c d} → Bif-hom× (C .id {c}) (D .id {d}) ≡ E .id
    Bif-×-seq : ∀ {c c' c'' d d' d''}
               (f : C [ c , c' ])(f' : C [ c' , c'' ])
               (g : D [ d , d' ])(g' : D [ d' , d'' ])
             → Bif-hom× (f ⋆⟨ C ⟩ f') (g ⋆⟨ D ⟩ g')
             ≡ Bif-hom× f g ⋆⟨ E ⟩ Bif-hom× f' g'
    Bif-L×-agree : ∀ {c c' d} → (f : C [ c , c' ])
                 → Bif-homL f d ≡ Bif-hom× f (D .id)
    Bif-R×-agree : ∀ {c d d'} → (g : D [ d , d' ])
                 → Bif-homR c g ≡ Bif-hom× (C .id) g

record BifunctorSepAx (C : Category ℓc ℓc')
                  (D : Category ℓd ℓd')
                  (E : Category ℓe ℓe')
       : Type (ℓ-max ℓc (ℓ-max ℓc' (ℓ-max ℓd (ℓ-max ℓd' (ℓ-max ℓe ℓe'))))) where
  field
    Bif-ob : C .ob → D .ob → E .ob

    Bif-homL : ∀ {c c'} → (f : C [ c , c' ]) → ∀ d
             → E [ Bif-ob c d , Bif-ob c' d ]
    Bif-L-id : ∀ {c d} → Bif-homL (C .id {c}) d ≡ E .id
    Bif-L-seq : ∀ {c c' c'' d} (f : C [ c , c' ])(f' : C [ c' , c'' ])
             → Bif-homL (f ⋆⟨ C ⟩ f') d ≡ Bif-homL f d ⋆⟨ E ⟩ Bif-homL f' d

    Bif-homR : ∀ {d d'} c → (g : D [ d , d' ]) → E [ Bif-ob c d , Bif-ob c d' ]
    Bif-R-id : ∀ {c d} → Bif-homR c (D .id {d}) ≡ E .id
    Bif-R-seq : ∀ {c d d' d''} (g : D [ d , d' ])(g' : D [ d' , d'' ])
             → Bif-homR c (g ⋆⟨ D ⟩ g') ≡ Bif-homR c g ⋆⟨ E ⟩ Bif-homR c g'

    Bif-hom× : ∀ {c c' d d'} (f : C [ c , c' ])(g : D [ d , d' ])
             → E [ Bif-ob c d , Bif-ob c' d' ]
    Bif-LR-fuse : ∀ {c c' d d'} → (f : C [ c , c' ]) (g : D [ d , d' ])
               → Bif-homL f d ⋆⟨ E ⟩ Bif-homR c' g
               ≡ Bif-hom× f g
    Bif-RL-fuse : ∀ {c c' d d'} → (f : C [ c , c' ]) (g : D [ d , d' ])
               → Bif-homR c g ⋆⟨ E ⟩ Bif-homL f d'
               ≡ Bif-hom× f g
private
  variable
    C D E : Category ℓ ℓ'

mkBifunctorSepAx : BifunctorSepAx C D E → Bifunctor C D E
mkBifunctorSepAx {C = C}{D = D}{E = E} F = G where
  open BifunctorSepAx F
  open Bifunctor
  G : Bifunctor C D E
  G .Bif-ob = F .Bif-ob
  G .Bif-homL = F .Bif-homL
  G .Bif-homR = F .Bif-homR
  G .Bif-hom× = F .Bif-hom×
  G .Bif-L-id = F .Bif-L-id
  G .Bif-L-seq = F .Bif-L-seq
  G .Bif-R-id = F .Bif-R-id
  G .Bif-R-seq = F .Bif-R-seq
  G .Bif-LR-fuse = F .Bif-LR-fuse
  G .Bif-RL-fuse = F .Bif-RL-fuse
  G .Bif-×-id = sym (F .Bif-LR-fuse _ _)
    ∙ cong₂ (seq' E) (F .Bif-L-id) (F .Bif-R-id)
    ∙ E .⋆IdR _
  G .Bif-×-seq f f' g g' =
    sym (F .Bif-LR-fuse _ _)
    ∙ cong₂ (seq' E) (F .Bif-L-seq _ _) (F .Bif-R-seq _ _)
    ∙ E .⋆Assoc _ _ _
    ∙ cong₂ (seq' E) refl
          (sym (E .⋆Assoc _ _ _)
          ∙ cong₂ (comp' E) refl (F .Bif-LR-fuse _ _ ∙ sym (F .Bif-RL-fuse _ _))
          ∙ E .⋆Assoc _ _ _
          ∙ cong₂ (seq' E) refl (F .Bif-LR-fuse _ _))
          -- ∙ {!!})
    ∙ sym (E .⋆Assoc _ _ _)
    ∙ cong₂ (comp' E) refl (F .Bif-LR-fuse _ _)

  G .Bif-L×-agree f =
    sym (E .⋆IdR _)
    ∙ cong₂ (seq' E) refl (sym (F .Bif-R-id))
    ∙ F .Bif-LR-fuse _ _
  G .Bif-R×-agree g =
    sym (E .⋆IdL _)
    ∙ cong₂ (comp' E) refl (sym (F .Bif-L-id))
    ∙ F .Bif-LR-fuse _ _

mkBifunctorParAx : BifunctorParAx C D E → Bifunctor C D E
mkBifunctorParAx {C = C}{D = D}{E = E} F = G where
  open BifunctorParAx F
  open Bifunctor
  G : Bifunctor C D E
  G .Bif-ob = F .Bif-ob
  G .Bif-homL = F .Bif-homL
  G .Bif-homR = F .Bif-homR
  G .Bif-hom× = F .Bif-hom×
  G .Bif-×-id = F .Bif-×-id
  G .Bif-×-seq = F .Bif-×-seq
  G .Bif-L×-agree = F .Bif-L×-agree
  G .Bif-R×-agree = F .Bif-R×-agree

  G .Bif-L-id = F .Bif-L×-agree _ ∙ F .Bif-×-id
  G .Bif-L-seq f f' = F .Bif-L×-agree _
    ∙ cong₂ (F .Bif-hom×) refl (sym (D .⋆IdR (D .id)))
    ∙ F .Bif-×-seq f f' (D .id) (D .id)
    ∙ cong₂ (seq' E) (sym (F .Bif-L×-agree _)) (sym (F .Bif-L×-agree _))
  G .Bif-R-id = F .Bif-R×-agree _ ∙ F .Bif-×-id
  G .Bif-R-seq g g' = G .Bif-R×-agree _
    ∙ cong₂ (F .Bif-hom×) (sym (C .⋆IdR (C .id))) refl
    ∙ F .Bif-×-seq _ _ _ _
    ∙ cong₂ (seq' E) (sym (F .Bif-R×-agree _)) (sym (F .Bif-R×-agree _))

  G .Bif-LR-fuse f g =
    cong₂ (seq' E) (F .Bif-L×-agree _) (F .Bif-R×-agree _)
    ∙ sym (F .Bif-×-seq _ _ _ _)
    ∙ cong₂ (F .Bif-hom×) (C .⋆IdR _) (D .⋆IdL _)
  G .Bif-RL-fuse f g =
    cong₂ (seq' E) (F .Bif-R×-agree _) (F .Bif-L×-agree _)
    ∙ sym (F .Bif-×-seq _ _ _ _)
    ∙ cong₂ (F .Bif-hom×) (C .⋆IdL _) (D .⋆IdR _)

open Bifunctor
-- action on objects
infix 30 _⟅_⟆b
_⟅_⟆b : (F : Bifunctor C D E)
     → C .ob × D .ob
     → E .ob
F ⟅ c , d ⟆b = Bif-ob F c d

-- actions on morphisms
infix 30 _⟪_⟫l
-- same infix level as on objects since these will
-- never be used in the same context
infix 30 _⟪_⟫r

-- same infix level as on objects since these will
-- never be used in the same context
infix 30 _⟪_⟫×

_⟪_⟫l : (F : Bifunctor C D E)
     → ∀ {c c' d}
     → C [ c , c' ]
     → E [(F ⟅ c , d ⟆b) , (F ⟅ c' , d ⟆b)]
F ⟪ f ⟫l = Bif-homL F f _

_⟪_⟫r : (F : Bifunctor C D E)
     → ∀ {c d d'}
     → D [ d , d' ]
     → E [(F ⟅ c , d ⟆b) , (F ⟅ c , d' ⟆b)]
F ⟪ f ⟫r = Bif-homR F _ f

_⟪_⟫× : (F : Bifunctor C D E)
      → ∀ {c c' d d'}
      → C [ c , c' ] × D [ d , d' ]
      → E [ F ⟅ c , d ⟆b , F ⟅ c' , d' ⟆b ]
F ⟪ f , g ⟫× = F .Bif-hom× f g

Bif-RL-commute
  : {C : Category ℓc ℓc'}{D : Category ℓd ℓd'}{E : Category ℓe ℓe'}
  → (F : Bifunctor C D E)
  → ∀ {c c' d d'} → (f : C [ c , c' ]) (g : D [ d , d' ])
  → F ⟪ g ⟫r ⋆⟨ E ⟩ F ⟪ f ⟫l ≡ F ⟪ f ⟫l ⋆⟨ E ⟩ F ⟪ g ⟫r
Bif-RL-commute F f g =
  F .Bif-RL-fuse f g ∙ sym (F .Bif-LR-fuse f g)

-- Some universal bifunctors:
-- app : Bifunctor (FUNCTOR C D) C D
-- app : Bifunctor C (FUNCTOR C D) D
-- pair : Bifunctor C D (C × D)