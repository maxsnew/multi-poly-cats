{-# OPTIONS --safe #-}
-- following 1 Lab
-- https://1lab.dev/Cat.Diagram.Coend.Sets.html

module Cubical.Categories.Constructions.Coend.Base where
    open import Cubical.Categories.Bifunctor.Base
    open import Cubical.Categories.Category
    open import Cubical.Categories.Functor
    open import Cubical.Categories.Instances.Sets

    open import Cubical.Foundations.HLevels
    open import Cubical.Foundations.Prelude

    private
        variable
            ℓC ℓC' ℓD ℓD' : Level

    module _ {C : Category ℓC ℓC'}
             {D : Category ℓD ℓD'}
             (F : Bifunctor (C ^op) C D) where

        module C = Category C
        module D = Category D

        record Cowedge : Set (ℓ-max ℓC (ℓ-max ℓC' (ℓ-max ℓD ℓD'))) where
            field
                nadir : D.ob
                ψ : (c : C.ob) → D [ F ⟅ c , c ⟆b , nadir ]
                {-
                    for all morphisms f : c ⇒ c' in category C,

                    F₀(c',c)---F₁(id(c'),f)---> F₀(c',c')
                     |                          |
                     F₁(f,id(c))               ψ(c')
                     ↓                          ↓
                    F₀(c,c)---ψ(c)-----------> nadir
                -}
                extranatural : {c c' : C.ob}(f : C [ c , c' ]) →
                    (F ⟪ C.id , f ⟫lr D.⋆  ψ c') ≡ ( F ⟪ f ,  C.id ⟫lr D.⋆ ψ c)

        -- TODO : Can probably define a Presheaf structure for Cowedge and then
        -- this should be isomorphic to a universal element of that presheaf.
        record Coend : Set ((ℓ-max ℓC (ℓ-max ℓC' (ℓ-max ℓD ℓD'))))  where
            open Cowedge
            field
                cowedge : Cowedge
                factor : (W : Cowedge ) → D [ cowedge .nadir , W .nadir ]
                commutes : (W : Cowedge )
                           (c : C.ob) →
                           (cowedge .ψ c D.⋆ factor W) ≡ W .ψ c
                unique : (W : Cowedge )
                         (factor' : D [ cowedge .nadir , W .nadir ]) →
                         (∀(c : C.ob) → (cowedge .ψ c D.⋆ factor') ≡ W .ψ c) →
                         factor' ≡ factor W

    module _ {C : Category ℓC ℓC'}
             (F : Bifunctor (C ^op) C (SET (ℓ-max ℓC ℓC')) ) where
        open import Cubical.HITs.SetCoequalizer
        open Category

        Set-Coend : Coend F
        Set-Coend = coend where
            open Cowedge
            open Coend

            lmap : Σ[ X ∈ ob C ]
                   Σ[ Y ∈ ob C ]
                   Σ[ f ∈ (C)[ Y , X ] ] fst( F ⟅ X , Y ⟆b )
                →  Σ[ X ∈ ob C ] fst ( F ⟅ X , X ⟆b)
            lmap (X , Y , f , Fxy ) = X , ( F ⟪ id C {X} , f ⟫lr ) Fxy

            rmap : Σ[ X ∈ ob C ]
                   Σ[ Y ∈ ob C ]
                   Σ[ f ∈ (C)[ Y , X ] ] fst( F ⟅ X , Y ⟆b )
                →  Σ[ X ∈ ob C ] fst ( F ⟅ X , X ⟆b)
            rmap (X , Y , f , Fxy ) = Y , ( F ⟪ f , id C {Y}  ⟫lr ) Fxy

            {-
                for morphism f : Y ⇒ X in category C,

                -- this diagram is just the coeq constructor

                F₀(X , Y)---rmap---> Σ[ X ∈ ob C] F (X , X)
                 |                          |
                 lmap                      inc
                 |                          |
        Σ[ X ∈ ob C] F (X , X)---inc-----> SetCoequalizer lmap rmap
            -}

            univ : Cowedge F
            univ .nadir = SetCoequalizer lmap rmap , squash
            univ .ψ X Fxx = inc (X , Fxx)
            univ .extranatural {Y} {X} f = funExt λ Fxy → coeq (X , Y , f , Fxy)

            open UniversalProperty using (inducedHom ; uniqueness)
            factoring : (W : Cowedge F) →
                        SetCoequalizer lmap rmap →
                        fst (W .nadir)
            factoring W =
                inducedHom
                    (W .nadir .snd)
                    (λ {(x , Fxx) → W .ψ x Fxx})
                    λ{(X , Y , f , Fxy) → funExt⁻ (W .extranatural f) Fxy}

            coend : Coend F
            coend .cowedge = univ
            coend .factor = factoring
            coend .commutes W c = refl
            coend .unique W factor' commutes' =
                -- uniqueness here follows from
                -- uniqueness of maps out of the coequalizer
                uniqueness
                    lmap
                    rmap
                    (W .nadir .snd)
                    (λ{ (c , Fcc) → W . ψ c Fcc})
                    (λ{( X , Y , f , Fxy ) → funExt⁻ (W .extranatural f) Fxy })
                    factor'
                    λ{(x , Fxx) → funExt⁻ (sym(commutes' x)) Fxx}
