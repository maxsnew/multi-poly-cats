-- Free category with a terminal object, over a Quiver
module Cubical.Categories.Constructions.Free.CategoryWithTerminal where

open import Cubical.Foundations.Prelude

open import Cubical.Categories.Category.Base
open import Cubical.Categories.Limits.Terminal.More
open import Cubical.Data.Quiver.Base
open import Cubical.Data.Sum.Base as Sum hiding (elim)
open import Cubical.Data.Unit
open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Presheaf
open import Cubical.Categories.Displayed.Presheaf
open import Cubical.Categories.Displayed.Limits.Terminal
open import Cubical.Foundations.Equiv
open import Cubical.Data.Sigma.Properties
open import Cubical.Categories.Displayed.Section.Base

private
  variable
    ℓg ℓg' ℓC ℓC' ℓCᴰ ℓCᴰ' : Level

CategoryWithTerminal' : (ℓC ℓC' : Level) → Type _
CategoryWithTerminal' ℓC ℓC' = Σ[ C ∈ Category ℓC ℓC' ] Terminal' C

-- freely throw in a terminal object
module _ (Ob : Type ℓg) where

    -- adjoin a new terminal object
    Ob' = Ob ⊎ Unit

    𝟙' : Ob'
    𝟙' = inr tt

    module _ (Q : QuiverOver Ob' ℓg') where
        open Category
        open QuiverOver
        open UniversalElement

        -- copied from Categories.Constructions.Free.Category.Quiver
        -- and suitably modified
        data Exp : Ob' → Ob' → Type (ℓ-max ℓg ℓg') where
            ↑_   : ∀ g → Exp (Q .dom g) (Q .cod g)
            idₑ  : ∀ {A} → Exp A A
            _⋆ₑ_ : ∀ {A B C} → (e : Exp A B) → (e' : Exp B C) → Exp A C
            ⋆ₑIdL : ∀ {A B} (e : Exp A B) → idₑ ⋆ₑ e ≡ e
            ⋆ₑIdR : ∀ {A B} (e : Exp A B) → e ⋆ₑ idₑ ≡ e
            ⋆ₑAssoc : ∀ {A B C D} (e : Exp A B)(f : Exp B C)(g : Exp C D)
                    → (e ⋆ₑ f) ⋆ₑ g ≡ e ⋆ₑ (f ⋆ₑ g)
            isSetExp : ∀ {A B} → isSet (Exp A B)
            !ₑ : ∀ {A} → Exp A 𝟙'
            isProp!ₑ : ∀ {A} → isProp (Exp A 𝟙')

        FC : Category _ _
        FC .ob = Ob'
        FC .Hom[_,_] = Exp
        FC .id = idₑ
        FC ._⋆_ = _⋆ₑ_
        FC .⋆IdL = ⋆ₑIdL
        FC .⋆IdR = ⋆ₑIdR
        FC .⋆Assoc = ⋆ₑAssoc
        FC .isSetHom = isSetExp

        FCTerminal' : Terminal' FC
        FCTerminal' .vertex = inr tt
        FCTerminal' .element = tt
        FCTerminal' .universal A .equiv-proof y =
            uniqueExists !ₑ refl (λ _ _ _ → refl) (λ _ _ → isProp!ₑ _ _)

        FreeCatw/Terminal' : CategoryWithTerminal' _ _
        FreeCatw/Terminal' = (FC , FCTerminal')

        module _ (Cᴰ : Categoryᴰ (FreeCatw/Terminal' .fst) ℓCᴰ ℓCᴰ')
            (term'ᴰ : Terminalᴰ Cᴰ (FreeCatw/Terminal' .snd)) where

            open import Cubical.Foundations.HLevels
            open import Cubical.Categories.Displayed.Reasoning
            open Section
            open UniversalElementᴰ
            open TerminalᴰNotation Cᴰ term'ᴰ

            private
                module FC = Category (FreeCatw/Terminal' .fst)
                module Cᴰ = Categoryᴰ Cᴰ

            -- given an interpretation of atomic objects
            module _ (ϕ : (v : Ob) → Cᴰ.ob[ inl v ]) where
                -- extend it to all objects
                ϕ* : (v : Ob') → Cᴰ.ob[ v ]
                ϕ* = Sum.elim (λ a → ϕ a) (λ b → term'ᴰ .vertexᴰ)

                -- and given an interpretation of atomic morphisms
                module _ (ψ : (e : Q .mor) → Cᴰ.Hom[ ↑ e ][ ϕ* (Q .dom e) , ϕ* (Q .cod e) ]) where

                    -- extend it to all morphisms
                    -- (copied from Cubical.Categories.Constructions.Free.Category.Quiver)
                    elim-F-homᴰ : ∀ {d d'} → (f : FC.Hom[ d , d' ]) →
                        Cᴰ.Hom[ f ][ ϕ* d , ϕ* d' ]
                    elim-F-homᴰ (↑ g) = ψ g
                    elim-F-homᴰ idₑ = Cᴰ.idᴰ
                    elim-F-homᴰ (f ⋆ₑ g) = elim-F-homᴰ f Cᴰ.⋆ᴰ elim-F-homᴰ g
                    elim-F-homᴰ (⋆ₑIdL f i) = Cᴰ.⋆IdLᴰ (elim-F-homᴰ f) i
                    elim-F-homᴰ (⋆ₑIdR f i) = Cᴰ.⋆IdRᴰ (elim-F-homᴰ f) i
                    elim-F-homᴰ (⋆ₑAssoc f g h i) =
                        Cᴰ.⋆Assocᴰ (elim-F-homᴰ f) (elim-F-homᴰ g) (elim-F-homᴰ h) i
                    elim-F-homᴰ (isSetExp f g p q i j) = isOfHLevel→isOfHLevelDep 2
                        ((λ x → Cᴰ.isSetHomᴰ))
                        ((elim-F-homᴰ f)) ((elim-F-homᴰ g))
                        ((cong elim-F-homᴰ p)) ((cong elim-F-homᴰ q))
                        ((isSetExp f g p q))
                        i j
                    elim-F-homᴰ {d = d} !ₑ = !tᴰ (ϕ* d)
                    elim-F-homᴰ {d = d} (isProp!ₑ f g i) = goal i
                        where
                        goal : elim-F-homᴰ f Cᴰ.≡[ isProp!ₑ f g ] elim-F-homᴰ g
                        goal = ≡[]-rectify Cᴰ
                            (≡[]∙ Cᴰ _ _
                            (𝟙ηᴰ {f = f} (elim-F-homᴰ f))
                            (symP (𝟙ηᴰ {f = g} (elim-F-homᴰ g))))

                    elim : GlobalSection Cᴰ
                    elim .F-obᴰ = ϕ*
                    elim .F-homᴰ = elim-F-homᴰ
                    elim .F-idᴰ = refl
                    elim .F-seqᴰ _ _ = refl
