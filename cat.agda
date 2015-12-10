-- Yu-Yang Lin
-- 26/11/2015
module cat where

open import Agda.Primitive
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

--=================================================================--
-- PART 1 : Small Categories                                       --
--=================================================================--
---------------------------------------------------------------------
-- For a small category we have the following definition           --
-- - Obj  : Set                           the set of objects       --
-- - Hom  : Obj → Obj → Set               the set of morphisms     --
-- - id   : ∀ X : Obj.Hom X X             Identity morphism        --
-- - _;_  : ∀ X, Y, Z : Obj.              Composition of morphisms --
--          Hom X Y → Hom Y Z → Hom X Z                            --
---------------------------------------------------------------------
-------------------------------------------------------------------
-- Added to this definition, we have the laws:                   --
-- -∀ X,Y : Obj. ∀ f : Hom. X Y. id ; f ≡ f    left identity  --
-- -∀ X,Y : Obj. ∀ f : Hom. X Y. f ; id ≡ f    right identity --
-- -∀ W,X,Y,Z : Obj.                              associativity  --
--    ∀ f : Hom. W X.                                            --
--    ∀ g : Hom. X Y.                                            --
--    ∀ h : Hom. Y Z.                                            --
--      f ; (g ; h) ≡ (f ; g) ; h                                --
-------------------------------------------------------------------
record Cat : Set₁ where
  field Ob  : Set
        Hom : Ob → Ob → Set
        id  : {X : Ob} → Hom X X
        _‣_ : {X Y Z : Ob} → Hom X Y → Hom Y Z → Hom X Z

        left_id  : {X Y : Ob} {f : Hom X Y} → id ‣ f ≡ f
        right_id : {X Y : Ob} {f : Hom X Y} → f ‣ id ≡ f
        assoc    : {W X Y Z : Ob}
                   {f : Hom W X}
                   {g : Hom X Y}
                   {h : Hom Y Z} → f ‣ (g ‣ h) ≡ (f ‣ g) ‣ h

--Now we can define a category--
--for instance, the category of endofunctions on Booleans--
--which rises from the monoid formed by the Boolean set and endofunctions--
data Bool : Set where
  true  : Bool
  false : Bool

data Unit : Set where
  unit : Unit

set𝔹 : Cat
set𝔹 = record
        { Ob  = Unit
        ; Hom = λ unit unit → Bool → Bool
        ; id  = λ b → b
        ; _‣_ = λ f g  → λ x → g (f x)
        ; left_id  = refl
        ; right_id = refl
        ; assoc    = refl
        }

--=================================================================--
-- PART 2 : Universe Polymorphic Category                          --
--=================================================================--
--If we wanted to define Set itself, we would need universe polymorphism--
record Category {l : Level} : Set (lsuc l) where
  field Ob  : Set l
        Hom : Ob → Ob → Set
        id  : {X : Ob} → Hom X X
        _‣_ : {X Y Z : Ob} → Hom X Y → Hom Y Z → Hom X Z

        left_id  : {X Y : Ob} {f : Hom X Y} → id ‣ f ≡ f
        right_id : {X Y : Ob} {f : Hom X Y} → f ‣ id ≡ f
        assoc    : {W X Y Z : Ob}
                   {f : Hom W X}
                   {g : Hom X Y}
                   {h : Hom Y Z} → f ‣ (g ‣ h) ≡ (f ‣ g) ‣ h

set : Category
set = record
        { Ob  = Set
        ; Hom = λ X Y → X → Y
        ; id  = λ x → x
        ; _‣_ = λ f g  → λ x → g (f x)
        ; left_id  = refl
        ; right_id = refl
        ; assoc    = refl
        }

--=================================================================--
-- PART 3 : Defining a Monad on category C
--=================================================================--
-- These are projections on the Category record to make life easier --
Ob      = Category.Ob
Hom     = Category.Hom
id      = Category.id
compose = Category._‣_

left  = Category.left_id
right = Category.right_id
assoc = Category.assoc
-------------------------------------------------------------------------------------------------------------------------
-- Given category C, a Monad on C consists of:                                                                         --
-- - T : C → C                                              an endofunctor                                             --
-- - η : {X : Ob C} → Hom C X (T X)                         a natural transformation                                   --
--                                                          from (X ∈ C) to a morphism (X → (T X)) ∈ C                 --
-- - μ : {X : Ob C} → Hom C (T T X) (T X)                   a natural transformation                                   --
--                                                          from (X ∈ C) to a morphism ((T T X) → (T X)) ∈ C           --
-- alternatively (as a Kleisli Triple):                                                                                --
--   T : Ob C → Ob C                                        the object part of the endofunctor                         --
-- - * : {X Y : Ob C} → Hom C X (T Y) → Hom C (T X) (T Y)   a transformation                                           --
--                                                          from morphism (f : X → T Y) to a morphism (f* : T X → T Y) --
-- Then we have the laws: left_monad_id, right_monad_id, monad_assoc.                                                  --
-------------------------------------------------------------------------------------------------------------------------
-- Here, we define a Monad as a Kleisli Triple instead of the traditional mathematical way. This is so I don't have to --
-- implement a record for functors. This is, additionally, more similar to monads defined in programming languages     --
-- such as Haskell.                                                                                                    --
-------------------------------------------------------------------------------------------------------------------------
record Monad {l : Level}{C : Category {l}} : Set (lsuc l) where
  field T  : Ob C → Ob C
        η  : {X : Ob C} → Hom C X (T X)
        _* : {X Y : Ob C} → Hom C X (T Y) → Hom C (T X) (T Y)

        monad_lid   : {X Y : Ob C} {f : Hom C X (T Y)} →
                      compose C η (f *) ≡ f
        monad_rid   : {X : Ob C} → (η {X})* ≡ id C {T X}
        monad_assoc : {X Y Z : Ob C} {f : Hom C X (T Y)} {g : Hom C Y (T Z)} →
                      compose C (f *) (g *) ≡ (compose C f (g *)) *

--Now we can check that our solution to the state monad was correct--
--First, we define the data type for the product and projections--
data _×_ (A B : Set) : Set where
  _,_ : A → B → A × B

π₁ : {A B : Set} → (A × B) → A
π₁ (a , b) = a

π₂ : {A B : Set} → (A × B) → B
π₂ (a , b) = b

πid : {A B : Set}{p : A × B} → π₁ p , π₂ p ≡ p
πid {A}{B}{a , b} = refl

--Would like to thank Martin Escardo and Paul Levy for help with this proof--
postulate exten : {X Y : Set}{f g : X → Y} → ((x : X) → f x ≡ g x) → (f ≡ g)

exten2 : {X Y Z : Set}{f g : X → Y → Z} → ((x : X)(y : Y) → f x y ≡ g x y) → (f ≡ g)
exten2 h = exten (λ x → exten(h x))

--Finally, we define the monad and prove it's properties--
state : Set → Monad {lsuc lzero}{set}
state S = record
          { T  = λ A → S → (S × A)
          ; η  = λ a → λ s → (s , a)
          ; _* = λ g f → λ s → g (π₂ (f s)) (π₁ (f s))
          ; monad_lid   = refl
          ; monad_rid   = lemma_rid
          ; monad_assoc = refl
          }
          where
            lemma_rid : {A : Ob set} →
                        (λ f s → π₁ (f s) , π₂ (f s))
                        ≡ id set {S → (S × A)}
            lemma_rid {A} =
              begin
                (λ f s → π₁ (f s) , π₂ (f s))
                ≡⟨ exten2 (λ f s → πid {p = f s}) ⟩
                (λ f s → f s)
                ≡⟨ refl ⟩
                (λ f → f)
              ∎
{-
(λ f s → π₁ (f s) , π₂ (f s))
(λ f s → f s)
(λ f → f)
-}
