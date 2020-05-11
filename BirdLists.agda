{-# OPTIONS --without-K #-}


module BirdLists where

-- * Intro *
--
-- This is an attempt to (re)implement in Agda some of the
-- operations on lists that Richard Bird introduced in his
-- seminal 1986 paper "An Introduction to the Theory of Lists"
-- (https://www.cs.ox.ac.uk/files/3378/PRG56.pdf).
--
-- The implementation is meant to accompany our reading of Bird's
-- text started on April 21st in the Potsdam Cartesian Seminar.
--
-- We'll try to stay as close as possible to Bird's concepts
-- and notations. But while Bird defines many functions (first)
-- informally, we shall give a proper formal implementation.
-- And, more importantly, whenever Bird (informally...) gives a
-- property of some function or operation, we shall try to state
-- this property formally and prove it.
--
-- At some points, we have to deviate:
--
-- - Our implementation language, Agda, requires functions to be
--   total. Bird's functional language (looking a lot like Haskell
--   which however wasn't there yet in 1986...) on the other hand,
--   allows non-total functions, and Bird doesn't worry too much
--   about totality. So, we'll have to do more work here, e.g.
--   restrict the domain (or expand the codomain) of functions
--   to make them total.
--
-- - We need a formal definition of List and ℕ right from
--   the start to be able to formally define the (higher order) functions
--   that Bird just describes in a non-formal, intuitive way.
--
-- (t.b.c.)
--
-- We will not use any Agda libraries but do everything from
-- scratch.


-- * Preparation I: equality and equational reasoning
--
-- We want to prove the equations stated in Bird's paper,
-- so we first make some tools for this. We'll need the
-- "equality" (or "identity") type

infix 5 _≡_

data _≡_ {A : Set} (x : A) : A → Set where
  refl : x ≡ x

-- For any |A : Set| and any |x y : A|, |x ≡ y| is a type.
-- | p : x ≡ y | stands for "p is a proof for | x ≡ y |. There
-- is just one constructor, |refl|, of type |x ≡ x|. One
-- would expect to be able to prove the following statements
-- were uip stands for "uniqueness of identity proofs":

{-

uip1 : {A : Set} → {x y : A} → ( p : x ≡ x) → p ≡ refl 
uip1 refl = refl

uip2 : {A : Set} → {x y : A} → ( p q : x ≡ y) → p ≡ q
uip2 refl refl = refl

-}

-- Indeed if you disable the "without-K" option in the first line,
-- these would typecheck. But "without-K", these are no longer provable,
-- and thus the identities (and indentities of identities of
-- identities...) can have interesting structure.

-- While some forms of pattern matching are forbidden with the
-- without-K option, others are fine. We can show that |_≡_| is
-- an equivalence relation: the constructor |refl {A} {x}| itself
-- is a proof of reflexivity

≡refl : {A : Set} → {x : A} → x ≡ x
≡refl = refl

-- |_≡_| is also transitive:

≡trans : {A : Set} → {x y z : A} → x ≡ y → y ≡ z → x ≡ z
≡trans refl refl = refl

-- and symmetric:

≡symm : {A : Set} → {x y : A} → x ≡ y → y ≡ x
≡symm refl = refl

-- Using |refl| and |≡trans|, we can prove more complicated equations
-- by concatenating simple steps. The following functions are nothing
-- more than |refl| and |≡trans| with funny names and argument placements.
-- Moreover, of the three arguments of |_≡⟨_⟩≡_|, the first is actually
-- redundand - it can be inferred from the type of the second one!
-- All this may seem weird, but is done to make our stepwise equality
-- proofs look very similar to "equational reasoning" on paper, see below.

_QED : {A : Set} -> (x : A) → x ≡ x
x QED = refl

infixr 10 _≡⟨_⟩≡_

_≡⟨_⟩≡_ : {A : Set} (x : A) {y z : A} → x ≡ y → y ≡ z → x ≡ z
x ≡⟨ p ⟩≡ q = ≡trans p q

-- We'll also often need

≡cong : {A B : Set} {x y : A} (f : A → B) → x ≡ y → f x ≡ f y
≡cong f refl = refl

-- expressing that |≡| is a congruence relation with respect to 
-- applying any function.

-- * Preparation II: basic data types

-- ** Lists

infixr 10 _::_

data List (A : Set) : Set where 
  []   : List A
  _::_ : A → List A → List A

-- and natural numbers

data ℕ : Set where
  zero : ℕ
  suc  : ℕ → ℕ

-- with addition

infixr 40 _+_

_+_ : ℕ → ℕ → ℕ
zero    + m = m
(suc n) + m = suc (n + m)

-- and (truncated) subtraction

infix 40 _-_

_-_ : ℕ → ℕ → ℕ
zero - m = zero
suc n - zero = suc n
suc n - suc m = n - m

-- First example of a polymorphic function defined by
-- pattern matching and using recursion: the length of a list

# : {A : Set} → List A → ℕ
# []        = zero
# (x :: xs) = suc (# xs)

-- Here is |*| ( pronounced and nowadays normally also
-- written |map|), the single most important polymorphic
-- function! Again we define it recursively using pattern
-- matching:

_* : {A B : Set} → (A → B) → List A → List B
(f *) []        = []
(f *) (x :: xs) = f x :: (f *) xs

-- Bird introduces the special notation [m..n] for
-- lists of integers. We can use |*| to
-- define it:

-- Agda likes neither ".." nor "…" (\ldots) in
-- the middle,of a mixfix operator, so we use "……" (twice \ldots)

infix 20 [_……_]

[_……_] : ℕ → ℕ → (List ℕ)
[ zero …… zero ]       = zero :: []
[ zero …… (suc n) ]    = zero :: (suc *) [ zero …… n ]
[ (suc m) …… zero ]    = []
[ (suc m) …… (suc n) ] = (suc *) [ m …… n ]


-- List concatenation

infixr 20 _++_

_++_ : {A : Set} → List A → List A → List A
[]        ++ ys = ys
(x :: xs) ++ ys = x :: xs ++ ys



-- Here's a very easy one: we defined the operation |++| so that
-- |[] ++ xs| is |xs| !  

[]leftid++ : {A : Set} → (xs : List A) → [] ++ xs ≡ xs
[]leftid++ xs = ([] ++ xs)
                ≡⟨ refl ⟩≡                                       -- this is just by definition of |++|
                (xs)
                QED

-- To show that |[]| is also a right identity for |++|, we have to
-- use an inductive argument

[]rightid++ : {A : Set} → (xs : List A) → xs ++ [] ≡ xs
[]rightid++ [] = refl                                            -- [] ++ [] ≡ [] is again by definition
[]rightid++ (x :: xs) = ((x :: xs) ++ [])
                        ≡⟨ refl ⟩≡                               -- def. of ++, now for the :: pattern
                        (x :: (xs ++ []))
                        ≡⟨ ≡cong (x ::_) ([]rightid++ xs) ⟩≡     -- We use ≡cong to apply the induction hypothesis
                        (x :: xs)                                -- | xs ++ [] ≡ xs | on the right of | x :: |,
                        QED                                      -- and are done.
                        
-- Associativity of |++|

++associative : {A : Set} → (xs ys zs : List A) → (xs ++ ys ++ zs) ≡ ((xs ++ ys) ++ zs)
++associative []        ys zs = refl
++associative (x :: xs) ys zs = ((x :: xs) ++ (ys ++ zs))
                                ≡⟨ refl ⟩≡                       -- by definition of ++
                                (x :: (xs ++ (ys ++ zs)))
                                ≡⟨ (≡cong (x ::_)
                                   (++associative xs ys zs)) ⟩≡  -- heart of the matter: use induction hypothesis
                                (x :: ((xs ++ ys) ++ zs))
                                ≡⟨ refl ⟩≡                       -- by def. ++ again
                                ((x :: (xs ++ ys)) ++ zs)
                                ≡⟨ refl ⟩≡                       -- by def. ++ again
                                (((x :: xs) ++ ys) ++ zs)
                                QED

-- The relationsship between |#|, |++|, and |+|

#maps++to+ : {A : Set} -> (xs ys : List A) → # (xs ++ ys) ≡ # xs + # ys
#maps++to+ {A} [] ys = (# ([] ++ ys ))                            -- first the base case where xs is empty
                       ≡⟨ ≡cong # ([]leftid++ ys) ⟩≡
                       (# ys)
                       ≡⟨ refl ⟩≡                                 -- by the definition of add
                       (zero + # ys)
                       ≡⟨ refl ⟩≡                                 -- by definition of #
                       ((# {A} []) + # ys)
                       QED
                       
#maps++to+ (x :: xs) ys  = (# ((x :: xs) ++ ys))                  -- now the induction step
                           ≡⟨ ≡cong #
                              (refl {x = x :: xs ++ ys}) ⟩≡       -- def. ++ (unfortunately, agda doesn't find the  
                           (# (x :: xs ++ ys))                    --          implicit argument of refl by itself)
                           ≡⟨ refl ⟩≡                             -- def. #
                           (suc (# (xs ++ ys))
                           ≡⟨ ≡cong suc (#maps++to+ xs ys) ⟩≡     -- use induction hypotheses
                           (suc (# xs + # ys))
                           ≡⟨ refl ⟩≡                             -- def. +
                           ((suc (# xs)) + # ys)
                           ≡⟨ refl ⟩≡                             -- def. #
                           (((# (x :: xs)) + (# ys)))
                           QED)


record BOU (A : Set) : Set where  -- binary operation with unit
  constructor BO
  field
    _⊕_ : A → A → A
    e   : A

infix 10 _/_

_/_ : {A : Set} → BOU A → List A → A
op@(BO _⊕_ e) / []        = e 
op@(BO _⊕_ e) / (x :: xs) = x ⊕ (op / xs)


-- _<<_ : {A : Set} → A → A → A
-- a << b = a


-- data Maybe (A : Set) : Set where
--   Nothing : Maybe A
--   Just    : A → Maybe A

-- M ( A → B ) -> M A → M B 

-- A → (A → A)
-- M A → M (A → A)
-- M A → M A → M A

-- _' : {A : Set} → (A → A → A) → (Maybe A → Maybe A → Maybe A)
-- (_o_) ' Nothing mb = Nothing
-- (_o_) ' ma 





-- * 1 Elementary operations
-- ** 1.1 List notation
-- ** 1.2 Length
-- ** 1.3 Concatenation
-- ** 1.4 Map
-- ** 1.5 Filter
-- ** 1.6 Operator precedence
-- * 2 Reduction
-- ** 2.1 The reduction operators
-- ** 2.2 Fictitious values
-- ** 2.3 Homomorphisms
-- ** 2.4 Definition by homomorphisms
-- ** 2.5 Example: processing text
-- ** 2.6 Promotion lemmas
-- ** 2.7 Selection and indeterminacy
-- * 3 Directed reduction and recursion
-- ** 3.1 Left and right reduction
-- ** 3.2 Recursive characterisation
-- ** 3.3 Efficiency considerations
-- ** 3.4 Duality and specialisation
-- ** 3.5 Accumulation
-- * 4 Segments and partitions
-- ** 4.1 Definitions
-- ** 4.2 Segment decomposition
-- ** 4.3 Extremal problems
-- ** 4.4 Partitions
-- ** 4.5 Conclusions