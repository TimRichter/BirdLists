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
-- text started on April 21st 2020 in the Potsdam Cartesian Seminar.
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
-- * Preparation II: basic data types - Lists and natural numbers
--   see module Basics

open import Basics


-- * 1. Elementary operations
-- ** 1.1 List notation

-- Bird introduces lists as "linearly ordered collections
-- of values of the same general nature" ...
--
-- We (in Basics) defined |List A| as an inductive datatype
-- with the constructors |[]| and |_::_| (read "cons").
-- Bird gives this representation later (p.23, using ":"
-- instead of "::"). For now just think of
-- a₁ :: a₂ :: ... aₙ :: []   as our notation for   
-- [a₁,a₂,...,aₙ].
--
-- the empty list has a polymorphic type:

aListOfAllTypes : {A : Set} → List A
aListOfAllTypes = []

-- note that we couldn't possibly have defined
-- this differently!
-- Speaking of polymorphism, Bird mentions the identity
-- function:

id : {A : Set} → A → A
id x = x

-- ** 1.2 Length

-- First example of a polymorphic function defined by
-- pattern matching and using recursion: the length of a list

# : {A : Set} → List A → ℕ
# []        = zero
# (x :: xs) = suc (# xs)

-- to formulate and prove |# [m ... n] = n - m + 1| we have
-- to define notation, see below...

-- ** 1.3 Concatenation

infixr 20 _++_

_++_ : {A : Set} → List A → List A → List A
[]        ++ ys = ys
(x :: xs) ++ ys = x :: xs ++ ys

-- Bird gives the type of concatenation as
-- | ++ : [α] × [α] → [α] |. We defined the
-- "curried" variant...

infixr 20 _×_
infixr 20 _,_

data _×_ (A B : Set) : Set where
  _,_ :  A → B → A × B

curry : {A B C : Set} → ((A × B) → C) → A → B → C
curry f x y = f (x , y)

uncurry : {A B C : Set} → (A → B → C) → (A × B) → C
uncurry g (x , y) = g x y

-- And now the first proofs.
-- Here's an easy one: we *defined* the operation |++| so that
-- |[] ++ xs| is |xs| !  

[]++leftunit : {A : Set} → (xs : List A) → [] ++ xs ≡ xs
[]++leftunit xs = ([] ++ xs)
                ≡⟨ refl ⟩≡                                       -- this is just by definition of |++|
                (xs)
                QED

-- To show that |[]| is also a right identity for |++|, we have to
-- use an inductive argument

[]++rightunit : {A : Set} → (xs : List A) → xs ++ [] ≡ xs
[]++rightunit [] = refl                                            -- [] ++ [] ≡ [] is again by definition
[]++rightunit (x :: xs) = ((x :: xs) ++ [])
                        ≡⟨ refl ⟩≡                               -- def. of ++, now for the :: pattern
                        (x :: (xs ++ []))
                        ≡⟨ ≡cong (x ::_) ([]++rightunit xs) ⟩≡     -- We use ≡cong to apply the induction hypothesis
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
                         ≡⟨ ≡cong # ([]++leftunit ys) ⟩≡
                       (# ys)
                         ≡⟨ refl ⟩≡                               -- by the definition of add
                       (zero + # ys)
                         ≡⟨ refl ⟩≡                               -- by definition of #
                       ((# {A} []) + # ys)
                         QED
                       
#maps++to+ (x :: xs) ys  = (# ((x :: xs) ++ ys))                  -- now the induction step
                             ≡⟨ ≡cong #
                              (refl {x = x :: xs ++ ys}) ⟩≡       -- def. ++ (unfortunately, agda doesn't find the  
                           (# (x :: xs ++ ys))                    --          implicit argument of refl by itself)
                             ≡⟨ refl ⟩≡                           -- def. #
                           (suc (# (xs ++ ys)))
                             ≡⟨ ≡cong suc (#maps++to+ xs ys) ⟩≡   -- use induction hypotheses
                           (suc (# xs + # ys))
                             ≡⟨ refl ⟩≡                           -- def. +
                           ((suc (# xs)) + # ys)
                             ≡⟨ refl ⟩≡                           -- def. #
                           (((# (x :: xs)) + (# ys)))
                             QED



-- ** 1.4 Map

-- Here is |*| (pronounced and often also written |map|),
-- a very important polymorphic function! Again we define
-- it recursively by pattern matching:

_*_ : {A B : Set} → (A → B) → List A → List B
f * []        = []
f * (x :: xs) = f x :: f * xs

-- Bird introduces the special notation [m..n] for
-- lists of integers. We can use |*| to define it:
-- Agda likes neither ".." nor "…" (\ldots) in the middle
-- of a mixfix operator, so we use "……" (twice \ldots)

infix 20 [_……_]

[_……_] : ℕ → ℕ → (List ℕ)
[ zero …… zero ]       = zero :: []
[ zero …… (suc n) ]    = zero :: suc * [ zero …… n ]
[ (suc m) …… zero ]    = []
[ (suc m) …… (suc n) ] = suc * [ m …… n ]


-- Now we can give the proof of | # [m ... n] = n - m + 1 |.
-- But we modify a little. Bird claims this formula to hold
-- whenever |m ≤ n|. If we write the right hand side expression
-- as | (suc n) - m | with our truncating |-|, we don't need
-- the |m ≤ n|:

-- runlength : (m n : ℕ) → (# [ m …… n ]) ≡ (suc n) - m

-- Before giving the (somewhat lengthy ... sorry) proof, we
-- formulate a lemma that might be handy elsewhere: 

*preserves# : {A B : Set} → (f : A → B) → (as : List A) → # (f * as) ≡ # as
*preserves# f [] = refl
*preserves# f (a :: as) = (# (f * (a :: as)))
                                   ≡⟨ refl ⟩≡                      -- def. * 
                                 (# (f a :: f * as))
                                   ≡⟨ refl ⟩≡                      -- def. #
                                 (suc (# (f * as)))
                                   ≡⟨ ≡cong suc (*preserves# f as) ⟩≡  -- induction hypothesis
                                 (suc (# as))
                                   ≡⟨ refl ⟩≡
                                 (# (a :: as))
                                   QED

runlength : (m n : ℕ) → (# [ m …… n ]) ≡ (suc n) - m
runlength zero    zero    = (# [ zero …… zero ])
                              ≡⟨ refl ⟩≡                          -- def. [ …… ]
                            (# (zero :: []))
                              ≡⟨ refl ⟩≡                          -- def. #
                            (suc ( # {A = ℕ} []))                 -- the typechecker needs a hint here...
                              ≡⟨ refl ⟩≡                          -- def. #
                            (suc zero)
                              ≡⟨ refl ⟩≡                          -- def. -
                            ((suc zero) - zero)
                              QED
runlength zero    (suc n) = (# [ zero …… (suc n) ])
                              ≡⟨ refl ⟩≡                          -- def. [ …… ], def. #
                            (suc (# (suc * [ zero …… n ])))
                              ≡⟨ ≡cong suc (*preserves# suc [ zero …… n ]) ⟩≡  -- apply lemma maplength
                            (suc (# [ zero …… n ]))
                              ≡⟨ ≡cong suc (runlength zero n) ⟩≡  -- induction hypothesis
                            (suc (suc n - zero))
                              ≡⟨ refl ⟩≡                          -- def. - (twice)
                            (suc (suc n)  - zero)
                              QED
runlength (suc m) zero = refl                                     -- both sides zero by the definitions
runlength (suc m) (suc n) = (# [ (suc m) …… (suc n) ])
                              ≡⟨ refl ⟩≡                          -- def. [ …… ]
                            (# (suc * [ m …… n ]))
                              ≡⟨ *preserves# suc [ m …… n ] ⟩≡   -- the lemma again
                            (# [ m …… n ])
                              ≡⟨ runlength m n ⟩≡                 -- induction hypothesis
                            (suc n - m)
                              ≡⟨ refl ⟩≡                          -- def. -
                            (suc (suc n) - suc m)
                              QED

-- map distributes over ++

map++distribute : {A B : Set} → (f : A → B) → (as₁ as₂ : List A) →
                                   f * (as₁ ++ as₂) ≡ (f * as₁) ++ (f * as₂)
map++distribute f [] _ = refl
map++distribute f (a :: as₁) as₂ = (f * ((a :: as₁) ++ as₂))
                                     ≡⟨ refl ⟩≡                          -- def. ++, def. *
                                   ((f a) :: f * (as₁ ++ as₂))
                                     ≡⟨ ≡cong ((f a) ::_)               
                                         (map++distribute f as₁ as₂) ⟩≡  -- induction hypothesis
                                   ((f a) :: (f * as₁) ++ (f * as₂))
                                     ≡⟨ refl ⟩≡                          -- def. ++, def. *
                                   ((f * (a :: as₁)) ++ (f * as₂))
                                     QED

-- function composition

infix 20 _∘_ 

_∘_ : {A B C : Set} → (B → C) → (A → B) → (A → C)
f ∘ g = λ x → f (g x)

-- map distributes backwards over function composition

map∘distribute : {A B C : Set} → (f : B → C) → (g : A → B) → (as : List A) →
                                   (f ∘ g) * as ≡ ((f *_) ∘ (g *_)) as
map∘distribute f g [] = refl
map∘distribute f g (a :: as) = ((f ∘ g) * (a :: as))
                                 ≡⟨ refl ⟩≡                    -- def. ∘, def. *
                               (f (g a) :: ((f ∘ g) * as))
                                 ≡⟨ ≡cong (f (g a) ::_)
                                   (map∘distribute f g as) ⟩≡
                               (f (g a) :: (((f *_) ∘ (g *_)) as))
                                 ≡⟨ refl ⟩≡
                               (((f *_) ∘ (g *_)) (a :: as))
                                 QED

-- discuss "inverse" of an injective function...
-- use something like this?

data FiberOver_of_ {A B : Set} : (b : B) → (f : A → B) → Set where
   _of_↦_since_ : (f : A → B) → (a : A) → (b : B) → ((f a) ≡ b) → FiberOver b of f




{- t.b.c.


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

-}



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
