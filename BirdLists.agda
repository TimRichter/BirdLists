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

++associative : {A : Set} → (xs ys zs : List A) → (xs ++ ys) ++ zs ≡ xs ++ ys ++ zs
++associative []        ys zs = refl
++associative (x :: xs) ys zs = (((x :: xs) ++ ys) ++ zs)
                                  ≡⟨ refl ⟩≡                       -- by definition of ++
                                ((x :: (xs ++ ys)) ++ zs)
                                  ≡⟨ refl ⟩≡                       -- by def. ++ again
                                (x :: ((xs ++ ys) ++ zs))
                                  ≡⟨ (≡cong (x ::_)
                                   (++associative xs ys zs)) ⟩≡    -- heart of the matter: use induction hypothesis
                                (x :: (xs ++ (ys ++ zs)))
                                  ≡⟨ refl ⟩≡                       -- by def. of ++ again
                                ((x :: xs) ++ (ys ++ zs))
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

infixr 18 _*_

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
-- the assumption |m ≤ n|:

-- runlength : (m n : ℕ) → (# [ m …… n ]) ≡ (suc n) - m

-- Before giving the (somewhat lengthy ... sorry) proof, we
-- prove that map preserves length. That might also be handy elsewhere. 

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

infix 20 _∘_   -- \o  or  \circ  or  \comp  

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


-- Bird writes (p 5): "... if f is an injective function with inverse f^{-1},
-- then (f *)^{-1} = f^{-1} * ."  I think he means: if for f : A → B there
-- exists invf : B → A such that ∀ a : A . invf (f a) ≡ a  ( f is usually called
-- "split injective" in this case), then (f *) is also split injective, more
-- precisely:   ∀ as : List A . invf * (f * as) ≡ as.

mapinv : {A B : Set} → (f : A → B) → (invf : B → A) → ((a : A) → invf (f a) ≡ a) →
         (as : List A) → invf * (f * as) ≡ as
mapinv f invf splits [] = refl
mapinv f invf splits (a :: as) = (invf * (f * (a :: as)))
                                   ≡⟨ refl ⟩≡
                                 (invf (f a) :: invf * (f * as))
                                   ≡⟨ ≡cong ( _:: invf * (f * as)) (splits a) ⟩≡
                                 (a :: invf * (f * as))
                                   ≡⟨ ≡cong ( a ::_ ) (mapinv f invf splits as) ⟩≡
                                 (a :: as)
                                   QED


-- ** 1.5 Filter

infixr 20 _◃_    -- \tw or \triangleleft
 
_◃_ : {A : Set} → (A → 𝔹) → List A → List A
p ◃ [] = []
p ◃ (a :: as) = if (p a) then a :: (p ◃ as) else (p ◃ as)


filter++distribute : {A : Set} → (p : A → 𝔹) → (xs ys : List A) → p ◃ (xs ++ ys) ≡ (p ◃ xs) ++ (p ◃ ys)
filter++distribute p [] ys = refl
filter++distribute p (x :: xs) ys with p x
filter++distribute p (x :: xs) ys | true  = ≡cong (x ::_) (filter++distribute p xs ys)
filter++distribute p (x :: xs) ys | false = filter++distribute p xs ys

-- commutativity of filter application
-- we first prove a lemma:

filterLemma : {A : Set} → (p q : A → 𝔹) → (x : A) → (xs : List A) →
              p ◃ q ◃ (x :: xs) ≡ if (p x) ∧ (q x) then x :: p ◃ q ◃ xs else p ◃ q ◃ xs
filterLemma p q x xs with q x
filterLemma p q x xs | true with p x
...                         | true  = refl
...                         | false = refl
filterLemma p q x xs | false with p x
...                         | true  = refl
...                         | false = refl


filtercommutes : {A : Set} → (p q : A → 𝔹) → (xs : List A) →
                 p ◃ q ◃ xs ≡ q ◃ p ◃ xs
filtercommutes p q [] = refl
filtercommutes p q (x :: xs) =
    (p ◃ q ◃ (x :: xs))
       ≡⟨ filterLemma p q x xs ⟩≡
    (if p x ∧ q x then x :: p ◃ q ◃ xs else p ◃ q ◃ xs)
       ≡⟨ ≡cong (if_then x :: p ◃ q ◃ xs else p ◃ q ◃ xs) (∧commutative (p x) (q x))⟩≡
    (if q x ∧ p x then x :: p ◃ q ◃ xs else p ◃ q ◃ xs)
       ≡⟨ ≡cong (λ y → if q x ∧ p x then (x :: y) else p ◃ q ◃ xs) (filtercommutes p q xs)⟩≡
    (if q x ∧ p x then x :: q ◃ p ◃ xs else p ◃ q ◃ xs)
       ≡⟨ ≡cong (λ y → if q x ∧ p x then (x :: q ◃ p ◃ xs) else y) (filtercommutes p q xs)⟩≡
    (if q x ∧ p x then x :: q ◃ p ◃ xs else q ◃ p ◃ xs)
       ≡⟨ ≡symm (filterLemma q p x xs) ⟩≡
    (q ◃ p ◃ (x :: xs))
       QED

filterIdempotent : {A : Set} → (p : A → 𝔹) → (xs : List A) →
                   p ◃ p ◃ xs ≡ p ◃ xs
filterIdempotent p [] = refl
filterIdempotent p (x :: xs) =
    (p ◃ p ◃ (x :: xs))
       ≡⟨ filterLemma p p x xs ⟩≡
    (if (p x) ∧ (p x) then x :: p ◃ p ◃ xs else p ◃ p ◃ xs )
       ≡⟨ ≡cong (if_then x :: p ◃ p ◃ xs else p ◃ p ◃ xs) (∧diag (p x)) ⟩≡
    (if (p x) then x :: p ◃ p ◃ xs else p ◃ p ◃ xs )
       ≡⟨ ≡cong (λ y → if p x then x :: y else p ◃ p ◃ xs) (filterIdempotent p xs) ⟩≡
    (if (p x) then x :: p ◃ xs else p ◃ p ◃ xs )
       ≡⟨ ≡cong (λ y → if p x then x :: p ◃ xs else y) (filterIdempotent p xs) ⟩≡
    (if (p x) then x :: p ◃ xs else p ◃ xs )
       ≡⟨ refl ⟩≡
    (p ◃ (x :: xs))
       QED

filterMap : {A B : Set} → (f : A → B) → (p : B → 𝔹) → (xs : List A) →
            p ◃ (f * xs) ≡ f * ((p ∘ f) ◃ xs)
filterMap f p [] = refl
filterMap f p (x :: xs) =
    (p ◃ (f * (x :: xs)))
      ≡⟨ refl ⟩≡
    (if p (f x) then f x :: p ◃ (f * xs) else p ◃ (f * xs))
      ≡⟨ ≡cong (λ y → if p (f x) then f x :: y else p ◃ (f * xs)) (filterMap f p xs) ⟩≡
    (if p (f x) then f x :: f * ((p ∘ f) ◃ xs) else p ◃ (f * xs))
      ≡⟨ ≡cong (λ y → if p (f x) then f x :: f * ((p ∘ f) ◃ xs) else y) (filterMap f p xs) ⟩≡
    (if p (f x) then (f x :: f * ((p ∘ f) ◃ xs)) else (f * ((p ∘ f) ◃ xs)))
      ≡⟨ ≡symm (iffun (f *_) (p (f x)) (x :: (p ∘ f) ◃ xs) ((p ∘ f) ◃ xs)) ⟩≡
    (f * (if p (f x) then x :: (p ∘ f) ◃ xs  else (p ∘ f) ◃ xs))  
      ≡⟨ refl ⟩≡
    (f * ((p ∘ f) ◃ (x :: xs)))
      QED

-- Bird remarks (p. 5) that the three properties above can be
-- written as equalities between functions, using function composition.
-- Note, however, that these are not our ≡-equalities, but rather
-- "pointwise" ≡-equalities of functions. The functions on both sides
-- compute the same value for each argument, but are not the same
-- as λ-terms! We therefore define "extensional equality":

infix 5 _≡≡_

_≡≡_ : {A B : Set} → (f g : A → B) → Set
_≡≡_ {A} f g = (x : A) → f x ≡ g x

-- Now the following are now just reformulations of the lemmata above:

filtercommutes' : {A : Set} → (p q : A → 𝔹) →
                  (p ◃_) ∘ (q ◃_) ≡≡ (q ◃_) ∘ (p ◃_)
filtercommutes' = filtercommutes

filterIdempotent' : {A : Set} → (p : A → 𝔹) →
                    (p ◃_) ∘ (p ◃_) ≡≡ (p ◃_)
filterIdempotent' = filterIdempotent

filterMap' : {A B : Set} → (f : A → B) → (p : B → 𝔹) →
             (p ◃_) ∘ (f *_) ≡≡  (f *_) ∘ ((p ∘ f) ◃_)
filterMap' = filterMap

-- ** 1.6 Operator precedence

-- these should be ok:
--   function application binds strongest
--   ++ binds weaker than map
-- anything else?


-- * 2 Reduction
-- ** 2.1 The reduction operators

-- Bird defines reduction informally:
--
--  ⊕ / [a₁,a₂,...,aₙ] = a₁ ⊕ a₂ ⊕ ... ⊕ aₙ
--
-- and says that "... the form ⊕ / x is only permitted when
-- ⊕ is an *associative* operator."
--
-- So we first define, for a binary operator ⊕ on a type A,
-- the type isAssociative:


isAssociative : {A : Set} → (_⊕_ : A → A → A) → Set
isAssociative {A} _⊕_ = (a b c : A) → (a ⊕ b) ⊕ c ≡ a ⊕ (b ⊕ c)

-- we already proved associativity of _++_ and of addition on ℕ 

isAssociative++ : {A : Set} → isAssociative {List A} (_++_)
isAssociative++ = ++associative

isAssociative+ℕ : isAssociative _+_
isAssociative+ℕ = +associative


-- - ⊕ / [] has to be a (left and right) unit for ⊕ ! f the operator ⊕
--   doesn't have a unit, ⊕ / [] is undefined


record BOU (A : Set) : Set where  -- binary operation with unit
  constructor BO
  field
    _⊕_ : A → A → A
    e   : A

{-

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
