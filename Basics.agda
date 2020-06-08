{-# OPTIONS --without-K #-}

module Basics where

-- * Preparation I: equality and equational reasoning
--
-- We want to prove the equations stated in Bird's paper,
-- so we first make some tools for this. We'll need the
-- "equality" (or "identity") type

infix 5 _≡_   -- \equiv

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

infixr 10 _≡⟨_⟩≡_   -- \equiv\langle \rangle\equiv

_≡⟨_⟩≡_ : {A : Set} (x : A) {y z : A} → x ≡ y → y ≡ z → x ≡ z
x ≡⟨ p ⟩≡ q = ≡trans p q

-- We'll also often need

≡cong : {A B : Set} {x y : A} (f : A → B) → x ≡ y → f x ≡ f y
≡cong f refl = refl

-- expressing that |≡| is a congruence relation with respect to 
-- applying any function.

≡transport : {A : Set} → {P : A → Set} → {x y : A} → x ≡ y → P x → P y
≡transport refl px = px


-- * Preparation II: basic data types - Lists and natural numbers

infixr 10 _::_

data List (A : Set) : Set where 
  []   : List A
  _::_ : A → List A → List A

data ℕ : Set where
  zero : ℕ
  suc  : ℕ → ℕ

-- We'll need addition

infixr 40 _+_

_+_ : ℕ → ℕ → ℕ
zero    + m = m
(suc n) + m = suc (n + m)

-- (truncated) subtraction

infix 40 _-_

_-_ : ℕ → ℕ → ℕ
zero - m = zero
suc n - zero = suc n
suc n - suc m = n - m


-- basic arithmetics lemmata

-- zero is left unit for +

zero+leftunit : (m : ℕ) → zero + m ≡ m
zero+leftunit m = refl

-- suc can be pulled out from a left summand

sucleft+suc : (m n : ℕ) → suc m + n ≡ suc (m + n)
sucleft+suc m n = refl

-- zero is a right unit for +

zero+rightunit : (m : ℕ) → m + zero ≡ m
zero+rightunit zero = refl
zero+rightunit (suc m) = (suc m + zero)
                         ≡⟨ sucleft+suc m zero ⟩≡
                         (suc (m + zero))
                         ≡⟨ ≡cong suc (zero+rightunit m) ⟩≡
                         (suc m)
                         QED

-- suc can be pulled out from a right summand

sucright+suc : (m n : ℕ) → m + suc n ≡ suc (m + n)
sucright+suc zero n = (zero + suc n)
                      ≡⟨ zero+leftunit _ ⟩≡
                      (suc n)
                      ≡⟨ ≡cong suc (≡symm (zero+leftunit n))⟩≡ 
                      (suc (zero + n))
                      QED
sucright+suc (suc m) n = (suc m + suc n)
                         ≡⟨ sucleft+suc m _ ⟩≡ 
                         (suc (m + suc n))
                         ≡⟨ ≡cong suc (sucright+suc m n)⟩≡
                         (suc (suc (m + n)))
                         ≡⟨ ≡cong suc (≡symm (sucleft+suc m n)) ⟩≡ 
                         (suc (suc m + n))
                         QED

-- + is commutative

+commutative : (m n : ℕ) → m + n ≡ n + m
+commutative zero n = (zero + n)
                      ≡⟨ zero+leftunit n ⟩≡
                      (n)
                      ≡⟨ ≡symm (zero+rightunit n)⟩≡ 
                      (n + zero)
                      QED
+commutative (suc m) n = (suc m + n)
                         ≡⟨ sucleft+suc m n ⟩≡ 
                         (suc (m + n))
                         ≡⟨ ≡cong suc (+commutative m n)⟩≡
                         (suc (n + m))
                         ≡⟨ ≡symm (sucright+suc n m) ⟩≡ 
                         (n + suc m)
                         QED
                         
-- + is associative

+associative : (l m n : ℕ) → (l + m) + n ≡ l + m + n
+associative zero m n = ((zero + m) + n)
                        ≡⟨ ≡cong (_+ n) (zero+leftunit m) ⟩≡
                        (m + n)
                        ≡⟨ zero+leftunit (m + n)⟩≡
                        (zero + m + n)
                        QED
+associative (suc l) m n = ((suc l + m) + n)
                           ≡⟨ ≡cong (_+ n) (sucleft+suc l m) ⟩≡
                           (suc (l + m) + n)
                           ≡⟨ (sucleft+suc (l + m) n) ⟩≡
                           (suc ((l + m) + n))
                           ≡⟨ ≡cong suc (+associative l m n)⟩≡
                           (suc (l + m + n))
                           ≡⟨ ≡symm (sucleft+suc l _) ⟩≡
                           (suc l + m + n)
                           QED
-- multiplication

infixr 41 _⋆_   -- \star

_⋆_ : ℕ → ℕ → ℕ
zero    ⋆ _ = zero
(suc m) ⋆ n = m ⋆ n + n 

one : ℕ
one = suc zero

two : ℕ
two = suc one

-- zero is left absorbing for ⋆

zero⋆leftabsorbing : (n : ℕ) → zero ⋆ n ≡ zero
zero⋆leftabsorbing n = refl

-- the suc clause of the definition of ⋆ as a lemma
suc⋆left : (m n : ℕ) → (suc m) ⋆ n ≡ m ⋆ n + n
suc⋆left m n = refl

-- zero is right absorbing for ⋆

zero⋆rightabsorbing : (n : ℕ) → n ⋆ zero ≡ zero
zero⋆rightabsorbing zero = zero⋆leftabsorbing zero
zero⋆rightabsorbing (suc n) = ((suc n) ⋆ zero)
                              ≡⟨ suc⋆left n zero ⟩≡
                              (n ⋆ zero + zero)
                              ≡⟨ zero+rightunit _ ⟩≡
                              (n ⋆ zero)
                              ≡⟨ zero⋆rightabsorbing n ⟩≡
                              (zero)
                              QED

suc⋆right : (m n : ℕ) → m ⋆ (suc n) ≡ m ⋆ n + m
suc⋆right zero n = (zero ⋆ suc n)
                   ≡⟨ zero⋆leftabsorbing (suc n) ⟩≡
                   (zero)
                   ≡⟨ ≡symm (zero⋆leftabsorbing n)⟩≡
                   (zero ⋆ n)
                   ≡⟨ ≡symm (zero+rightunit (zero ⋆ n)) ⟩≡ 
                   (zero ⋆ n + zero)
                   QED
suc⋆right (suc m) n = (suc m ⋆ suc n)
                      ≡⟨ suc⋆left m (suc n) ⟩≡
                      ( m ⋆ suc n + suc n )
                      ≡⟨ ≡cong (_+ suc n) (suc⋆right m n) ⟩≡
                      ((m ⋆ n + m) + suc n) 
                      ≡⟨ +associative (m ⋆ n) m (suc n)⟩≡
                      (m ⋆ n + m + suc n)
                      ≡⟨ ≡cong (m ⋆ n +_) (sucright+suc m n)⟩≡
                      (m ⋆ n + suc (m + n))
                      ≡⟨ ≡cong (m ⋆ n +_) (≡symm (sucleft+suc m n))⟩≡
                      (m ⋆ n + suc m + n)
                      ≡⟨ ≡cong (m ⋆ n +_) (+commutative (suc m) n)⟩≡
                      (m ⋆ n + n + suc m)
                      ≡⟨ ≡symm (+associative (m ⋆ n) n (suc m))⟩≡
                      ((m ⋆ n + n) + suc m)
                      ≡⟨ ≡cong (_+ suc m) (≡symm (suc⋆left m n))⟩≡
                      ((suc m) ⋆ n + suc m)
                      QED

⋆commutative : (m n : ℕ) → m ⋆ n ≡ n ⋆ m
⋆commutative zero n = (zero ⋆ n)
                      ≡⟨ zero⋆leftabsorbing n ⟩≡
                      zero
                      ≡⟨ ≡symm (zero⋆rightabsorbing n)⟩≡
                      (n ⋆ zero)
                      QED
⋆commutative (suc m) n = ((suc m) ⋆ n)
                         ≡⟨ suc⋆left m n ⟩≡
                         (m ⋆ n + n)
                         ≡⟨ ≡cong (_+ n) (⋆commutative m n)⟩≡
                         (n ⋆ m + n)
                         ≡⟨ ≡symm (suc⋆right n m)⟩≡ 
                         (n ⋆ suc m)
                         QED

one⋆leftunit : (n : ℕ) → one ⋆ n ≡ n
one⋆leftunit n = (one ⋆ n)
                 ≡⟨ refl ⟩≡
                 ((suc zero) ⋆ n)
                 ≡⟨ suc⋆left zero n ⟩≡
                 (zero ⋆ n + n)
                 ≡⟨ ≡cong (_+ n) (zero⋆leftabsorbing n) ⟩≡
                 (zero + n)
                 ≡⟨ zero+leftunit n ⟩≡
                 (n)
                 QED

one⋆rightunit : (n : ℕ) → n ⋆ one ≡ n
one⋆rightunit n = (n ⋆ one)
                  ≡⟨ ⋆commutative n one ⟩≡
                  (one ⋆ n)
                  ≡⟨ one⋆leftunit n ⟩≡
                  n
                  QED

two⋆ : (n : ℕ) → (two ⋆ n) ≡ n + n
two⋆ n = (two ⋆ n)
         ≡⟨ refl ⟩≡ 
         ((suc one) ⋆ n)
         ≡⟨ suc⋆left one n ⟩≡
         (one ⋆ n + n)
         ≡⟨ ≡cong (_+ n) (one⋆leftunit n) ⟩≡
         (n + n)
         QED

two⋆suc : (n : ℕ) → two ⋆ (suc n) ≡ suc (suc (two ⋆ n))
two⋆suc n = (two ⋆ (suc n))
            ≡⟨ suc⋆right _ _ ⟩≡
            (two ⋆ n + two)
            ≡⟨ refl ⟩≡
            (two ⋆ n + suc (suc zero))
            ≡⟨ sucright+suc (two ⋆ n) _ ⟩≡
            (suc (two ⋆ n + suc zero))
            ≡⟨ ≡cong suc (sucright+suc (two ⋆ n) _) ⟩≡
            (suc (suc (two ⋆ n + zero )))
            ≡⟨ ≡cong (\k → suc (suc k)) (zero+rightunit _) ⟩≡
            (suc (suc (two ⋆ n)))
            QED

-- datatypes for logic 

data Either_Or_ (A B : Set) : Set where
  inl : A → Either A Or B
  inr : B → Either A Or B

data _And_ (A B : Set) : Set where
  _and_ : A → B → A And B

-- less than

infix 10 _<_

data _<_ : ℕ → ℕ → Set where
  zero<suc : {n : ℕ} → zero < suc n
  sucsuc<  : {n m : ℕ} → n < m → suc n < suc m

-- and less than or equal

infix 10 _≤_

_≤_ : ℕ → ℕ → Set
m ≤ n = Either (m < n) Or (m ≡ n)

-- n < suc n

n<sucn : (n : ℕ) → n < suc n
n<sucn zero = zero<suc
n<sucn (suc n) = sucsuc< (n<sucn n)

-- < is transitive

<trans : {l m n : ℕ} → l < m → m < n → l < n
<trans {n = suc o} zero<suc _ = zero<suc {n = o}
<trans (sucsuc< lm) (sucsuc< mn) = sucsuc< (<trans lm mn)

-- m < suc n  is (logically) equivalent to m ≤ n :

<→≤ : (m n : ℕ) → m < suc n → m ≤ n
<→≤ zero zero zero<suc = inr refl
<→≤ zero (suc n) _ = inl zero<suc
<→≤ (suc m) (suc n) (sucsuc< m<sn) with (<→≤ m n m<sn)
<→≤ (suc m) (suc n) (sucsuc< m<sn) | inl m<n  = inl (sucsuc< m<n)
<→≤ (suc m) (suc n) (sucsuc< m<sn) | inr m≡n  = inr (≡cong suc m≡n)

≤→< : (m n : ℕ) → m ≤ n → m < suc n
≤→< m n (inl m<n) = <trans m<n (n<sucn n)
≤→< m n (inr m≡n) = ≡transport m≡n (n<sucn m)




{-- binary view ... t.b.c. 


data BinView : ℕ → Set where
  bzero : BinView zero
  b⋆2+1 : (n : ℕ) → BinView (suc (two ⋆ n))
  b⋆2+2 : (n : ℕ) → BinView (suc (suc (two ⋆ n)))

binview : (n : ℕ) → BinView n
binview zero = bzero
binview (suc n) with (binview n)
binview (suc n) | bzero = b⋆2+1 zero
binview (suc n) | b⋆2+1 m = b⋆2+2 m
binview (suc n) | b⋆2+2 m = ≡transport {P = BinView} (≡cong suc (two⋆suc m)) (b⋆2+1 (suc m))


data Bin : Set where
  xb : Bin
  _O : Bin -> Bin
  _I : Bin -> Bin

-}

-- Booleans:

data 𝔹 : Set where
  true : 𝔹
  false : 𝔹

infixl 15 _∧_
infixl 15 _∨_

_∧_ : 𝔹 → 𝔹 → 𝔹
true ∧ true = true
true ∧ false = false
false ∧ _ = false

_∨_ : 𝔹 → 𝔹 → 𝔹
false ∨ false = false
false ∨ true  = true
true  ∨ _     = true 

∧commutative : (x y : 𝔹) → x ∧ y ≡ y ∧ x
∧commutative true  true  = refl
∧commutative false true  = refl
∧commutative true  false = refl
∧commutative false false = refl

if_then_else_ : {A : Set} → 𝔹 → A → A → A
if true then a else _ = a
if false then _ else a = a

iffun : {A B : Set} → (g : A → B) → (c : 𝔹) → (t f : A) → g (if c then t else f) ≡ if c then g t else g f
iffun g true t f = refl
iffun g false t f = refl

∧diag : (b : 𝔹) → b ∧ b ≡ b
∧diag true  = refl
∧diag false = refl



-- lifting Booleans to type

data YesOrNo (b : 𝔹) : Set where
  Yes : b ≡ true  → YesOrNo b
  No  : b ≡ false → YesOrNo b 

yesOrNo : (b : 𝔹) → YesOrNo b
yesOrNo true = Yes refl
yesOrNo false = No refl
