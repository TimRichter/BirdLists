{-# OPTIONS --without-K #-}

module Digressions where

open import Basics

-- * Digression 1: induction principles :
--   "properties" of e.g. natural numbers can be modeled as
--   functions  |ℕ → Set| : the idea is that for some |P : ℕ -> Set|,
--   and |m : ℕ|, the inhabitants of the type |P m|  are proofs (or evidences)
--   that |P| holds for |m|. To prove |P m| for all |m| amounts to give a
--   (dependent) function |(m : ℕ) → P m|. Induction principles help to
--   construct such functions. Each inductive data type comes with a
--   "structural" induction principle, which in the case of |ℕ| is:

step_ind : (P : ℕ → Set) → (P zero) → ((n : ℕ) → P n → P (suc n)) → (k : ℕ) → P k

--   Note that the second and third argument of |step_ind| are directly related
--   to the two constructors |zero| and |suc| of |ℕ|. Definitions by pattern matching
--   implicitely use this induction principle! So the following proof of |step_ind|
--   by pattern matching is somewhat of a tautology!

step_ind P pzero pstep zero = pzero
step_ind P pzero pstep (suc k) = pstep k (step_ind P pzero pstep k)

--   another important (and more conveniently to work with) induction
--   principle on |ℕ| states that to prove some property |Q : ℕ → Set| for
--   all |n : ℕ| (i.e. to define a dependent function |(n : ℕ) → Q n|, it
--   is enough to, for each |n : ℕ|, construct a proof of |Q n| under the
--   the assumtion that for any |m : ℕ| with |m < n| we have |Q m|:
--
--   wf<_ind : (Q : ℕ → Set) →
--             ((n : ℕ) → ((m : ℕ) → m < n → Q m) → Q n) →
--             (k : ℕ) → Q k
--
--   "wf" stands for "well-founded induction" - it works for any "well-founded"
--   relation, here |<| on ℕ. |step_ind| is also a well-founded induction, but
--   for another well-founded relation: the sucessor relation on |ℕ|. For more
--   look into the Agda standard library:
--   https://github.com/agda/agda-stdlib/blob/master/src/Induction/WellFounded.agda
--
--   We can prove that step_ind and wf<_ind are equivalent by implementing functions
--   both ways between the types of wf<_ind and step_ind. First the easier direction
--   we already did in the seminar:

wf<_to_step : ((Q : ℕ → Set) →
               ((n : ℕ) → ((m : ℕ) → m < n → Q m) → Q n) →
               (k : ℕ) → Q k ) →
              ((P : ℕ → Set) →
               (P zero) →
               ((n : ℕ) → P n → P (suc n)) →
               (k : ℕ) → P k )

wf<_to_step wfip P pzero pstep k = wfip P wfstep k where
    wfstep : (n : ℕ) → ((m : ℕ) → m < n → P m) → P n
    wfstep zero _ = pzero
    wfstep (suc n) allsmallerp = pstep n (allsmallerp n ((n<sucn n))) 

-- Note that to construct an element of |P k| from the induction principle |wfip|
-- and the premises |pzero| and |pstep|, we use |wfip| with the same property |P|
-- and construct the premise |wfstep| of |wfip| directly from |pzero| and |pstep|,
-- without using ex falso quodlibet!

-- The other direction is a little trickier

step_to_wf< : ((P : ℕ → Set) →
               (P zero) →
               ((n : ℕ) → P n → P (suc n)) →
               (k : ℕ) → P k) →
               (Q : ℕ → Set) →
               ((n : ℕ) → ((m : ℕ) → m < n → Q m) → Q n) →
               (k : ℕ) → Q k

step_to_wf< stip Q wfstep k = wfstep k pk where
    pk : (m : ℕ) → m < k → Q m
    pk = stip P p0 pstep k where
      P : ℕ → Set
      P n = (m : ℕ) → m < n → Q m      
      p0 : P zero
      p0 _ ()     -- absurd
      pstep : (n : ℕ) → P n → P (suc n)
      pstep n pn m m<sn with (<→≤ m n m<sn)
      pstep n pn m m<sn | inl m<n = pn m m<n
      pstep n pn m m<sn | inr m≡n = ≡transport (≡symm m≡n ) (wfstep n pn)


-- Here we use the given "step induction principle" |stip| on a predicate |Q|
-- constructed from |P|. We use ex falso quodlibet to construct the function
-- | q0 : (m : ℕ) → m < zero → P m | : there is no |m| with |m < zero|, so if
-- we get one, we can construct anything, e.g. an element of |P m| - in Agda
-- we do this with the "absurd" pattern (). To construct |qstep|, i.e. deduce
-- |Q (suc n) = (m : ℕ) → m < (suc n) → P m| from |qn : Q n = ...|,  we make
-- a case distinction on |m|: if |m < n|, we recycle |qn|'s proof of |P m|,
-- in the remaining case |m ≡ n|, we use |wfstep| (≡transport is needed to
-- convince the typechecker that in this case |P n| "is" |P m|). Finally,
-- after applying |stip| with the thus built arguments to obtain |Q k|, we
-- again use |wfstep| (renamed to |pfromq| for readability) to get |P k|.
