{-# OPTIONS --copatterns #-}

------------------------------------------------------------------------
-- Infinite data structures in Agda
--
-- Streams, infinite binary trees and conversions between them
------------------------------------------------------------------------

module IDS where

open import Coinduction hiding (unfold)

open import Data.Bool
open import Data.Nat hiding (_⊔_)
import Data.List as L
open L using (List; []; _∷_)
open import Data.Product hiding (zip) renaming (map to mapP)
open import Data.Sum using (_⊎_)

open import Function

open import Level using (_⊔_)

open import Relation.Binary.PropositionalEquality


------------------------------------------------------------------------
-- Data types
------------------------------------------------------------------------


------------------------------------------------------------------------
-- Infinite streams as coinductively defined records

record Stream {a} (A : Set a) : Set a where
  coinductive
  constructor _<:_
  field
    head : A
    tail : Stream {a} A

open Stream

------------------------------------------------------------------------
-- Predicates on streams

-- Any is inductively defined
data Any {a p} {A : Set a}
         (P : A → Set p) : Stream A → Set (a ⊔ p) where
  here  : ∀ {s} (px : P (head s))     → Any P s
  there : ∀ {s} (ps : Any P (tail s)) → Any P s

-- All is a coinductive predicate
record All {a p} {A : Set a}
           (P : A → Set p) (s : Stream A) : Set (a ⊔ p) where
  coinductive
  field
    ✓-head : P (head s)
    ✓-tail : All P (tail s)

open All

------------------------------------------------------------------------
-- AE (for always eventually) is not well-founded. In order to make it
-- definable, we had to make this explicit by annotating the coinductive
-- component with ∞.

data AE {a p} {A : Set a}
        (P : A → Set p) : Stream A → Set (a ⊔ p) where
  here  : ∀ {s} (px : P (head s)) → (ps : ∞ (AE P (tail s))) → AE P s
  there : ∀ {s} (ps : AE P (tail s))                         → AE P s


------------------------------------------------------------------------
-- Bisimulation for streams

infix 4 _≈_

record _≈_ {a} {A : Set a} (s₁ s₂ : Stream A) : Set a where
  coinductive
  field
    ≈-head : head s₁ ≡ head s₂
    ≈-tail : tail s₁ ≈ tail s₂

open _≈_


------------------------------------------------------------------------
-- Infinite binary trees

record BTree {a} (A : Set a) : Set a where
  coinductive
  constructor _<|_|>_
  field
    left  : BTree A
    label : A
    right : BTree A

open BTree

------------------------------------------------------------------------
-- Bisimulation for trees

infix 4 _≈T_

record _≈T_ {a} {A : Set a} (x y : BTree A) : Set a where
  coinductive
  field
    ≈-left  : left x  ≈T left y
    ≈-label : label x ≡  label y
    ≈-right : right x ≈T right y

open _≈T_


------------------------------------------------------------------------
-- Functions on streams
------------------------------------------------------------------------


------------------------------------------------------------------------
-- Unfolding a coalgebra. Here, stream coalgebras are defined by an
-- initial state `y`, a projection `h` and a transition function `t`.

unfold : ∀ {a b} {A : Set a} {B : Set b} → (B → A) → (B → B) → B → Stream {a} A
head (unfold h t y) = h y
tail (unfold h t y) = unfold h t (t y)

-- Interestingly, the following equivalent definition is not accepted,
-- throwing a termination checker error (clearly the function, being
-- coinductively defined, never terminates, but it's not supposed to!):
--
-- unfold h t y = (h y) <: (unfold h t (t y))

-- The stream containing all natural numbers
nats : Stream ℕ
nats = unfold id suc 0


------------------------------------------------------------------------
-- Interleaving two streams

-- Using copatterns
_⋈_ : ∀ {a} {A : Set a} → Stream A → Stream A → Stream A
head (x ⋈ y) = head x
tail (x ⋈ y) = y ⋈ (tail x)

-- The equivalent explicit definition (not using copatterns) again
-- gives a termination checker error:
--
-- x ⋈ y = (head x) <: (y ⋈ tail x)

-- As a coalgebra
_⋈′_ : ∀ {a} {A : Set a} → Stream A → Stream A → Stream A
_⋈′_ {A = A} x y = unfold (head ∘ proj₁) next (x , y)
  where
    next : Stream A × Stream A → Stream A × Stream A
    next (x , y) = y , tail x

-- Bisimulation proof
⋈↔⋈′ : ∀ {a} {A : Set a} → (x : Stream A) (y : Stream A) →
       x ⋈ y ≈ x ⋈′ y
≈-head (⋈↔⋈′ x y) = refl
≈-tail (⋈↔⋈′ x y) = ⋈↔⋈′ y (tail x)


------------------------------------------------------------------------
-- Zipping and unzipping two streams

-- Using copatterns
zip : ∀ {a b} → {A : Set a} {B : Set b} →
      Stream A → Stream B → Stream (A × B)
head (zip x y) = (head x , head y)
tail (zip x y) = zip (tail x) (tail y)

-- As a coalgebra
zip′ : ∀ {a b} → {A : Set a} {B : Set b} →
       Stream A → Stream B → Stream (A × B)
zip′ x y = unfold (mapP head head) (mapP tail tail) (x , y)

-- Bisimulation proof
zip↔zip′ : ∀ {a b} → {A : Set a} {B : Set b}
           (x : Stream A) (y : Stream B) → zip x y ≈ zip′ x y
≈-head (zip↔zip′ x y) = refl
≈-tail (zip↔zip′ x y) = zip↔zip′ (tail x) (tail y)

-- Unzipping using nested (!!) copatterns
unzip : ∀ {a b} → {A : Set a} {B : Set b} →
        Stream (A × B) → Stream A × Stream B
head (proj₁ (unzip s)) = proj₁ (head s)
tail (proj₁ (unzip s)) = proj₁ (unzip (tail s))
head (proj₂ (unzip s)) = proj₂ (head s)
tail (proj₂ (unzip s)) = proj₂ (unzip (tail s))

-- Bisimulation proof: zip is unzip's left inverse
zip∘unzip : ∀ {a b} → {A : Set a} {B : Set b} (s : Stream (A × B)) →
            uncurry zip (unzip s) ≈ s
≈-head (zip∘unzip s) = refl
≈-tail (zip∘unzip s) = zip∘unzip (tail s)

------------------------------------------------------------------------
-- More list-like functions on streams

-- Map a function over a stream
map : ∀ {a b} {A : Set a} {B : Set b} → (A → B) → Stream A → Stream B
map f = unfold (f ∘ head) tail

-- List the first n elements of a stream
take : ∀ {a} {A : Set a} → ℕ → Stream A → List A
take 0       x = []
take (suc n) x = (head x) ∷ (take n (tail x))

-- Drop the first n elements from a stream
drop : ∀ {a} {A : Set a} → ℕ → Stream A → Stream A
drop 0       x = x
drop (suc n) x = drop n (tail x)

-- Get the n'th element of the stream
_!_ : ∀ {a} → {A : Set a} → Stream A → ℕ → A
s ! zero = head s
s ! suc n = tail s ! n

-- Combines take and drop
split : ∀ {a} {A : Set a} → ℕ → Stream A → List A × Stream A
split n s = take n s , drop n s


------------------------------------------------------------------------
-- Finding elements and splitting streams with Any

-- Split a stream on an instance of Any. The head of the stream that is
-- returned fulfills the predicate.
takeUntil : ∀ {a p} {A : Set a} {P : A → Set p} →
            (s : Stream A) → Any P s → List A × Stream A
takeUntil         s (here  px)  = [] , s
takeUntil {A = A} s (there any) = head s ∷ (proj₁ p) , proj₂ p
  where
    p : List A × Stream A
    p = takeUntil (tail s) any

-- Proof that the head of the stream returned by takeUntil really does
-- fulfill the predicate
takeUntil-lemma : ∀ {a p} → {A : Set a} {P : A → Set p}
                  (s : Stream A) (any : Any P s) →
                  P (head (proj₂ (takeUntil s any)))
takeUntil-lemma s (here px)   = px
takeUntil-lemma s (there any) = takeUntil-lemma (tail s) any

-- This function discards the elements preceding the one the Any
-- instance points to. The result comes with a proof that the head of
-- the stream now fulfills the predicate.
find : ∀ {a p} {A : Set a} {P : A → Set p} →
       (s : Stream A) → Any P s → Σ (Stream A) (P ∘ head)
find s (here  px)  = s , px
find s (there any) = find (tail s) any

-- `find` returns its own proof of correctness, making this lemma
-- trivial.
find-lemma : ∀ {a p} → {A : Set a} {P : A → Set p}
             (s : Stream A) (any : Any P s) →
             P (head (proj₁ (find s any)))
find-lemma s any with find s any
find-lemma s any | _ , prf = prf


------------------------------------------------------------------------
-- Finding elements and splitting streams with AE (always eventually)

-- Drop the elements preceding the first one pointed to by AE. For
-- convenience, we also return a proof the the head of the stream
-- fulfills the predicate, and an AE instance for its tail.
dropUntil : ∀ {a p} {A : Set a} {P : A → Set p} →
            (s : Stream A) → AE P s →
            ∃ (λ (s : Stream A) → P (head s) × AE P (tail s))
dropUntil s (here px ps) = s , (px , ♭ ps)
dropUntil s (there ae)   = dropUntil (tail s) ae

-- Filter a stream by AE. We return the proof of P x along with every
-- element x of the resulting stream.
filter : ∀ {a p} → {A : Set a} (P : A → Set p) (s : Stream A) →
         AE P s → Stream (Σ A P)
head (filter P s (here px ps)) = head s , px
head (filter P s (there ae))   = head (filter P (tail s) ae)
tail (filter P s (here px ps)) = filter P (tail s) (♭ ps)
tail (filter P s (there ae))   = tail (filter P (tail s) ae)

-- A variant that only returns the elements (no proofs)
filter′ : ∀ {a p} → {A : Set a} (P : A → Set p) (s : Stream A) →
          AE P s → Stream A
head (filter′ P s (here px ps)) = head s
head (filter′ P s (there ae))   = head (filter′ P (tail s) ae)
tail (filter′ P s (here px ps)) = filter′ P (tail s) (♭ ps)
tail (filter′ P s (there ae))   = tail (filter′ P (tail s) ae)

-- And the corresponding manual proof
filter′-lemma : ∀ {a p} → {A : Set a} (P : A → Set p) (s : Stream A)
                (ae : AE P s) → All P (filter′ P s ae)
✓-head (filter′-lemma P s (here px ps)) = px
✓-head (filter′-lemma P s (there ae))   = ✓-head (filter′-lemma P (tail s) ae)
✓-tail (filter′-lemma P s (here px ps)) = filter′-lemma P (tail s) (♭ ps)
✓-tail (filter′-lemma P s (there ae))   = ✓-tail (filter′-lemma P (tail s) ae)

------------------------------------------------------------------------
-- Streamy functions

-- Repeat something forever
repeat : ∀ {a} → {A : Set a} → A → Stream A
head (repeat x) = x
tail (repeat x) = repeat x

-- As a coalgebra
repeat′ : ∀ {a} → {A : Set a} → A → Stream A
repeat′ = unfold id id

-- Bisimulation proof: trivial.
repeat↔repeat′ : ∀ {a} → {A : Set a} (x : A) → repeat x ≈ repeat′ x
≈-head (repeat↔repeat′ x) = refl
≈-tail (repeat↔repeat′ x) = repeat↔repeat′ x

-- Example always-eventually proof: the result of interleaving
-- `repeat x` and `repeat y` always eventually contains an element
-- equal to `x`.
ae-eq : ∀ {a} {A : Set a} (x y : A) → AE (_≡_ x) (repeat x ⋈ repeat y)
ae-eq x y = here refl (♯ (there (ae-eq x y)))

-- Every other element, starting with head
evens : ∀ {a} {A : Set a} → Stream A → Stream A
evens = unfold head (tail ∘ tail)

-- Every other element, starting with the head of the tail
odds : ∀ {a} {A : Set a} → Stream A → Stream A
odds = evens ∘ tail

-- Prepends the elements of a list to a stream
_++_ : ∀ {a} → {A : Set a} → List A → Stream A → Stream A
head ([]       ++ s) = head s
tail ([]       ++ s) = tail s
head ((x ∷ xs) ++ s) = x
tail ((x ∷ xs) ++ s) = xs ++ s


------------------------------------------------------------------------
-- Fibonacci series as a stream

-- Elementwise sum of two streams using copatterns
add : Stream ℕ → Stream ℕ → Stream ℕ
head (add x y) = head x + head y
tail (add x y) = add (tail x) (tail y)

-- A variant using `map`
add′ : Stream ℕ → Stream ℕ → Stream ℕ
add′ x y = map (uncurry _+_) (zip x y)

-- Bisimulation proof
add↔add′ : ∀ x y → add x y ≈ add′ x y
≈-head (add↔add′ x y) = refl
≈-tail (add↔add′ x y) = add↔add′ (tail x) (tail y)

-- The Fibonacci series as a coalgebra
fib : Stream ℕ
fib = unfold proj₁ next (0 , 1)
  where
    next : ℕ × ℕ → ℕ × ℕ
    next (m , n) = n , (m + n)


------------------------------------------------------------------------
-- Functions on infinite binary trees
------------------------------------------------------------------------


-- Unfolding a binary tree. A binary tree coalgebra is defined as an
-- initial state `y`, a projection `h` and a transition function `t`,
-- which returns a pair. The first element of that pair is used to
-- generate the left branch of the tree and second element for the
-- right branch.
unfoldT : ∀ {a b} {A : Set a} {B : Set b} →
          (B → A) → (B → B) → (B → B) → B → BTree {a} A
label (unfoldT h l r y) = h y
left  (unfoldT h l r y) = unfoldT h l r (l y)
right (unfoldT h l r y) = unfoldT h l r (r y)

-- Generate an infinite tree with `x` as the label everywhere
repeatT : ∀ {a} {A : Set a} → A → BTree A
repeatT = unfoldT id id id

-- The left spine of the tree as a stream using copatterns
lspine : ∀ {a} {A : Set a} → BTree A → Stream A
head (lspine t) = label t
tail (lspine t) = lspine (left t)

-- As a stream coalgebra
lspine′ : ∀ {a} {A : Set a} → BTree A → Stream A
lspine′ = unfold label left


------------------------------------------------------------------------
-- Binary trees to streams
------------------------------------------------------------------------

fromStream : ∀ {a} → {A : Set a} → Stream A → BTree A
fromStream {A = A} s = unfoldT (head ∘ proj₁) l (mapP tail suc ∘ l) (s , zero)
  where
    l : Stream A × ℕ → Stream A × ℕ
    l (s , n) = drop (suc n) s , suc (2 * n)

fromStream′ : ∀ {a} → {A : Set a} → Stream A → BTree A
fromStream′ {A = A} s = unfoldT (_!_ s) (suc ∘ (_*_ 2)) ((_*_ 2) ∘ suc) zero


------------------------------------------------------------------------
-- Random stuff
------------------------------------------------------------------------


{-
record Unit {ℓ} : Set ℓ where
  constructor unit

open import Data.Empty

¬ : ∀ {ℓ} → Set ℓ → Set ℓ
¬ P = P → ⊥

data noskips : ∀ {a} {A : Set a} (P : A → Set a) → (s : Stream A) → AE P s → Set a
  base : noskips P s (here px ps) , noskips P (tail s) (♭ ps)
  next : noskips P s (there ae) = (¬ (P (head s))) × noskips P (tail s) ae
-}

GreaterThan : ℕ → ℕ → Set
GreaterThan m n = n ≤ m

Any≥ : ∀ m n → Any (GreaterThan m) (drop n nats)
Any≥ m n = {!!}

partition : ∀ {a} {A : Set a} → (A → Bool) → ℕ → Stream A → (List A × List A) × Stream A
partition p n s = L.partition p (take n s) , drop n s

record AE′ {a p} {A : Set a}
           (P : A → Set p) (s : Stream A) : Set (a ⊔ p) where
  coinductive
  field
    steps : ℕ
    then  : P (head (drop steps s))
    after : AE′ P (tail (drop steps s))
--      next : Σ ℕ (λ n → P (head (drop n s)) × AE′ P (tail (drop n s)))

open AE′

findAE′ : ∀ {a p} {A : Set a} {P : A → Set p} → (s : Stream A) → AE′ P s →
          Σ (Stream A) (λ s → P (head s) × AE′ P (tail s))
findAE′ s ae = drop (steps ae) s , (then ae , after ae) -- drop (proj₁ (now ae)) s , (proj₂ (now ae) , {!!})

{-
filter : ∀ {a p} {A : Set a} → (P : A → Set p) → (s : Stream A) → AE P s →
         Stream (Σ A P)
filter {A = A} P s ae = unfold proj step (findAE s ae)
  where
    State = Σ (Stream A) (λ s → P (head s) × AE P (tail s))

    proj : State → Σ A P
    proj (s , P-head , ae-tail) = head s , P-head

    step : State → State
    step (s , P-head , ae-tail) = findAE (tail s) ae-tail
-}

unfoldAE′ : ∀ {a b p} {A : Set a} {B : Set b} →
            (P : A → Set p) → (s : Stream A) → B →
            (p : B → ℕ) → ((st : B) → P (head (drop (p st) s))) →
            ((st : B) → AE′ P (tail (drop (p st) s))) →
            AE′ P s -- (g : ℕ → ℕ) → ℕ → (P : A → Set p) → (s : Stream A) → (∀ i → P (head (drop (g i) s))) → AE′ P s
steps (unfoldAE′ P s i f g h) = f i
then  (unfoldAE′ P s i f g h) = g i
after (unfoldAE′ P s i f g h) = {!!}
