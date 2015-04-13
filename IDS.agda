{-# OPTIONS --copatterns #-}

module IDS where

  open import Level using (_⊔_)

  open import Function

  open import Data.Bool
  open import Data.Maybe using (Maybe; just; nothing)
  open import Data.Nat hiding (_⊔_)

  import Data.List as L
  open L using (List; []; _∷_)
  import Data.Product as P
  open P using (Σ; _,_; <_,_>; _×_; proj₁; proj₂; uncurry; swap)
  import Data.Sum as S
  open S using (_⊎_)

  open import Relation.Binary.PropositionalEquality

  record Stream {a} (A : Set a) : Set a where
    coinductive
    constructor _<:_
    field
      head : A
      tail : Stream {a} A

  open Stream

  data Any {a p} {A : Set a}
           (P : A → Set p) : Stream A → Set (a ⊔ p) where
    here  : ∀ {s} (px : P (head s))     → Any P s
    there : ∀ {s} (ps : Any P (tail s)) → Any P s

  open import Coinduction hiding (unfold)

  data AE {a p} {A : Set a}
          (P : A → Set p) : Stream A → Set (a ⊔ p) where
    here  : ∀ {s} (px : P (head s)) → (ps : ∞ (AE P (tail s))) → AE P s
    there : ∀ {s} (ps : AE P (tail s))                         → AE P s

  record _≈_ {a} {A : Set a} (s₁ s₂ : Stream A) : Set a where
    coinductive
    field
      ≈-head : head s₁ ≡ head s₂
      ≈-tail : tail s₁ ≈ tail s₂

  open _≈_

  record BTree {a} (A : Set a) : Set a where
    coinductive
    constructor _<|_|>_
    field
      left  : BTree A
      label : A
      right : BTree A

  unfold : ∀ {a b} {A : Set a} {B : Set b} → (B → A) → (B → B) → B → Stream {a} A
  head (unfold h t y) = h y
  tail (unfold h t y) = unfold h t (t y)
--  unfold h t y = (h y) <: (unfold h t (t y))

  nats : Stream ℕ
  nats = unfold id suc 0

  _⋈_ : ∀ {a} {A : Set a} → Stream A → Stream A → Stream A
--  x ⋈ y = record { head = head x ; tail = y ⋈ tail x }
  head (x ⋈ y) = head x
  tail (x ⋈ y) = y ⋈ (tail x)

  _⋈′_ : ∀ {a} {A : Set a} → Stream A → Stream A → Stream A
  _⋈′_ {A = A} x y = unfold (head ∘ proj₁) next (x , y)
    where
      next : Stream A × Stream A → Stream A × Stream A
      next (x , y) = y , tail x

  zip : ∀ {a b} {A : Set a} {B : Set b} → Stream A → Stream B → Stream (A × B)
  head (zip x y) = (head x , head y)
  tail (zip x y) = zip (tail x) (tail y)

  zip′ : ∀ {a b} {A : Set a} {B : Set b} → Stream A → Stream B → Stream (A × B)
  zip′ x y = unfold (P.map head head) (P.map tail tail) (x , y)

  map : ∀ {a b} {A : Set a} {B : Set b} → (A → B) → Stream A → Stream B
  map f = unfold (f ∘ head) tail

  take : ∀ {a} {A : Set a} → ℕ → Stream A → List A
  take 0       x = []
  take (suc n) x = (head x) ∷ (take n (tail x))

  drop : ∀ {a} {A : Set a} → ℕ → Stream A → Stream A
  drop 0       x = x
  drop (suc n) x = drop n (tail x)

  split : ∀ {a} {A : Set a} → ℕ → Stream A → List A × Stream A
  split n s = take n s , drop n s

  takeUntil : ∀ {a p} {A : Set a} {P : A → Set p} →
             (s : Stream A) → Any P s → List A × Stream A
  takeUntil         ._ (here  {s} px)  = [] , s
  takeUntil {A = A} ._ (there {s} any) = head s ∷ (proj₁ p) , proj₂ p
    where
      p : List A × Stream A
      p = takeUntil (tail s) any

  find : ∀ {a p} {A : Set a} {P : A → Set p} →
         (s : Stream A) → Any P s → Σ (Stream A) (P ∘ head)
  find s (here  px)  = s , px
  find s (there any) = find (tail s) any

  dropUntil : ∀ {a p} {A : Set a} {P : A → Set p} →
              (s : Stream A) → AE P s →
              P.∃ (λ (s : Stream A) → P (head s) × AE P (tail s))
  dropUntil s (here px ps) = s , (px , ♭ ps)
  dropUntil s (there ae)   = dropUntil (tail s) ae

  repeat : ∀ {a} {A : Set a} → A → Stream A
  head (repeat x) = x
  tail (repeat x) = repeat x

  all-eq : ∀ {a} {A : Set a} (x y : A) → AE (_≡_ x) (repeat x ⋈ repeat y)
  all-eq x y = here refl (♯ (there (all-eq x y)))

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

  filter : ∀ {a p} {A : Set a} → (P : A → Set p) → (s : Stream A) → AE P s →
           Stream (Σ A P)
  head (filter P s (here px ps)) = head s , px
  head (filter P s (there ae))   = head (filter P (tail s) ae)
  tail (filter P s (here px ps)) = filter P (tail s) (♭ ps)
  tail (filter P s (there ae))   = tail (filter P (tail s) ae)

  add : Stream ℕ → Stream ℕ → Stream ℕ
  head (add x y) = head x + head y
  tail (add x y) = add (tail x) (tail y)

  add′ : Stream ℕ → Stream ℕ → Stream ℕ
  add′ x y = map (uncurry _+_) (zip x y)

  add-lemma : ∀ s₁ s₂ → add s₁ s₂ ≈ add′ s₁ s₂
  ≈-head (add-lemma s₁ s₂) = refl
  ≈-tail (add-lemma s₁ s₂) = add-lemma (tail s₁) (tail s₂)

  evens : ∀ {a} {A : Set a} → Stream A → Stream A
  evens = unfold head (tail ∘ tail)

  odds : ∀ {a} {A : Set a} → Stream A → Stream A
  odds = evens ∘ tail

  fib : Stream ℕ
  fib = unfold proj₁ next (0 , 1)
    where
      next : ℕ × ℕ → ℕ × ℕ
      next (m , n) = n , (m + n)

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

{-
  now  (all-eq x y) = 0 , refl
  then (all-eq x y) = 1 , (all-eq x y)
-}
{-
  all-eq : ∀ {a} {A : Set a} (x y : A) → AE (_≡_ x) (repeat x ⋈ repeat y)
  all-eq x y = here refl (there (all-eq x y))
-}

  repeat′ : ∀ {a} {A : Set a} → A → Stream A
  repeat′ = unfold id id

------------------------------------------

  open BTree

  unfoldT : ∀ {a b} {A : Set a} {B : Set b} → (B → A) → (B → B × B) → B → BTree {a} A
  label (unfoldT h y t) = h t
  left  (unfoldT h y t) = unfoldT h y (proj₁ (y t))
  right (unfoldT h y t) = unfoldT h y (proj₂ (y t))

  repeatT : ∀ {a} {A : Set a} → A → BTree A
  repeatT = unfoldT id (λ x → x , x)

  lspine : ∀ {a} {A : Set a} → BTree A → Stream A
  head (lspine t) = label t
  tail (lspine t) = lspine (left t)

  lspine′ : ∀ {a} {A : Set a} → BTree A → Stream A
  lspine′ = unfold label left
