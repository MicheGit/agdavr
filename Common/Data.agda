module Common.Data where

data ℕ : Set where
    zero : ℕ
    succ : ℕ → ℕ

data Bool : Set where
    false true : Bool

not : Bool → Bool
not true = false
not false = true

infix 1 _∨_
data _∨_ (A B : Set) : Set where
    left  : A → A ∨ B
    right : B → A ∨ B

infixr 2 _∧_
infixr 4 _,_
data _∧_ (A B : Set) : Set where
    _,_ : A → B → A ∧ B
    
distr-∧-∨ : {A B C : Set} → A ∧ (B ∨ C) → A ∧ B ∨ A ∧ C
distr-∧-∨ (a , left x) = left (a , x)
distr-∧-∨ (a , right x) = right (a , x)

data _≡_ {X : Set} : X → X → Set where
  refl : {x : X} → x ≡ x

trans-≡ : {A : Set} {a b c : A} → a ≡ b → b ≡ c → a ≡ c
trans-≡ refl refl = refl

comm-≡ : {A : Set} {a b : A} → a ≡ b → b ≡ a
comm-≡ refl = refl

subst : {A : Set} (P : A → Set) {x y : A} → (x ≡ y) → P x → P y
subst P refl u = u

infix 2 Σ
data Σ (A : Set) (B : A → Set) : Set where
  _,_ : (x : A) → (y : B x) → Σ A B

syntax Σ A (λ x → B) = Σ[ x ∈ A ] B

data _≤_ : ℕ → ℕ → Set where
    ≤-base : {x : ℕ} → zero ≤ x
    ≤-succ : {x y : ℕ} → x ≤ y → succ x ≤ succ y

≤-refl : {n : ℕ} → n ≤ n
≤-refl {zero} = ≤-base
≤-refl {succ n} = ≤-succ (≤-refl {n})

cmp : (a : ℕ) → (b : ℕ) → (a ≤ b) ∨ (b ≤ a)
cmp zero b = left ≤-base
cmp a zero = right ≤-base
cmp (succ a) (succ b) with cmp a b
... | left  a≤b = left (≤-succ a≤b)
... | right b≤a = right (≤-succ b≤a)

distr-Σ-∨ : {A : Set} {B C : A → Set} → (Σ[ a ∈ A ] (B a ∨ C a)) → (Σ[ a ∈ A ] (B a)) ∨ (Σ[ a ∈ A ] (C a))
distr-Σ-∨ (a , left x)  = left (a , x)
distr-Σ-∨ (a , right x) = right (a , x)

fmap-right : {A B C : Set} → (B → C) → (A ∨ B) → (A ∨ C)
fmap-right f (left x) = left x
fmap-right f (right x) = right (f x)

data _<_ : (a : ℕ) → (b : ℕ) → Set where
    <-base : {x : ℕ} → zero < succ x
    <-succ : {x y : ℕ} → x < y → succ x < succ y

less-leq : {a b : ℕ} → a ≤ b → a < succ b
less-leq ≤-base = <-base
less-leq (≤-succ a) = <-succ (less-leq a)

leq-less : {a b : ℕ} → succ a ≤ b → a < b
leq-less (≤-succ a≤b) = less-leq a≤b