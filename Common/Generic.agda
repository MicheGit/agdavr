module Common.Generic (⊥ : Set) where

open import Common.Data public

infix 3 ¬_
¬_ : Set → Set
¬ X = X → ⊥

⊥-elim-dn : {A : Set} → ⊥ → ¬ ¬ A
⊥-elim-dn b = λ _ → b

-- double negation is a monad
return : {A : Set} → A → ¬ ¬ A
return a = λ z → z a

infixr 5 _⟫=_
_⟫=_ : {A B : Set} → ¬ ¬ A → (A → ¬ ¬ B) → ¬ ¬ B
a ⟫= b = λ z → a (λ z₁ → b z₁ z)

escape : {A : Set} → ¬ ¬ ⊥ → ⊥
escape nb = nb (λ z → z)

dn-lem : {A : Set} → ¬ ¬ (A ∨ ¬ A)
dn-lem = λ z → z (right (λ x → z (left x)))

neg : (b : Bool) → Set → Set
neg true p = p
neg false p = ¬ p

bool-lem : {g b : Bool} → b ≡ g → ¬ b ≡ not g
bool-lem {false} {false} b≡g = (λ ())
bool-lem {true} {true} b≡g = (λ ())

bool-neg-dn : {g b : Bool} → ¬ b ≡ g → ¬ ¬ b ≡ not g
bool-neg-dn {false} {false} neq = λ _ → neq refl
bool-neg-dn {true} {true} neq = λ _ → neq refl
bool-neg-dn {false} {true} neq = λ z → z refl
bool-neg-dn {true} {false} neq = λ z → z refl

eq : (a : Bool) → (b : Bool) → Σ[ c ∈ Bool ] (neg c (a ≡ b))
eq true true = true , refl
eq false false = true , refl
eq false true = false , λ ()
eq true false = false , λ ()

and-neg-dn : {A B : Set} → ¬ (A ∧ B) → ¬ ¬ (¬ A ∨ ¬ B)
and-neg-dn f nor = nor (left (λ x → nor (right (λ x₁ → f (x , x₁)))))

left-dn : {A B : Set} → ¬ ¬ A → ¬ ¬ (A ∨ B)
left-dn na nor = na (λ z → nor (left z))

left-escape : {A B : Set} → A ∨ ¬ ¬ B → ¬ ¬ (A ∨ B)
left-escape (left x) = λ z → z (left x)
left-escape (right x) = λ z → x (λ z₁ → z (right z₁))

switch : {A B : Set} → (B → A) → ¬ A → ¬ B
switch f na b = na (f b)

smth : {A B : Set} → (¬ A → B) → ¬ B → ¬ ¬ A
smth f nb na = nb (f na)

neg-forall : {A : Set} {B : A → Set} → ((a : A) → B a) → ¬ (Σ[ a ∈ A ] (¬ B a))
neg-forall f (x , y) = y (f x)

neg-exists : {A : Set} {B : A → Set} → ((a : A) → B a) → ¬ (Σ[ a ∈ A ] (¬ B a))
neg-exists f (a , nba) = nba (f a)

neg-exists₁ : {A : Set} {B : A → Set} → ((a : A) → ¬ B a) → ¬ (Σ[ a ∈ A ] (B a))
neg-exists₁ f (a , ba) = f a ba