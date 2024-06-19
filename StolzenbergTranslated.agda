module StolzenbergTranslated where

open import Common.Default

stolz-comp : (f : ℕ → Bool) → ¬ ((Σ[ a ∈ ℕ ] ((b : ℕ) → a ≤ b → ¬ f b ≡ false)) ∧ (Σ[ a ∈ ℕ ] ((b : ℕ) → a ≤ b → ¬ f b ≡ true)))
stolz-comp f ( ( a , atrue) , ( b , btrue ) ) with cmp a b
... | left  a≤b = atrue b a≤b (bool-neg (btrue b ≤-refl))
... | right b≤a = btrue a b≤a (bool-neg (atrue a ≤-refl))

lemma : (g : Bool) → (f : ℕ → Bool) → ¬ (Σ[ a ∈ ℕ ] ((b : ℕ) → a ≤ b → ¬ f b ≡ g)) → ((a : ℕ) → ¬ ¬ (Σ[ b ∈ ℕ ] (a ≤ b ∧ f b ≡ g)))
lemma g f nex a nnex = nex (a , λ b a≤b fb≡g → nnex (b , a≤b , fb≡g))

fmap-∨ : {L R A B : Set} → (f : L → A) → (g : R → B) → L ∨ R → A ∨ B
fmap-∨ f g (left x) = left (f x)
fmap-∨ f g (right x) = right (g x)

equiv-∧ : {A B : Set} → ¬ (A ∧ B) → ¬ ¬ (¬ A ∨ ¬ B)
equiv-∧ f nor = nor (left (λ x → nor (right (λ x₁ → f (x , x₁)))))

fmap-¬-¬ : {A B : Set} → (A → B) → ¬ ¬ A → ¬ ¬ B
fmap-¬-¬ f nna nb = nna (λ z → nb (f z)) 

theorem : (f : ℕ → Bool) → ¬ ¬ (((a : ℕ) → ¬ ¬ (Σ[ b ∈ ℕ ] (a ≤ b ∧ f b ≡ false))) ∨ ((a : ℕ) → ¬ ¬ (Σ[ b ∈ ℕ ] (a ≤ b ∧ f b ≡ true))))
theorem f = fmap-¬-¬ (fmap-∨ (lemma false f) (lemma true f)) (equiv-∧ (stolz-comp f))