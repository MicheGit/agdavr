module EX3-2 where


module ConstructiveManually where

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

-- Ex. 3.2.a

module Classical where

    open import Common.Default

    postulate 
        lem : {A : Set} → A ∨ ¬ A 
    
    thm' : {f : ℕ → Bool} (a : ℕ) → (Σ[ b ∈ ℕ ] (a ≤ b ∧ f b ≡ false)) ∨ (Σ[ b ∈ ℕ ] (a ≤ b ∧ f b ≡ true)) 
    thm' a = distr-Σ-∨ (a , distr-∧-∨ (≤-refl , fmap-right bool-neg lem))

    theorem : (f : ℕ → Bool) → ((a : ℕ) → (Σ[ b ∈ ℕ ] (a ≤ b ∧ f b ≡ false))) ∨ ((a : ℕ) → (Σ[ b ∈ ℕ ] (a ≤ b ∧ f b ≡ true)))
    theorem f = {!   !}
    
-- Ex 3.2.b
{-
    The infinite pidgeon hole does not admit a direct constructive proof since it 
        is in the form of A ∨ B.
        
    A realizer for the pidgeon hole would be in one of this two forms:
        π₁ ∙ e ↓ 0 and then π₂ ∙ e ⊩ (∀ a ∈ ℕ : ∃ b ∈ ℕ (a ≤ b ∧ f b ≡ false))
        π₁ ∙ e ↓ (succ n) for some n and then π₂ ∙ e ⊩ (∀ a ∈ ℕ : ∃ b ∈ ℕ (a ≤ b ∧ f b ≡ true)).

    Both forms are unrealizable since each would be generally false by themself alone:
        ̸⊩ (∀ a ∈ ℕ : ∃ b ∈ ℕ (a ≤ b ∧ f b ≡ false))
        since we can provide f ≔ 𝟙 and it would be false,
        ̸⊩ (∀ a ∈ ℕ : ∃ b ∈ ℕ (a ≤ b ∧ f b ≡ true))
        similarly we can provide f ≔ 𝟘 and it would be false too.
-}

-- Ex 3.2.c 

module LemmaC where

    open import Common.Default

    one = succ zero
    two = succ one

    lemma : (f : ℕ → Bool) → Σ[ i ∈ ℕ ] (Σ[ j ∈ ℕ ] (i < j ∧ f i ≡ f j))
    lemma f with eq (f zero) (f one) | eq (f one) (f two)
    ... | true  , zero≡one | _               = zero , one , <-base , zero≡one
    ... | false , zero≢one | true , one≡two  = one , two , <-succ <-base , one≡two 
    ... | false , zero≢one | false , one≢two = zero , ( two , <-base , comp-¬ zero≢one one≢two )

-- Ex 3.2.d

module LemmaD where

    module AssumeBottom (⊥ : Set) where

        open import Common.Generic (⊥)

        module _ (f : ℕ → Bool) where
            Stolzenberg→ : Bool → Set
            Stolzenberg→ g = ((a : ℕ) → (Σ[ b ∈ ℕ ] (a ≤ b ∧ f b ≡ g)))

            Stolzenberg : Set
            Stolzenberg = (Stolzenberg→ false) ∨ (Stolzenberg→ true)

            -- NegStolzenberg→False : Set
            -- NegStolzenberg→False = (Σ[ a ∈ ℕ ] ((b : ℕ) → (a ≤ b → f b ≡ true)))

            -- NegStolzenberg→True : Set
            -- NegStolzenberg→True = (Σ[ a ∈ ℕ ] ((b : ℕ) → (a ≤ b → ¬ f b ≡ true)))

            -- try1 : (Stolzenberg→ false) → ¬ NegStolzenberg→False
            -- try1 sf (a , promise) with sf a
            -- ... | x , (a≤x , fx≡false ) = bool-lem fx≡false (promise x a≤x)

            either : (b : Bool) → b ≡ false ∨ b ≡ true
            either true = right refl
            either false = left refl

            -- ⊥-elim : {A : Set} → ⊥ → A
            -- ⊥-elim = {!   !}

            -- int1 : ¬ NegStolzenberg→False → Stolzenberg→ false
            -- int1 ns a = {!   !}

            -- try2 : ¬ NegStolzenberg→False → ¬ ¬ ¬ ¬ Stolzenberg→ false
            -- try2 ns nf = {!   !}


            -- lem⇒thm : {A : Set} → (A ∨ ¬ A) → (¬ NegStolzenberg→False ∨ ¬ NegStolzenberg→True) → ¬ ¬ ((Stolzenberg→ false) ∨ (Stolzenberg→ true))
            -- lem⇒thm lem (left  x) = try2 x ⟫= left-dn
            -- lem⇒thm lem (right x) = {!   !}

            -- theorem : ¬ ¬ Stolzenberg
            -- theorem = dn-lem ⟫= λ lem → and-neg-dn lemma₁ ⟫= lem⇒thm lem -- lem⇒thm lem
            --     where 
            --         lemma₁ : ¬ (NegStolzenberg→False ∧ NegStolzenberg→True)
            --         lemma₁ ((a , pra) , (b , prb)) with cmp a b
            --         ... | left a≤b = prb b ≤-refl (pra b a≤b)
            --         ... | right b≤a = prb a b≤a (pra a ≤-refl)

            StolzL : Set
            StolzL = ((a : ℕ) → (Σ[ b ∈ ℕ ] (a ≤ b ∧ f b ≡ false)))

            StolzR : Set
            StolzR = ((a : ℕ) → (Σ[ b ∈ ℕ ] (a ≤ b ∧ f b ≡ true)))
        
            -- lemma₁ : (Σ[ a ∈ ℕ ] ((b : ℕ) → a ≤ b → f b ≡ true)) → ¬ StolzL
            -- lemma₁ ( a , prms ) sl with sl a
            -- ... | ( b , ( a≤b , fb≡false )) = bool-lem fb≡false (prms b a≤b)

            lemma₂ : ¬ StolzL → ¬ ¬ (Σ[ a ∈ ℕ ] ((b : ℕ) → a ≤ b → f b ≡ true))
            lemma₂ nsl nex = {!   !}

            lemma₃ : (Σ[ a ∈ ℕ ] ((b : ℕ) → a ≤ b → f b ≡ true)) → StolzR
            lemma₃ (a , prm ) a₁ with cmp a a₁
            ... | left a≤a₁ = a₁ , (≤-refl , prm a₁ a≤a₁)
            ... | right a₁≤a = a , (a₁≤a , prm a ≤-refl)
            
            lemma₄ : ¬ StolzL → ¬ ¬ StolzR
            lemma₄ f = lemma₂ f ⟫= λ x → return (lemma₃ x)

            lemma₅ : StolzL ∨ ¬ StolzL → StolzL ∨ ¬ ¬ StolzR
            lemma₅ = fmap-right lemma₄

            theorem' : ¬ ¬ Stolzenberg
            theorem' = dn-lem ⟫= λ lem → left-escape (lemma₅ lem)

    

  
  