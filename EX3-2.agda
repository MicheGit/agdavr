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

    import Common.Data as D

    Stolzenberg→ : (D.ℕ → D.Bool) → D.Bool → Set
    Stolzenberg→ f g = ((a : D.ℕ) → (D.Σ[ b ∈ D.ℕ ] (a D.≤ b D.∧ f b D.≡ g)))

    Stolzenberg : (D.ℕ → D.Bool) → Set
    Stolzenberg f = (Stolzenberg→ f D.false) D.∨ (Stolzenberg→ f D.true)

    module ProveStolz (⊥ : Set) where

        open import Common.Generic (⊥) public

        module _ (f : ℕ → Bool) where

            StolzL : Set
            StolzL = ((a : ℕ) → (Σ[ b ∈ ℕ ] (a ≤ b ∧ f b ≡ false)))

            StolzR : Set
            StolzR = ((a : ℕ) → (Σ[ b ∈ ℕ ] (a ≤ b ∧ f b ≡ true)))
        
            -- lemma₁ : (Σ[ a ∈ ℕ ] ((b : ℕ) → a ≤ b → f b ≡ true)) → ¬ StolzL
            -- lemma₁ ( a , prms ) sl with sl a
            -- ... | ( b , ( a≤b , fb≡false )) = bool-lem fb≡false (prms b a≤b)

            lemma₀ : (Σ[ a ∈ ℕ ] ((b : ℕ) → a ≤ b → f b ≡ true)) ∨ StolzL
            lemma₀ = {!   !}

            lemma₁ : ¬ (Σ[ a ∈ ℕ ] ((b : ℕ) → a ≤ b → f b ≡ true)) → StolzL
            lemma₁ prf a = {!   !}

            lemma₂ : ¬ StolzL → ¬ ¬ (Σ[ a ∈ ℕ ] ((b : ℕ) → a ≤ b → f b ≡ true))
            lemma₂ = smth lemma₁

            lemma₃ : (Σ[ a ∈ ℕ ] ((b : ℕ) → a ≤ b → f b ≡ true)) → StolzR
            lemma₃ (a , prm ) a₁ with cmp a a₁
            ... | left a≤a₁ = a₁ , (≤-refl , prm a₁ a≤a₁)
            ... | right a₁≤a = a , (a₁≤a , prm a ≤-refl)
            
            lemma₄ : ¬ StolzL → ¬ ¬ StolzR
            lemma₄ f = lemma₂ f ⟫= λ x → return (lemma₃ x)

            lemma₅ : StolzL ∨ ¬ StolzL → StolzL ∨ ¬ ¬ StolzR
            lemma₅ = fmap-right lemma₄

            theorem' : ¬ ¬ Stolzenberg f
            theorem' = dn-lem ⟫= λ lem → left-escape (lemma₅ lem)
    
    module ProofStolz (f : D.ℕ → D.Bool) where
        open ProveStolz (Stolzenberg f) public
        
        proof : Stolzenberg f
        proof = escape (theorem' f)
    
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

    import Common.Data as D

    one = D.succ D.zero
    two = D.succ one

    module _ (f : D.ℕ → D.Bool) where
        open Classical.ProofStolz (f)

        -- Here the program can just apply the proof twice to find two different 
        -- numbers a and b s.t. f a ≡ f b. 
        -- It doesn't search necessarily for one or two after zero

        lemma : (Σ[ i ∈ ℕ ] (Σ[ j ∈ ℕ ] (i < j ∧ f i ≡ f j)))
        lemma with proof
        lemma | D.left  x with x zero
        lemma | D.left  x | a , (zero≤a , fa≡false ) with x (succ a)
        lemma | D.left  x | a , (zero≤a , fa≡false ) | b , (a≤b , fb≡false ) = a , (b , (leq-less a≤b , trans-≡ fa≡false (comm-≡ fb≡false)))
        lemma | D.right x with x zero
        lemma | D.right x | a , (zero≤a , fa≡true ) with x (succ a)
        lemma | D.right x | a , (zero≤a , fa≡true ) | b , (a≤b , fb≡true ) = a , (b , (leq-less a≤b , trans-≡ fa≡true (comm-≡ fb≡true)))

    

    

    

  
  