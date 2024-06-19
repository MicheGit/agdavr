module EX3-2 where

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

            postulate
                lemma₂ : ¬ StolzL → ¬ ¬ (Σ[ a ∈ ℕ ] ((b : ℕ) → a ≤ b → f b ≡ true))
                -- lemma₂ nf nex = {!   !} -- smth lemma₁

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
    The infinite pidgeon hole does not admit a constructive proof since it 
        requires a realizer for
          ¬ (∀a ∈ ℕ . ∃b ∈ ℕ . a ≤ b ∧ f b ≡ 0) → (∃a ∈ ℕ . ∀b ∈ ℕ . a ≤ b → f b ≡ 1).

    Such a realizer should be a program that returns a result in the form of:
        π₁ ∙ e = n (a number)
        π₂ ∙ e ⊩ ∀b ∈ ℕ . n ≤ b → f b ≡ 1
                ^^^^^^^ this basically means that we must provide a function 
                        that takes a number b, a proof that that b is greater than
                        n and it must return a general proof of f b ≡ 1
    
    Which is impossible, since such algorithm has to check all numbers after n, 
    to be sure of the fact that it is the last number st f n ≡ 0

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

    

    

    

  
    