module Drinker where

open import Common

drinker : (f : ℕ → Bool) → ¬ ¬ (Σ[ n ∈ ℕ ] (f n ≡ true → ((m : ℕ) → ¬ ¬ (f m ≡ true))))
drinker f = λ not-drinker →              -- Assume that Drinker's tautology is false.
    not-drinker (zero , λ _ →            -- We can say that Drinker's tautology holds
        λ m not-fm≡true →                --  for all natural numbers m, since if ¬ (f m ≡ true)    
            not-drinker (m ,             --  then we can select m itself to make the condition hold vacuously.
                λ fm≡true _ _ → not-fm≡true fm≡true))
            -- But this is in contrast to the assumption that Drinker's tautology is false.
