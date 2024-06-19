module Common.Void where

data ⊥ : Set where

⊥-elim : {A : Set} → ⊥ → A
⊥-elim ()