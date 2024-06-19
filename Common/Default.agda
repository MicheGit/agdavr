module Common.Default where

open import Common.Void public
open import Common.Generic (⊥) public

bool-neg : {g b : Bool} → ¬ b ≡ g → b ≡ not g
bool-neg {false} {false} neg = ⊥-elim (neg refl)
bool-neg {false} {true} neg = refl
bool-neg {true} {false} neg = refl
bool-neg {true} {true} neg = ⊥-elim (neg refl)

comp-¬ : {a b c : Bool} → ¬ a ≡ b → ¬ b ≡ c → a ≡ c
comp-¬ {false} {b} {false} na nb = refl
comp-¬ {true} {b} {true} na nb = refl
comp-¬ {false} {false} {true} na nb = ⊥-elim (na refl)
comp-¬ {true} {true} {false} na nb = ⊥-elim (na refl)
comp-¬ {a} {false} {false} na nb = ⊥-elim (nb refl)
comp-¬ {a} {true} {true} na nb = ⊥-elim (nb refl)
