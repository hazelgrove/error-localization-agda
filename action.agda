open import prelude

module action where
  -- movement direction
  data Dir : Set where
    Child  : (n : ℕ) → Dir
    Parent : Dir

  -- construction shape
  data Shape : Set where
    Arrow : Shape
    Num   : Shape
    Bool  : Shape
    Var   : (x : ℕ) → Shape
    Lam   : (x : ℕ) → Shape
    Ap₁   : Shape
    Ap₂   : Shape
    Let₁  : (x : ℕ) → Shape
    Let₂  : (x : ℕ) → Shape
    Lit   : (n : ℕ) → Shape
    Plus₁ : Shape
    Plus₂ : Shape
    True  : Shape
    False : Shape
    If₁   : Shape
    If₂   : Shape
    If₃   : Shape

  -- actions
  data Action : Set where
    Move      : (δ : Dir) → Action
    Construct : (ψ : Shape) → Action
    Del       : Action
