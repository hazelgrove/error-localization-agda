open import prelude

module action where
  Var : Set
  Var = ℕ

  -- movement direction
  data Dir : Set where
    child  : (n : ℕ) → Dir
    parent : Dir

  -- construction shape
  data Shape : Set where
    tarrow : Shape
    tnum   : Shape
    tbool  : Shape
    var    : (x : Var) → Shape
    lam    : (x : Var) → Shape
    ap₁    : Shape
    ap₂    : Shape
    let₁   : (x : Var) → Shape
    let₂   : (x : Var) → Shape
    num    : (n : ℕ) → Shape
    plus₁  : Shape
    plus₂  : Shape
    tt     : Shape
    ff     : Shape
    if₁    : Shape
    if₂    : Shape
    if₃    : Shape

  -- actions
  data Action : Set where
    move      : (δ : Dir) → Action
    construct : (ψ : Shape) → Action
    del       : Action
