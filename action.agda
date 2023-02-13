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

  -- shape sorts
  data TShape : Shape → Set where
    STArrow : TShape tarrow
    STNum   : TShape tnum
    STBool  : TShape tbool

  data EShape : Shape → Set where
    SEVar   : (x : Var)
            → EShape (var x)
    SELam   : (x : Var)
            → EShape (lam x)
    SEAp₁   : EShape ap₁
    SEAp₂   : EShape ap₂
    SELet₁  : (x : Var)
            → EShape (let₁ x)
    SELet₂  : (x : Var)
            → EShape (let₂ x)
    SENum   : (n : ℕ)
            → EShape (num n)
    SEPlus₁ : EShape plus₁
    SEPlus₂ : EShape plus₂
    SETrue  : EShape tt
    SEFalse : EShape ff
    SEIf₁   : EShape if₁
    SEIf₂   : EShape if₂
    SEIf₃   : EShape if₃
