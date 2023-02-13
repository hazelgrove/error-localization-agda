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

  -- action lists
  data ActionList : Set where
    ∙   : ActionList
    _∷_ : (α : Action) → (ᾱ : ActionList) → ActionList

  module movements where
    data _movements : ActionList → Set where
      AMINil  : ∙ movements
      AMICons : ∀ {ᾱ : ActionList}
              → (δ : Dir)
              → (mv : ᾱ movements)
              → ((move δ) ∷ ᾱ) movements

  module sort where
    -- shape sorts
    data _tshape : Shape → Set where
      STArrow : tarrow tshape
      STNum   : tnum tshape
      STBool  : tbool tshape

    data _eshape : Shape → Set where
      SEVar   : (x : Var)
              → (var x) eshape
      SELam   : (x : Var)
              → (lam x) eshape
      SEAp₁   : ap₁ eshape
      SEAp₂   : ap₂ eshape
      SELet₁  : (x : Var)
              → (let₁ x) eshape
      SELet₂  : (x : Var)
              → (let₂ x) eshape
      SENum   : (n : ℕ)
              → (num n) eshape
      SEPlus₁ : plus₁ eshape
      SEPlus₂ : plus₂ eshape
      SETrue  : tt eshape
      SEFalse : ff eshape
      SEIf₁   : if₁ eshape
      SEIf₂   : if₂ eshape
      SEIf₃   : if₃ eshape

    -- sort decidability
    TShape? : (ψ : Shape) → Dec (ψ tshape)
    TShape? tarrow   = yes STArrow
    TShape? tnum     = yes STNum
    TShape? tbool    = yes STBool
    TShape? (var x)  = no (λ ())
    TShape? (lam x)  = no (λ ())
    TShape? ap₁      = no (λ ())
    TShape? ap₂      = no (λ ())
    TShape? (let₁ x) = no (λ ())
    TShape? (let₂ x) = no (λ ())
    TShape? (num n)  = no (λ ())
    TShape? plus₁    = no (λ ())
    TShape? plus₂    = no (λ ())
    TShape? tt       = no (λ ())
    TShape? ff       = no (λ ())
    TShape? if₁      = no (λ ())
    TShape? if₂      = no (λ ())
    TShape? if₃      = no (λ ())

    EShape? : (ψ : Shape) → Dec (ψ eshape)
    EShape? tarrow   = no (λ ())
    EShape? tnum     = no (λ ())
    EShape? tbool    = no (λ ())
    EShape? (var x)  = yes (SEVar x)
    EShape? (lam x)  = yes (SELam x)
    EShape? ap₁      = yes SEAp₁
    EShape? ap₂      = yes SEAp₂
    EShape? (let₁ x) = yes (SELet₁ x)
    EShape? (let₂ x) = yes (SELet₂ x)
    EShape? (num n)  = yes (SENum n)
    EShape? plus₁    = yes SEPlus₁
    EShape? plus₂    = yes SEPlus₂
    EShape? tt       = yes SETrue
    EShape? ff       = yes SEFalse
    EShape? if₁      = yes SEIf₁
    EShape? if₂      = yes SEIf₂
    EShape? if₃      = yes SEIf₃

  open sort public
