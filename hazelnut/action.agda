open import prelude
open import core

module hazelnut.action where
  -- movement direction
  data Dir : Set where
    child  : (n : ℕ) → Dir
    parent : Dir

  -- construction shape
  data Shape : Set where
    tarrow₁ : Shape
    tarrow₂ : Shape
    tprod₁  : Shape
    tprod₂  : Shape
    tnum    : Shape
    tbool   : Shape
    var     : (x : Var) → Shape
    lam     : (x : Var) → Shape
    ap₁     : (u : Hole) → Shape
    ap₂     : (u : Hole) → Shape
    let₁    : (x : Var) → (u : Hole) → Shape
    let₂    : (x : Var) → (u : Hole) → Shape
    num     : (n : ℕ) → Shape
    plus₁   : (u : Hole) → Shape
    plus₂   : (u : Hole) → Shape
    tt      : Shape
    ff      : Shape
    if₁     : (u₁ : Hole) → (u₂ : Hole) → Shape
    if₂     : (u₁ : Hole) → (u₂ : Hole) → Shape
    if₃     : (u₁ : Hole) → (u₂ : Hole) → Shape
    pair₁   : (u : Hole) → Shape
    pair₂   : (u : Hole) → Shape
    projl   : Shape
    projr   : Shape

  -- actions
  data Action : Set where
    move      : (δ : Dir) → Action
    construct : (ψ : Shape) → Action
    del       : (u : Hole) → Action

  -- action lists
  ActionList : Set
  ActionList = List Action

  module movements where
    data _movements : ActionList → Set where
      AMINil  : [] movements
      AMICons : ∀ {ᾱ : ActionList}
              → (δ : Dir)
              → (mv : ᾱ movements)
              → ((move δ) ∷ ᾱ) movements

    movements-++ : ∀ {ᾱ₁ ᾱ₂} → ᾱ₁ movements → ᾱ₂ movements → (ᾱ₁ ++ ᾱ₂) movements
    movements-++ AMINil           ᾱmv  = ᾱmv
    movements-++ (AMICons δ ᾱmv₁) ᾱmv₂ = AMICons δ (movements-++ ᾱmv₁ ᾱmv₂)

  module sort where
    -- shape sorts
    data _tshape : Shape → Set where
      STArrow₁ : tarrow₁ tshape
      STArrow₂ : tarrow₂ tshape
      STProd₁  : tprod₁ tshape
      STProd₂  : tprod₂ tshape
      STNum    : tnum tshape
      STBool   : tbool tshape

    data _eshape : Shape → Set where
      SEVar   : (x : Var)
              → (var x) eshape
      SELam   : (x : Var)
              → (lam x) eshape
      SEAp₁   : (u : Hole)
              → (ap₁ u) eshape
      SEAp₂   : (u : Hole)
              → (ap₂ u) eshape
      SELet₁  : (x : Var)
              → (u : Hole)
              → (let₁ x u) eshape
      SELet₂  : (x : Var)
              → (u : Hole)
              → (let₂ x u) eshape
      SENum   : (n : ℕ)
              → (num n) eshape
      SEPlus₁ : (u : Hole)
              → (plus₁ u) eshape
      SEPlus₂ : (u : Hole)
              → (plus₂ u) eshape
      SETrue  : tt eshape
      SEFalse : ff eshape
      SEIf₁   : (u₁ : Hole)
              → (u₂ : Hole)
              → (if₁ u₁ u₂) eshape
      SEIf₂   : (u₁ : Hole)
              → (u₂ : Hole)
              → (if₂ u₁ u₂) eshape
      SEIf₃   : (u₁ : Hole)
              → (u₂ : Hole)
              → (if₃ u₁ u₂) eshape
      SEPair₁ : (u : Hole)
              → (pair₁ u) eshape
      SEPair₂ : (u : Hole)
              → (pair₂ u) eshape
      SEProjL : projl eshape
      SEProjR : projr eshape

    -- sort decidability
    TShape? : (ψ : Shape) → Dec (ψ tshape)
    TShape? tarrow₁     = yes STArrow₁
    TShape? tarrow₂     = yes STArrow₂
    TShape? tprod₁      = yes STProd₁
    TShape? tprod₂      = yes STProd₂
    TShape? tnum        = yes STNum
    TShape? tbool       = yes STBool
    TShape? (var x)     = no (λ ())
    TShape? (lam x)     = no (λ ())
    TShape? (ap₁ u)     = no (λ ())
    TShape? (ap₂ u)     = no (λ ())
    TShape? (let₁ x u)  = no (λ ())
    TShape? (let₂ x u)  = no (λ ())
    TShape? (num n)     = no (λ ())
    TShape? (plus₁ u)   = no (λ ())
    TShape? (plus₂ u)   = no (λ ())
    TShape? tt          = no (λ ())
    TShape? ff          = no (λ ())
    TShape? (if₁ u₁ u₂) = no (λ ())
    TShape? (if₂ u₁ u₂) = no (λ ())
    TShape? (if₃ u₁ u₂) = no (λ ())
    TShape? (pair₁ u)   = no (λ ())
    TShape? (pair₂ u)   = no (λ ())
    TShape? projl       = no (λ ())
    TShape? projr       = no (λ ())

    EShape? : (ψ : Shape) → Dec (ψ eshape)
    EShape? tarrow₁     = no (λ ())
    EShape? tarrow₂     = no (λ ())
    EShape? tprod₁      = no (λ ())
    EShape? tprod₂      = no (λ ())
    EShape? tnum        = no (λ ())
    EShape? tbool       = no (λ ())
    EShape? (var x)     = yes (SEVar x)
    EShape? (lam x)     = yes (SELam x)
    EShape? (ap₁ u)     = yes (SEAp₁ u)
    EShape? (ap₂ u)     = yes (SEAp₂ u)
    EShape? (let₁ x u)  = yes (SELet₁ x u)
    EShape? (let₂ x u)  = yes (SELet₂ x u)
    EShape? (num n)     = yes (SENum n)
    EShape? (plus₁ u)   = yes (SEPlus₁ u)
    EShape? (plus₂ u)   = yes (SEPlus₂ u)
    EShape? tt          = yes SETrue
    EShape? ff          = yes SEFalse
    EShape? (if₁ u₁ u₂) = yes (SEIf₁ u₁ u₂)
    EShape? (if₂ u₁ u₂) = yes (SEIf₂ u₁ u₂)
    EShape? (if₃ u₁ u₂) = yes (SEIf₃ u₁ u₂)
    EShape? (pair₁ u)   = yes (SEPair₁ u)
    EShape? (pair₂ u)   = yes (SEPair₂ u)
    EShape? projl       = yes SEProjL
    EShape? projr       = yes SEProjR

  open movements public
  open sort public
