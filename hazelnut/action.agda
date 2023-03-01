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
      ASortArrow₁ : tarrow₁ tshape
      ASortArrow₂ : tarrow₂ tshape
      ASortProd₁  : tprod₁ tshape
      ASortProd₂  : tprod₂ tshape
      ASortNum    : tnum tshape
      ASortBool   : tbool tshape

    data _eshape : Shape → Set where
      ASortVar   : (x : Var)
              → (var x) eshape
      ASortLam   : (x : Var)
              → (lam x) eshape
      ASortAp₁   : (u : Hole)
              → (ap₁ u) eshape
      ASortAp₂   : (u : Hole)
              → (ap₂ u) eshape
      ASortLet₁  : (x : Var)
              → (u : Hole)
              → (let₁ x u) eshape
      ASortLet₂  : (x : Var)
              → (u : Hole)
              → (let₂ x u) eshape
      ASortNum   : (n : ℕ)
              → (num n) eshape
      ASortPlus₁ : (u : Hole)
              → (plus₁ u) eshape
      ASortPlus₂ : (u : Hole)
              → (plus₂ u) eshape
      ASortTrue  : tt eshape
      ASortFalse : ff eshape
      ASortIf₁   : (u₁ : Hole)
              → (u₂ : Hole)
              → (if₁ u₁ u₂) eshape
      ASortIf₂   : (u₁ : Hole)
              → (u₂ : Hole)
              → (if₂ u₁ u₂) eshape
      ASortIf₃   : (u₁ : Hole)
              → (u₂ : Hole)
              → (if₃ u₁ u₂) eshape
      ASortPair₁ : (u : Hole)
              → (pair₁ u) eshape
      ASortPair₂ : (u : Hole)
              → (pair₂ u) eshape
      ASortProjL : projl eshape
      ASortProjR : projr eshape

    -- sort decidability
    TShape? : (ψ : Shape) → Dec (ψ tshape)
    TShape? tarrow₁     = yes ASortArrow₁
    TShape? tarrow₂     = yes ASortArrow₂
    TShape? tprod₁      = yes ASortProd₁
    TShape? tprod₂      = yes ASortProd₂
    TShape? tnum        = yes ASortNum
    TShape? tbool       = yes ASortBool
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
    EShape? (var x)     = yes (ASortVar x)
    EShape? (lam x)     = yes (ASortLam x)
    EShape? (ap₁ u)     = yes (ASortAp₁ u)
    EShape? (ap₂ u)     = yes (ASortAp₂ u)
    EShape? (let₁ x u)  = yes (ASortLet₁ x u)
    EShape? (let₂ x u)  = yes (ASortLet₂ x u)
    EShape? (num n)     = yes (ASortNum n)
    EShape? (plus₁ u)   = yes (ASortPlus₁ u)
    EShape? (plus₂ u)   = yes (ASortPlus₂ u)
    EShape? tt          = yes ASortTrue
    EShape? ff          = yes ASortFalse
    EShape? (if₁ u₁ u₂) = yes (ASortIf₁ u₁ u₂)
    EShape? (if₂ u₁ u₂) = yes (ASortIf₂ u₁ u₂)
    EShape? (if₃ u₁ u₂) = yes (ASortIf₃ u₁ u₂)
    EShape? (pair₁ u)   = yes (ASortPair₁ u)
    EShape? (pair₂ u)   = yes (ASortPair₂ u)
    EShape? projl       = yes ASortProjL
    EShape? projr       = yes ASortProjR

  open movements public
  open sort public
