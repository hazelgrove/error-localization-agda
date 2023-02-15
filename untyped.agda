open import prelude
open import core

open import zexp
open import action

module untyped where
  -- type actions
  data _+_+τ>_ : (τ : ZTyp) → (α : Action) → (τ′ : ZTyp) → Set where
    -- movement
    TMArrChild1 : ∀ {τ₁ τ₂ : Typ}
                 → ▹ τ₁ -→ τ₂ ◃ + move (child 1) +τ> ▹ τ₁ ◃ -→₁ τ₂
    TMArrChild2 : ∀ {τ₁ τ₂ : Typ}
                 → ▹ τ₁ -→ τ₂ ◃ + move (child 2) +τ> τ₁ -→₂ ▹ τ₂ ◃
    TMArrParent1 : ∀ {τ₁ τ₂ : Typ}
                 → ▹ τ₁ ◃ -→₁ τ₂ + move parent +τ> ▹ τ₁ -→ τ₂ ◃
    TMArrParent2 : ∀ {τ₁ τ₂ : Typ}
                 → τ₁ -→₂ ▹ τ₂ ◃ + move parent +τ> ▹ τ₁ -→ τ₂ ◃

    -- deletion
    TDel : ∀ {τ : Typ} {u : Hole}
         → ▹ τ ◃ + (del u) +τ> ▹ unknown ◃

    -- construction
    TConArrow1 : ∀ {τ : Typ}
               → ▹ τ ◃ + construct tarrow₁ +τ> τ -→₂ ▹ unknown ◃
    TConArrow2 : ∀ {τ : Typ}
               → ▹ τ ◃ + construct tarrow₂ +τ> ▹ unknown ◃ -→₁ τ
    TConNum    : ▹ unknown ◃ + construct tnum +τ> ▹ num ◃
    TConBool   : ▹ unknown ◃ + construct tbool +τ> ▹ bool ◃

    -- zipper
    TZipArr1 : ∀ {τ^ τ^′ : ZTyp} {τ : Typ} {α : Action}
             → (τ^+>τ^′ : τ^ + α +τ> τ^′)
             → τ^ -→₁ τ + α +τ> τ^′ -→₁ τ
    TZipArr2 : ∀ {τ^ τ^′ : ZTyp} {τ : Typ} {α : Action}
             → (τ^+>τ^′ : τ^ + α +τ> τ^′)
             → τ -→₂ τ^ + α +τ> τ -→₂ τ^′

  -- expression actions
  data _+_+e>_ : (ê : ZExp) → (α : Action) → (ê′ : ZExp) → Set where
    -- movement
    EMLamChild1  : ∀ {x τ e}
                 → ‵▹ ‵λ x ∶ τ ∙ e ◃ + move (child 1) +e> (‵λ₁ x ∶ ▹ τ ◃ ∙ e)
    EMLamChild2  : ∀ {x τ e}
                 → ‵▹ ‵λ x ∶ τ ∙ e ◃ + move (child 2) +e> (‵λ₂ x ∶ τ ∙ ‵▹ e ◃)
    EMLamParent1 : ∀ {x τ e}
                 → (‵λ₁ x ∶ ▹ τ ◃ ∙ e) + move parent +e> ‵▹ ‵λ x ∶ τ ∙ e ◃
    EMLamParent2 : ∀ {x τ e}
                 → (‵λ₂ x ∶ τ ∙ ‵▹ e ◃) + move parent +e> ‵▹ ‵λ x ∶ τ ∙ e ◃

    EMApChild1  : ∀ {e₁ e₂}
                → ‵▹ ‵ e₁ ∙ e₂ ◃ + move (child 1) +e> (‵ ‵▹ e₁ ◃ ∙₁ e₂)
    EMApChild2  : ∀ {e₁ e₂}
                → ‵▹ ‵ e₁ ∙ e₂ ◃ + move (child 2) +e> (‵ e₁ ∙₂ ‵▹ e₂ ◃)
    EMApParent1  : ∀ {e₁ e₂}
                → (‵ ‵▹ e₁ ◃ ∙₁ e₂) + move parent +e> ‵▹ ‵ e₁ ∙ e₂ ◃
    EMApParent2  : ∀ {e₁ e₂}
                → (‵ e₁ ∙₂ ‵▹ e₂ ◃) + move parent +e> ‵▹ ‵ e₁ ∙ e₂ ◃

    EMLetChild1  : ∀ {x e₁ e₂}
                → ‵▹ ‵ x ← e₁ ∙ e₂ ◃ + move (child 1) +e> (‵ x ←₁ ‵▹ e₁ ◃ ∙ e₂)
    EMLetChild2  : ∀ {x e₁ e₂}
                → ‵▹ ‵ x ← e₁ ∙ e₂ ◃ + move (child 2) +e> (‵ x ←₂ e₁ ∙ ‵▹ e₂ ◃)
    EMLetParent1  : ∀ {x e₁ e₂}
                → (‵ x ←₁ ‵▹ e₁ ◃ ∙ e₂) + move parent +e> ‵▹ ‵ x ← e₁ ∙ e₂ ◃
    EMLetParent2  : ∀ {x e₁ e₂}
                → (‵ x ←₂ e₁ ∙ ‵▹ e₂ ◃) + move parent +e> ‵▹ ‵ x ← e₁ ∙ e₂ ◃

    EMPlusChild1  : ∀ {e₁ e₂}
                → ‵▹ ‵ e₁ + e₂ ◃ + move (child 1) +e> (‵ ‵▹ e₁ ◃ +₁ e₂)
    EMPlusChild2  : ∀ {e₁ e₂}
                → ‵▹ ‵ e₁ + e₂ ◃ + move (child 2) +e> (‵ e₁ +₂ ‵▹ e₂ ◃)
    EMPlusParent1  : ∀ {e₁ e₂}
                → (‵ ‵▹ e₁ ◃ +₁ e₂) + move parent +e> ‵▹ ‵ e₁ + e₂ ◃
    EMPlusParent2  : ∀ {e₁ e₂}
                → (‵ e₁ +₂ ‵▹ e₂ ◃) + move parent +e> ‵▹ ‵ e₁ + e₂ ◃

    EMIfChild1  : ∀ {e₁ e₂ e₃}
                → ‵▹ ‵ e₁ ∙ e₂ ∙ e₃ ◃ + move (child 1) +e> (‵ ‵▹ e₁ ◃ ∙₁ e₂ ∙ e₃)
    EMIfChild2  : ∀ {e₁ e₂ e₃}
                → ‵▹ ‵ e₁ ∙ e₂ ∙ e₃ ◃ + move (child 2) +e> (‵ e₁ ∙₂ ‵▹ e₂ ◃ ∙ e₃)
    EMIfChild3  : ∀ {e₁ e₂ e₃}
                → ‵▹ ‵ e₁ ∙ e₂ ∙ e₃ ◃ + move (child 3) +e> (‵ e₁ ∙₃ e₂ ∙ ‵▹ e₃ ◃)
    EMIfParent1  : ∀ {e₁ e₂ e₃}
                → (‵ ‵▹ e₁ ◃ ∙₁ e₂ ∙ e₃) + move parent +e> ‵▹ ‵ e₁ ∙ e₂ ∙ e₃ ◃
    EMIfParent2  : ∀ {e₁ e₂ e₃}
                → (‵ e₁ ∙₂ ‵▹ e₂ ◃ ∙ e₃) + move parent +e> ‵▹ ‵ e₁ ∙ e₂ ∙ e₃ ◃
    EMIfParent3  : ∀ {e₁ e₂ e₃}
                → (‵ e₁ ∙₃ e₂ ∙ ‵▹ e₃ ◃) + move parent +e> ‵▹ ‵ e₁ ∙ e₂ ∙ e₃ ◃

    -- deletion
    EDel : ∀ {e u}
         → ‵▹ e ◃ + (del u) +e> ‵▹ ‵⦇-⦈^ u ◃

    -- construction
    EConVar   : ∀ {u x}
              → ‵▹ ‵⦇-⦈^ u ◃ + construct (var x) +e> ‵▹ ‵ x ◃
    EConLam   : ∀ {e x}
              → ‵▹ e ◃ + construct (lam x) +e> (‵λ₁ x ∶ ▹ unknown ◃ ∙ e)
    EConAp1   : ∀ {e u}
              → ‵▹ e ◃ + construct (ap₁ u) +e> (‵ e ∙₂ ‵▹ ‵⦇-⦈^ u ◃)
    EConAp2   : ∀ {e u}
              → ‵▹ e ◃ + construct (ap₂ u) +e> (‵ ‵▹ ‵⦇-⦈^ u ◃ ∙₁ e)
    EConLet1  : ∀ {e x u}
              → ‵▹ e ◃ + construct (let₁ x u) +e> (‵ x ←₂ e ∙ ‵▹ ‵⦇-⦈^ u ◃)
    EConLet2  : ∀ {e x u}
              → ‵▹ e ◃ + construct (let₂ x u) +e> (‵ x ←₁ ‵▹ ‵⦇-⦈^ u ◃ ∙ e)
    EConNum   : ∀ {u n}
              → ‵▹ ‵⦇-⦈^ u ◃ + construct (num n) +e> ‵▹ ‵ℕ n ◃
    EConPlus1 : ∀ {e u}
              → ‵▹ e ◃ + construct (plus₁ u) +e> (‵ e +₂ ‵▹ ‵⦇-⦈^ u ◃)
    EConPlus2 : ∀ {e u}
              → ‵▹ e ◃ + construct (plus₂ u) +e> (‵ ‵▹ ‵⦇-⦈^ u ◃ +₁ e)
    EConTrue  : ∀ {u}
              → ‵▹ ‵⦇-⦈^ u ◃ + construct tt +e> ‵▹ ‵tt ◃
    EConFalse : ∀ {u}
              → ‵▹ ‵⦇-⦈^ u ◃ + construct ff +e> ‵▹ ‵ff ◃
    EConIf1   : ∀ {e u₁ u₂}
              → ‵▹ e ◃ + construct (if₁ u₁ u₂) +e> (‵ e ∙₂ ‵▹ ‵⦇-⦈^ u₁ ◃ ∙ ‵⦇-⦈^ u₂)
    EConIf2   : ∀ {e u₁ u₂}
              → ‵▹ e ◃ + construct (if₂ u₁ u₂) +e> (‵ ‵▹ ‵⦇-⦈^ u₁ ◃ ∙₁ e ∙ ‵⦇-⦈^ u₂)
    EConIf3   : ∀ {e u₁ u₂}
              → ‵▹ e ◃ + construct (if₃ u₁ u₂) +e> (‵ ‵▹ ‵⦇-⦈^ u₁ ◃ ∙₁ ‵⦇-⦈^ u₂ ∙ e)

    -- zipper cases
    EZipLam1 : ∀ {x τ^ e α τ^′}
             → (τ^+>τ^′ : τ^ + α +τ> τ^′)
             → (‵λ₁ x ∶ τ^ ∙ e) + α +e> (‵λ₁ x ∶ τ^′ ∙ e)
    EZipLam2 : ∀ {x τ ê α ê′}
             → (ê+>ê′ : ê + α +e> ê′)
             → (‵λ₂ x ∶ τ ∙ ê) + α +e> (‵λ₂ x ∶ τ ∙ ê′)
    EZipAp1  : ∀ {ê e α ê′}
             → (ê+>ê′ : ê + α +e> ê′)
             → (‵ ê ∙₁ e) + α +e> (‵ ê′ ∙₁ e)
    EZipAp2  : ∀ {e ê α ê′}
             → (ê+>ê′ : ê + α +e> ê′)
             → (‵ e ∙₂ ê) + α +e> (‵ e ∙₂ ê′)
    EZipLet1 : ∀ {x ê e α ê′}
             → (ê+>ê′ : ê + α +e> ê′)
             → (‵ x ←₁ ê ∙ e) + α +e> (‵ x ←₁ ê′ ∙ e)
    EZipLet2 : ∀ {x e ê α ê′}
             → (ê+>ê′ : ê + α +e> ê′)
             → (‵ x ←₂ e ∙ ê) + α +e> (‵ x ←₂ e ∙ ê′)
    EZipPlus1 : ∀ {ê e α ê′}
             → (ê+>ê′ : ê + α +e> ê′)
             → (‵ ê +₁ e) + α +e> (‵ ê′ +₁ e)
    EZipPlus2 : ∀ {e ê α ê′}
             → (ê+>ê′ : ê + α +e> ê′)
             → (‵ e +₂ ê) + α +e> (‵ e +₂ ê′)
    EZipIf1  : ∀ {ê e₁ e₂ α ê′}
             → (ê+>ê′ : ê + α +e> ê′)
             → (‵ ê ∙₁ e₁ ∙ e₂) + α +e> (‵ ê′ ∙₁ e₁ ∙ e₂)
    EZipIf2  : ∀ {e₁ ê e₂ α ê′}
             → (ê+>ê′ : ê + α +e> ê′)
             → (‵ e₁ ∙₂ ê ∙ e₂) + α +e> (‵ e₁ ∙₂ ê′ ∙ e₂)
    EZipIf3  : ∀ {e₁ e₂ ê α ê′}
             → (ê+>ê′ : ê + α +e> ê′)
             → (‵ e₁ ∙₃ e₂ ∙ ê) + α +e> (‵ e₁ ∙₃ e₂ ∙ ê′)

  -- iterated actions
  data _+_+τ>*_ : (τ^ : ZTyp) → (ᾱ : ActionList) → (τ^′ : ZTyp) → Set where
    TIRefl : ∀ {τ^}
           → τ^ + [] +τ>* τ^
    TITyp  : ∀ {τ^ τ^′ τ^″ α ᾱ}
           → (τ^+>τ^′ : τ^ + α +τ> τ^′)
           → (τ^′+>*τ^″ : τ^′ + ᾱ +τ>* τ^″)
           → τ^ + α ∷ ᾱ +τ>* τ^″

  data _+_+e>*_ : (ê : ZExp) → (ᾱ : ActionList) → (ê′ : ZExp) → Set where
    EIRefl : ∀ {ê}
            → ê + [] +e>* ê
    EIExp   : ∀ {ê ê′ ê″ α ᾱ}
            → (ê+>ê′ : ê + α +e> ê′)
            → (ê′+>*ê″ : ê′ + ᾱ +e>* ê″)
            → ê + α ∷ ᾱ +e>* ê″

  +τ>*-++ : ∀ {τ^ τ^′ τ^″ ᾱ₁ ᾱ₂} → τ^ + ᾱ₁ +τ>* τ^′ → τ^′ + ᾱ₂ +τ>* τ^″ → τ^ + (ᾱ₁ ++ ᾱ₂) +τ>* τ^″
  +τ>*-++ TIRefl                    τ^+>*τ^″  = τ^+>*τ^″
  +τ>*-++ (TITyp τ^+>τ^′ τ^′+>*τ^″) τ^″+>*τ^‴ = TITyp τ^+>τ^′ (+τ>*-++ τ^′+>*τ^″ τ^″+>*τ^‴)

  +e>*-++ : ∀ {ê ê′ ê″ ᾱ₁ ᾱ₂} → ê + ᾱ₁ +e>* ê′ → ê′ + ᾱ₂ +e>* ê″ → ê + (ᾱ₁ ++ ᾱ₂) +e>* ê″
  +e>*-++ EIRefl                ê+>*ê″  = ê+>*ê″
  +e>*-++ (EIExp ê+>ê′ ê′+>*ê″) ê″+>*ê‴ = EIExp ê+>ê′ (+e>*-++ ê′+>*ê″ ê″+>*ê‴)

  -- type zippers
  ziplem-tarr1 : ∀ {τ^ τ^′ τ ᾱ} → τ^ + ᾱ +τ>* τ^′ → (τ^ -→₁ τ) + ᾱ +τ>* (τ^′ -→₁ τ)
  ziplem-tarr1 TIRefl                    = TIRefl
  ziplem-tarr1 (TITyp τ^+>τ^′ τ^′+>*τ^″) = TITyp (TZipArr1 τ^+>τ^′) (ziplem-tarr1 τ^′+>*τ^″)

  ziplem-tarr2 : ∀ {τ^ τ^′ τ ᾱ} → τ^ + ᾱ +τ>* τ^′ → (τ -→₂ τ^) + ᾱ +τ>* (τ -→₂ τ^′)
  ziplem-tarr2 TIRefl                    = TIRefl
  ziplem-tarr2 (TITyp τ^+>τ^′ τ^′+>*τ^″) = TITyp (TZipArr2 τ^+>τ^′) (ziplem-tarr2 τ^′+>*τ^″)

  -- expression zippers
  ziplem-lam1 : ∀ {x τ^ τ^′ e ᾱ} → τ^ + ᾱ +τ>* τ^′ → (‵λ₁ x ∶ τ^ ∙ e) + ᾱ +e>* (‵λ₁ x ∶ τ^′ ∙ e)
  ziplem-lam1 TIRefl                    = EIRefl
  ziplem-lam1 (TITyp τ^+>τ^′ τ^′+>*τ^″) = EIExp (EZipLam1 τ^+>τ^′) (ziplem-lam1 τ^′+>*τ^″)

  ziplem-lam2 : ∀ {x τ ê ê′ ᾱ} → ê + ᾱ +e>* ê′ → (‵λ₂ x ∶ τ ∙ ê) + ᾱ +e>* (‵λ₂ x ∶ τ ∙ ê′)
  ziplem-lam2 EIRefl                = EIRefl
  ziplem-lam2 (EIExp ê+>ê′ ê′+>*ê″) = EIExp (EZipLam2 ê+>ê′) (ziplem-lam2 ê′+>*ê″)

  ziplem-ap1 : ∀ {ê e ê′ ᾱ} → ê + ᾱ +e>* ê′ → (‵ ê ∙₁ e) + ᾱ +e>* (‵ ê′ ∙₁ e)
  ziplem-ap1 EIRefl                = EIRefl
  ziplem-ap1 (EIExp ê+>ê′ ê′+>*ê″) = EIExp (EZipAp1 ê+>ê′) (ziplem-ap1 ê′+>*ê″)

  ziplem-ap2 : ∀ {e ê ê′ ᾱ} → ê + ᾱ +e>* ê′ → (‵ e ∙₂ ê) + ᾱ +e>* (‵ e ∙₂ ê′)
  ziplem-ap2 EIRefl                = EIRefl
  ziplem-ap2 (EIExp ê+>ê′ ê′+>*ê″) = EIExp (EZipAp2 ê+>ê′) (ziplem-ap2 ê′+>*ê″)

  ziplem-let1 : ∀ {x ê e ê′ ᾱ} → ê + ᾱ +e>* ê′ → (‵ x ←₁ ê ∙ e) + ᾱ +e>* (‵ x ←₁ ê′ ∙ e)
  ziplem-let1 EIRefl                = EIRefl
  ziplem-let1 (EIExp ê+>ê′ ê′+>*ê″) = EIExp (EZipLet1 ê+>ê′) (ziplem-let1 ê′+>*ê″)

  ziplem-let2 : ∀ {x e ê ê′ ᾱ} → ê + ᾱ +e>* ê′ → (‵ x ←₂ e ∙ ê) + ᾱ +e>* (‵ x ←₂ e ∙ ê′)
  ziplem-let2 EIRefl                = EIRefl
  ziplem-let2 (EIExp ê+>ê′ ê′+>*ê″) = EIExp (EZipLet2 ê+>ê′) (ziplem-let2 ê′+>*ê″)

  ziplem-plus1 : ∀ {ê e ê′ ᾱ} → ê + ᾱ +e>* ê′ → (‵ ê +₁ e) + ᾱ +e>* (‵ ê′ +₁ e)
  ziplem-plus1 EIRefl                = EIRefl
  ziplem-plus1 (EIExp ê+>ê′ ê′+>*ê″) = EIExp (EZipPlus1 ê+>ê′) (ziplem-plus1 ê′+>*ê″)

  ziplem-plus2 : ∀ {e ê ê′ ᾱ} → ê + ᾱ +e>* ê′ → (‵ e +₂ ê) + ᾱ +e>* (‵ e +₂ ê′)
  ziplem-plus2 EIRefl                = EIRefl
  ziplem-plus2 (EIExp ê+>ê′ ê′+>*ê″) = EIExp (EZipPlus2 ê+>ê′) (ziplem-plus2 ê′+>*ê″)

  ziplem-if1 : ∀ {ê e₁ e₂ ê′ ᾱ} → ê + ᾱ +e>* ê′ → (‵ ê ∙₁ e₁ ∙ e₂) + ᾱ +e>* (‵ ê′ ∙₁ e₁ ∙ e₂)
  ziplem-if1 EIRefl                = EIRefl
  ziplem-if1 (EIExp ê+>ê′ ê′+>*ê″) = EIExp (EZipIf1 ê+>ê′) (ziplem-if1 ê′+>*ê″)

  ziplem-if2 : ∀ {e₁ ê e₂ ê′ ᾱ} → ê + ᾱ +e>* ê′ → (‵ e₁ ∙₂ ê ∙ e₂) + ᾱ +e>* (‵ e₁ ∙₂ ê′ ∙ e₂)
  ziplem-if2 EIRefl                = EIRefl
  ziplem-if2 (EIExp ê+>ê′ ê′+>*ê″) = EIExp (EZipIf2 ê+>ê′) (ziplem-if2 ê′+>*ê″)

  ziplem-if3 : ∀ {ê e₁ e₂ ê′ ᾱ} → ê + ᾱ +e>* ê′ → (‵ e₁ ∙₃ e₂ ∙ ê) + ᾱ +e>* (‵ e₁ ∙₃ e₂ ∙ ê′)
  ziplem-if3 EIRefl                = EIRefl
  ziplem-if3 (EIExp ê+>ê′ ê′+>*ê″) = EIExp (EZipIf3 ê+>ê′) (ziplem-if3 ê′+>*ê″)

  -- movement erasure invariance
  movement-erasure-invariance-τ : ∀ {τ^ τ^′ δ} → τ^ + move δ +τ> τ^′ → τ^ ◇τ ≡ τ^′ ◇τ
  movement-erasure-invariance-τ TMArrChild1       = refl
  movement-erasure-invariance-τ TMArrChild2       = refl
  movement-erasure-invariance-τ TMArrParent1      = refl
  movement-erasure-invariance-τ TMArrParent2      = refl
  movement-erasure-invariance-τ (TZipArr1 τ^+>τ^′)
    rewrite movement-erasure-invariance-τ τ^+>τ^′ = refl
  movement-erasure-invariance-τ (TZipArr2 τ^+>τ^′)
    rewrite movement-erasure-invariance-τ τ^+>τ^′ = refl

  movement-erasure-invariance-e : ∀ {ê ê′ δ} → ê + move δ +e> ê′ → ê ◇ ≡ ê′ ◇
  movement-erasure-invariance-e EMLamChild1       = refl
  movement-erasure-invariance-e EMLamChild2       = refl
  movement-erasure-invariance-e EMLamParent1      = refl
  movement-erasure-invariance-e EMLamParent2      = refl
  movement-erasure-invariance-e EMApChild1        = refl
  movement-erasure-invariance-e EMApChild2        = refl
  movement-erasure-invariance-e EMApParent1       = refl
  movement-erasure-invariance-e EMApParent2       = refl
  movement-erasure-invariance-e EMLetChild1       = refl
  movement-erasure-invariance-e EMLetChild2       = refl
  movement-erasure-invariance-e EMLetParent1      = refl
  movement-erasure-invariance-e EMLetParent2      = refl
  movement-erasure-invariance-e EMPlusChild1      = refl
  movement-erasure-invariance-e EMPlusChild2      = refl
  movement-erasure-invariance-e EMPlusParent1     = refl
  movement-erasure-invariance-e EMPlusParent2     = refl
  movement-erasure-invariance-e EMIfChild1        = refl
  movement-erasure-invariance-e EMIfChild2        = refl
  movement-erasure-invariance-e EMIfChild3        = refl
  movement-erasure-invariance-e EMIfParent1       = refl
  movement-erasure-invariance-e EMIfParent2       = refl
  movement-erasure-invariance-e EMIfParent3       = refl
  movement-erasure-invariance-e (EZipLam1 τ^+>τ^′)
    rewrite movement-erasure-invariance-τ τ^+>τ^′ = refl
  movement-erasure-invariance-e (EZipLam2 ê+>ê′)
    rewrite movement-erasure-invariance-e ê+>ê′   = refl
  movement-erasure-invariance-e (EZipAp1 ê+>ê′) 
    rewrite movement-erasure-invariance-e ê+>ê′   = refl
  movement-erasure-invariance-e (EZipAp2 ê+>ê′) 
    rewrite movement-erasure-invariance-e ê+>ê′   = refl
  movement-erasure-invariance-e (EZipLet1 ê+>ê′) 
    rewrite movement-erasure-invariance-e ê+>ê′   = refl
  movement-erasure-invariance-e (EZipLet2 ê+>ê′) 
    rewrite movement-erasure-invariance-e ê+>ê′   = refl
  movement-erasure-invariance-e (EZipPlus1 ê+>ê′) 
    rewrite movement-erasure-invariance-e ê+>ê′   = refl
  movement-erasure-invariance-e (EZipPlus2 ê+>ê′) 
    rewrite movement-erasure-invariance-e ê+>ê′   = refl
  movement-erasure-invariance-e (EZipIf1 ê+>ê′) 
    rewrite movement-erasure-invariance-e ê+>ê′   = refl
  movement-erasure-invariance-e (EZipIf2 ê+>ê′) 
    rewrite movement-erasure-invariance-e ê+>ê′   = refl
  movement-erasure-invariance-e (EZipIf3 ê+>ê′)
    rewrite movement-erasure-invariance-e ê+>ê′   = refl

  -- reach up for types
  reachup-τ : (τ^ : ZTyp) → ∃[ ᾱ ] ᾱ movements × τ^ + ᾱ +τ>* ▹ τ^ ◇τ ◃
  reachup-τ ▹ τ ◃ = ⟨ [] , ⟨ AMINil , TIRefl ⟩ ⟩
  reachup-τ (τ^ -→₁ τ)
    with ⟨ ᾱ , ⟨ ᾱmv , τ^+>* ⟩ ⟩ ← reachup-τ τ^
       = ⟨ ᾱ ++ ∣[ move parent ] ,
         ⟨ movements-++ ᾱmv (AMICons parent AMINil) ,
           +τ>*-++ (ziplem-tarr1 τ^+>*) (TITyp TMArrParent1 TIRefl) ⟩ ⟩
  reachup-τ (τ -→₂ τ^)
    with ⟨ ᾱ , ⟨ ᾱmv , τ^+>* ⟩ ⟩ ← reachup-τ τ^
       = ⟨ ᾱ ++ ∣[ move parent ] ,
         ⟨ movements-++ ᾱmv (AMICons parent AMINil) ,
           +τ>*-++ (ziplem-tarr2 τ^+>*) (TITyp TMArrParent2 TIRefl) ⟩ ⟩

  -- reach up for expressions
  reachup-e : (ê : ZExp) → ∃[ ᾱ ] ᾱ movements × ê + ᾱ +e>* ‵▹ ê ◇ ◃
  reachup-e ‵▹ e ◃ = ⟨ [] , ⟨ AMINil , EIRefl ⟩ ⟩
  reachup-e (‵λ₁ x ∶ τ^ ∙ e)
    with ⟨ ᾱ , ⟨ ᾱmv , τ^+>* ⟩ ⟩ ← reachup-τ τ^
       = ⟨ ᾱ ++ ∣[ move parent ] ,
         ⟨ movements-++ ᾱmv (AMICons parent AMINil) ,
           +e>*-++ (ziplem-lam1 τ^+>*) (EIExp EMLamParent1 EIRefl) ⟩ ⟩
  reachup-e (‵λ₂ x ∶ τ ∙ ê)
    with ⟨ ᾱ , ⟨ ᾱmv , ê+>* ⟩ ⟩ ← reachup-e ê
       = ⟨ ᾱ ++ ∣[ move parent ] ,
         ⟨ movements-++ ᾱmv (AMICons parent AMINil) ,
           +e>*-++ (ziplem-lam2 ê+>*) (EIExp EMLamParent2 EIRefl) ⟩ ⟩
  reachup-e (‵ ê ∙₁ e)
    with ⟨ ᾱ , ⟨ ᾱmv , ê+>* ⟩ ⟩ ← reachup-e ê
       = ⟨ ᾱ ++ ∣[ move parent ] ,
         ⟨ movements-++ ᾱmv (AMICons parent AMINil) ,
           +e>*-++ (ziplem-ap1 ê+>*) (EIExp EMApParent1 EIRefl) ⟩ ⟩
  reachup-e (‵ e ∙₂ ê)
    with ⟨ ᾱ , ⟨ ᾱmv , ê+>* ⟩ ⟩ ← reachup-e ê
       = ⟨ ᾱ ++ ∣[ move parent ] ,
         ⟨ movements-++ ᾱmv (AMICons parent AMINil) ,
           +e>*-++ (ziplem-ap2 ê+>*) (EIExp EMApParent2 EIRefl) ⟩ ⟩
  reachup-e (‵ x ←₁ ê ∙ e)
    with ⟨ ᾱ , ⟨ ᾱmv , ê+>* ⟩ ⟩ ← reachup-e ê
       = ⟨ ᾱ ++ ∣[ move parent ] ,
         ⟨ movements-++ ᾱmv (AMICons parent AMINil) ,
           +e>*-++ (ziplem-let1 ê+>*) (EIExp EMLetParent1 EIRefl) ⟩ ⟩
  reachup-e (‵ x ←₂ e ∙ ê)
    with ⟨ ᾱ , ⟨ ᾱmv , ê+>* ⟩ ⟩ ← reachup-e ê
       = ⟨ ᾱ ++ ∣[ move parent ] ,
         ⟨ movements-++ ᾱmv (AMICons parent AMINil) ,
           +e>*-++ (ziplem-let2 ê+>*) (EIExp EMLetParent2 EIRefl) ⟩ ⟩
  reachup-e (‵ ê +₁ e)
    with ⟨ ᾱ , ⟨ ᾱmv , ê+>* ⟩ ⟩ ← reachup-e ê
       = ⟨ ᾱ ++ ∣[ move parent ] ,
         ⟨ movements-++ ᾱmv (AMICons parent AMINil) ,
           +e>*-++ (ziplem-plus1 ê+>*) (EIExp EMPlusParent1 EIRefl) ⟩ ⟩
  reachup-e (‵ e +₂ ê)
    with ⟨ ᾱ , ⟨ ᾱmv , ê+>* ⟩ ⟩ ← reachup-e ê
       = ⟨ ᾱ ++ ∣[ move parent ] ,
         ⟨ movements-++ ᾱmv (AMICons parent AMINil) ,
           +e>*-++ (ziplem-plus2 ê+>*) (EIExp EMPlusParent2 EIRefl) ⟩ ⟩
  reachup-e (‵ ê ∙₁ e₂ ∙ e₃)
    with ⟨ ᾱ , ⟨ ᾱmv , ê+>* ⟩ ⟩ ← reachup-e ê
       = ⟨ ᾱ ++ ∣[ move parent ] ,
         ⟨ movements-++ ᾱmv (AMICons parent AMINil) ,
           +e>*-++ (ziplem-if1 ê+>*) (EIExp EMIfParent1 EIRefl) ⟩ ⟩
  reachup-e (‵ e₁ ∙₂ ê ∙ e₃)
    with ⟨ ᾱ , ⟨ ᾱmv , ê+>* ⟩ ⟩ ← reachup-e ê
       = ⟨ ᾱ ++ ∣[ move parent ] ,
         ⟨ movements-++ ᾱmv (AMICons parent AMINil) ,
           +e>*-++ (ziplem-if2 ê+>*) (EIExp EMIfParent2 EIRefl) ⟩ ⟩
  reachup-e (‵ e₁ ∙₃ e₂ ∙ ê)
    with ⟨ ᾱ , ⟨ ᾱmv , ê+>* ⟩ ⟩ ← reachup-e ê
       = ⟨ ᾱ ++ ∣[ move parent ] ,
         ⟨ movements-++ ᾱmv (AMICons parent AMINil) ,
           +e>*-++ (ziplem-if3 ê+>*) (EIExp EMIfParent3 EIRefl) ⟩ ⟩

  -- reach down for types
  reachdown-τ : (τ^ : ZTyp) → ∃[ ᾱ ] ᾱ movements ×  ▹ τ^ ◇τ ◃ + ᾱ +τ>* τ^
  reachdown-τ ▹ τ ◃ = ⟨ [] , ⟨ AMINil , TIRefl ⟩ ⟩
  reachdown-τ (τ^ -→₁ τ)
    with ⟨ ᾱ , ⟨ ᾱmv , +>*τ^ ⟩ ⟩ ← reachdown-τ τ^
       = ⟨ move (child 1) ∷ ᾱ ,
         ⟨ AMICons (child 1) ᾱmv ,
           TITyp TMArrChild1 (ziplem-tarr1 +>*τ^) ⟩ ⟩
  reachdown-τ (τ -→₂ τ^)
    with ⟨ ᾱ , ⟨ ᾱmv , +>*τ^ ⟩ ⟩ ← reachdown-τ τ^
       = ⟨ move (child 2) ∷ ᾱ ,
         ⟨ AMICons (child 2) ᾱmv ,
           TITyp TMArrChild2 (ziplem-tarr2 +>*τ^) ⟩ ⟩

  reachdown-e : (ê : ZExp) → ∃[ ᾱ ] ᾱ movements ×  ‵▹ ê ◇ ◃ + ᾱ +e>* ê
  reachdown-e ‵▹ e ◃ = ⟨ [] , ⟨ AMINil , EIRefl ⟩ ⟩
  reachdown-e (‵λ₁ x ∶ τ^ ∙ e)
    with ⟨ ᾱ , ⟨ ᾱmv , +>*τ^ ⟩ ⟩ ← reachdown-τ τ^
       = ⟨ move (child 1) ∷ ᾱ ,
         ⟨ AMICons (child 1) ᾱmv ,
           EIExp EMLamChild1 (ziplem-lam1 +>*τ^) ⟩ ⟩
  reachdown-e (‵λ₂ x ∶ τ ∙ ê)
    with ⟨ ᾱ , ⟨ ᾱmv , +>*ê ⟩ ⟩ ← reachdown-e ê
       = ⟨ move (child 2) ∷ ᾱ ,
         ⟨ AMICons (child 2) ᾱmv ,
           EIExp EMLamChild2 (ziplem-lam2 +>*ê) ⟩ ⟩
  reachdown-e (‵ ê ∙₁ e)
    with ⟨ ᾱ , ⟨ ᾱmv , +>*ê ⟩ ⟩ ← reachdown-e ê
       = ⟨ move (child 1) ∷ ᾱ ,
         ⟨ AMICons (child 1) ᾱmv ,
           EIExp EMApChild1 (ziplem-ap1 +>*ê) ⟩ ⟩
  reachdown-e (‵ e ∙₂ ê)
    with ⟨ ᾱ , ⟨ ᾱmv , +>*ê ⟩ ⟩ ← reachdown-e ê
       = ⟨ move (child 2) ∷ ᾱ ,
         ⟨ AMICons (child 2) ᾱmv ,
           EIExp EMApChild2 (ziplem-ap2 +>*ê) ⟩ ⟩
  reachdown-e (‵ x ←₁ ê ∙ e)
    with ⟨ ᾱ , ⟨ ᾱmv , +>*ê ⟩ ⟩ ← reachdown-e ê
       = ⟨ move (child 1) ∷ ᾱ ,
         ⟨ AMICons (child 1) ᾱmv ,
           EIExp EMLetChild1 (ziplem-let1 +>*ê) ⟩ ⟩
  reachdown-e (‵ x ←₂ e ∙ ê)
    with ⟨ ᾱ , ⟨ ᾱmv , +>*ê ⟩ ⟩ ← reachdown-e ê
       = ⟨ move (child 2) ∷ ᾱ ,
         ⟨ AMICons (child 2) ᾱmv ,
           EIExp EMLetChild2 (ziplem-let2 +>*ê) ⟩ ⟩
  reachdown-e (‵ ê +₁ e)
    with ⟨ ᾱ , ⟨ ᾱmv , +>*ê ⟩ ⟩ ← reachdown-e ê
       = ⟨ move (child 1) ∷ ᾱ ,
         ⟨ AMICons (child 1) ᾱmv ,
           EIExp EMPlusChild1 (ziplem-plus1 +>*ê) ⟩ ⟩
  reachdown-e (‵ e +₂ ê)
    with ⟨ ᾱ , ⟨ ᾱmv , +>*ê ⟩ ⟩ ← reachdown-e ê
       = ⟨ move (child 2) ∷ ᾱ ,
         ⟨ AMICons (child 2) ᾱmv ,
           EIExp EMPlusChild2 (ziplem-plus2 +>*ê) ⟩ ⟩
  reachdown-e (‵ ê ∙₁ e₂ ∙ e₃)
    with ⟨ ᾱ , ⟨ ᾱmv , +>*ê ⟩ ⟩ ← reachdown-e ê
       = ⟨ move (child 1) ∷ ᾱ ,
         ⟨ AMICons (child 1) ᾱmv ,
           EIExp EMIfChild1 (ziplem-if1 +>*ê) ⟩ ⟩
  reachdown-e (‵ e₁ ∙₂ ê ∙ e₃)
    with ⟨ ᾱ , ⟨ ᾱmv , +>*ê ⟩ ⟩ ← reachdown-e ê
       = ⟨ move (child 2) ∷ ᾱ ,
         ⟨ AMICons (child 2) ᾱmv ,
           EIExp EMIfChild2 (ziplem-if2 +>*ê) ⟩ ⟩
  reachdown-e (‵ e₁ ∙₃ e₂ ∙ ê)
    with ⟨ ᾱ , ⟨ ᾱmv , +>*ê ⟩ ⟩ ← reachdown-e ê
       = ⟨ move (child 3) ∷ ᾱ ,
         ⟨ AMICons (child 3) ᾱmv ,
           EIExp EMIfChild3 (ziplem-if3 +>*ê) ⟩ ⟩

  reachability-τ : (τ₁^ τ₂^ : ZTyp) → τ₁^ ◇τ ≡ τ₂^ ◇τ → ∃[ ᾱ ] ᾱ movements × τ₁^ + ᾱ +τ>* τ₂^
  reachability-τ τ₁^ τ₂^ eq
    with ⟨ ᾱ₁ , ⟨ ᾱ₁mv , τ₁^+>*  ⟩ ⟩ ← reachup-τ τ₁^
       | ⟨ ᾱ₂ , ⟨ ᾱ₂mv , +>*τ₂^  ⟩ ⟩ ← reachdown-τ τ₂^
       = ⟨ ᾱ₁ ++ ᾱ₂ , ⟨ movements-++ ᾱ₁mv ᾱ₂mv , +τ>*-++ τ₁^+>* (transport (λ { τ → ▹ τ ◃ + ᾱ₂ +τ>* τ₂^ }) (≡-sym eq) +>*τ₂^) ⟩ ⟩

  reachability-e : (ê₁ ê₂ : ZExp) → ê₁ ◇ ≡ ê₂ ◇ → ∃[ ᾱ ] ᾱ movements × ê₁ + ᾱ +e>* ê₂
  reachability-e ê₁ ê₂ eq
    with ⟨ ᾱ₁ , ⟨ ᾱ₁mv , ê₁+>*  ⟩ ⟩ ← reachup-e ê₁
       | ⟨ ᾱ₂ , ⟨ ᾱ₂mv , +>*ê₂  ⟩ ⟩ ← reachdown-e ê₂
       = ⟨ ᾱ₁ ++ ᾱ₂ , ⟨ movements-++ ᾱ₁mv ᾱ₂mv , +e>*-++ ê₁+>* (transport (λ { e → ‵▹ e ◃ + ᾱ₂ +e>* ê₂ }) (≡-sym eq) +>*ê₂) ⟩ ⟩

  -- constructability of types
  constructability-τ : (τ : Typ) → ∃[ ᾱ ] ▹ unknown ◃ + ᾱ +τ>* ▹ τ ◃
  constructability-τ num = ⟨ ∣[ construct tnum ] , TITyp TConNum TIRefl ⟩
  constructability-τ bool = ⟨ ∣[ construct tbool ] , TITyp TConBool TIRefl ⟩
  constructability-τ unknown = ⟨ [] , TIRefl ⟩
  constructability-τ (τ₁ -→ τ₂)
    with ⟨ ᾱ₁ , +>*τ₁ ⟩ ← constructability-τ τ₁
       | ⟨ ᾱ₂ , +>*τ₂ ⟩ ← constructability-τ τ₂
       = ⟨ ᾱ₁ ++ construct tarrow₁ ∷ ᾱ₂ ++ ∣[ move parent ] ,
           +τ>*-++ +>*τ₁ (TITyp TConArrow1 (+τ>*-++ (ziplem-tarr2 +>*τ₂) (TITyp TMArrParent2 TIRefl))) ⟩

  uz : Hole
  uz = 0

  -- constructability of expressions
  constructability-e : ∀ {u} → (e : UExp) → ∃[ ᾱ ] ‵▹ ‵⦇-⦈^ u ◃ + ᾱ +e>* ‵▹ e ◃
  constructability-e (‵⦇-⦈^ u) = ⟨ ∣[ del _ ] , EIExp EDel EIRefl ⟩
  constructability-e (‵ x) = ⟨ ∣[ construct (var x) ] , EIExp EConVar EIRefl ⟩
  constructability-e (‵λ x ∶ τ ∙ e)
    with ⟨ ᾱ₁ , +>*e ⟩ ← constructability-e e
       | ⟨ ᾱ₂ , +>*τ ⟩ ← constructability-τ τ
       = ⟨ ᾱ₁ ++ construct (lam x) ∷ ᾱ₂ ++ ∣[ move parent ] ,
           +e>*-++ +>*e
             (EIExp EConLam
               (+e>*-++ (ziplem-lam1 +>*τ)
                 (EIExp EMLamParent1 EIRefl))) ⟩
  constructability-e (‵ e₁ ∙ e₂)
    with ⟨ ᾱ₁ , +>*e₁ ⟩ ← constructability-e e₁
       | ⟨ ᾱ₂ , +>*e₂ ⟩ ← constructability-e e₂
       = ⟨ ᾱ₁ ++ construct (ap₁ uz) ∷ ᾱ₂ ++ ∣[ move parent ] ,
           +e>*-++ +>*e₁
             (EIExp EConAp1
               (+e>*-++ (ziplem-ap2 +>*e₂)
                 (EIExp EMApParent2 EIRefl))) ⟩
  constructability-e (‵ x ← e₁ ∙ e₂)
    with ⟨ ᾱ₁ , +>*e₁ ⟩ ← constructability-e e₁
       | ⟨ ᾱ₂ , +>*e₂ ⟩ ← constructability-e e₂
       = ⟨ ᾱ₁ ++ construct (let₁ x uz) ∷ ᾱ₂ ++ ∣[ move parent ] ,
           +e>*-++ +>*e₁
             (EIExp EConLet1
               (+e>*-++ (ziplem-let2 +>*e₂)
                 (EIExp EMLetParent2 EIRefl))) ⟩
  constructability-e (‵ℕ n) = ⟨ ∣[ construct (num n) ] , EIExp EConNum EIRefl ⟩
  constructability-e (‵ e₁ + e₂)
    with ⟨ ᾱ₁ , +>*e₁ ⟩ ← constructability-e e₁
       | ⟨ ᾱ₂ , +>*e₂ ⟩ ← constructability-e e₂
       = ⟨ ᾱ₁ ++ construct (plus₁ uz) ∷ ᾱ₂ ++ ∣[ move parent ] ,
           +e>*-++ +>*e₁
             (EIExp EConPlus1
               (+e>*-++ (ziplem-plus2 +>*e₂)
                 (EIExp EMPlusParent2 EIRefl))) ⟩
  constructability-e ‵tt = ⟨ ∣[ construct tt ] , EIExp EConTrue EIRefl ⟩
  constructability-e ‵ff = ⟨ ∣[ construct ff ] , EIExp EConFalse EIRefl ⟩
  constructability-e (‵ e₁ ∙ e₂ ∙ e₃)
    with ⟨ ᾱ₁ , +>*e₁ ⟩ ← constructability-e e₁
       | ⟨ ᾱ₂ , +>*e₂ ⟩ ← constructability-e e₂
       | ⟨ ᾱ₃ , +>*e₃ ⟩ ← constructability-e e₃
       = ⟨ ᾱ₁ ++ construct (if₁ uz uz) ∷ ᾱ₂ ++ move parent ∷ move (child 3) ∷ ᾱ₃ ++ ∣[ move parent ] ,
           +e>*-++ +>*e₁
             (EIExp EConIf1
               (+e>*-++ (ziplem-if2 +>*e₂)
                 (EIExp EMIfParent2
                   (EIExp EMIfChild3
                     (+e>*-++ (ziplem-if3 +>*e₃)
                       (EIExp EMIfParent3 EIRefl)))))) ⟩

  determinism-τ : ∀ {τ^ τ^′ τ^″ α} → τ^ + α +τ> τ^′ → τ^ + α +τ> τ^″ → τ^′ ≡ τ^″
  determinism-τ TMArrChild1        TMArrChild1  = refl
  determinism-τ TMArrChild2        TMArrChild2  = refl
  determinism-τ TMArrParent1       TMArrParent1 = refl
  determinism-τ TMArrParent2       TMArrParent2 = refl
  determinism-τ TMArrParent2       (TZipArr2 ())
  determinism-τ TDel               TDel         = refl
  determinism-τ TConArrow1         TConArrow1   = refl
  determinism-τ TConArrow2         TConArrow2   = refl
  determinism-τ TConNum            TConNum      = refl
  determinism-τ TConBool           TConBool     = refl
  determinism-τ (TZipArr1 τ^+>τ^′) (TZipArr1 τ^+>τ^″)
    rewrite determinism-τ τ^+>τ^′ τ^+>τ^″       = refl
  determinism-τ (TZipArr2 τ^+>τ^′) (TZipArr2 τ^+>τ^″)
    rewrite determinism-τ τ^+>τ^′ τ^+>τ^″       = refl

  determinism*-τ : ∀ {τ^ τ^′ τ^″ ᾱ} → τ^ + ᾱ +τ>* τ^′ → τ^ + ᾱ +τ>* τ^″ → τ^′ ≡ τ^″
  determinism*-τ TIRefl                     TIRefl = refl
  determinism*-τ (TITyp τ₁^+>τ₂^ τ₂^+>*τ₃^) (TITyp τ₁^+>τ₂^′ τ₂^+>*τ₃^′)
    rewrite determinism-τ τ₁^+>τ₂^ τ₁^+>τ₂^′
    rewrite determinism*-τ τ₂^+>*τ₃^ τ₂^+>*τ₃^′    = refl
