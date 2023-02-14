open import prelude
open import typ
open import uexp
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
    TDel : ∀ {τ : Typ}
         → ▹ τ ◃ + del +τ> ▹ unknown ◃

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
         → ‵▹ e ◃ + del +e> ‵▹ ‵⦇-⦈^ u ◃

    -- construction
    EConVar   : ∀ {u x}
              → ‵▹ ‵⦇-⦈^ u ◃ + construct (var x) +e> ‵▹ ‵ x ◃
    EConLam   : ∀ {e x}
              → ‵▹ e ◃ + construct (lam x) +e> (‵λ₁ x ∶ ▹ unknown ◃ ∙ e)
    EConAp1   : ∀ {e u}
              → ‵▹ e ◃ + construct ap₁ +e> (‵ e ∙₂ ‵▹ ‵⦇-⦈^ u ◃)
    EConAp2   : ∀ {e u}
              → ‵▹ e ◃ + construct ap₂ +e> (‵ ‵▹ ‵⦇-⦈^ u ◃ ∙₁ e)
    EConLet1  : ∀ {e x u}
              → ‵▹ e ◃ + construct (let₁ x) +e> (‵ x ←₂ e ∙ ‵▹ ‵⦇-⦈^ u ◃)
    EConLet2  : ∀ {e x u}
              → ‵▹ e ◃ + construct (let₂ x) +e> (‵ x ←₁ ‵▹ ‵⦇-⦈^ u ◃ ∙ e)
    EConNum   : ∀ {u n}
              → ‵▹ ‵⦇-⦈^ u ◃ + construct (num n) +e> ‵▹ ‵ℕ n ◃
    EConPlus1 : ∀ {e u}
              → ‵▹ e ◃ + construct ap₁ +e> (‵ e +₂ ‵▹ ‵⦇-⦈^ u ◃)
    EConPlus2 : ∀ {e u}
              → ‵▹ e ◃ + construct ap₂ +e> (‵ ‵▹ ‵⦇-⦈^ u ◃ +₁ e)
    EConTrue  : ∀ {u}
              → ‵▹ ‵⦇-⦈^ u ◃ + construct tt +e> ‵▹ ‵tt ◃
    EConFalse : ∀ {u}
              → ‵▹ ‵⦇-⦈^ u ◃ + construct ff +e> ‵▹ ‵ff ◃
    EConIf1   : ∀ {e u₁ u₂}
              → ‵▹ e ◃ + construct if₁ +e> (‵ e ∙₂ ‵▹ ‵⦇-⦈^ u₁ ◃ ∙ ‵⦇-⦈^ u₂)
    EConIf2   : ∀ {e u₁ u₂}
              → ‵▹ e ◃ + construct if₂ +e> (‵ ‵▹ ‵⦇-⦈^ u₁ ◃ ∙₁ e ∙ ‵⦇-⦈^ u₂)
    EConIf3   : ∀ {e u₁ u₂}
              → ‵▹ e ◃ + construct if₃ +e> (‵ ‵▹ ‵⦇-⦈^ u₁ ◃ ∙₁ ‵⦇-⦈^ u₂ ∙ e)

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
    EIRefil : ∀ {ê}
            → ê + [] +e>* ê
    EIExp   : ∀ {ê ê′ ê″ α ᾱ}
            → (ê+>ê′ : ê + α +e> ê′)
            → (ê′+>*ê″ : ê′ + ᾱ +e>* ê″)
            → ê + α ∷ ᾱ +e>* ê″

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
