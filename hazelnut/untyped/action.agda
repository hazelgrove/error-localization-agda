open import prelude
open import core

open import hazelnut.action
open import hazelnut.untyped.zexp

module hazelnut.untyped.action where
  -- type actions
  data _+_+τ>_ : (τ : ZTyp) → (α : Action) → (τ′ : ZTyp) → Set where
    -- movement
    ATMArrChild1   : ∀ {τ₁ τ₂ : Typ}
                   → ▹ τ₁ -→ τ₂ ◃ + move (child 1) +τ> ▹ τ₁ ◃ -→₁ τ₂
    ATMArrChild2   : ∀ {τ₁ τ₂ : Typ}
                   → ▹ τ₁ -→ τ₂ ◃ + move (child 2) +τ> τ₁ -→₂ ▹ τ₂ ◃
    ATMArrParent1  : ∀ {τ₁ τ₂ : Typ}
                   → ▹ τ₁ ◃ -→₁ τ₂ + move parent +τ> ▹ τ₁ -→ τ₂ ◃
    ATMArrParent2  : ∀ {τ₁ τ₂ : Typ}
                   → τ₁ -→₂ ▹ τ₂ ◃ + move parent +τ> ▹ τ₁ -→ τ₂ ◃
    ATMProdChild1  : ∀ {τ₁ τ₂ : Typ}
                   → ▹ τ₁ -× τ₂ ◃ + move (child 1) +τ> ▹ τ₁ ◃ -×₁ τ₂
    ATMProdChild2  : ∀ {τ₁ τ₂ : Typ}
                   → ▹ τ₁ -× τ₂ ◃ + move (child 2) +τ> τ₁ -×₂ ▹ τ₂ ◃
    ATMProdParent1 : ∀ {τ₁ τ₂ : Typ}
                   → ▹ τ₁ ◃ -×₁ τ₂ + move parent +τ> ▹ τ₁ -× τ₂ ◃
    ATMProdParent2 : ∀ {τ₁ τ₂ : Typ}
                   → τ₁ -×₂ ▹ τ₂ ◃ + move parent +τ> ▹ τ₁ -× τ₂ ◃

    -- deletion
    ATDel : ∀ {τ : Typ} {u : Hole}
          → ▹ τ ◃ + (del u) +τ> ▹ unknown ◃

    -- construction
    ATConArrow1 : ∀ {τ : Typ}
                → ▹ τ ◃ + construct tarrow₁ +τ> τ -→₂ ▹ unknown ◃
    ATConArrow2 : ∀ {τ : Typ}
                → ▹ τ ◃ + construct tarrow₂ +τ> ▹ unknown ◃ -→₁ τ
    ATConProd1  : ∀ {τ : Typ}
                → ▹ τ ◃ + construct tprod₁ +τ> τ -×₂ ▹ unknown ◃
    ATConProd2  : ∀ {τ : Typ}
                → ▹ τ ◃ + construct tprod₂ +τ> ▹ unknown ◃ -×₁ τ
    ATConNum    : ▹ unknown ◃ + construct tnum +τ> ▹ num ◃
    ATConBool   : ▹ unknown ◃ + construct tbool +τ> ▹ bool ◃

    -- zipper
    ATZipArr1  : ∀ {τ^ τ^′ : ZTyp} {τ : Typ} {α : Action}
               → (τ^+>τ^′ : τ^ + α +τ> τ^′)
               → τ^ -→₁ τ + α +τ> τ^′ -→₁ τ
    ATZipArr2  : ∀ {τ^ τ^′ : ZTyp} {τ : Typ} {α : Action}
               → (τ^+>τ^′ : τ^ + α +τ> τ^′)
               → τ -→₂ τ^ + α +τ> τ -→₂ τ^′
    ATZipProd1 : ∀ {τ^ τ^′ : ZTyp} {τ : Typ} {α : Action}
               → (τ^+>τ^′ : τ^ + α +τ> τ^′)
               → τ^ -×₁ τ + α +τ> τ^′ -×₁ τ
    ATZipProd2 : ∀ {τ^ τ^′ : ZTyp} {τ : Typ} {α : Action}
               → (τ^+>τ^′ : τ^ + α +τ> τ^′)
               → τ -×₂ τ^ + α +τ> τ -×₂ τ^′

  -- expression actions
  data _+_+e>_ : (ê : ZExp) → (α : Action) → (ê′ : ZExp) → Set where
    -- movement
    AEMLamChild1   : ∀ {x τ e}
                   → ‵▹ ‵λ x ∶ τ ∙ e ◃ + move (child 1) +e> (‵λ₁ x ∶ ▹ τ ◃ ∙ e)
    AEMLamChild2   : ∀ {x τ e}
                   → ‵▹ ‵λ x ∶ τ ∙ e ◃ + move (child 2) +e> (‵λ₂ x ∶ τ ∙ ‵▹ e ◃)
    AEMLamParent1  : ∀ {x τ e}
                   → (‵λ₁ x ∶ ▹ τ ◃ ∙ e) + move parent +e> ‵▹ ‵λ x ∶ τ ∙ e ◃
    AEMLamParent2  : ∀ {x τ e}
                   → (‵λ₂ x ∶ τ ∙ ‵▹ e ◃) + move parent +e> ‵▹ ‵λ x ∶ τ ∙ e ◃

    AEMApChild1    : ∀ {e₁ e₂}
                   → ‵▹ ‵ e₁ ∙ e₂ ◃ + move (child 1) +e> (‵ ‵▹ e₁ ◃ ∙₁ e₂)
    AEMApChild2    : ∀ {e₁ e₂}
                   → ‵▹ ‵ e₁ ∙ e₂ ◃ + move (child 2) +e> (‵ e₁ ∙₂ ‵▹ e₂ ◃)
    AEMApParent1   : ∀ {e₁ e₂}
                   → (‵ ‵▹ e₁ ◃ ∙₁ e₂) + move parent +e> ‵▹ ‵ e₁ ∙ e₂ ◃
    AEMApParent2   : ∀ {e₁ e₂}
                   → (‵ e₁ ∙₂ ‵▹ e₂ ◃) + move parent +e> ‵▹ ‵ e₁ ∙ e₂ ◃

    AEMLetChild1   : ∀ {x e₁ e₂}
                   → ‵▹ ‵ x ← e₁ ∙ e₂ ◃ + move (child 1) +e> (‵ x ←₁ ‵▹ e₁ ◃ ∙ e₂)
    AEMLetChild2   : ∀ {x e₁ e₂}
                   → ‵▹ ‵ x ← e₁ ∙ e₂ ◃ + move (child 2) +e> (‵ x ←₂ e₁ ∙ ‵▹ e₂ ◃)
    AEMLetParent1  : ∀ {x e₁ e₂}
                   → (‵ x ←₁ ‵▹ e₁ ◃ ∙ e₂) + move parent +e> ‵▹ ‵ x ← e₁ ∙ e₂ ◃
    AEMLetParent2  : ∀ {x e₁ e₂}
                   → (‵ x ←₂ e₁ ∙ ‵▹ e₂ ◃) + move parent +e> ‵▹ ‵ x ← e₁ ∙ e₂ ◃

    AEMPlusChild1  : ∀ {e₁ e₂}
                   → ‵▹ ‵ e₁ + e₂ ◃ + move (child 1) +e> (‵ ‵▹ e₁ ◃ +₁ e₂)
    AEMPlusChild2  : ∀ {e₁ e₂}
                   → ‵▹ ‵ e₁ + e₂ ◃ + move (child 2) +e> (‵ e₁ +₂ ‵▹ e₂ ◃)
    AEMPlusParent1 : ∀ {e₁ e₂}
                   → (‵ ‵▹ e₁ ◃ +₁ e₂) + move parent +e> ‵▹ ‵ e₁ + e₂ ◃
    AEMPlusParent2 : ∀ {e₁ e₂}
                   → (‵ e₁ +₂ ‵▹ e₂ ◃) + move parent +e> ‵▹ ‵ e₁ + e₂ ◃

    AEMIfChild1    : ∀ {e₁ e₂ e₃}
                   → ‵▹ ‵ e₁ ∙ e₂ ∙ e₃ ◃ + move (child 1) +e> (‵ ‵▹ e₁ ◃ ∙₁ e₂ ∙ e₃)
    AEMIfChild2    : ∀ {e₁ e₂ e₃}
                   → ‵▹ ‵ e₁ ∙ e₂ ∙ e₃ ◃ + move (child 2) +e> (‵ e₁ ∙₂ ‵▹ e₂ ◃ ∙ e₃)
    AEMIfChild3    : ∀ {e₁ e₂ e₃}
                   → ‵▹ ‵ e₁ ∙ e₂ ∙ e₃ ◃ + move (child 3) +e> (‵ e₁ ∙₃ e₂ ∙ ‵▹ e₃ ◃)
    AEMIfParent1   : ∀ {e₁ e₂ e₃}
                   → (‵ ‵▹ e₁ ◃ ∙₁ e₂ ∙ e₃) + move parent +e> ‵▹ ‵ e₁ ∙ e₂ ∙ e₃ ◃
    AEMIfParent2   : ∀ {e₁ e₂ e₃}
                   → (‵ e₁ ∙₂ ‵▹ e₂ ◃ ∙ e₃) + move parent +e> ‵▹ ‵ e₁ ∙ e₂ ∙ e₃ ◃
    AEMIfParent3   : ∀ {e₁ e₂ e₃}
                   → (‵ e₁ ∙₃ e₂ ∙ ‵▹ e₃ ◃) + move parent +e> ‵▹ ‵ e₁ ∙ e₂ ∙ e₃ ◃

    AEMPairChild1  : ∀ {e₁ e₂}
                   → ‵▹ ‵⟨ e₁ , e₂ ⟩ ◃ + move (child 1) +e> ‵⟨ ‵▹ e₁ ◃ ,₁ e₂ ⟩
    AEMPairChild2  : ∀ {e₁ e₂}
                   → ‵▹ ‵⟨ e₁ , e₂ ⟩ ◃ + move (child 2) +e> ‵⟨ e₁ ,₂ ‵▹ e₂ ◃ ⟩
    AEMPairParent1 : ∀ {e₁ e₂}
                   → ‵⟨ ‵▹ e₁ ◃ ,₁ e₂ ⟩ + move parent +e> ‵▹ ‵⟨ e₁ , e₂ ⟩ ◃
    AEMPairParent2 : ∀ {e₁ e₂}
                   → ‵⟨ e₁ ,₂ ‵▹ e₂ ◃ ⟩ + move parent +e> ‵▹ ‵⟨ e₁ , e₂ ⟩ ◃

    AEMProjLChild  : ∀ {e}
                   → ‵▹ ‵π₁ e ◃ + move (child 1) +e> (‵π₁ ‵▹ e ◃)
    AEMProjLParent : ∀ {e}
                   → (‵π₁ ‵▹ e ◃) + move parent +e> ‵▹ ‵π₁ e ◃
    AEMProjRChild  : ∀ {e}
                   → ‵▹ ‵π₂ e ◃ + move (child 1) +e> (‵π₂ ‵▹ e ◃)
    AEMProjRParent : ∀ {e}
                   → (‵π₂ ‵▹ e ◃) + move parent +e> ‵▹ ‵π₂ e ◃

    -- deletion
    AEDel : ∀ {e u}
          → ‵▹ e ◃ + (del u) +e> ‵▹ ‵⦇-⦈^ u ◃

    -- construction
    AEConVar   : ∀ {u x}
               → ‵▹ ‵⦇-⦈^ u ◃ + construct (var x) +e> ‵▹ ‵ x ◃
    AEConLam   : ∀ {e x}
               → ‵▹ e ◃ + construct (lam x) +e> (‵λ₁ x ∶ ▹ unknown ◃ ∙ e)
    AEConAp1   : ∀ {e u}
               → ‵▹ e ◃ + construct (ap₁ u) +e> (‵ e ∙₂ ‵▹ ‵⦇-⦈^ u ◃)
    AEConAp2   : ∀ {e u}
               → ‵▹ e ◃ + construct (ap₂ u) +e> (‵ ‵▹ ‵⦇-⦈^ u ◃ ∙₁ e)
    AEConLet1  : ∀ {e x u}
               → ‵▹ e ◃ + construct (let₁ x u) +e> (‵ x ←₂ e ∙ ‵▹ ‵⦇-⦈^ u ◃)
    AEConLet2  : ∀ {e x u}
               → ‵▹ e ◃ + construct (let₂ x u) +e> (‵ x ←₁ ‵▹ ‵⦇-⦈^ u ◃ ∙ e)
    AEConNum   : ∀ {u n}
               → ‵▹ ‵⦇-⦈^ u ◃ + construct (num n) +e> ‵▹ ‵ℕ n ◃
    AEConPlus1 : ∀ {e u}
               → ‵▹ e ◃ + construct (plus₁ u) +e> (‵ e +₂ ‵▹ ‵⦇-⦈^ u ◃)
    AEConPlus2 : ∀ {e u}
               → ‵▹ e ◃ + construct (plus₂ u) +e> (‵ ‵▹ ‵⦇-⦈^ u ◃ +₁ e)
    AEConTrue  : ∀ {u}
               → ‵▹ ‵⦇-⦈^ u ◃ + construct tt +e> ‵▹ ‵tt ◃
    AEConFalse : ∀ {u}
               → ‵▹ ‵⦇-⦈^ u ◃ + construct ff +e> ‵▹ ‵ff ◃
    AEConIf1   : ∀ {e u₁ u₂}
               → ‵▹ e ◃ + construct (if₁ u₁ u₂) +e> (‵ e ∙₂ ‵▹ ‵⦇-⦈^ u₁ ◃ ∙ ‵⦇-⦈^ u₂)
    AEConIf2   : ∀ {e u₁ u₂}
               → ‵▹ e ◃ + construct (if₂ u₁ u₂) +e> (‵ ‵▹ ‵⦇-⦈^ u₁ ◃ ∙₁ e ∙ ‵⦇-⦈^ u₂)
    AEConIf3   : ∀ {e u₁ u₂}
               → ‵▹ e ◃ + construct (if₃ u₁ u₂) +e> (‵ ‵▹ ‵⦇-⦈^ u₁ ◃ ∙₁ ‵⦇-⦈^ u₂ ∙ e)
    AEConPair1 : ∀ {e u}
               → ‵▹ e ◃ + construct (pair₁ u) +e> ‵⟨ e ,₂ ‵▹ ‵⦇-⦈^ u ◃ ⟩
    AEConPair2 : ∀ {e u}
               → ‵▹ e ◃ + construct (pair₂ u) +e> ‵⟨ ‵▹ ‵⦇-⦈^ u ◃ ,₁ e ⟩
    AEConProjL : ∀ {e}
               → ‵▹ e ◃ + construct projl +e> ‵▹ ‵π₁ e ◃
    AEConProjR : ∀ {e}
               → ‵▹ e ◃ + construct projr +e> ‵▹ ‵π₂ e ◃

    -- zipper cases
    AEZipLam1  : ∀ {x τ^ e α τ^′}
               → (τ^+>τ^′ : τ^ + α +τ> τ^′)
               → (‵λ₁ x ∶ τ^ ∙ e) + α +e> (‵λ₁ x ∶ τ^′ ∙ e)
    AEZipLam2  : ∀ {x τ ê α ê′}
               → (ê+>ê′ : ê + α +e> ê′)
               → (‵λ₂ x ∶ τ ∙ ê) + α +e> (‵λ₂ x ∶ τ ∙ ê′)
    AEZipAp1   : ∀ {ê e α ê′}
               → (ê+>ê′ : ê + α +e> ê′)
               → (‵ ê ∙₁ e) + α +e> (‵ ê′ ∙₁ e)
    AEZipAp2   : ∀ {e ê α ê′}
               → (ê+>ê′ : ê + α +e> ê′)
               → (‵ e ∙₂ ê) + α +e> (‵ e ∙₂ ê′)
    AEZipLet1  : ∀ {x ê e α ê′}
               → (ê+>ê′ : ê + α +e> ê′)
               → (‵ x ←₁ ê ∙ e) + α +e> (‵ x ←₁ ê′ ∙ e)
    AEZipLet2  : ∀ {x e ê α ê′}
               → (ê+>ê′ : ê + α +e> ê′)
               → (‵ x ←₂ e ∙ ê) + α +e> (‵ x ←₂ e ∙ ê′)
    AEZipPlus1 : ∀ {ê e α ê′}
               → (ê+>ê′ : ê + α +e> ê′)
               → (‵ ê +₁ e) + α +e> (‵ ê′ +₁ e)
    AEZipPlus2 : ∀ {e ê α ê′}
               → (ê+>ê′ : ê + α +e> ê′)
               → (‵ e +₂ ê) + α +e> (‵ e +₂ ê′)
    AEZipIf1   : ∀ {ê e₁ e₂ α ê′}
               → (ê+>ê′ : ê + α +e> ê′)
               → (‵ ê ∙₁ e₁ ∙ e₂) + α +e> (‵ ê′ ∙₁ e₁ ∙ e₂)
    AEZipIf2   : ∀ {e₁ ê e₂ α ê′}
               → (ê+>ê′ : ê + α +e> ê′)
               → (‵ e₁ ∙₂ ê ∙ e₂) + α +e> (‵ e₁ ∙₂ ê′ ∙ e₂)
    AEZipIf3   : ∀ {e₁ e₂ ê α ê′}
               → (ê+>ê′ : ê + α +e> ê′)
               → (‵ e₁ ∙₃ e₂ ∙ ê) + α +e> (‵ e₁ ∙₃ e₂ ∙ ê′)
    AEZipPair1 : ∀ {ê e α ê′}
               → (ê+>ê′ : ê + α +e> ê′)
               → (‵⟨ ê ,₁ e ⟩) + α +e> (‵⟨ ê′ ,₁ e ⟩)
    AEZipPair2 : ∀ {e ê α ê′}
               → (ê+>ê′ : ê + α +e> ê′)
               → (‵⟨ e ,₂ ê ⟩) + α +e> (‵⟨ e ,₂ ê′ ⟩)
    AEZipProjL : ∀ {ê α ê′}
               → (ê+>ê′ : ê + α +e> ê′)
               → (‵π₁ ê) + α +e> (‵π₁ ê′)
    AEZipProjR : ∀ {ê α ê′}
               → (ê+>ê′ : ê + α +e> ê′)
               → (‵π₂ ê) + α +e> (‵π₂ ê′)

  -- iterated actions
  data _+_+τ>*_ : (τ^ : ZTyp) → (ᾱ : ActionList) → (τ^′ : ZTyp) → Set where
    ATIRefl : ∀ {τ^}
            → τ^ + [] +τ>* τ^
    ATITyp  : ∀ {τ^ τ^′ τ^″ α ᾱ}
            → (τ^+>τ^′ : τ^ + α +τ> τ^′)
            → (τ^′+>*τ^″ : τ^′ + ᾱ +τ>* τ^″)
            → τ^ + α ∷ ᾱ +τ>* τ^″

  data _+_+e>*_ : (ê : ZExp) → (ᾱ : ActionList) → (ê′ : ZExp) → Set where
    AEIRefl : ∀ {ê}
            → ê + [] +e>* ê
    AEIExp  : ∀ {ê ê′ ê″ α ᾱ}
            → (ê+>ê′ : ê + α +e> ê′)
            → (ê′+>*ê″ : ê′ + ᾱ +e>* ê″)
            → ê + α ∷ ᾱ +e>* ê″

  +τ>*-++ : ∀ {τ^ τ^′ τ^″ ᾱ₁ ᾱ₂} → τ^ + ᾱ₁ +τ>* τ^′ → τ^′ + ᾱ₂ +τ>* τ^″ → τ^ + (ᾱ₁ ++ ᾱ₂) +τ>* τ^″
  +τ>*-++ ATIRefl                    τ^+>*τ^″  = τ^+>*τ^″
  +τ>*-++ (ATITyp τ^+>τ^′ τ^′+>*τ^″) τ^″+>*τ^‴ = ATITyp τ^+>τ^′ (+τ>*-++ τ^′+>*τ^″ τ^″+>*τ^‴)

  +e>*-++ : ∀ {ê ê′ ê″ ᾱ₁ ᾱ₂} → ê + ᾱ₁ +e>* ê′ → ê′ + ᾱ₂ +e>* ê″ → ê + (ᾱ₁ ++ ᾱ₂) +e>* ê″
  +e>*-++ AEIRefl                ê+>*ê″  = ê+>*ê″
  +e>*-++ (AEIExp ê+>ê′ ê′+>*ê″) ê″+>*ê‴ = AEIExp ê+>ê′ (+e>*-++ ê′+>*ê″ ê″+>*ê‴)

  -- type zippers
  ziplem-tarr1 : ∀ {τ^ τ^′ τ ᾱ} → τ^ + ᾱ +τ>* τ^′ → (τ^ -→₁ τ) + ᾱ +τ>* (τ^′ -→₁ τ)
  ziplem-tarr1 ATIRefl                    = ATIRefl
  ziplem-tarr1 (ATITyp τ^+>τ^′ τ^′+>*τ^″) = ATITyp (ATZipArr1 τ^+>τ^′) (ziplem-tarr1 τ^′+>*τ^″)

  ziplem-tarr2 : ∀ {τ^ τ^′ τ ᾱ} → τ^ + ᾱ +τ>* τ^′ → (τ -→₂ τ^) + ᾱ +τ>* (τ -→₂ τ^′)
  ziplem-tarr2 ATIRefl                    = ATIRefl
  ziplem-tarr2 (ATITyp τ^+>τ^′ τ^′+>*τ^″) = ATITyp (ATZipArr2 τ^+>τ^′) (ziplem-tarr2 τ^′+>*τ^″)

  ziplem-tprod1 : ∀ {τ^ τ^′ τ ᾱ} → τ^ + ᾱ +τ>* τ^′ → (τ^ -×₁ τ) + ᾱ +τ>* (τ^′ -×₁ τ)
  ziplem-tprod1 ATIRefl                    = ATIRefl
  ziplem-tprod1 (ATITyp τ^+>τ^′ τ^′+>*τ^″) = ATITyp (ATZipProd1 τ^+>τ^′) (ziplem-tprod1 τ^′+>*τ^″)

  ziplem-tprod2 : ∀ {τ^ τ^′ τ ᾱ} → τ^ + ᾱ +τ>* τ^′ → (τ -×₂ τ^) + ᾱ +τ>* (τ -×₂ τ^′)
  ziplem-tprod2 ATIRefl                    = ATIRefl
  ziplem-tprod2 (ATITyp τ^+>τ^′ τ^′+>*τ^″) = ATITyp (ATZipProd2 τ^+>τ^′) (ziplem-tprod2 τ^′+>*τ^″)

  -- expression zippers
  ziplem-lam1 : ∀ {x τ^ τ^′ e ᾱ} → τ^ + ᾱ +τ>* τ^′ → (‵λ₁ x ∶ τ^ ∙ e) + ᾱ +e>* (‵λ₁ x ∶ τ^′ ∙ e)
  ziplem-lam1 ATIRefl                    = AEIRefl
  ziplem-lam1 (ATITyp τ^+>τ^′ τ^′+>*τ^″) = AEIExp (AEZipLam1 τ^+>τ^′) (ziplem-lam1 τ^′+>*τ^″)

  ziplem-lam2 : ∀ {x τ ê ê′ ᾱ} → ê + ᾱ +e>* ê′ → (‵λ₂ x ∶ τ ∙ ê) + ᾱ +e>* (‵λ₂ x ∶ τ ∙ ê′)
  ziplem-lam2 AEIRefl                = AEIRefl
  ziplem-lam2 (AEIExp ê+>ê′ ê′+>*ê″) = AEIExp (AEZipLam2 ê+>ê′) (ziplem-lam2 ê′+>*ê″)

  ziplem-ap1 : ∀ {ê e ê′ ᾱ} → ê + ᾱ +e>* ê′ → (‵ ê ∙₁ e) + ᾱ +e>* (‵ ê′ ∙₁ e)
  ziplem-ap1 AEIRefl                = AEIRefl
  ziplem-ap1 (AEIExp ê+>ê′ ê′+>*ê″) = AEIExp (AEZipAp1 ê+>ê′) (ziplem-ap1 ê′+>*ê″)

  ziplem-ap2 : ∀ {e ê ê′ ᾱ} → ê + ᾱ +e>* ê′ → (‵ e ∙₂ ê) + ᾱ +e>* (‵ e ∙₂ ê′)
  ziplem-ap2 AEIRefl                = AEIRefl
  ziplem-ap2 (AEIExp ê+>ê′ ê′+>*ê″) = AEIExp (AEZipAp2 ê+>ê′) (ziplem-ap2 ê′+>*ê″)

  ziplem-let1 : ∀ {x ê e ê′ ᾱ} → ê + ᾱ +e>* ê′ → (‵ x ←₁ ê ∙ e) + ᾱ +e>* (‵ x ←₁ ê′ ∙ e)
  ziplem-let1 AEIRefl                = AEIRefl
  ziplem-let1 (AEIExp ê+>ê′ ê′+>*ê″) = AEIExp (AEZipLet1 ê+>ê′) (ziplem-let1 ê′+>*ê″)

  ziplem-let2 : ∀ {x e ê ê′ ᾱ} → ê + ᾱ +e>* ê′ → (‵ x ←₂ e ∙ ê) + ᾱ +e>* (‵ x ←₂ e ∙ ê′)
  ziplem-let2 AEIRefl                = AEIRefl
  ziplem-let2 (AEIExp ê+>ê′ ê′+>*ê″) = AEIExp (AEZipLet2 ê+>ê′) (ziplem-let2 ê′+>*ê″)

  ziplem-plus1 : ∀ {ê e ê′ ᾱ} → ê + ᾱ +e>* ê′ → (‵ ê +₁ e) + ᾱ +e>* (‵ ê′ +₁ e)
  ziplem-plus1 AEIRefl                = AEIRefl
  ziplem-plus1 (AEIExp ê+>ê′ ê′+>*ê″) = AEIExp (AEZipPlus1 ê+>ê′) (ziplem-plus1 ê′+>*ê″)

  ziplem-plus2 : ∀ {e ê ê′ ᾱ} → ê + ᾱ +e>* ê′ → (‵ e +₂ ê) + ᾱ +e>* (‵ e +₂ ê′)
  ziplem-plus2 AEIRefl                = AEIRefl
  ziplem-plus2 (AEIExp ê+>ê′ ê′+>*ê″) = AEIExp (AEZipPlus2 ê+>ê′) (ziplem-plus2 ê′+>*ê″)

  ziplem-if1 : ∀ {ê e₁ e₂ ê′ ᾱ} → ê + ᾱ +e>* ê′ → (‵ ê ∙₁ e₁ ∙ e₂) + ᾱ +e>* (‵ ê′ ∙₁ e₁ ∙ e₂)
  ziplem-if1 AEIRefl                = AEIRefl
  ziplem-if1 (AEIExp ê+>ê′ ê′+>*ê″) = AEIExp (AEZipIf1 ê+>ê′) (ziplem-if1 ê′+>*ê″)

  ziplem-if2 : ∀ {e₁ ê e₂ ê′ ᾱ} → ê + ᾱ +e>* ê′ → (‵ e₁ ∙₂ ê ∙ e₂) + ᾱ +e>* (‵ e₁ ∙₂ ê′ ∙ e₂)
  ziplem-if2 AEIRefl                = AEIRefl
  ziplem-if2 (AEIExp ê+>ê′ ê′+>*ê″) = AEIExp (AEZipIf2 ê+>ê′) (ziplem-if2 ê′+>*ê″)

  ziplem-if3 : ∀ {ê e₁ e₂ ê′ ᾱ} → ê + ᾱ +e>* ê′ → (‵ e₁ ∙₃ e₂ ∙ ê) + ᾱ +e>* (‵ e₁ ∙₃ e₂ ∙ ê′)
  ziplem-if3 AEIRefl                = AEIRefl
  ziplem-if3 (AEIExp ê+>ê′ ê′+>*ê″) = AEIExp (AEZipIf3 ê+>ê′) (ziplem-if3 ê′+>*ê″)

  ziplem-pair1 : ∀ {ê e ê′ ᾱ} → ê + ᾱ +e>* ê′ → (‵⟨ ê ,₁ e ⟩) + ᾱ +e>* (‵⟨ ê′ ,₁ e ⟩)
  ziplem-pair1 AEIRefl                = AEIRefl
  ziplem-pair1 (AEIExp ê+>ê′ ê′+>*ê″) = AEIExp (AEZipPair1 ê+>ê′) (ziplem-pair1 ê′+>*ê″)

  ziplem-pair2 : ∀ {e ê ê′ ᾱ} → ê + ᾱ +e>* ê′ → (‵⟨ e ,₂ ê ⟩) + ᾱ +e>* (‵⟨ e ,₂ ê′ ⟩)
  ziplem-pair2 AEIRefl                = AEIRefl
  ziplem-pair2 (AEIExp ê+>ê′ ê′+>*ê″) = AEIExp (AEZipPair2 ê+>ê′) (ziplem-pair2 ê′+>*ê″)

  ziplem-projl : ∀ {ê ê′ ᾱ} → ê + ᾱ +e>* ê′ → (‵π₁ ê) + ᾱ +e>* (‵π₁ ê′)
  ziplem-projl AEIRefl                = AEIRefl
  ziplem-projl (AEIExp ê+>ê′ ê′+>*ê″) = AEIExp (AEZipProjL ê+>ê′) (ziplem-projl ê′+>*ê″)

  ziplem-projr : ∀ {ê ê′ ᾱ} → ê + ᾱ +e>* ê′ → (‵π₂ ê) + ᾱ +e>* (‵π₂ ê′)
  ziplem-projr AEIRefl                = AEIRefl
  ziplem-projr (AEIExp ê+>ê′ ê′+>*ê″) = AEIExp (AEZipProjR ê+>ê′) (ziplem-projr ê′+>*ê″)
