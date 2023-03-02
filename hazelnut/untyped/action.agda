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
    EMApParent1 : ∀ {e₁ e₂}
                → (‵ ‵▹ e₁ ◃ ∙₁ e₂) + move parent +e> ‵▹ ‵ e₁ ∙ e₂ ◃
    EMApParent2 : ∀ {e₁ e₂}
                → (‵ e₁ ∙₂ ‵▹ e₂ ◃) + move parent +e> ‵▹ ‵ e₁ ∙ e₂ ◃

    EMLetChild1  : ∀ {x e₁ e₂}
                 → ‵▹ ‵ x ← e₁ ∙ e₂ ◃ + move (child 1) +e> (‵ x ←₁ ‵▹ e₁ ◃ ∙ e₂)
    EMLetChild2  : ∀ {x e₁ e₂}
                 → ‵▹ ‵ x ← e₁ ∙ e₂ ◃ + move (child 2) +e> (‵ x ←₂ e₁ ∙ ‵▹ e₂ ◃)
    EMLetParent1 : ∀ {x e₁ e₂}
                 → (‵ x ←₁ ‵▹ e₁ ◃ ∙ e₂) + move parent +e> ‵▹ ‵ x ← e₁ ∙ e₂ ◃
    EMLetParent2 : ∀ {x e₁ e₂}
                 → (‵ x ←₂ e₁ ∙ ‵▹ e₂ ◃) + move parent +e> ‵▹ ‵ x ← e₁ ∙ e₂ ◃

    EMPlusChild1  : ∀ {e₁ e₂}
                  → ‵▹ ‵ e₁ + e₂ ◃ + move (child 1) +e> (‵ ‵▹ e₁ ◃ +₁ e₂)
    EMPlusChild2  : ∀ {e₁ e₂}
                  → ‵▹ ‵ e₁ + e₂ ◃ + move (child 2) +e> (‵ e₁ +₂ ‵▹ e₂ ◃)
    EMPlusParent1 : ∀ {e₁ e₂}
                  → (‵ ‵▹ e₁ ◃ +₁ e₂) + move parent +e> ‵▹ ‵ e₁ + e₂ ◃
    EMPlusParent2 : ∀ {e₁ e₂}
                  → (‵ e₁ +₂ ‵▹ e₂ ◃) + move parent +e> ‵▹ ‵ e₁ + e₂ ◃

    EMIfChild1  : ∀ {e₁ e₂ e₃}
                → ‵▹ ‵ e₁ ∙ e₂ ∙ e₃ ◃ + move (child 1) +e> (‵ ‵▹ e₁ ◃ ∙₁ e₂ ∙ e₃)
    EMIfChild2  : ∀ {e₁ e₂ e₃}
                → ‵▹ ‵ e₁ ∙ e₂ ∙ e₃ ◃ + move (child 2) +e> (‵ e₁ ∙₂ ‵▹ e₂ ◃ ∙ e₃)
    EMIfChild3  : ∀ {e₁ e₂ e₃}
                → ‵▹ ‵ e₁ ∙ e₂ ∙ e₃ ◃ + move (child 3) +e> (‵ e₁ ∙₃ e₂ ∙ ‵▹ e₃ ◃)
    EMIfParent1 : ∀ {e₁ e₂ e₃}
                → (‵ ‵▹ e₁ ◃ ∙₁ e₂ ∙ e₃) + move parent +e> ‵▹ ‵ e₁ ∙ e₂ ∙ e₃ ◃
    EMIfParent2 : ∀ {e₁ e₂ e₃}
                → (‵ e₁ ∙₂ ‵▹ e₂ ◃ ∙ e₃) + move parent +e> ‵▹ ‵ e₁ ∙ e₂ ∙ e₃ ◃
    EMIfParent3 : ∀ {e₁ e₂ e₃}
                → (‵ e₁ ∙₃ e₂ ∙ ‵▹ e₃ ◃) + move parent +e> ‵▹ ‵ e₁ ∙ e₂ ∙ e₃ ◃

    EMPairChild1 : ∀ {e₁ e₂}
                 → ‵▹ ‵⟨ e₁ , e₂ ⟩ ◃ + move (child 1) +e> ‵⟨ ‵▹ e₁ ◃ ,₁ e₂ ⟩
    EMPairChild2 : ∀ {e₁ e₂}
                 → ‵▹ ‵⟨ e₁ , e₂ ⟩ ◃ + move (child 2) +e> ‵⟨ e₁ ,₂ ‵▹ e₂ ◃ ⟩
    EMPairParent1 : ∀ {e₁ e₂}
                 → ‵⟨ ‵▹ e₁ ◃ ,₁ e₂ ⟩ + move parent +e> ‵▹ ‵⟨ e₁ , e₂ ⟩ ◃
    EMPairParent2 : ∀ {e₁ e₂}
                 → ‵⟨ e₁ ,₂ ‵▹ e₂ ◃ ⟩ + move parent +e> ‵▹ ‵⟨ e₁ , e₂ ⟩ ◃

    EMProjLChild : ∀ {e}
                 → ‵▹ ‵π₁ e ◃ + move (child 1) +e> (‵π₁ ‵▹ e ◃)
    EMProjLParent : ∀ {e}
                 → (‵π₁ ‵▹ e ◃) + move parent +e> ‵▹ ‵π₁ e ◃
    EMProjRChild : ∀ {e}
                 → ‵▹ ‵π₂ e ◃ + move (child 1) +e> (‵π₂ ‵▹ e ◃)
    EMProjRParent : ∀ {e}
                 → (‵π₂ ‵▹ e ◃) + move parent +e> ‵▹ ‵π₂ e ◃

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
    EConPair1 : ∀ {e u}
              → ‵▹ e ◃ + construct (pair₁ u) +e> ‵⟨ e ,₂ ‵▹ ‵⦇-⦈^ u ◃ ⟩
    EConPair2 : ∀ {e u}
              → ‵▹ e ◃ + construct (pair₂ u) +e> ‵⟨ ‵▹ ‵⦇-⦈^ u ◃ ,₁ e ⟩
    EConProjL : ∀ {e}
              → ‵▹ e ◃ + construct projl +e> ‵▹ ‵π₁ e ◃
    EConProjR : ∀ {e}
              → ‵▹ e ◃ + construct projr +e> ‵▹ ‵π₂ e ◃

    -- zipper cases
    EZipLam1  : ∀ {x τ^ e α τ^′}
              → (τ^+>τ^′ : τ^ + α +τ> τ^′)
              → (‵λ₁ x ∶ τ^ ∙ e) + α +e> (‵λ₁ x ∶ τ^′ ∙ e)
    EZipLam2  : ∀ {x τ ê α ê′}
              → (ê+>ê′ : ê + α +e> ê′)
              → (‵λ₂ x ∶ τ ∙ ê) + α +e> (‵λ₂ x ∶ τ ∙ ê′)
    EZipAp1   : ∀ {ê e α ê′}
              → (ê+>ê′ : ê + α +e> ê′)
              → (‵ ê ∙₁ e) + α +e> (‵ ê′ ∙₁ e)
    EZipAp2   : ∀ {e ê α ê′}
              → (ê+>ê′ : ê + α +e> ê′)
              → (‵ e ∙₂ ê) + α +e> (‵ e ∙₂ ê′)
    EZipLet1  : ∀ {x ê e α ê′}
              → (ê+>ê′ : ê + α +e> ê′)
              → (‵ x ←₁ ê ∙ e) + α +e> (‵ x ←₁ ê′ ∙ e)
    EZipLet2  : ∀ {x e ê α ê′}
              → (ê+>ê′ : ê + α +e> ê′)
              → (‵ x ←₂ e ∙ ê) + α +e> (‵ x ←₂ e ∙ ê′)
    EZipPlus1 : ∀ {ê e α ê′}
              → (ê+>ê′ : ê + α +e> ê′)
              → (‵ ê +₁ e) + α +e> (‵ ê′ +₁ e)
    EZipPlus2 : ∀ {e ê α ê′}
              → (ê+>ê′ : ê + α +e> ê′)
              → (‵ e +₂ ê) + α +e> (‵ e +₂ ê′)
    EZipIf1   : ∀ {ê e₁ e₂ α ê′}
              → (ê+>ê′ : ê + α +e> ê′)
              → (‵ ê ∙₁ e₁ ∙ e₂) + α +e> (‵ ê′ ∙₁ e₁ ∙ e₂)
    EZipIf2   : ∀ {e₁ ê e₂ α ê′}
              → (ê+>ê′ : ê + α +e> ê′)
              → (‵ e₁ ∙₂ ê ∙ e₂) + α +e> (‵ e₁ ∙₂ ê′ ∙ e₂)
    EZipIf3   : ∀ {e₁ e₂ ê α ê′}
              → (ê+>ê′ : ê + α +e> ê′)
              → (‵ e₁ ∙₃ e₂ ∙ ê) + α +e> (‵ e₁ ∙₃ e₂ ∙ ê′)
    EZipPair1 : ∀ {ê e α ê′}
              → (ê+>ê′ : ê + α +e> ê′)
              → (‵⟨ ê ,₁ e ⟩) + α +e> (‵⟨ ê′ ,₁ e ⟩)
    EZipPair2 : ∀ {e ê α ê′}
              → (ê+>ê′ : ê + α +e> ê′)
              → (‵⟨ e ,₂ ê ⟩) + α +e> (‵⟨ e ,₂ ê′ ⟩)
    EZipProjL : ∀ {ê α ê′}
              → (ê+>ê′ : ê + α +e> ê′)
              → (‵π₁ ê) + α +e> (‵π₁ ê′)
    EZipProjR : ∀ {ê α ê′}
              → (ê+>ê′ : ê + α +e> ê′)
              → (‵π₂ ê) + α +e> (‵π₂ ê′)

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
  ziplem-tarr1 (TITyp τ^+>τ^′ τ^′+>*τ^″) = TITyp (ATZipArr1 τ^+>τ^′) (ziplem-tarr1 τ^′+>*τ^″)

  ziplem-tarr2 : ∀ {τ^ τ^′ τ ᾱ} → τ^ + ᾱ +τ>* τ^′ → (τ -→₂ τ^) + ᾱ +τ>* (τ -→₂ τ^′)
  ziplem-tarr2 TIRefl                    = TIRefl
  ziplem-tarr2 (TITyp τ^+>τ^′ τ^′+>*τ^″) = TITyp (ATZipArr2 τ^+>τ^′) (ziplem-tarr2 τ^′+>*τ^″)

  ziplem-tprod1 : ∀ {τ^ τ^′ τ ᾱ} → τ^ + ᾱ +τ>* τ^′ → (τ^ -×₁ τ) + ᾱ +τ>* (τ^′ -×₁ τ)
  ziplem-tprod1 TIRefl                    = TIRefl
  ziplem-tprod1 (TITyp τ^+>τ^′ τ^′+>*τ^″) = TITyp (ATZipProd1 τ^+>τ^′) (ziplem-tprod1 τ^′+>*τ^″)

  ziplem-tprod2 : ∀ {τ^ τ^′ τ ᾱ} → τ^ + ᾱ +τ>* τ^′ → (τ -×₂ τ^) + ᾱ +τ>* (τ -×₂ τ^′)
  ziplem-tprod2 TIRefl                    = TIRefl
  ziplem-tprod2 (TITyp τ^+>τ^′ τ^′+>*τ^″) = TITyp (ATZipProd2 τ^+>τ^′) (ziplem-tprod2 τ^′+>*τ^″)

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

  ziplem-pair1 : ∀ {ê e ê′ ᾱ} → ê + ᾱ +e>* ê′ → (‵⟨ ê ,₁ e ⟩) + ᾱ +e>* (‵⟨ ê′ ,₁ e ⟩)
  ziplem-pair1 EIRefl                = EIRefl
  ziplem-pair1 (EIExp ê+>ê′ ê′+>*ê″) = EIExp (EZipPair1 ê+>ê′) (ziplem-pair1 ê′+>*ê″)

  ziplem-pair2 : ∀ {e ê ê′ ᾱ} → ê + ᾱ +e>* ê′ → (‵⟨ e ,₂ ê ⟩) + ᾱ +e>* (‵⟨ e ,₂ ê′ ⟩)
  ziplem-pair2 EIRefl                = EIRefl
  ziplem-pair2 (EIExp ê+>ê′ ê′+>*ê″) = EIExp (EZipPair2 ê+>ê′) (ziplem-pair2 ê′+>*ê″)

  ziplem-projl : ∀ {ê ê′ ᾱ} → ê + ᾱ +e>* ê′ → (‵π₁ ê) + ᾱ +e>* (‵π₁ ê′)
  ziplem-projl EIRefl                = EIRefl
  ziplem-projl (EIExp ê+>ê′ ê′+>*ê″) = EIExp (EZipProjL ê+>ê′) (ziplem-projl ê′+>*ê″)

  ziplem-projr : ∀ {ê ê′ ᾱ} → ê + ᾱ +e>* ê′ → (‵π₂ ê) + ᾱ +e>* (‵π₂ ê′)
  ziplem-projr EIRefl                = EIRefl
  ziplem-projr (EIExp ê+>ê′ ê′+>*ê″) = EIExp (EZipProjR ê+>ê′) (ziplem-projr ê′+>*ê″)
