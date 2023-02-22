open import prelude
open import core

open import hazelnut.action
open import hazelnut.typed.ztyp
open import hazelnut.typed.zexp

module hazelnut.typed.action where
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

  -- iterated type actions
  data _+_+τ>*_ : (τ^ : ZTyp) → (ᾱ : ActionList) → (τ^′ : ZTyp) → Set where
    TIRefl : ∀ {τ^}
           → τ^ + [] +τ>* τ^
    TITyp  : ∀ {τ^ τ^′ τ^″ α ᾱ}
           → (τ^+>τ^′ : τ^ + α +τ> τ^′)
           → (τ^′+>*τ^″ : τ^′ + ᾱ +τ>* τ^″)
           → τ^ + α ∷ ᾱ +τ>* τ^″

  +τ>*-++ : ∀ {τ^ τ^′ τ^″ ᾱ₁ ᾱ₂} → τ^ + ᾱ₁ +τ>* τ^′ → τ^′ + ᾱ₂ +τ>* τ^″ → τ^ + (ᾱ₁ ++ ᾱ₂) +τ>* τ^″
  +τ>*-++ TIRefl                    τ^+>*τ^″  = τ^+>*τ^″
  +τ>*-++ (TITyp τ^+>τ^′ τ^′+>*τ^″) τ^″+>*τ^‴ = TITyp τ^+>τ^′ (+τ>*-++ τ^′+>*τ^″ τ^″+>*τ^‴)

  -- type zippers
  ziplem-tarr1 : ∀ {τ^ τ^′ τ ᾱ} → τ^ + ᾱ +τ>* τ^′ → (τ^ -→₁ τ) + ᾱ +τ>* (τ^′ -→₁ τ)
  ziplem-tarr1 TIRefl                    = TIRefl
  ziplem-tarr1 (TITyp τ^+>τ^′ τ^′+>*τ^″) = TITyp (TZipArr1 τ^+>τ^′) (ziplem-tarr1 τ^′+>*τ^″)

  ziplem-tarr2 : ∀ {τ^ τ^′ τ ᾱ} → τ^ + ᾱ +τ>* τ^′ → (τ -→₂ τ^) + ᾱ +τ>* (τ -→₂ τ^′)
  ziplem-tarr2 TIRefl                    = TIRefl
  ziplem-tarr2 (TITyp τ^+>τ^′ τ^′+>*τ^″) = TITyp (TZipArr2 τ^+>τ^′) (ziplem-tarr2 τ^′+>*τ^″)

  mutual
    -- synthetic expression movements
    data _+_+⇒_ : ∀ {Γ τ τ′} → (ê : - Γ ⊢⇒ τ) → (δ : Dir) → (ê′ : - Γ ⊢⇒ τ′) → Set where
      -- movement
      ESMLamChild1 : ∀ {Γ x τ}
        → {ě : Γ , τ ⊢⇒ τ}
        → ⊢▹ ⊢λ∶ τ ∙ ě [ x ] ◃ + child 1 +⇒ ⊢λ₁∶ ▹ τ ◃ ∙ ě [ x ]
      ESMLamChild2 : ∀ {Γ x τ}
        → {ě : Γ , τ ⊢⇒ τ}
        → ⊢▹ ⊢λ∶ τ ∙ ě [ x ] ◃ + child 2 +⇒ ⊢λ₂∶ τ ∙ ⊢▹ ě ◃ [ x ]
      ESMLamParent1 : ∀ {Γ x τ}
        → {ě : Γ , τ ⊢⇒ τ}
        → ⊢λ₁∶ ▹ τ ◃ ∙ ě [ x ] + parent +⇒ ⊢▹ ⊢λ∶ τ ∙ ě [ x ] ◃
      ESMLamParent2 : ∀ {Γ x τ}
        → {ě : Γ , τ ⊢⇒ τ}
        → ⊢λ₂∶ τ ∙ ⊢▹ ě ◃ [ x ] + parent +⇒ ⊢▹ ⊢λ∶ τ ∙ ě [ x ] ◃

      ESMAp1Child1 : ∀ {Γ τ τ₁ τ₂}
        → {ě₁ : Γ ⊢⇒ τ}
        → {τ▸ : τ ▸ τ₁ -→ τ₂}
        → {ě₂ : Γ ⊢⇐ τ₁}
        → ⊢▹ ⊢ ě₁ ∙ ě₂ [ τ▸ ] ◃ + child 1 +⇒ ⊢ ⊢▹ ě₁ ◃ ∙₁ ě₂ [ τ▸ ]
      ESMAp1Child2 : ∀ {Γ τ τ₁ τ₂}
        → {ě₁ : Γ ⊢⇒ τ}
        → {τ▸ : τ ▸ τ₁ -→ τ₂}
        → {ě₂ : Γ ⊢⇐ τ₁}
        → ⊢▹ ⊢ ě₁ ∙ ě₂ [ τ▸ ] ◃ + child 2 +⇒ ⊢ ě₁ ∙₂ ⊢▹ ě₂ ◃ [ τ▸ ]
      ESMAp1Parent1 : ∀ {Γ τ τ₁ τ₂}
        → {ě₁ : Γ ⊢⇒ τ}
        → {τ▸ : τ ▸ τ₁ -→ τ₂}
        → {ě₂ : Γ ⊢⇐ τ₁}
        → ⊢ ⊢▹ ě₁ ◃ ∙₁ ě₂ [ τ▸ ] + parent +⇒ ⊢▹ ⊢ ě₁ ∙ ě₂ [ τ▸ ] ◃
      ESMAp1Parent2 : ∀ {Γ τ τ₁ τ₂}
        → {ě₁ : Γ ⊢⇒ τ}
        → {τ▸ : τ ▸ τ₁ -→ τ₂}
        → {ě₂ : Γ ⊢⇐ τ₁}
        → ⊢ ě₁ ∙₂ ⊢▹ ě₂ ◃ [ τ▸ ] + parent +⇒ ⊢▹ ⊢ ě₁ ∙ ě₂ [ τ▸ ] ◃

      ESMAp2Child1 : ∀ {Γ τ}
        → {ě₁ : Γ ⊢⇒ τ}
        → {τ!▸ : τ !▸}
        → {ě₂ : Γ ⊢⇐ unknown}
        → ⊢▹ ⊢⸨ ě₁ ⸩∙ ě₂ [ τ!▸ ] ◃ + child 1 +⇒ ⊢⸨ ⊢▹ ě₁ ◃ ⸩∙₁ ě₂ [ τ!▸ ]
      ESMAp2Child2 : ∀ {Γ τ}
        → {ě₁ : Γ ⊢⇒ τ}
        → {τ!▸ : τ !▸}
        → {ě₂ : Γ ⊢⇐ unknown}
        → ⊢▹ ⊢⸨ ě₁ ⸩∙ ě₂ [ τ!▸ ] ◃ + child 2 +⇒ ⊢⸨ ě₁ ⸩∙₂ ⊢▹ ě₂ ◃ [ τ!▸ ]
      ESMAp2Parent1 : ∀ {Γ τ}
        → {ě₁ : Γ ⊢⇒ τ}
        → {τ!▸ : τ !▸}
        → {ě₂ : Γ ⊢⇐ unknown}
        → ⊢⸨ ⊢▹ ě₁ ◃ ⸩∙₁ ě₂ [ τ!▸ ] + parent +⇒ ⊢▹ ⊢⸨ ě₁ ⸩∙ ě₂ [ τ!▸ ] ◃
      ESMAp2Parent2 : ∀ {Γ τ}
        → {ě₁ : Γ ⊢⇒ τ}
        → {τ!▸ : τ !▸}
        → {ě₂ : Γ ⊢⇐ unknown}
        → ⊢⸨ ě₁ ⸩∙₂ ⊢▹ ě₂ ◃ [ τ!▸ ] + parent +⇒ ⊢▹ ⊢⸨ ě₁ ⸩∙ ě₂ [ τ!▸ ] ◃

      ESMLetChild1 : ∀ {Γ τ₁ τ₂}
        → {ě₁ : Γ ⊢⇒ τ₁}
        → {ě₂ : Γ , τ₁ ⊢⇒ τ₂}
        → {x : Var}
        → ⊢▹ ⊢← ě₁ ∙ ě₂ [ x ] ◃ + child 1 +⇒ ⊢←₁ ⊢▹ ě₁ ◃ ∙ ě₂ [ x ]
      ESMLetChild2 : ∀ {Γ τ₁ τ₂}
        → {ě₁ : Γ ⊢⇒ τ₁}
        → {ě₂ : Γ , τ₁ ⊢⇒ τ₂}
        → {x : Var}
        → ⊢▹ ⊢← ě₁ ∙ ě₂ [ x ] ◃ + child 2 +⇒ ⊢←₂ ě₁ ∙ ⊢▹ ě₂ ◃ [ x ]
      ESMLetParent1 : ∀ {Γ τ₁ τ₂}
        → {ě₁ : Γ ⊢⇒ τ₁}
        → {ě₂ : Γ , τ₁ ⊢⇒ τ₂}
        → {x : Var}
        → ⊢←₁ ⊢▹ ě₁ ◃ ∙ ě₂ [ x ] + parent +⇒ ⊢▹ ⊢← ě₁ ∙ ě₂ [ x ] ◃
      ESMLetParent2 : ∀ {Γ τ₁ τ₂}
        → {ě₁ : Γ ⊢⇒ τ₁}
        → {ě₂ : Γ , τ₁ ⊢⇒ τ₂}
        → {x : Var}
        → ⊢←₂ ě₁ ∙ ⊢▹ ě₂ ◃ [ x ] + parent +⇒ ⊢▹ ⊢← ě₁ ∙ ě₂ [ x ] ◃

      ESMPlusChild1 : ∀ {Γ}
        → {ě₁ : Γ ⊢⇐ num}
        → {ě₂ : Γ ⊢⇐ num}
        → ⊢▹ ⊢ ě₁ + ě₂ ◃ + child 1 +⇒ (⊢ ⊢▹ ě₁ ◃ +₁ ě₂)
      ESMPlusChild2 : ∀ {Γ}
        → {ě₁ : Γ ⊢⇐ num}
        → {ě₂ : Γ ⊢⇐ num}
        → ⊢▹ ⊢ ě₁ + ě₂ ◃ + child 2 +⇒ (⊢ ě₁ +₂ ⊢▹ ě₂ ◃)
      ESMPlusParent1 : ∀ {Γ}
        → {ě₁ : Γ ⊢⇐ num}
        → {ě₂ : Γ ⊢⇐ num}
        → (⊢ ⊢▹ ě₁ ◃ +₁ ě₂) + parent +⇒ ⊢▹ ⊢ ě₁ + ě₂ ◃
      ESMPlusParent2 : ∀ {Γ}
        → {ě₁ : Γ ⊢⇐ num}
        → {ě₂ : Γ ⊢⇐ num}
        → (⊢ ě₁ +₂ ⊢▹ ě₂ ◃) + parent +⇒ ⊢▹ ⊢ ě₁ + ě₂ ◃

      ESMIfChild1 : ∀ {Γ τ₁ τ₂ τ}
        → {ě₁ : Γ ⊢⇐ bool}
        → {ě₂ : Γ ⊢⇒ τ₁}
        → {ě₃ : Γ ⊢⇒ τ₂}
        → {τ₁⊔τ₂ : τ₁ ⊔ τ₂ ⇒ τ}
        → ⊢▹ ⊢ ě₁ ∙ ě₂ ∙ ě₃ [ τ₁⊔τ₂ ] ◃ + child 1 +⇒ ⊢ ⊢▹ ě₁ ◃ ∙₁ ě₂ ∙ ě₃ [ τ₁⊔τ₂ ]
      ESMIfChild2 : ∀ {Γ τ₁ τ₂ τ}
        → {ě₁ : Γ ⊢⇐ bool}
        → {ě₂ : Γ ⊢⇒ τ₁}
        → {ě₃ : Γ ⊢⇒ τ₂}
        → {τ₁⊔τ₂ : τ₁ ⊔ τ₂ ⇒ τ}
        → ⊢▹ ⊢ ě₁ ∙ ě₂ ∙ ě₃ [ τ₁⊔τ₂ ] ◃ + child 2 +⇒ ⊢ ě₁ ∙₂ ⊢▹ ě₂ ◃ ∙ ě₃ [ τ₁⊔τ₂ ]
      ESMIfChild3 : ∀ {Γ τ₁ τ₂ τ}
        → {ě₁ : Γ ⊢⇐ bool}
        → {ě₂ : Γ ⊢⇒ τ₁}
        → {ě₃ : Γ ⊢⇒ τ₂}
        → {τ₁⊔τ₂ : τ₁ ⊔ τ₂ ⇒ τ}
        → ⊢▹ ⊢ ě₁ ∙ ě₂ ∙ ě₃ [ τ₁⊔τ₂ ] ◃ + child 3 +⇒ ⊢ ě₁ ∙₃ ě₂ ∙ ⊢▹ ě₃ ◃ [ τ₁⊔τ₂ ]
      ESMIfParent1 : ∀ {Γ τ₁ τ₂ τ}
        → {ě₁ : Γ ⊢⇐ bool}
        → {ě₂ : Γ ⊢⇒ τ₁}
        → {ě₃ : Γ ⊢⇒ τ₂}
        → {τ₁⊔τ₂ : τ₁ ⊔ τ₂ ⇒ τ}
        → ⊢ ⊢▹ ě₁ ◃ ∙₁ ě₂ ∙ ě₃ [ τ₁⊔τ₂ ] + parent +⇒ ⊢▹ ⊢ ě₁ ∙ ě₂ ∙ ě₃ [ τ₁⊔τ₂ ] ◃
      ESMIfParent2 : ∀ {Γ τ₁ τ₂ τ}
        → {ě₁ : Γ ⊢⇐ bool}
        → {ě₂ : Γ ⊢⇒ τ₁}
        → {ě₃ : Γ ⊢⇒ τ₂}
        → {τ₁⊔τ₂ : τ₁ ⊔ τ₂ ⇒ τ}
        → ⊢ ě₁ ∙₂ ⊢▹ ě₂ ◃ ∙ ě₃ [ τ₁⊔τ₂ ] + parent +⇒ ⊢▹ ⊢ ě₁ ∙ ě₂ ∙ ě₃ [ τ₁⊔τ₂ ] ◃
      ESMIfParent3 : ∀ {Γ τ₁ τ₂ τ}
        → {ě₁ : Γ ⊢⇐ bool}
        → {ě₂ : Γ ⊢⇒ τ₁}
        → {ě₃ : Γ ⊢⇒ τ₂}
        → {τ₁⊔τ₂ : τ₁ ⊔ τ₂ ⇒ τ}
        → ⊢ ě₁ ∙₃ ě₂ ∙ ⊢▹ ě₃ ◃ [ τ₁⊔τ₂ ] + parent +⇒ ⊢▹ ⊢ ě₁ ∙ ě₂ ∙ ě₃ [ τ₁⊔τ₂ ] ◃

      ESMInconsistentBranchesChild1 : ∀ {Γ τ₁ τ₂}
        → {ě₁ : Γ ⊢⇐ bool}
        → {ě₂ : Γ ⊢⇒ τ₁}
        → {ě₃ : Γ ⊢⇒ τ₂}
        → {τ₁~̸τ₂ : τ₁ ~̸ τ₂}
        → ⊢▹ ⊢⦉ ě₁ ∙ ě₂ ∙ ě₃ ⦊[ τ₁~̸τ₂ ] ◃ + child 1 +⇒ ⊢⦉ ⊢▹ ě₁ ◃ ∙₁ ě₂ ∙ ě₃ ⦊[ τ₁~̸τ₂ ]
      ESMInconsistentBranchesChild2 : ∀ {Γ τ₁ τ₂}
        → {ě₁ : Γ ⊢⇐ bool}
        → {ě₂ : Γ ⊢⇒ τ₁}
        → {ě₃ : Γ ⊢⇒ τ₂}
        → {τ₁~̸τ₂ : τ₁ ~̸ τ₂}
        → ⊢▹ ⊢⦉ ě₁ ∙ ě₂ ∙ ě₃ ⦊[ τ₁~̸τ₂ ] ◃ + child 2 +⇒ ⊢⦉ ě₁ ∙₂ ⊢▹ ě₂ ◃ ∙ ě₃ ⦊[ τ₁~̸τ₂ ]
      ESMInconsistentBranchesChild3 : ∀ {Γ τ₁ τ₂}
        → {ě₁ : Γ ⊢⇐ bool}
        → {ě₂ : Γ ⊢⇒ τ₁}
        → {ě₃ : Γ ⊢⇒ τ₂}
        → {τ₁~̸τ₂ : τ₁ ~̸ τ₂}
        → ⊢▹ ⊢⦉ ě₁ ∙ ě₂ ∙ ě₃ ⦊[ τ₁~̸τ₂ ] ◃ + child 3 +⇒ ⊢⦉ ě₁ ∙₃ ě₂ ∙ ⊢▹ ě₃ ◃ ⦊[ τ₁~̸τ₂ ]
      ESMInconsistentBranchesParent1 : ∀ {Γ τ₁ τ₂}
        → {ě₁ : Γ ⊢⇐ bool}
        → {ě₂ : Γ ⊢⇒ τ₁}
        → {ě₃ : Γ ⊢⇒ τ₂}
        → {τ₁~̸τ₂ : τ₁ ~̸ τ₂}
        → ⊢⦉ ⊢▹ ě₁ ◃ ∙₁ ě₂ ∙ ě₃ ⦊[ τ₁~̸τ₂ ] + parent +⇒ ⊢▹ ⊢⦉ ě₁ ∙ ě₂ ∙ ě₃ ⦊[ τ₁~̸τ₂ ] ◃
      ESMInconsistentBranchesParent2 : ∀ {Γ τ₁ τ₂}
        → {ě₁ : Γ ⊢⇐ bool}
        → {ě₂ : Γ ⊢⇒ τ₁}
        → {ě₃ : Γ ⊢⇒ τ₂}
        → {τ₁~̸τ₂ : τ₁ ~̸ τ₂}
        → ⊢⦉ ě₁ ∙₂ ⊢▹ ě₂ ◃ ∙ ě₃ ⦊[ τ₁~̸τ₂ ] + parent +⇒ ⊢▹ ⊢⦉ ě₁ ∙ ě₂ ∙ ě₃ ⦊[ τ₁~̸τ₂ ] ◃
      ESMInconsistentBranchesParent3 : ∀ {Γ τ₁ τ₂}
        → {ě₁ : Γ ⊢⇐ bool}
        → {ě₂ : Γ ⊢⇒ τ₁}
        → {ě₃ : Γ ⊢⇒ τ₂}
        → {τ₁~̸τ₂ : τ₁ ~̸ τ₂}
        → ⊢⦉ ě₁ ∙₃ ě₂ ∙ ⊢▹ ě₃ ◃ ⦊[ τ₁~̸τ₂ ] + parent +⇒ ⊢▹ ⊢⦉ ě₁ ∙ ě₂ ∙ ě₃ ⦊[ τ₁~̸τ₂ ] ◃
