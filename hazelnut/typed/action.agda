open import prelude
open import core
open import marking

open import hazelnut.action
open import hazelnut.typed.ztyp
open import hazelnut.typed.zexp

module hazelnut.typed.action where
  -- type actions
  data _~_~τ>_ : (τ : ZTyp) → (α : Action) → (τ′ : ZTyp) → Set where
    -- movement
    TMArrChild1 : ∀ {τ₁ τ₂ : Typ}
                 → ▹ τ₁ -→ τ₂ ◃ ~ move (child 1) ~τ> ▹ τ₁ ◃ -→₁ τ₂
    TMArrChild2 : ∀ {τ₁ τ₂ : Typ}
                 → ▹ τ₁ -→ τ₂ ◃ ~ move (child 2) ~τ> τ₁ -→₂ ▹ τ₂ ◃
    TMArrParent1 : ∀ {τ₁ τ₂ : Typ}
                 → ▹ τ₁ ◃ -→₁ τ₂ ~ move parent ~τ> ▹ τ₁ -→ τ₂ ◃
    TMArrParent2 : ∀ {τ₁ τ₂ : Typ}
                 → τ₁ -→₂ ▹ τ₂ ◃ ~ move parent ~τ> ▹ τ₁ -→ τ₂ ◃

    -- deletion
    TDel : ∀ {τ : Typ} {u : Hole}
         → ▹ τ ◃ ~ (del u) ~τ> ▹ unknown ◃

    -- construction
    TConArrow1 : ∀ {τ : Typ}
               → ▹ τ ◃ ~ construct tarrow₁ ~τ> τ -→₂ ▹ unknown ◃
    TConArrow2 : ∀ {τ : Typ}
               → ▹ τ ◃ ~ construct tarrow₂ ~τ> ▹ unknown ◃ -→₁ τ
    TConNum    : ▹ unknown ◃ ~ construct tnum ~τ> ▹ num ◃
    TConBool   : ▹ unknown ◃ ~ construct tbool ~τ> ▹ bool ◃

    -- zipper
    TZipArr1 : ∀ {τ^ τ^′ : ZTyp} {τ : Typ} {α : Action}
             → (τ^~>τ^′ : τ^ ~ α ~τ> τ^′)
             → τ^ -→₁ τ ~ α ~τ> τ^′ -→₁ τ
    TZipArr2 : ∀ {τ^ τ^′ : ZTyp} {τ : Typ} {α : Action}
             → (τ^~>τ^′ : τ^ ~ α ~τ> τ^′)
             → τ -→₂ τ^ ~ α ~τ> τ -→₂ τ^′

  -- iterated type actions
  data _~_~τ>*_ : (τ^ : ZTyp) → (ᾱ : ActionList) → (τ^′ : ZTyp) → Set where
    TIRefl : ∀ {τ^}
           → τ^ ~ [] ~τ>* τ^
    TITyp  : ∀ {τ^ τ^′ τ^″ α ᾱ}
           → (τ^~>τ^′ : τ^ ~ α ~τ> τ^′)
           → (τ^′~>*τ^″ : τ^′ ~ ᾱ ~τ>* τ^″)
           → τ^ ~ α ∷ ᾱ ~τ>* τ^″

  ~τ>*-++ : ∀ {τ^ τ^′ τ^″ ᾱ₁ ᾱ₂} → τ^ ~ ᾱ₁ ~τ>* τ^′ → τ^′ ~ ᾱ₂ ~τ>* τ^″ → τ^ ~ (ᾱ₁ ++ ᾱ₂) ~τ>* τ^″
  ~τ>*-++ TIRefl                    τ^~>*τ^″  = τ^~>*τ^″
  ~τ>*-++ (TITyp τ^~>τ^′ τ^′~>*τ^″) τ^″~>*τ^‴ = TITyp τ^~>τ^′ (~τ>*-++ τ^′~>*τ^″ τ^″~>*τ^‴)

  -- type zippers
  ziplem-tarr1 : ∀ {τ^ τ^′ τ ᾱ} → τ^ ~ ᾱ ~τ>* τ^′ → (τ^ -→₁ τ) ~ ᾱ ~τ>* (τ^′ -→₁ τ)
  ziplem-tarr1 TIRefl                    = TIRefl
  ziplem-tarr1 (TITyp τ^~>τ^′ τ^′~>*τ^″) = TITyp (TZipArr1 τ^~>τ^′) (ziplem-tarr1 τ^′~>*τ^″)

  ziplem-tarr2 : ∀ {τ^ τ^′ τ ᾱ} → τ^ ~ ᾱ ~τ>* τ^′ → (τ -→₂ τ^) ~ ᾱ ~τ>* (τ -→₂ τ^′)
  ziplem-tarr2 TIRefl                    = TIRefl
  ziplem-tarr2 (TITyp τ^~>τ^′ τ^′~>*τ^″) = TITyp (TZipArr2 τ^~>τ^′) (ziplem-tarr2 τ^′~>*τ^″)

  mutual
    -- synthetic expression movements
    data _+_+⇒_ : ∀ {Γ τ τ′} → (ê : - Γ ⊢⇒ τ) → (δ : Dir) → (ê′ : - Γ ⊢⇒ τ′) → Set where
      -- movement
      ESMLamChild1 : ∀ {Γ x τ}
        → {ě : Γ , x ∶ τ ⊢⇒ τ}
        → ⊢▹ ⊢λ x ∶ τ ∙ ě ◃ + child 1 +⇒ (⊢λ₁ x ∶ ▹ τ ◃ ∙ ě)
      ESMLamChild2 : ∀ {Γ x τ}
        → {ě : Γ , x ∶ τ ⊢⇒ τ}
        → ⊢▹ ⊢λ x ∶ τ ∙ ě ◃ + child 2 +⇒ (⊢λ₂ x ∶ τ ∙ ⊢▹ ě ◃)
      ESMLamParent1 : ∀ {Γ x τ}
        → {ě : Γ , x ∶ τ ⊢⇒ τ}
        → (⊢λ₁ x ∶ ▹ τ ◃ ∙ ě) + parent +⇒ ⊢▹ ⊢λ x ∶ τ ∙ ě ◃
      ESMLamParent2 : ∀ {Γ x τ}
        → {ě : Γ , x ∶ τ ⊢⇒ τ}
        → (⊢λ₂ x ∶ τ ∙ ⊢▹ ě ◃) + parent +⇒ ⊢▹ ⊢λ x ∶ τ ∙ ě ◃

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
        → {τ!▸ : τ !▸-→}
        → {ě₂ : Γ ⊢⇐ unknown}
        → ⊢▹ ⊢⸨ ě₁ ⸩∙ ě₂ [ τ!▸ ] ◃ + child 1 +⇒ ⊢⸨ ⊢▹ ě₁ ◃ ⸩∙₁ ě₂ [ τ!▸ ]
      ESMAp2Child2 : ∀ {Γ τ}
        → {ě₁ : Γ ⊢⇒ τ}
        → {τ!▸ : τ !▸-→}
        → {ě₂ : Γ ⊢⇐ unknown}
        → ⊢▹ ⊢⸨ ě₁ ⸩∙ ě₂ [ τ!▸ ] ◃ + child 2 +⇒ ⊢⸨ ě₁ ⸩∙₂ ⊢▹ ě₂ ◃ [ τ!▸ ]
      ESMAp2Parent1 : ∀ {Γ τ}
        → {ě₁ : Γ ⊢⇒ τ}
        → {τ!▸ : τ !▸-→}
        → {ě₂ : Γ ⊢⇐ unknown}
        → ⊢⸨ ⊢▹ ě₁ ◃ ⸩∙₁ ě₂ [ τ!▸ ] + parent +⇒ ⊢▹ ⊢⸨ ě₁ ⸩∙ ě₂ [ τ!▸ ] ◃
      ESMAp2Parent2 : ∀ {Γ τ}
        → {ě₁ : Γ ⊢⇒ τ}
        → {τ!▸ : τ !▸-→}
        → {ě₂ : Γ ⊢⇐ unknown}
        → ⊢⸨ ě₁ ⸩∙₂ ⊢▹ ě₂ ◃ [ τ!▸ ] + parent +⇒ ⊢▹ ⊢⸨ ě₁ ⸩∙ ě₂ [ τ!▸ ] ◃

      ESMLetChild1 : ∀ {Γ x τ₁ τ₂}
        → {ě₁ : Γ ⊢⇒ τ₁}
        → {ě₂ : Γ , x ∶ τ₁ ⊢⇒ τ₂}
        → ⊢▹ ⊢ x ← ě₁ ∙ ě₂ ◃ + child 1 +⇒ (⊢ x ←₁ ⊢▹ ě₁ ◃ ∙ ě₂)
      ESMLetChild2 : ∀ {Γ x τ₁ τ₂}
        → {ě₁ : Γ ⊢⇒ τ₁}
        → {ě₂ : Γ , x ∶ τ₁ ⊢⇒ τ₂}
        → ⊢▹ ⊢ x ← ě₁ ∙ ě₂ ◃ + child 2 +⇒ (⊢ x ←₂ ě₁ ∙ ⊢▹ ě₂ ◃)
      ESMLetParent1 : ∀ {Γ x τ₁ τ₂}
        → {ě₁ : Γ ⊢⇒ τ₁}
        → {ě₂ : Γ , x ∶ τ₁ ⊢⇒ τ₂}
        → (⊢ x ←₁ ⊢▹ ě₁ ◃ ∙ ě₂) + parent +⇒ ⊢▹ ⊢ x ← ě₁ ∙ ě₂ ◃
      ESMLetParent2 : ∀ {Γ x τ₁ τ₂}
        → {ě₁ : Γ ⊢⇒ τ₁}
        → {ě₂ : Γ , x ∶ τ₁ ⊢⇒ τ₂}
        → (⊢ x ←₂ ě₁ ∙ ⊢▹ ě₂ ◃) + parent +⇒ ⊢▹ ⊢ x ← ě₁ ∙ ě₂ ◃

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

    MSu-+⇒ : ∀ {Γ τ} {ě : Γ ⊢⇒ τ} {n : ℕ} {ê : - Γ ⊢⇒ τ} → MSubsumable ě → ⊢▹ ě ◃ + child n +⇒ ê → ZSubsumable ê
    MSu-+⇒ MSuAp1                  ESMAp1Child1                  = ZSuZipApL1
    MSu-+⇒ MSuAp1                  ESMAp1Child2                  = ZSuZipApR1
    MSu-+⇒ MSuAp2                  ESMAp2Child1                  = ZSuZipApL2
    MSu-+⇒ MSuAp2                  ESMAp2Child2                  = ZSuZipApR2
    MSu-+⇒ MSuPlus                 ESMPlusChild1                 = ZSuPlus1
    MSu-+⇒ MSuPlus                 ESMPlusChild2                 = ZSuPlus2
    MSu-+⇒ MSuInconsistentBranches ESMInconsistentBranchesChild1 = ZSuInconsistentBranchesC
    MSu-+⇒ MSuInconsistentBranches ESMInconsistentBranchesChild2 = ZSuInconsistentBranchesL
    MSu-+⇒ MSuInconsistentBranches ESMInconsistentBranchesChild3 = ZSuInconsistentBranchesR

    ZSu-+⇒ : ∀ {Γ τ} {ê : - Γ ⊢⇒ τ} {ě : Γ ⊢⇒ τ} → ZSubsumable ê → ê + parent +⇒ ⊢▹ ě ◃ → MSubsumable ě
    ZSu-+⇒ ZSuZipApL1               ESMAp1Parent1                  = MSuAp1
    ZSu-+⇒ ZSuZipApR1               ESMAp1Parent2                  = MSuAp1
    ZSu-+⇒ ZSuZipApL2               ESMAp2Parent1                  = MSuAp2
    ZSu-+⇒ ZSuZipApR2               ESMAp2Parent2                  = MSuAp2
    ZSu-+⇒ ZSuPlus1                 ESMPlusParent1                 = MSuPlus
    ZSu-+⇒ ZSuPlus2                 ESMPlusParent2                 = MSuPlus
    ZSu-+⇒ ZSuInconsistentBranchesC ESMInconsistentBranchesParent1 = MSuInconsistentBranches
    ZSu-+⇒ ZSuInconsistentBranchesL ESMInconsistentBranchesParent2 = MSuInconsistentBranches
    ZSu-+⇒ ZSuInconsistentBranchesR ESMInconsistentBranchesParent3 = MSuInconsistentBranches

    -- analytic expression movements
    data _+_+⇐_ : ∀ {Γ τ} → (ê : - Γ ⊢⇐ τ) → (δ : Dir) → (ê′ : - Γ ⊢⇐ τ) → Set where
      EAMLam1Child1 : ∀ {Γ x τ τ₁ τ₂ τ₃}
        → {ě : Γ , x ∶ τ ⊢⇐ τ₂}
        → {τ₃▸ : τ₃ ▸ τ₁ -→ τ₂}
        → {τ~τ₁ : τ ~ τ₁}
        → ⊢▹ ⊢λ x ∶ τ ∙ ě [ τ₃▸ ∙ τ~τ₁ ] ◃ + child 1 +⇐ ⊢λ₁ x ∶ ▹ τ ◃ ∙ ě [ τ₃▸ ∙ τ~τ₁ ]
      EAMLam1Child2 : ∀ {Γ x τ τ₁ τ₂ τ₃}
        → {ě : Γ , x ∶ τ ⊢⇐ τ₂}
        → {τ₃▸ : τ₃ ▸ τ₁ -→ τ₂}
        → {τ~τ₁ : τ ~ τ₁}
        → ⊢▹ ⊢λ x ∶ τ ∙ ě [ τ₃▸ ∙ τ~τ₁ ] ◃ + child 2 +⇐ ⊢λ₂ x ∶ τ ∙ ⊢▹ ě ◃ [ τ₃▸ ∙ τ~τ₁ ]
      EAMLam1Parent1 : ∀ {Γ x τ τ₁ τ₂ τ₃}
        → {ě : Γ , x ∶ τ ⊢⇐ τ₂}
        → {τ₃▸ : τ₃ ▸ τ₁ -→ τ₂}
        → {τ~τ₁ : τ ~ τ₁}
        → ⊢λ₁ x ∶ ▹ τ ◃ ∙ ě [ τ₃▸ ∙ τ~τ₁ ] + parent +⇐ ⊢▹ ⊢λ x ∶ τ ∙ ě [ τ₃▸ ∙ τ~τ₁ ] ◃
      EAMLam1Parent2 : ∀ {Γ x τ τ₁ τ₂ τ₃}
        → {ě : Γ , x ∶ τ ⊢⇐ τ₂}
        → {τ₃▸ : τ₃ ▸ τ₁ -→ τ₂}
        → {τ~τ₁ : τ ~ τ₁}
        → ⊢λ₂ x ∶ τ ∙ ⊢▹ ě ◃ [ τ₃▸ ∙ τ~τ₁ ] + parent +⇐ ⊢▹ ⊢λ x ∶ τ ∙ ě [ τ₃▸ ∙ τ~τ₁ ] ◃

      EAMLam2Child1 : ∀ {Γ x τ τ′}
        → {ě : Γ , x ∶ τ ⊢⇐ unknown}
        → {τ′!▸ : τ′ !▸-→}
        → ⊢▹ ⊢⸨λ x ∶ τ ∙ ě ⸩[ τ′!▸ ] ◃ + child 1 +⇐ ⊢⸨λ₁ x ∶ ▹ τ ◃ ∙ ě ⸩[ τ′!▸ ]
      EAMLam2Child2 : ∀ {Γ x τ τ′}
        → {ě : Γ , x ∶ τ ⊢⇐ unknown}
        → {τ′!▸ : τ′ !▸-→}
        → ⊢▹ ⊢⸨λ x ∶ τ ∙ ě ⸩[ τ′!▸ ] ◃ + child 2 +⇐ ⊢⸨λ₂ x ∶ τ ∙ ⊢▹ ě ◃ ⸩[ τ′!▸ ]
      EAMLam2Parent1 : ∀ {Γ x τ τ′}
        → {ě : Γ , x ∶ τ ⊢⇐ unknown}
        → {τ′!▸ : τ′ !▸-→}
        → ⊢⸨λ₁ x ∶ ▹ τ ◃ ∙ ě ⸩[ τ′!▸ ] + parent +⇐ ⊢▹ ⊢⸨λ x ∶ τ ∙ ě ⸩[ τ′!▸ ] ◃
      EAMLam2Parent2 : ∀ {Γ x τ τ′}
        → {ě : Γ , x ∶ τ ⊢⇐ unknown}
        → {τ′!▸ : τ′ !▸-→}
        → ⊢⸨λ₂ x ∶ τ ∙ ⊢▹ ě ◃ ⸩[ τ′!▸ ] + parent +⇐ ⊢▹ ⊢⸨λ x ∶ τ ∙ ě ⸩[ τ′!▸ ] ◃

      EAMLam3Child1 : ∀ {Γ x τ τ₁ τ₂ τ₃}
        → {ě : Γ , x ∶ τ ⊢⇐ τ₂}
        → {τ₃▸ : τ₃ ▸ τ₁ -→ τ₂}
        → {τ~̸τ₁ : τ ~̸ τ₁}
        → ⊢▹ ⊢λ x ∶⸨ τ ⸩∙ ě [ τ₃▸ ∙ τ~̸τ₁ ] ◃ + child 1 +⇐ ⊢λ₁ x ∶⸨ ▹ τ ◃ ⸩∙ ě [ τ₃▸ ∙ τ~̸τ₁ ]
      EAMLam3Child2 : ∀ {Γ x τ τ₁ τ₂ τ₃}
        → {ě : Γ , x ∶ τ ⊢⇐ τ₂}
        → {τ₃▸ : τ₃ ▸ τ₁ -→ τ₂}
        → {τ~̸τ₁ : τ ~̸ τ₁}
        → ⊢▹ ⊢λ x ∶⸨ τ ⸩∙ ě [ τ₃▸ ∙ τ~̸τ₁ ] ◃ + child 2 +⇐ ⊢λ₂ x ∶⸨ τ ⸩∙ ⊢▹ ě ◃ [ τ₃▸ ∙ τ~̸τ₁ ]
      EAMLam3Parent1 : ∀ {Γ x τ τ₁ τ₂ τ₃}
        → {ě : Γ , x ∶ τ ⊢⇐ τ₂}
        → {τ₃▸ : τ₃ ▸ τ₁ -→ τ₂}
        → {τ~̸τ₁ : τ ~̸ τ₁}
        → ⊢λ₁ x ∶⸨ ▹ τ ◃ ⸩∙ ě [ τ₃▸ ∙ τ~̸τ₁ ] + parent +⇐ ⊢▹ ⊢λ x ∶⸨ τ ⸩∙ ě [ τ₃▸ ∙ τ~̸τ₁ ] ◃
      EAMLam3Parent2 : ∀ {Γ x τ τ₁ τ₂ τ₃}
        → {ě : Γ , x ∶ τ ⊢⇐ τ₂}
        → {τ₃▸ : τ₃ ▸ τ₁ -→ τ₂}
        → {τ~̸τ₁ : τ ~̸ τ₁}
        → ⊢λ₂ x ∶⸨ τ ⸩∙ ⊢▹ ě ◃ [ τ₃▸ ∙ τ~̸τ₁ ] + parent +⇐ ⊢▹ ⊢λ x ∶⸨ τ ⸩∙ ě [ τ₃▸ ∙ τ~̸τ₁ ] ◃

      EAMLetChild1 : ∀ {Γ x τ₁ τ₂}
        → {ě₁ : Γ ⊢⇒ τ₁}
        → {ě₂ : Γ , x ∶ τ₁ ⊢⇐ τ₂}
        → ⊢▹ ⊢ x ← ě₁ ∙ ě₂ ◃ + child 1 +⇐ (⊢ x ←₁ ⊢▹ ě₁ ◃ ∙ ě₂)
      EAMLetChild2 : ∀ {Γ x τ₁ τ₂}
        → {ě₁ : Γ ⊢⇒ τ₁}
        → {ě₂ : Γ , x ∶ τ₁ ⊢⇐ τ₂}
        → ⊢▹ ⊢ x ← ě₁ ∙ ě₂ ◃ + child 2 +⇐ (⊢ x ←₂ ě₁ ∙ ⊢▹ ě₂ ◃)
      EAMLetParent1 : ∀ {Γ x τ₁ τ₂}
        → {ě₁ : Γ ⊢⇒ τ₁}
        → {ě₂ : Γ , x ∶ τ₁ ⊢⇐ τ₂}
        → (⊢ x ←₁ ⊢▹ ě₁ ◃ ∙ ě₂) + parent +⇐ ⊢▹ ⊢ x ← ě₁ ∙ ě₂ ◃
      EAMLetParent2 : ∀ {Γ x τ₁ τ₂}
        → {ě₁ : Γ ⊢⇒ τ₁}
        → {ě₂ : Γ , x ∶ τ₁ ⊢⇐ τ₂}
        → (⊢ x ←₂ ě₁ ∙ ⊢▹ ě₂ ◃) + parent +⇐ ⊢▹ ⊢ x ← ě₁ ∙ ě₂ ◃

      EAMIfChild1 : ∀ {Γ τ}
        → {ě₁ : Γ ⊢⇐ bool}
        → {ě₂ : Γ ⊢⇐ τ}
        → {ě₃ : Γ ⊢⇐ τ}
        → ⊢▹ ⊢ ě₁ ∙ ě₂ ∙ ě₃ ◃ + child 1 +⇐ (⊢ ⊢▹ ě₁ ◃ ∙₁ ě₂ ∙ ě₃)
      EAMIfChild2 : ∀ {Γ τ}
        → {ě₁ : Γ ⊢⇐ bool}
        → {ě₂ : Γ ⊢⇐ τ}
        → {ě₃ : Γ ⊢⇐ τ}
        → ⊢▹ ⊢ ě₁ ∙ ě₂ ∙ ě₃ ◃ + child 2 +⇐ (⊢ ě₁ ∙₂ ⊢▹ ě₂ ◃ ∙ ě₃)
      EAMIfChild3 : ∀ {Γ τ}
        → {ě₁ : Γ ⊢⇐ bool}
        → {ě₂ : Γ ⊢⇐ τ}
        → {ě₃ : Γ ⊢⇐ τ}
        → ⊢▹ ⊢ ě₁ ∙ ě₂ ∙ ě₃ ◃ + child 3 +⇐ (⊢ ě₁ ∙₃ ě₂ ∙ ⊢▹ ě₃ ◃)
      EAMIfParent1 : ∀ {Γ τ}
        → {ě₁ : Γ ⊢⇐ bool}
        → {ě₂ : Γ ⊢⇐ τ}
        → {ě₃ : Γ ⊢⇐ τ}
        → (⊢ ⊢▹ ě₁ ◃ ∙₁ ě₂ ∙ ě₃) + parent +⇐ ⊢▹ ⊢ ě₁ ∙ ě₂ ∙ ě₃ ◃
      EAMIfParent2 : ∀ {Γ τ}
        → {ě₁ : Γ ⊢⇐ bool}
        → {ě₂ : Γ ⊢⇐ τ}
        → {ě₃ : Γ ⊢⇐ τ}
        → (⊢ ě₁ ∙₂ ⊢▹ ě₂ ◃ ∙ ě₃) + parent +⇐ ⊢▹ ⊢ ě₁ ∙ ě₂ ∙ ě₃ ◃
      EAMIfParent3 : ∀ {Γ τ}
        → {ě₁ : Γ ⊢⇐ bool}
        → {ě₂ : Γ ⊢⇐ τ}
        → {ě₃ : Γ ⊢⇐ τ}
        → (⊢ ě₁ ∙₃ ě₂ ∙ ⊢▹ ě₃ ◃) + parent +⇐ ⊢▹ ⊢ ě₁ ∙ ě₂ ∙ ě₃ ◃

      EAMInconsistentTypesChild : ∀ {Γ τ τ′ n}
        → {ě : Γ ⊢⇒ τ′}
        → {ê : - Γ ⊢⇒ τ′}
        → {+⇒ê : ⊢▹ ě ◃ + child n +⇒ ê}
        → {τ~̸τ′ : τ ~̸ τ′}
        → {su : MSubsumable ě}
        → ⊢▹ ⊢⸨ ě ⸩[ τ~̸τ′ ∙ su ] ◃ + child n +⇐ ⊢⸨ ê ⸩[ τ~̸τ′ ∙ MSu-+⇒ su +⇒ê ]
      EAMInconsistentTypesParent : ∀ {Γ τ τ′}
        → {ê : - Γ ⊢⇒ τ′}
        → {ě : Γ ⊢⇒ τ′}
        → {ê+⇒ : ê + parent +⇒ ⊢▹ ě ◃}
        → {τ~̸τ′ : τ ~̸ τ′}
        → {zsu : ZSubsumable ê}
        → ⊢⸨ ê ⸩[ τ~̸τ′ ∙ zsu ] + parent +⇐ ⊢▹ ⊢⸨ ě ⸩[ τ~̸τ′ ∙ ZSu-+⇒ zsu ê+⇒ ] ◃

      EAMSubsumeChild : ∀ {Γ τ τ′ n}
        → {ě : Γ ⊢⇒ τ′}
        → {ê : - Γ ⊢⇒ τ′}
        → {+⇒ê : ⊢▹ ě ◃ + child n +⇒ ê}
        → {τ~τ′ : τ ~ τ′}
        → {su : MSubsumable ě}
        → ⊢▹ ⊢∙ ě [ τ~τ′ ∙ su ] ◃ + child n +⇐ ⊢∙ ê [ τ~τ′ ∙ MSu-+⇒ su +⇒ê ]
      EAMSubsumeParent : ∀ {Γ τ τ′}
        → {ê : - Γ ⊢⇒ τ′}
        → {ě : Γ ⊢⇒ τ′}
        → {ê+⇒ : ê + parent +⇒ ⊢▹ ě ◃}
        → {τ~τ′ : τ ~ τ′}
        → {zsu : ZSubsumable ê}
        → ⊢∙ ê [ τ~τ′ ∙ zsu ] + parent +⇐ ⊢▹ ⊢∙ ě [ τ~τ′ ∙ ZSu-+⇒ zsu ê+⇒ ] ◃

  mutual
    -- synthetic expression actions
    data _⊢_~_~⇒_ : ∀ {τ τ′ : Typ} → (Γ : Ctx) → (ê : - Γ ⊢⇒ τ) → (α : Action) → (ê : - Γ ⊢⇒ τ′) → Set where
      -- movement
      ESMove : ∀ {Γ τ δ}
        → {ê : - Γ ⊢⇒ τ}
        → {ê′ : - Γ ⊢⇒ τ}
        → {ê+⇒ê′ : ê + δ +⇒ ê′}
        → Γ ⊢ ê ~ move δ ~⇒ ê′

      -- deletion
      ESDel : ∀ {Γ τ u}
        → {ě : Γ ⊢⇒ τ}
        → Γ ⊢ ⊢▹ ě ◃ ~ del u ~⇒ ⊢▹ ⊢⦇-⦈^ u ◃

      -- construction
      ESConBoundVar : ∀ {Γ u τ x}
        → (∋x : Γ ∋ x ∶ τ)
        → Γ ⊢ ⊢▹ ⊢⦇-⦈^ u ◃ ~ construct (var x) ~⇒ ⊢▹ ⊢ ∋x ◃
      ESConUnboundVar : ∀ {Γ u y}
        → (∌y : Γ ∌ y)
        → Γ ⊢ ⊢▹ ⊢⦇-⦈^ u ◃ ~ construct (var y) ~⇒ ⊢▹ ⊢⟦ ∌y ⟧ ◃
      ESConLam : ∀ {Γ τ x τ′}
        → {ě : Γ ⊢⇒ τ}
        → {ě′ : Γ , x ∶ unknown ⊢⇒ τ′}
        → (↬⇒ě′ : Γ , x ∶ unknown ⊢ (ě ⇒□) ↬⇒ ě′)
        → Γ ⊢ ⊢▹ ě ◃ ~ construct (lam x) ~⇒ (⊢λ₁ x ∶ ▹ unknown ◃ ∙ ě′)
      ESConApL1 : ∀ {Γ τ τ₁ τ₂ u}
        → {ě : Γ ⊢⇒ τ}
        → (τ▸ : τ ▸ τ₁ -→ τ₂)
        → Γ ⊢ ⊢▹ ě ◃ ~ construct (ap₁ u) ~⇒ ⊢ ě ∙₂ (⊢▹ ⊢∙ ⊢⦇-⦈^ u [ ~-unknown₂ ∙ MSuHole ] ◃) [ τ▸ ]
      ESConApL2 : ∀ {Γ τ u}
        → {ě : Γ ⊢⇒ τ}
        → (τ!▸ : τ !▸-→)
        → Γ ⊢ ⊢▹ ě ◃ ~ construct (ap₁ u) ~⇒ ⊢⸨ ě ⸩∙₂ (⊢▹ ⊢∙ ⊢⦇-⦈^ u [ ~-unknown₂ ∙ MSuHole ] ◃) [ τ!▸ ]
      ESConApR : ∀ {Γ τ u}
        → {ě : Γ ⊢⇒ τ}
        → Γ ⊢ ⊢▹ ě ◃ ~ construct (ap₂ u) ~⇒ ⊢ (⊢▹ ⊢⦇-⦈^ u ◃) ∙₁ (proj₁ (⊢⇒-⊢⇐ ě)) [ TMAHole ]
      ESConLet1 : ∀ {Γ τ x u}
        → {ě : Γ ⊢⇒ τ}
        → Γ ⊢ ⊢▹ ě ◃ ~ construct (let₁ x u) ~⇒ (⊢ x ←₂ ě ∙ ⊢▹ ⊢⦇-⦈^ u ◃)
      ESConLet2 : ∀ {Γ τ x u τ′}
        → {ě : Γ ⊢⇒ τ}
        → {ě′ : Γ , x ∶ unknown ⊢⇒ τ′}
        → (↬⇒ě′ : Γ , x ∶ unknown ⊢ (ě ⇒□) ↬⇒ ě′)
        → Γ ⊢ ⊢▹ ě ◃ ~ construct (let₂ x u) ~⇒ (⊢ x ←₁ ⊢▹ ⊢⦇-⦈^ u ◃ ∙ ě′)
      ESConNum : ∀ {Γ u n}
        → Γ ⊢ ⊢▹ ⊢⦇-⦈^ u ◃ ~ construct (num n) ~⇒ ⊢▹ ⊢ℕ n ◃
      ESConPlusL1 : ∀ {Γ τ u}
        → {ě : Γ ⊢⇒ τ}
        → (τ~num : τ ~ num)
        → Γ ⊢ ⊢▹ ě ◃ ~ construct (plus₁ u) ~⇒ (⊢ (proj₁ (⊢⇒-⊢⇐ ě)) +₂ (⊢▹ ⊢∙ ⊢⦇-⦈^ u [ ~-unknown₂ ∙ MSuHole ] ◃))
      ESConPlusL2 : ∀ {Γ τ u}
        → {ě : Γ ⊢⇒ τ}
        → (τ~̸num : τ ~̸ num)
        → Γ ⊢ ⊢▹ ě ◃ ~ construct (plus₁ u) ~⇒ (⊢ (proj₁ (⊢⇒-⊢⇐ ě)) +₂ (⊢▹ ⊢∙ ⊢⦇-⦈^ u [ ~-unknown₂ ∙ MSuHole ] ◃))
      ESConPlusR1 : ∀ {Γ τ u}
        → {ě : Γ ⊢⇒ τ}
        → (τ~num : τ ~ num)
        → Γ ⊢ ⊢▹ ě ◃ ~ construct (plus₂ u) ~⇒ (⊢ (⊢▹ ⊢∙ ⊢⦇-⦈^ u [ ~-unknown₂ ∙ MSuHole ] ◃) +₁ (proj₁ (⊢⇒-⊢⇐ ě)))
      ESConPlusR2 : ∀ {Γ τ u}
        → {ě : Γ ⊢⇒ τ}
        → (τ~̸num : τ ~̸ num)
        → Γ ⊢ ⊢▹ ě ◃ ~ construct (plus₂ u) ~⇒ (⊢ (⊢▹ ⊢∙ ⊢⦇-⦈^ u [ ~-unknown₂ ∙ MSuHole ] ◃) +₁ (proj₁ (⊢⇒-⊢⇐ ě)))
      ESConIfC1 : ∀ {Γ τ u₁ u₂}
        → {ě : Γ ⊢⇒ τ}
        → (τ~bool : τ ~ bool)
        → Γ ⊢ ⊢▹ ě ◃ ~ construct (if₁ u₁ u₂) ~⇒ (⊢ (proj₁ (⊢⇒-⊢⇐ ě)) ∙₂ (⊢▹ ⊢⦇-⦈^ u₁ ◃) ∙ (⊢⦇-⦈^ u₂) [ TJUnknown ])
      ESConIfC2 : ∀ {Γ τ u₁ u₂}
        → {ě : Γ ⊢⇒ τ}
        → (τ~̸bool : τ ~̸ bool)
        → Γ ⊢ ⊢▹ ě ◃ ~ construct (if₁ u₁ u₂) ~⇒ (⊢ (proj₁ (⊢⇒-⊢⇐ ě)) ∙₂ (⊢▹ ⊢⦇-⦈^ u₁ ◃) ∙ (⊢⦇-⦈^ u₂) [ TJUnknown ])
      ESConIfL : ∀ {Γ τ u₁ u₂}
        → {ě : Γ ⊢⇒ τ}
        → Γ ⊢ ⊢▹ ě ◃ ~ construct (if₂ u₁ u₂) ~⇒ (⊢ (⊢▹ ⊢∙ ⊢⦇-⦈^ u₁ [ ~-unknown₂ ∙ MSuHole ] ◃) ∙₁ ě ∙ (⊢⦇-⦈^ u₂) [ ⊔-unknown₂ ])
      ESConIfR : ∀ {Γ τ u₁ u₂}
        → {ě : Γ ⊢⇒ τ}
        → Γ ⊢ ⊢▹ ě ◃ ~ construct (if₃ u₁ u₂) ~⇒ (⊢ (⊢▹ ⊢∙ ⊢⦇-⦈^ u₁ [ ~-unknown₂ ∙ MSuHole ] ◃) ∙₁ (⊢⦇-⦈^ u₂) ∙ ě [ ⊔-unknown₁ ])

      -- zipper cases
      ESZipLamT1 : ∀ {Γ x τ₁^ τ₁^′ τ₂ α}
        → {ě : Γ , x ∶ (τ₁^ ◇τ) ⊢⇒ τ₂}
        → (~>τ₁′ : τ₁^ ~ α ~τ> τ₁^′)
        → (τ₁^≡τ₁′ : (τ₁^ ◇τ) ≡ (τ₁^′ ◇τ))
        → Γ ⊢ (⊢λ₁ x ∶ τ₁^ ∙ ě) ~ α ~⇒ (⊢λ₁ x ∶ τ₁^′ ∙ proj₁ (◇≡-⊢⇒ {Γ} {x} {τ₁^} {τ₁^′} ě τ₁^≡τ₁′))
      ESZipLamT2 : ∀ {Γ x τ₁^ τ₁^′ τ₂ τ₂′ α}
        → {ě : Γ , x ∶ (τ₁^ ◇τ) ⊢⇒ τ₂}
        → {ě′ : Γ , x ∶ (τ₁^′ ◇τ) ⊢⇒ τ₂′}
        → (~>τ₁′ : τ₁^ ~ α ~τ> τ₁^′)
        → (τ₁^≢τ₁′ : (τ₁^ ◇τ) ≢ (τ₁^′ ◇τ))
        → (↬⇒ě′ : Γ , x ∶ (τ₁^′ ◇τ) ⊢ (ě ⇒□) ↬⇒ ě′)
        → Γ ⊢ (⊢λ₁ x ∶ τ₁^ ∙ ě) ~ α ~⇒ (⊢λ₁ x ∶ τ₁^′ ∙ ě′)
      ESZipLamE : ∀ {Γ x τ₁ τ₂ τ₂′ α}
        → {ê : - Γ , x ∶ τ₁ ⊢⇒ τ₂}
        → {ê′ : - Γ , x ∶ τ₁ ⊢⇒ τ₂′}
        → (~⇒ê′ : (Γ , x ∶ τ₁) ⊢ ê ~ α ~⇒ ê′)
        → Γ ⊢ (⊢λ₂ x ∶ τ₁ ∙ ê) ~ α ~⇒ (⊢λ₂ x ∶ τ₁ ∙ ê′)
      -- ESZipApL1 : ∀ {Γ τ τ₁ τ₂ τ₃ τ₁′ τ₂′ τ₃′ α}
        -- → {τ₁▸ : τ₁ ▸ τ₂ -→ τ₃}
        -- → (ê₁ : - Γ ⊢⇒ τ₁)
        -- → {ê₁′ : - Γ ⊢⇒ τ₁′}
        -- → {τ₁′▸ : τ₁′ ▸ τ₂′ -→ τ₃′}
        -- → {ě₂ : Γ ⊢⇐ τ₂}
        -- → Γ ⊢ ⊢ ê₁ ∙₁ ě₂ [ τ₁▸ ] ~ α ~⇒ ⊢ ê₁′ ∙₁ (proj₁ (⊢⇐-⊢⇐ ě₂)) [ τ₁′▸ ]

    -- analytic expression actions
    data _⊢_~_~⇐_ : ∀ {τ : Typ} → (Γ : Ctx) → (ê : - Γ ⊢⇐ τ) → (α : Action) → (ê : - Γ ⊢⇐ τ) → Set where
      -- movement
      EAMove : ∀ {Γ τ δ}
        → {ê : - Γ ⊢⇐ τ}
        → {ê′ : - Γ ⊢⇐ τ}
        → {ê+⇐ê′ : ê + δ +⇐ ê′}
        → Γ ⊢ ê ~ move δ ~⇐ ê′

      -- deletion
      EADel : ∀ {Γ τ u}
        → {ě : Γ ⊢⇐ τ}
        → Γ ⊢ ⊢▹ ě ◃ ~ del u ~⇐ ⊢▹ ⊢∙ ⊢⦇-⦈^ u [ ~-unknown₂ ∙ MSuHole ] ◃
