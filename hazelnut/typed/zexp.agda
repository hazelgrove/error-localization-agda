open import prelude
open import core

open import hazelnut.typed.ztyp

-- cursor expressions
module hazelnut.typed.zexp where
  -- zippered expressions
  mutual
    data -_⊢⇒_ : (Γ : Ctx) → (τ : Typ) → Set where
      ⊢▹_◃ : ∀ {Γ : Ctx} {τ}
        → (ě : Γ ⊢⇒ τ)
        → - Γ ⊢⇒ τ

      ⊢λ₁_∶_∙_ : ∀ {Γ τ}
        → (x : Var)
        → (τ^ : ZTyp)
        → (ě : Γ , x ∶ (τ^ ◇τ) ⊢⇒ τ)
        → - Γ ⊢⇒ ((τ^ ◇τ) -→ τ)

      ⊢λ₂_∶_∙_ : ∀ {Γ τ′}
        → (x : Var)
        → (τ : Typ)
        → (ê : - Γ , x ∶ τ ⊢⇒ τ′)
        → - Γ ⊢⇒ (τ -→ τ′)

      ⊢_∙₁_[_] : ∀ {Γ τ τ₁ τ₂}
        → (ê₁ : - Γ ⊢⇒ τ)
        → (ě₂ : Γ ⊢⇐ τ₁)
        → (τ▸ : τ ▸ τ₁ -→ τ₂)
        → - Γ ⊢⇒ τ₂

      ⊢_∙₂_[_] : ∀ {Γ τ τ₁ τ₂}
        → (ě₁ : Γ ⊢⇒ τ)
        → (ê₂ : - Γ ⊢⇐ τ₁)
        → (τ▸ : τ ▸ τ₁ -→ τ₂)
        → - Γ ⊢⇒ τ₂

      ⊢⸨_⸩∙₁_[_] : ∀ {Γ τ}
        → (ê₁ : - Γ ⊢⇒ τ)
        → (ě₂ : Γ ⊢⇐ unknown)
        → (τ!▸ : τ !▸)
        → - Γ ⊢⇒ unknown

      ⊢⸨_⸩∙₂_[_] : ∀ {Γ τ}
        → (ě₁ : Γ ⊢⇒ τ)
        → (ê₂ : - Γ ⊢⇐ unknown)
        → (τ!▸ : τ !▸)
        → - Γ ⊢⇒ unknown

      ⊢_←₁_∙_ : ∀ {Γ τ₁ τ₂}
        → (x : Var)
        → (ê₁ : - Γ ⊢⇒ τ₁)
        → (ě₂ : Γ , x ∶ τ₁ ⊢⇒ τ₂)
        → - Γ ⊢⇒ τ₂

      ⊢_←₂_∙_ : ∀ {Γ τ₁ τ₂}
        → (x : Var)
        → (ě₁ : Γ ⊢⇒ τ₁)
        → (ê₂ : - Γ , x ∶ τ₁ ⊢⇒ τ₂)
        → - Γ ⊢⇒ τ₂

      ⊢_+₁_ : ∀ {Γ}
        → (ê₁ : - Γ ⊢⇐ num)
        → (ě₂ : Γ ⊢⇐ num)
        → - Γ ⊢⇒ num

      ⊢_+₂_ : ∀ {Γ}
        → (ě₁ : Γ ⊢⇐ num)
        → (ê₂ : - Γ ⊢⇐ num)
        → - Γ ⊢⇒ num

      ⊢_∙₁_∙_[_] : ∀ {Γ τ₁ τ₂ τ}
        → (ê₁ : - Γ ⊢⇐ bool)
        → (ě₂ : Γ ⊢⇒ τ₁)
        → (ě₃ : Γ ⊢⇒ τ₂)
        → (τ₁⊔τ₂ : τ₁ ⊔ τ₂ ⇒ τ)
        → - Γ ⊢⇒ τ

      ⊢_∙₂_∙_[_] : ∀ {Γ τ₁ τ₂ τ}
        → (ě₁ : Γ ⊢⇐ bool)
        → (ê₂ : - Γ ⊢⇒ τ₁)
        → (ě₃ : Γ ⊢⇒ τ₂)
        → (τ₁⊔τ₂ : τ₁ ⊔ τ₂ ⇒ τ)
        → - Γ ⊢⇒ τ

      ⊢_∙₃_∙_[_] : ∀ {Γ τ₁ τ₂ τ}
        → (ě₁ : Γ ⊢⇐ bool)
        → (ě₂ : Γ ⊢⇒ τ₁)
        → (ê₃ : - Γ ⊢⇒ τ₂)
        → (τ₁⊔τ₂ : τ₁ ⊔ τ₂ ⇒ τ)
        → - Γ ⊢⇒ τ

      ⊢⦉_∙₁_∙_⦊[_] : ∀ {Γ τ₁ τ₂}
        → (ê₁ : - Γ ⊢⇐ bool)
        → (ě₂ : Γ ⊢⇒ τ₁)
        → (ě₃ : Γ ⊢⇒ τ₂)
        → (τ₁~̸τ₂ : τ₁ ~̸ τ₂)
        → - Γ ⊢⇒ unknown

      ⊢⦉_∙₂_∙_⦊[_] : ∀ {Γ τ₁ τ₂}
        → (ě₁ : Γ ⊢⇐ bool)
        → (ê₂ : - Γ ⊢⇒ τ₁)
        → (ě₃ : Γ ⊢⇒ τ₂)
        → (τ₁~̸τ₂ : τ₁ ~̸ τ₂)
        → - Γ ⊢⇒ unknown

      ⊢⦉_∙₃_∙_⦊[_] : ∀ {Γ τ₁ τ₂}
        → (ě₁ : Γ ⊢⇐ bool)
        → (ě₂ : Γ ⊢⇒ τ₁)
        → (ê₃ : - Γ ⊢⇒ τ₂)
        → (τ₁~̸τ₂ : τ₁ ~̸ τ₂)
        → - Γ ⊢⇒ unknown

    data ZSubsumable : {Γ : Ctx} {τ : Typ} → (ê : - Γ ⊢⇒ τ) → Set where
      ZSuCursor : ∀ {Γ τ}
        → {ě : Γ ⊢⇒ τ}
        → (su : MSubsumable ě)
        → ZSubsumable {Γ} (⊢▹ ě ◃)

      ZSuZipApL1 : ∀ {Γ τ τ₁ τ₂}
        → {ê₁ : - Γ ⊢⇒ τ}
        → {ě₂ : Γ ⊢⇐ τ₁}
        → {τ▸ : τ ▸ τ₁ -→ τ₂}
        → ZSubsumable {Γ} (⊢ ê₁ ∙₁ ě₂ [ τ▸ ])

      ZSuZipApR1 : ∀ {Γ τ τ₁ τ₂}
        → {ě₁ : Γ ⊢⇒ τ}
        → {ê₂ : - Γ ⊢⇐ τ₁}
        → {τ▸ : τ ▸ τ₁ -→ τ₂}
        → ZSubsumable {Γ} (⊢ ě₁ ∙₂ ê₂ [ τ▸ ])

      ZSuZipApL2 : ∀ {Γ τ}
        → {ê₁ : - Γ ⊢⇒ τ}
        → {ě₂ : Γ ⊢⇐ unknown}
        → {τ!▸ : τ !▸}
        → ZSubsumable {Γ} (⊢⸨ ê₁ ⸩∙₁ ě₂ [ τ!▸ ])

      ZSuZipApR2 : ∀ {Γ τ}
        → {ě₁ : Γ ⊢⇒ τ}
        → {ê₂ : - Γ ⊢⇐ unknown}
        → {τ!▸ : τ !▸}
        → ZSubsumable {Γ} (⊢⸨ ě₁ ⸩∙₂ ê₂ [ τ!▸ ])

      ZSuPlus1 : ∀ {Γ}
        → {ê₁ : - Γ ⊢⇐ num}
        → {ě₂ : Γ ⊢⇐ num}
        → ZSubsumable {Γ} (⊢ ê₁ +₁ ě₂)

      ZSuPlus2 : ∀ {Γ}
        → {ě₁ : Γ ⊢⇐ num}
        → {ê₂ : - Γ ⊢⇐ num}
        → ZSubsumable {Γ} (⊢ ě₁ +₂ ê₂)

      ZSuInconsistentBranchesC : ∀ {Γ τ₁ τ₂}
        → {ê₁ : - Γ ⊢⇐ bool}
        → {ě₂ : Γ ⊢⇒ τ₁}
        → {ě₃ : Γ ⊢⇒ τ₂}
        → {τ₁~̸τ₂ : τ₁ ~̸ τ₂}
        → ZSubsumable {Γ} (⊢⦉ ê₁ ∙₁ ě₂ ∙ ě₃ ⦊[ τ₁~̸τ₂ ])

      ZSuInconsistentBranchesL : ∀ {Γ τ₁ τ₂}
        → {ě₁ : Γ ⊢⇐ bool}
        → {ê₂ : - Γ ⊢⇒ τ₁}
        → {ě₃ : Γ ⊢⇒ τ₂}
        → {τ₁~̸τ₂ : τ₁ ~̸ τ₂}
        → ZSubsumable {Γ} (⊢⦉ ě₁ ∙₂ ê₂ ∙ ě₃ ⦊[ τ₁~̸τ₂ ])

      ZSuInconsistentBranchesR : ∀ {Γ τ₁ τ₂}
        → {ě₁ : Γ ⊢⇐ bool}
        → {ě₂ : Γ ⊢⇒ τ₁}
        → {ê₃ : - Γ ⊢⇒ τ₂}
        → {τ₁~̸τ₂ : τ₁ ~̸ τ₂}
        → ZSubsumable {Γ} (⊢⦉ ě₁ ∙₃ ě₂ ∙ ê₃ ⦊[ τ₁~̸τ₂ ])

    data -_⊢⇐_ : (Γ : Ctx) → (τ : Typ) → Set where
      ⊢▹_◃ : ∀ {Γ : Ctx} {τ}
        → (ě : Γ ⊢⇐ τ)
        → - Γ ⊢⇐ τ

      ⊢λ₁_∶_∙_[_∙_] : ∀ {Γ τ₁ τ₂ τ₃}
        → (x : Var)
        → (τ^ : ZTyp)
        → (ě : Γ , x ∶ (τ^ ◇τ) ⊢⇐ τ₂)
        → (τ₃▸ : τ₃ ▸ τ₁ -→ τ₂)
        → (τ~τ₁ : (τ^ ◇τ) ~ τ₁)
        → - Γ ⊢⇐ τ₃

      ⊢λ₂_∶_∙_[_∙_] : ∀ {Γ τ₁ τ₂ τ₃}
        → (x : Var)
        → (τ : Typ)
        → (ê : - Γ , x ∶ τ ⊢⇐ τ₂)
        → (τ₃▸ : τ₃ ▸ τ₁ -→ τ₂)
        → (τ~τ₁ : τ ~ τ₁)
        → - Γ ⊢⇐ τ₃

      ⊢⸨λ₁_∶_∙_⸩[_] : ∀ {Γ τ′}
        → (x : Var)
        → (τ^ : ZTyp)
        → (ě : Γ , x ∶ (τ^ ◇τ) ⊢⇐ unknown)
        → (τ′!▸ : τ′ !▸)
        → - Γ ⊢⇐ τ′

      ⊢⸨λ₂_∶_∙_⸩[_] : ∀ {Γ τ′}
        → (x : Var)
        → (τ : Typ)
        → (ê : - Γ , x ∶ τ ⊢⇐ unknown)
        → (τ′!▸ : τ′ !▸)
        → - Γ ⊢⇐ τ′

      ⊢λ₁_∶⸨_⸩∙_[_∙_] : ∀ {Γ τ₁ τ₂ τ₃}
        → (x : Var)
        → (τ^ : ZTyp)
        → (ě : Γ , x ∶ (τ^ ◇τ) ⊢⇐ τ₂)
        → (τ₃▸ : τ₃ ▸ τ₁ -→ τ₂)
        → (τ~̸τ₁ : (τ^ ◇τ) ~̸ τ₁)
        → - Γ ⊢⇐ τ₃

      ⊢λ₂_∶⸨_⸩∙_[_∙_] : ∀ {Γ τ₁ τ₂ τ₃}
        → (x : Var)
        → (τ : Typ)
        → (ê : - Γ , x ∶ τ ⊢⇐ τ₂)
        → (τ₃▸ : τ₃ ▸ τ₁ -→ τ₂)
        → (τ~̸τ₁ : τ ~̸ τ₁)
        → - Γ ⊢⇐ τ₃

      ⊢_←₁_∙_ : ∀ {Γ τ₁ τ₂}
        → (x : Var)
        → (ê₁ : - Γ ⊢⇒ τ₁)
        → (ě₂ : Γ , x ∶ τ₁ ⊢⇐ τ₂)
        → - Γ ⊢⇐ τ₂

      ⊢_←₂_∙_ : ∀ {Γ τ₁ τ₂}
        → (x : Var)
        → (ě₁ : Γ ⊢⇒ τ₁)
        → (ê₂ : - Γ , x ∶ τ₁ ⊢⇐ τ₂)
        → - Γ ⊢⇐ τ₂

      ⊢_∙₁_∙_ : ∀ {Γ τ}
        → (ê₁ : - Γ ⊢⇐ bool)
        → (ě₂ : Γ ⊢⇐ τ)
        → (ě₃ : Γ ⊢⇐ τ)
        → - Γ ⊢⇐ τ

      ⊢_∙₂_∙_ : ∀ {Γ τ}
        → (ě₁ : Γ ⊢⇐ bool)
        → (ê₂ : - Γ ⊢⇐ τ)
        → (ě₃ : Γ ⊢⇐ τ)
        → - Γ ⊢⇐ τ

      ⊢_∙₃_∙_ : ∀ {Γ τ}
        → (ě₁ : Γ ⊢⇐ bool)
        → (ě₂ : Γ ⊢⇐ τ)
        → (ê₃ : - Γ ⊢⇐ τ)
        → - Γ ⊢⇐ τ

      ⊢⸨_⸩[_∙_] : ∀ {Γ τ τ′}
        → (ê : - Γ ⊢⇒ τ′)
        → (τ~̸τ′ : τ ~̸ τ′)
        → (zsu : ZSubsumable ê)
        → - Γ ⊢⇐ τ

      ⊢∙_[_∙_] : ∀ {Γ τ τ′}
        → (ê : - Γ ⊢⇒ τ′)
        → (τ~τ′ : τ ~ τ′)
        → (zsu : ZSubsumable ê)
        → - Γ ⊢⇐ τ

  -- well-formedness judgments
  mutual
    data _WF⇒ : ∀ {Γ τ} → (ê : - Γ ⊢⇒ τ) → Set where
      WFCursor : ∀ {Γ : Ctx} {τ}
        → {ě : Γ ⊢⇒ τ}
        → ⊢▹ ě ◃ WF⇒

      WFLamT : ∀ {Γ x τ}
        → {τ^ : ZTyp}
        → {ě : Γ , x ∶ (τ^ ◇τ) ⊢⇒ τ}
        → (⊢λ₁ x ∶ τ^ ∙ ě) WF⇒

      WFLamE : ∀ {Γ  x τ′}
        → {τ : Typ}
        → {ê : - Γ , x ∶ τ ⊢⇒ τ′}
        → (wf : ê WF⇒)
        → (⊢λ₂ x ∶ τ ∙ ê) WF⇒

      WFApL1 : ∀ {Γ τ τ₁ τ₂}
        → {ê₁ : - Γ ⊢⇒ τ}
        → {ě₂ : Γ ⊢⇐ τ₁}
        → {τ▸ : τ ▸ τ₁ -→ τ₂}
        → (wf : ê₁ WF⇒)
        → ⊢ ê₁ ∙₁ ě₂ [ τ▸ ] WF⇒

      WFApR1 : ∀ {Γ τ τ₁ τ₂}
        → {ě₁ : Γ ⊢⇒ τ}
        → {ê₂ : - Γ ⊢⇐ τ₁}
        → {τ▸ : τ ▸ τ₁ -→ τ₂}
        → (wf : ê₂ WF⇐)
        → ⊢ ě₁ ∙₂ ê₂ [ τ▸ ] WF⇒

      WFApL2 : ∀ {Γ τ}
        → {ê₁ : - Γ ⊢⇒ τ}
        → {ě₂ : Γ ⊢⇐ unknown}
        → {τ!▸ : τ !▸}
        → (wf : ê₁ WF⇒)
        → ⊢⸨ ê₁ ⸩∙₁ ě₂ [ τ!▸ ] WF⇒

      WFApR2 : ∀ {Γ τ}
        → {ě₁ : Γ ⊢⇒ τ}
        → {ê₂ : - Γ ⊢⇐ unknown}
        → {τ!▸ : τ !▸}
        → (wf : ê₂ WF⇐)
        → ⊢⸨ ě₁ ⸩∙₂ ê₂ [ τ!▸ ] WF⇒

      WFLetL : ∀ {Γ x τ₁ τ₂}
        → {ê₁ : - Γ ⊢⇒ τ₁}
        → {ě₂ : Γ , x ∶ τ₁ ⊢⇒ τ₂}
        → (wf : ê₁ WF⇒)
        → (⊢ x ←₁ ê₁ ∙ ě₂) WF⇒

      WFLetR : ∀ {Γ x τ₁ τ₂}
        → {ě₁ : Γ ⊢⇒ τ₁}
        → {ê₂ : - Γ , x ∶ τ₁ ⊢⇒ τ₂}
        → (wf : ê₂ WF⇒)
        → (⊢ x ←₂ ě₁ ∙ ê₂) WF⇒

      WFPlusL : ∀ {Γ}
        → {ê₁ : - Γ ⊢⇐ num}
        → {ě₂ : Γ ⊢⇐ num}
        → (wf : ê₁ WF⇐)
        → (⊢ ê₁ +₁ ě₂) WF⇒

      WFPlusR : ∀ {Γ}
        → {ě₁ : Γ ⊢⇐ num}
        → {ê₂ : - Γ ⊢⇐ num}
        → (wf : ê₂ WF⇐)
        → (⊢ ě₁ +₂ ê₂) WF⇒

      WFIfC : ∀ {Γ τ₁ τ₂ τ}
        → {ê₁ : - Γ ⊢⇐ bool}
        → {ě₂ : Γ ⊢⇒ τ₁}
        → {ě₃ : Γ ⊢⇒ τ₂}
        → {τ₁⊔τ₂ : τ₁ ⊔ τ₂ ⇒ τ}
        → (wf : ê₁ WF⇐)
        → ⊢ ê₁ ∙₁ ě₂ ∙ ě₃ [ τ₁⊔τ₂ ] WF⇒

      WFIfL : ∀ {Γ τ₁ τ₂ τ}
        → {ě₁ : Γ ⊢⇐ bool}
        → {ê₂ : - Γ ⊢⇒ τ₁}
        → {ě₃ : Γ ⊢⇒ τ₂}
        → {τ₁⊔τ₂ : τ₁ ⊔ τ₂ ⇒ τ}
        → (wf : ê₂ WF⇒)
        → ⊢ ě₁ ∙₂ ê₂ ∙ ě₃ [ τ₁⊔τ₂ ] WF⇒

      WFIfR : ∀ {Γ τ₁ τ₂ τ}
        → {ě₁ : Γ ⊢⇐ bool}
        → {ě₂ : Γ ⊢⇒ τ₁}
        → {ê₃ : - Γ ⊢⇒ τ₂}
        → {τ₁⊔τ₂ : τ₁ ⊔ τ₂ ⇒ τ}
        → (wf : ê₃ WF⇒)
        → ⊢ ě₁ ∙₃ ě₂ ∙ ê₃ [ τ₁⊔τ₂ ] WF⇒

      WFInconsistentBranchesC : ∀ {Γ τ₁ τ₂}
        → {ê₁ : - Γ ⊢⇐ bool}
        → {ě₂ : Γ ⊢⇒ τ₁}
        → {ě₃ : Γ ⊢⇒ τ₂}
        → {τ₁~̸τ₂ : τ₁ ~̸ τ₂}
        → (wf : ê₁ WF⇐)
        → ⊢⦉ ê₁ ∙₁ ě₂ ∙ ě₃ ⦊[ τ₁~̸τ₂ ] WF⇒

      WFInconsistentBranchesL : ∀ {Γ τ₁ τ₂}
        → {ě₁ : Γ ⊢⇐ bool}
        → {ê₂ : - Γ ⊢⇒ τ₁}
        → {ě₃ : Γ ⊢⇒ τ₂}
        → {τ₁~̸τ₂ : τ₁ ~̸ τ₂}
        → (wf : ê₂ WF⇒)
        → ⊢⦉ ě₁ ∙₂ ê₂ ∙ ě₃ ⦊[ τ₁~̸τ₂ ] WF⇒

      WFInconsistentBranchesR : ∀ {Γ τ₁ τ₂}
        → {ě₁ : Γ ⊢⇐ bool}
        → {ě₂ : Γ ⊢⇒ τ₁}
        → {ê₃ : - Γ ⊢⇒ τ₂}
        → {τ₁~̸τ₂ : τ₁ ~̸ τ₂}
        → (wf : ê₃ WF⇒)
        → ⊢⦉ ě₁ ∙₃ ě₂ ∙ ê₃ ⦊[ τ₁~̸τ₂ ] WF⇒

    data _WF⇐ : ∀ {Γ τ} → (ê : - Γ ⊢⇐ τ) → Set where
      WFCursor : ∀ {Γ : Ctx} {τ}
        → {ě : Γ ⊢⇐ τ}
        → ⊢▹ ě ◃ WF⇐

      WFLamT1 : ∀ {Γ  x τ₁ τ₂ τ₃}
        → {τ^ : ZTyp}
        → {ě : Γ , x ∶ (τ^ ◇τ) ⊢⇐ τ₂}
        → {τ₃▸ : τ₃ ▸ τ₁ -→ τ₂}
        → {τ~τ₁ : (τ^ ◇τ) ~ τ₁}
        → ⊢λ₁ x ∶ τ^ ∙ ě [ τ₃▸ ∙ τ~τ₁ ] WF⇐

      WFLamE1 : ∀ {Γ x τ₁ τ₂ τ₃}
        → {τ : Typ}
        → {ê : - Γ , x ∶ τ ⊢⇐ τ₂}
        → {τ₃▸ : τ₃ ▸ τ₁ -→ τ₂}
        → {τ~τ₁ : τ ~ τ₁}
        → (wf : ê WF⇐)
        → ⊢λ₂ x ∶ τ ∙ ê [ τ₃▸ ∙ τ~τ₁ ] WF⇐

      WFLamT2 : ∀ {Γ x τ′}
        → {τ^ : ZTyp}
        → {ě : Γ , x ∶ (τ^ ◇τ) ⊢⇐ unknown}
        → {τ′!▸ : τ′ !▸}
        → ⊢⸨λ₁ x ∶ τ^ ∙ ě ⸩[ τ′!▸ ] WF⇐

      WFLamE2 : ∀ {Γ x τ′}
        → {τ : Typ}
        → {ê : - Γ , x ∶ τ ⊢⇐ unknown}
        → {τ′!▸ : τ′ !▸}
        → (wf : ê WF⇐)
        → ⊢⸨λ₂ x ∶ τ ∙ ê ⸩[ τ′!▸ ] WF⇐

      WFLamT3 : ∀ {Γ x τ₁ τ₂ τ₃}
        → {τ^ : ZTyp}
        → {ě : Γ , x ∶ (τ^ ◇τ) ⊢⇐ τ₂}
        → {τ₃▸ : τ₃ ▸ τ₁ -→ τ₂}
        → {τ~̸τ₁ : (τ^ ◇τ) ~̸ τ₁}
        → ⊢λ₁ x ∶⸨ τ^ ⸩∙ ě [ τ₃▸ ∙ τ~̸τ₁ ] WF⇐

      WFLamE3 : ∀ {Γ x τ₁ τ₂ τ₃}
        → {τ : Typ}
        → {ê : - Γ , x ∶ τ ⊢⇐ τ₂}
        → {τ₃▸ : τ₃ ▸ τ₁ -→ τ₂}
        → {τ~̸τ₁ : τ ~̸ τ₁}
        → (wf : ê WF⇐)
        → ⊢λ₂ x ∶⸨ τ ⸩∙ ê [ τ₃▸ ∙ τ~̸τ₁ ] WF⇐

      WFLetL : ∀ {Γ x τ₁ τ₂}
        → {ê₁ : - Γ ⊢⇒ τ₁}
        → {ě₂ : Γ , x ∶ τ₁ ⊢⇐ τ₂}
        → (wf : ê₁ WF⇒)
        → (⊢ x ←₁ ê₁ ∙ ě₂) WF⇐

      WFLetR : ∀ {Γ x τ₁ τ₂}
        → {ě₁ : Γ ⊢⇒ τ₁}
        → {ê₂ : - Γ , x ∶ τ₁ ⊢⇐ τ₂}
        → (wf : ê₂ WF⇐)
        → (⊢ x ←₂ ě₁ ∙ ê₂) WF⇐

      WFIfC : ∀ {Γ τ}
        → {ê₁ : - Γ ⊢⇐ bool}
        → {ě₂ : Γ ⊢⇐ τ}
        → {ě₃ : Γ ⊢⇐ τ}
        → (wf : ê₁ WF⇐)
        → (⊢ ê₁ ∙₁ ě₂ ∙ ě₃) WF⇐

      WFIfL : ∀ {Γ τ}
        → {ě₁ : Γ ⊢⇐ bool}
        → {ê₂ : - Γ ⊢⇐ τ}
        → {ě₃ : Γ ⊢⇐ τ}
        → (wf : ê₂ WF⇐)
        → (⊢ ě₁ ∙₂ ê₂ ∙ ě₃) WF⇐

      WFIfR : ∀ {Γ τ}
        → {ě₁ : Γ ⊢⇐ bool}
        → {ě₂ : Γ ⊢⇐ τ}
        → {ê₃ : - Γ ⊢⇐ τ}
        → (wf : ê₃ WF⇐)
        → (⊢ ě₁ ∙₃ ě₂ ∙ ê₃) WF⇐

      WFInconsistentTypes : ∀ {Γ τ τ′}
        → {ê : - Γ ⊢⇒ τ′}
        → {τ~̸τ′ : τ ~̸ τ′}
        → {zsu : ZSubsumable ê}
        → (wf : ê WF⇒)
        → (nc : ¬ (∃[ ě ] ê ≡ ⊢▹ ě ◃))
        → ⊢⸨ ê ⸩[ τ~̸τ′ ∙ zsu ] WF⇐

      WFSubsume : ∀ {Γ τ τ′}
        → {ê : - Γ ⊢⇒ τ′}
        → {τ~τ′ : τ ~ τ′}
        → {zsu : ZSubsumable ê}
        → (wf : ê WF⇒)
        → ⊢∙ ê [ τ~τ′ ∙ zsu ] WF⇐

  -- well-formedness decidability
  is-cursor? : ∀ {Γ τ} → (ê : - Γ ⊢⇒ τ) → Dec (∃[ ě ] ê ≡ ⊢▹ ě ◃)
  is-cursor? ⊢▹ ě ◃                      = yes ⟨ ě , refl ⟩
  is-cursor? (⊢λ₁ x ∶ τ^ ∙ ě)            = no λ()
  is-cursor? (⊢λ₂ x ∶ τ ∙ ê)             = no λ()
  is-cursor? ⊢ ê ∙₁ ě₂ [ τ▸ ]            = no λ()
  is-cursor? ⊢ ě₁ ∙₂ ê₂ [ τ▸ ]           = no λ()
  is-cursor? ⊢⸨ ê ⸩∙₁ ě₂ [ τ!▸ ]         = no λ()
  is-cursor? ⊢⸨ ě₁ ⸩∙₂ ê₂ [ τ!▸ ]        = no λ()
  is-cursor? (⊢ x ←₁ ê ∙ ě₂)             = no λ()
  is-cursor? (⊢ x ←₂ ě₁ ∙ ê₂)            = no λ()
  is-cursor? (⊢ ê₁ +₁ ě₂)                = no λ()
  is-cursor? (⊢ ě₁ +₂ ê₂)                = no λ()
  is-cursor? ⊢ ê₁ ∙₁ ě₂ ∙ ě₃ [ τ₁⊔τ₂ ]   = no λ()
  is-cursor? ⊢ ě₁ ∙₂ ê₂ ∙ ě₃ [ τ₁⊔τ₂ ]   = no λ()
  is-cursor? ⊢ ě₁ ∙₃ ě₂ ∙ ê₃ [ τ₁⊔τ₂ ]   = no λ()
  is-cursor? ⊢⦉ ê₁ ∙₁ ě₂ ∙ ě₃ ⦊[ τ₁~̸τ₂ ] = no λ()
  is-cursor? ⊢⦉ ě₁ ∙₂ ê₂ ∙ ě₃ ⦊[ τ₁~̸τ₂ ] = no λ()
  is-cursor? ⊢⦉ ě₁ ∙₃ ě₂ ∙ ê₃ ⦊[ τ₁~̸τ₂ ] = no λ()

  mutual
    _WF⇒? : ∀ {Γ τ} → (ê : - Γ ⊢⇒ τ) → Dec (ê WF⇒)
    ⊢▹ ě ◃ WF⇒? = yes WFCursor
    (⊢λ₁ x ∶ τ^ ∙ ě) WF⇒? = yes WFLamT
    (⊢λ₂ x ∶ τ ∙ ê) WF⇒?
      with ê WF⇒?
    ...  | yes wf = yes (WFLamE wf)
    ...  | no !wf = no λ { (WFLamE wf) → !wf wf }
    ⊢ ê₁ ∙₁ ě₂ [ τ▸ ] WF⇒?
      with ê₁ WF⇒?
    ...  | yes wf = yes (WFApL1 wf)
    ...  | no !wf = no λ { (WFApL1 wf) → !wf wf }
    ⊢ ě₁ ∙₂ ê₂ [ τ▸ ] WF⇒?
      with ê₂ WF⇐?
    ...  | yes wf = yes (WFApR1 wf)
    ...  | no !wf = no λ { (WFApR1 wf) → !wf wf }
    ⊢⸨ ê₁ ⸩∙₁ ě₂ [ τ!▸ ] WF⇒?
      with ê₁ WF⇒?
    ...  | yes wf = yes (WFApL2 wf)
    ...  | no !wf = no λ { (WFApL2 wf) → !wf wf }
    ⊢⸨ ě₁ ⸩∙₂ ê₂ [ τ!▸ ] WF⇒?
      with ê₂ WF⇐?
    ...  | yes wf = yes (WFApR2 wf)
    ...  | no !wf = no λ { (WFApR2 wf) → !wf wf }
    (⊢ x ←₁ ê₁ ∙ ě₂) WF⇒?
      with ê₁ WF⇒?
    ...  | yes wf = yes (WFLetL wf)
    ...  | no !wf = no λ { (WFLetL wf) → !wf wf }
    (⊢ x ←₂ ě₁ ∙ ê₂) WF⇒?
      with ê₂ WF⇒?
    ...  | yes wf = yes (WFLetR wf)
    ...  | no !wf = no λ { (WFLetR wf) → !wf wf }
    (⊢ ê₁ +₁ ě₂) WF⇒?
      with ê₁ WF⇐?
    ...  | yes wf = yes (WFPlusL wf)
    ...  | no !wf = no λ { (WFPlusL wf) → !wf wf }
    (⊢ ě₁ +₂ ê₂) WF⇒?
      with ê₂ WF⇐?
    ...  | yes wf = yes (WFPlusR wf)
    ...  | no !wf = no λ { (WFPlusR wf) → !wf wf }
    ⊢ ê₁ ∙₁ ě₂ ∙ ě₃ [ τ₁⊔τ₂ ] WF⇒?
      with ê₁ WF⇐?
    ...  | yes wf = yes (WFIfC wf)
    ...  | no !wf = no λ { (WFIfC wf) → !wf wf }
    ⊢ ě₁ ∙₂ ê₂ ∙ ě₃ [ τ₁⊔τ₂ ] WF⇒?
      with ê₂ WF⇒?
    ...  | yes wf = yes (WFIfL wf)
    ...  | no !wf = no λ { (WFIfL wf) → !wf wf }
    ⊢ ě₁ ∙₃ ě₂ ∙ ê₃ [ τ₁⊔τ₂ ] WF⇒?
      with ê₃ WF⇒?
    ...  | yes wf = yes (WFIfR wf)
    ...  | no !wf = no λ { (WFIfR wf) → !wf wf }
    ⊢⦉ ê₁ ∙₁ ě₂ ∙ ě₃ ⦊[ τ₁~̸τ₂ ] WF⇒?
      with ê₁ WF⇐?
    ...  | yes wf = yes (WFInconsistentBranchesC wf)
    ...  | no !wf = no λ { (WFInconsistentBranchesC wf) → !wf wf }
    ⊢⦉ ě₁ ∙₂ ê₂ ∙ ě₃ ⦊[ τ₁~̸τ₂ ] WF⇒?
      with ê₂ WF⇒?
    ...  | yes wf = yes (WFInconsistentBranchesL wf)
    ...  | no !wf = no λ { (WFInconsistentBranchesL wf) → !wf wf }
    ⊢⦉ ě₁ ∙₃ ě₂ ∙ ê₃ ⦊[ τ₁~̸τ₂ ] WF⇒?
      with ê₃ WF⇒?
    ...  | yes wf = yes (WFInconsistentBranchesR wf)
    ...  | no !wf = no λ { (WFInconsistentBranchesR wf) → !wf wf }

    _WF⇐? : ∀ {Γ τ} → (ê : - Γ ⊢⇐ τ) → Dec (ê WF⇐)
    ⊢▹ ě ◃ WF⇐? = yes WFCursor
    ⊢λ₁ x ∶ τ^ ∙ ě [ τ₃▸ ∙ τ~τ₁ ] WF⇐? = yes WFLamT1
    ⊢λ₂ x ∶ τ ∙ ê [ τ₃▸ ∙ τ~τ₁ ] WF⇐?
      with ê WF⇐?
    ...  | yes wf = yes (WFLamE1 wf)
    ...  | no !wf = no λ { (WFLamE1 wf) → !wf wf }
    ⊢⸨λ₁ x ∶ τ^ ∙ ě ⸩[ τ′!▸ ] WF⇐? = yes WFLamT2
    ⊢⸨λ₂ x ∶ τ ∙ ê ⸩[ τ′!▸ ] WF⇐?
      with ê WF⇐?
    ...  | yes wf = yes (WFLamE2 wf)
    ...  | no !wf = no λ { (WFLamE2 wf) → !wf wf }
    ⊢λ₁ x ∶⸨ τ^ ⸩∙ ě [ τ₃▸ ∙ τ~̸τ₁ ] WF⇐? = yes WFLamT3
    ⊢λ₂ x ∶⸨ τ ⸩∙ ê [ τ₃▸ ∙ τ~̸τ₁ ] WF⇐?
      with ê WF⇐?
    ...  | yes wf = yes (WFLamE3 wf)
    ...  | no !wf = no λ { (WFLamE3 wf) → !wf wf }
    (⊢ x ←₁ ê₁ ∙ ě₂) WF⇐?
      with ê₁ WF⇒?
    ...  | yes wf = yes (WFLetL wf)
    ...  | no !wf = no λ { (WFLetL wf) → !wf wf }
    (⊢ x ←₂ ě₁ ∙ ê₂) WF⇐?
      with ê₂ WF⇐?
    ...  | yes wf = yes (WFLetR wf)
    ...  | no !wf = no λ { (WFLetR wf) → !wf wf }
    (⊢ ê₁ ∙₁ ě₂ ∙ ě₃) WF⇐?
      with ê₁ WF⇐?
    ...  | yes wf = yes (WFIfC wf)
    ...  | no !wf = no λ { (WFIfC wf) → !wf wf }
    (⊢ ě₁ ∙₂ ê₂ ∙ ě₃) WF⇐?
      with ê₂ WF⇐?
    ...  | yes wf = yes (WFIfL wf)
    ...  | no !wf = no λ { (WFIfL wf) → !wf wf }
    (⊢ ě₁ ∙₃ ě₂ ∙ ê₃) WF⇐?
      with ê₃ WF⇐?
    ...  | yes wf = yes (WFIfR wf)
    ...  | no !wf = no λ { (WFIfR wf) → !wf wf }
    ⊢⸨ ê ⸩[ τ~̸τ′ ∙ zsu ] WF⇐?
      with ê WF⇒?
    ...  | no !wf = no λ { (WFInconsistentTypes wf nc) → !wf wf }
    ...  | yes wf with is-cursor? ê
    ...              | yes ic = no λ { (WFInconsistentTypes wf nc) → nc ic }
    ...              | no  nc = yes (WFInconsistentTypes wf nc)
    ⊢∙ ê [ τ~τ′ ∙ zsu ] WF⇐?
      with ê WF⇒?
    ...  | yes wf = yes (WFSubsume wf)
    ...  | no !wf = no λ { (WFSubsume wf) → !wf wf }

  -- functional cursor erasure
  mutual
    _◇⇒ : ∀ {Γ τ} → (ê : - Γ ⊢⇒ τ) → Γ ⊢⇒ τ
    ⊢▹ ě ◃ ◇⇒ = ě
    (⊢λ₁ x ∶ τ^ ∙ ě)           ◇⇒ = ⊢λ x ∶ (τ^ ◇τ) ∙ ě
    (⊢λ₂ x ∶ τ ∙ ê)            ◇⇒ = ⊢λ x ∶ τ ∙ (ê ◇⇒)
    (⊢ ê ∙₁ ě [ τ▸ ])             ◇⇒ = ⊢ (ê ◇⇒) ∙ ě [ τ▸ ]
    (⊢ ě ∙₂ ê [ τ▸ ])             ◇⇒ = ⊢ ě ∙ (ê ◇⇐) [ τ▸ ]
    (⊢⸨ ê ⸩∙₁ ě [ τ!▸ ])          ◇⇒ = ⊢⸨ (ê ◇⇒) ⸩∙ ě [ τ!▸ ]
    (⊢⸨ ě ⸩∙₂ ê [ τ!▸ ])          ◇⇒ = ⊢⸨ ě ⸩∙ (ê ◇⇐) [ τ!▸ ]
    (⊢ x ←₁ ê ∙ ě)             ◇⇒ = ⊢ x ← (ê ◇⇒) ∙ ě
    (⊢ x ←₂ ě ∙ ê)             ◇⇒ = ⊢ x ← ě ∙ (ê ◇⇒)
    (⊢ ê +₁ ě)                    ◇⇒ = ⊢ (ê ◇⇐) + ě
    (⊢ ě +₂ ê)                    ◇⇒ = ⊢ ě + (ê ◇⇐)
    (⊢ ê ∙₁ ě₂ ∙ ě₃ [ τ₁⊔τ₂ ])    ◇⇒ = ⊢ (ê ◇⇐) ∙ ě₂ ∙ ě₃ [ τ₁⊔τ₂ ]
    (⊢ ě₁ ∙₂ ê ∙ ě₃ [ τ₁⊔τ₂ ])    ◇⇒ = ⊢ ě₁ ∙ (ê ◇⇒) ∙ ě₃ [ τ₁⊔τ₂ ]
    (⊢ ě₁ ∙₃ ě₂ ∙ ê₃ [ τ₁⊔τ₂ ])   ◇⇒ = ⊢ ě₁ ∙ ě₂ ∙ (ê₃ ◇⇒) [ τ₁⊔τ₂ ]
    (⊢⦉ ê₁ ∙₁ ě₂ ∙ ě₃ ⦊[ τ₁~̸τ₂ ]) ◇⇒ = ⊢⦉ (ê₁ ◇⇐) ∙ ě₂ ∙ ě₃ ⦊[ τ₁~̸τ₂ ]
    (⊢⦉ ě₁ ∙₂ ê₂ ∙ ě₃ ⦊[ τ₁~̸τ₂ ]) ◇⇒ = ⊢⦉ ě₁ ∙ (ê₂ ◇⇒) ∙ ě₃ ⦊[ τ₁~̸τ₂ ]
    (⊢⦉ ě₁ ∙₃ ě₂ ∙ ê₃ ⦊[ τ₁~̸τ₂ ]) ◇⇒ = ⊢⦉ ě₁ ∙ ě₂ ∙ (ê₃ ◇⇒) ⦊[ τ₁~̸τ₂ ]

    ZSu→MSu : ∀ {Γ τ} {ê : - Γ ⊢⇒ τ} → (zsu : ZSubsumable ê) → MSubsumable (ê ◇⇒)
    ZSu→MSu (ZSuCursor su) = su
    ZSu→MSu ZSuZipApL1 = MSuAp1
    ZSu→MSu ZSuZipApR1 = MSuAp1
    ZSu→MSu ZSuZipApL2 = MSuAp2
    ZSu→MSu ZSuZipApR2 = MSuAp2
    ZSu→MSu ZSuPlus1 = MSuPlus
    ZSu→MSu ZSuPlus2 = MSuPlus
    ZSu→MSu ZSuInconsistentBranchesC = MSuInconsistentBranches
    ZSu→MSu ZSuInconsistentBranchesL = MSuInconsistentBranches
    ZSu→MSu ZSuInconsistentBranchesR = MSuInconsistentBranches

    _◇⇐ : ∀ {Γ τ} → (ê : - Γ ⊢⇐ τ) → Γ ⊢⇐ τ
    ⊢▹ ě ◃ ◇⇐ = ě
    ⊢λ₁ x ∶ τ^ ∙ ě [ τ₃▸ ∙ τ~τ₁ ] ◇⇐ = ⊢λ x ∶ (τ^ ◇τ) ∙ ě [ τ₃▸ ∙ τ~τ₁ ]
    ⊢λ₂ x ∶ τ ∙ ê [ τ₃▸ ∙ τ~τ₁ ] ◇⇐ = ⊢λ x ∶ τ ∙ (ê ◇⇐) [ τ₃▸ ∙ τ~τ₁ ]
    ⊢⸨λ₁ x ∶ τ^ ∙ ě ⸩[ τ′!▸ ] ◇⇐ = ⊢⸨λ x ∶ (τ^ ◇τ) ∙ ě ⸩[ τ′!▸ ]
    ⊢⸨λ₂ x ∶ τ ∙ ê ⸩[ τ′!▸ ] ◇⇐ = ⊢⸨λ x ∶ τ ∙ (ê ◇⇐) ⸩[ τ′!▸ ]
    ⊢λ₁ x ∶⸨ τ^ ⸩∙ ě [ τ₃▸ ∙ τ~̸τ₁ ] ◇⇐ = ⊢λ x ∶⸨ τ^ ◇τ ⸩∙ ě [ τ₃▸ ∙ τ~̸τ₁ ]
    ⊢λ₂ x ∶⸨ τ ⸩∙ ê [ τ₃▸ ∙ τ~̸τ₁ ] ◇⇐ = ⊢λ x ∶⸨ τ ⸩∙ (ê ◇⇐) [ τ₃▸ ∙ τ~̸τ₁ ]
    (⊢ x ←₁ ê₁ ∙ ě₂) ◇⇐ = ⊢ x ← (ê₁ ◇⇒) ∙ ě₂
    (⊢ x ←₂ ě₁ ∙ ê₂) ◇⇐ = ⊢ x ← ě₁ ∙ (ê₂ ◇⇐)
    (⊢ ê₁ ∙₁ ě₂ ∙ ě₃) ◇⇐ = ⊢ (ê₁ ◇⇐) ∙ ě₂ ∙ ě₃
    (⊢ ě₁ ∙₂ ê₂ ∙ ě₃) ◇⇐ = ⊢ ě₁ ∙ (ê₂ ◇⇐) ∙ ě₃
    (⊢ ě₁ ∙₃ ě₂ ∙ ê₃) ◇⇐ = ⊢ ě₁ ∙ ě₂ ∙ (ê₃ ◇⇐)
    ⊢⸨ ê ⸩[ τ~̸τ′ ∙ zsu ] ◇⇐ = ⊢⸨ ê ◇⇒ ⸩[ τ~̸τ′ ∙ (ZSu→MSu zsu) ]
    ⊢∙ ê [ τ~τ′ ∙ zsu ] ◇⇐ = ⊢∙ (ê ◇⇒) [ τ~τ′ ∙ (ZSu→MSu zsu) ]

  ◇≡-⊢⇒ : ∀ {Γ x τ^ τ^′ τ} → (ě : Γ , x ∶ (τ^ ◇τ) ⊢⇒ τ) → (τ^ ◇τ) ≡ (τ^′ ◇τ) → Σ[ ě′ ∈ Γ , x ∶ (τ^′ ◇τ) ⊢⇒ τ ] (ě ⇒□) ≡ (ě′ ⇒□)
  ◇≡-⊢⇒ ě eq rewrite eq = ⟨ ě , refl ⟩