open import prelude

open import core.typ
open import core.hole
open import core.var
open import core.ctx

-- instrinsically typed marked expressions
module core.mexp where
  infix  4 _⊢⇒_
  infix  4 _⊢⇐_

  mutual
    -- synthesis
    data _⊢⇒_ : (Γ : Ctx) (τ : Typ) → Set where
      -- MSHole
      ⊢⦇-⦈^_ : ∀ {Γ}
        → (u : Hole)
        → Γ ⊢⇒ unknown

      -- MSVar
      ⊢_[_] : ∀ {Γ x τ}
        → (∋x : Γ ∋ x ∶ τ)
        → (x : Var)
        → Γ ⊢⇒ τ

      -- MSLam
      ⊢λ_∶_∙_ : ∀ {Γ τ′}
        → (x : Var)
        → (τ : Typ)
        → (ě : Γ , x ∶ τ ⊢⇒ τ′)
        → Γ ⊢⇒ τ -→ τ′

      -- MSAp1
      ⊢_∙_[_] : ∀ {Γ τ τ₁ τ₂}
        → (ě₁ : Γ ⊢⇒ τ)
        → (ě₂ : Γ ⊢⇐ τ₁)
        → (τ▸ : τ ▸ τ₁ -→ τ₂)
        → Γ ⊢⇒ τ₂

      -- MSAp2
      ⊢⸨_⸩∙_[_] : ∀ {Γ τ}
        → (ě₁ : Γ ⊢⇒ τ)
        → (ě₂ : Γ ⊢⇐ unknown)
        → (τ!▸ : τ !▸)
        → Γ ⊢⇒ unknown

      -- MSLet
      ⊢_←_∙_ : ∀ {Γ τ₁ τ₂}
        → (x : Var)
        → (ě₁ : Γ ⊢⇒ τ₁)
        → (ě₂ : Γ , x ∶ τ₁ ⊢⇒ τ₂)
        → Γ ⊢⇒ τ₂

      -- MSNum
      ⊢ℕ_ : ∀ {Γ}
        → (n : ℕ)
        → Γ ⊢⇒ num

      -- MSPlus
      ⊢_+_ : ∀ {Γ}
        → (ě₁ : Γ ⊢⇐ num)
        → (ě₂ : Γ ⊢⇐ num)
        → Γ ⊢⇒ num

      -- MSTrue
      ⊢tt : ∀ {Γ}
        → Γ ⊢⇒ bool

      -- MSFalse
      ⊢ff : ∀ {Γ}
        → Γ ⊢⇒ bool

      -- MSIf
      ⊢_∙_∙_[_]  : ∀ {Γ τ₁ τ₂ τ}
        → (ě₁ : Γ ⊢⇐ bool)
        → (ě₂ : Γ ⊢⇒ τ₁)
        → (ě₃ : Γ ⊢⇒ τ₂)
        → (τ₁⊔τ₂ : τ₁ ⊔ τ₂ ⇒ τ)
        → Γ ⊢⇒ τ

      -- MSUnbound
      -- TODO Enforce that y is unboudnd in Γ
      ⊢⟦_⟧ : ∀ {Γ}
        → (y : FreeVar)
        → Γ ⊢⇒ unknown

      -- MSInconsistentBranches
      ⊢⦉_∙_∙_⦊[_] : ∀ {Γ τ₁ τ₂}
        → (ě₁ : Γ ⊢⇐ bool)
        → (ě₂ : Γ ⊢⇒ τ₁)
        → (ě₃ : Γ ⊢⇒ τ₂)
        → (τ₁~̸τ₂ : τ₁ ~̸ τ₂)
        → Γ ⊢⇒ unknown

    data MSubsumable : {Γ : Ctx} {τ : Typ} → (ě : Γ ⊢⇒ τ) → Set where
      MSuHole : ∀ {Γ}
        → {u : Hole}
        → MSubsumable {Γ} (⊢⦇-⦈^ u)

      MSuVar : ∀ {Γ x τ}
        → {∋x : Γ ∋ x ∶ τ}
        → {x : Var}
        → MSubsumable {Γ} (⊢ ∋x [ x ])

      MSuAp1 : ∀ {Γ τ τ₁ τ₂}
        → {ě₁ : Γ ⊢⇒ τ}
        → {ě₂ : Γ ⊢⇐ τ₁}
        → {τ▸ : τ ▸ τ₁ -→ τ₂}
        → MSubsumable {Γ} (⊢ ě₁ ∙ ě₂ [ τ▸ ])

      MSuAp2 : ∀ {Γ τ}
        → {ě₁ : Γ ⊢⇒ τ}
        → {ě₂ : Γ ⊢⇐ unknown}
        → {τ!▸ : τ !▸}
        → MSubsumable {Γ} (⊢⸨ ě₁ ⸩∙ ě₂ [ τ!▸ ])

      MSuNum : ∀ {Γ}
        → {n : ℕ}
        → MSubsumable {Γ} (⊢ℕ n)

      MSuPlus : ∀ {Γ}
        → {ě₁ : Γ ⊢⇐ num}
        → {ě₂ : Γ ⊢⇐ num}
        → MSubsumable {Γ} (⊢ ě₁ + ě₂)

      MSuTrue : ∀ {Γ}
        → MSubsumable {Γ} (⊢tt)

      MSuFalse : ∀ {Γ}
        → MSubsumable {Γ} (⊢ff)

      MSuUnbound : ∀ {Γ}
        → {x : FreeVar}
        → MSubsumable {Γ} (⊢⟦ x ⟧)

      MSuInconsistentBranches : ∀ {Γ τ₁ τ₂}
        → {ě₁ : Γ ⊢⇐ bool}
        → {ě₂ : Γ ⊢⇒ τ₁}
        → {ě₃ : Γ ⊢⇒ τ₂}
        → {τ₁~̸τ₂ : τ₁ ~̸ τ₂}
        → MSubsumable {Γ} (⊢⦉ ě₁ ∙ ě₂ ∙ ě₃ ⦊[ τ₁~̸τ₂ ])

    -- analysis
    data _⊢⇐_ : (Γ : Ctx) (τ : Typ) → Set where
      -- MALam1
      ⊢λ_∶_∙_[_∙_] : ∀ {Γ τ₁ τ₂ τ₃}
        → (x : Var)
        → (τ : Typ)
        → (ě : Γ , x ∶ τ ⊢⇐ τ₂)
        → (τ₃▸ : τ₃ ▸ τ₁ -→ τ₂)
        → (τ~τ₁ : τ ~ τ₁)
        → Γ ⊢⇐ τ₃

      -- MALam2
      ⊢⸨λ_∶_∙_⸩[_] : ∀ {Γ τ′}
        → (x : Var)
        → (τ : Typ)
        → (ě : Γ , x ∶ τ ⊢⇐ unknown)
        → (τ′!▸ : τ′ !▸)
        → Γ ⊢⇐ τ′

      -- MALam3
      ⊢λ_∶⸨_⸩∙_[_∙_] : ∀ {Γ τ₁ τ₂ τ₃}
        → (x : Var)
        → (τ : Typ)
        → (ě : Γ , x ∶ τ ⊢⇐ τ₂)
        → (τ₃▸ : τ₃ ▸ τ₁ -→ τ₂)
        → (τ~̸τ₁ : τ ~̸ τ₁)
        → Γ ⊢⇐ τ₃

      -- MALet
      ⊢_←_∙_ : ∀ {Γ τ₁ τ₂}
        → (x : Var)
        → (ě₁ : Γ ⊢⇒ τ₁)
        → (ě₂ : Γ , x ∶ τ₁ ⊢⇐ τ₂)
        → Γ ⊢⇐ τ₂

      -- MAIf
      ⊢_∙_∙_ : ∀ {Γ τ}
        → (ě₁ : Γ ⊢⇐ bool)
        → (ě₂ : Γ ⊢⇐ τ)
        → (ě₃ : Γ ⊢⇐ τ)
        → Γ ⊢⇐ τ

      -- MAInconsistentTypes
      ⊢⸨_⸩[_∙_] : ∀ {Γ τ τ′}
        → (ě : Γ ⊢⇒ τ′)
        → (τ~̸τ′ : τ ~̸ τ′)
        → (su : MSubsumable ě)
        → Γ ⊢⇐ τ

      -- MAMSubsume
      ⊢∙_[_∙_] : ∀ {Γ τ τ′}
        → (ě : Γ ⊢⇒ τ′)
        → (τ~τ′ : τ ~ τ′)
        → (su : MSubsumable ě)
        → Γ ⊢⇐ τ
