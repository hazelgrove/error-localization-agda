open import prelude

open import core.typ
open import core.hole
open import core.var

-- instrinsically typed marked expressions
module core.mexp where
  infix  4 _⊢⇒_
  infix  4 _⊢⇐_
  infix  4 _∋_
  infixl 5 _,_

  data Ctx : Set where
    ∅   : Ctx
    _,_ : Ctx → Typ → Ctx

  data _∋_ : (Γ : Ctx) (τ : Typ) → Set where
    Z  : ∀ {Γ τ}            → Γ , τ  ∋ τ
    S  : ∀ {Γ τ τ′} → Γ ∋ τ → Γ , τ′ ∋ τ

  mutual
    -- synthesis
    data _⊢⇒_ : (Γ : Ctx) (τ : Typ) → Set where
      -- MSHole
      ⊢⦇-⦈^_ : ∀ {Γ}
        → (u : Hole)
        → Γ ⊢⇒ unknown

      -- MSVar
      ⊢_[_] : ∀ {Γ τ}
        → (∋x : Γ ∋ τ)
        → (x : Var)
        → Γ ⊢⇒ τ

      -- MSLam
      ⊢λ∶_∙_[_] : ∀ {Γ τ′}
        → (τ : Typ)
        → (ě : Γ , τ ⊢⇒ τ′)
        → (x : Var)
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
      ⊢←_∙_[_] : ∀ {Γ τ₁ τ₂}
        → (ě₁ : Γ ⊢⇒ τ₁)
        → (ě₂ : Γ , τ₁ ⊢⇒ τ₂)
        → (x : Var)
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

      MSuVar : ∀ {Γ τ}
        → {∋x : Γ ∋ τ}
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
      ⊢λ∶_∙_[_∙_∙_] : ∀ {Γ τ₁ τ₂ τ₃}
        → (τ : Typ)
        → (ě : Γ , τ ⊢⇐ τ₂)
        → (τ₃▸ : τ₃ ▸ τ₁ -→ τ₂)
        → (τ~τ₁ : τ ~ τ₁)
        → (x : Var)
        → Γ ⊢⇐ τ₃

      -- MALam2
      ⊢⸨λ∶_∙_⸩[_∙_] : ∀ {Γ τ′}
        → (τ : Typ)
        → (ě : Γ , τ ⊢⇐ unknown)
        → (τ′!▸ : τ′ !▸)
        → (x : Var)
        → Γ ⊢⇐ τ′

      -- MALam3
      ⊢λ∶⸨_⸩∙_[_∙_∙_] : ∀ {Γ τ₁ τ₂ τ₃}
        → (τ : Typ)
        → (ě : Γ , τ ⊢⇐ τ₂)
        → (τ₃▸ : τ₃ ▸ τ₁ -→ τ₂)
        → (τ~̸τ₁ : τ ~̸ τ₁)
        → (x : Var)
        → Γ ⊢⇐ τ₃

      -- MALet
      ⊢←_∙_[_] : ∀ {Γ τ₁ τ₂}
        → (ě₁ : Γ ⊢⇒ τ₁)
        → (ě₂ : Γ , τ₁ ⊢⇐ τ₂)
        → (x : Var)
        → Γ ⊢⇐ τ₂

      -- MAIf
      ⊢_∙_∙_ : ∀ {Γ τ}
        → (ě₁ : Γ ⊢⇐ bool)
        → (ě₂ : Γ ⊢⇐ τ)
        → (ě₂ : Γ ⊢⇐ τ)
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
