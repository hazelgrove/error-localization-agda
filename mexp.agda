open import prelude
open import typ

-- instrinsically typed marked expressions
module mexp where
  infix  4 _⊢⇒_
  infix  4 _⊢⇐_
  infix  4 _∋_
  infixl 5 _,_

  -- variables
  FreeVar : Set
  FreeVar = ℕ

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
        → ℕ
        → Γ ⊢⇒ unknown

      -- MSVar
      ⊢_ : ∀ {Γ τ}
        → Γ ∋ τ
        → Γ ⊢⇒ τ

      -- MSLam
      ⊢λ∶_∙_ : ∀ {Γ τ₂}
        → (τ₁ : Typ)
        → Γ , τ₁ ⊢⇒ τ₂
        → Γ ⊢⇒ τ₁ -→ τ₂

      -- MSAp1
      ⊢_∙_[_] : ∀ {Γ τ τ₁ τ₂}
        → Γ ⊢⇒ τ
        → Γ ⊢⇐ τ₁
        → τ ▸ τ₁ -→ τ₂
        → Γ ⊢⇒ τ₂

      -- MSAp2
      ⊢⸨_⸩∙_[_] : ∀ {Γ τ}
        → Γ ⊢⇒ τ
        → Γ ⊢⇐ unknown
        → τ !▸
        → Γ ⊢⇒ unknown

      -- MSNum
      ⊢ℕ_ : ∀ {Γ}
        → ℕ
        → Γ ⊢⇒ num

      -- MSPlus
      ⊢_+_ : ∀ {Γ}
        → Γ ⊢⇐ num
        → Γ ⊢⇐ num
        → Γ ⊢⇒ num

      -- MSTrue
      ⊢tt : ∀ {Γ}
        → Γ ⊢⇒ bool

      -- MSFalse
      ⊢ff : ∀ {Γ}
        → Γ ⊢⇒ bool

      -- MSIf
      ⊢_∙_∙_[_]  : ∀ {Γ τ₁ τ₂ τ}
        → Γ ⊢⇐ bool
        → Γ ⊢⇒ τ₁
        → Γ ⊢⇒ τ₂
        → τ₁ ⊔ τ₂ ⇒ τ
        → Γ ⊢⇒ τ

      -- MSUnbound
      ⊢⟦_⟧ : ∀ {Γ}
        → FreeVar
        → Γ ⊢⇒ unknown

      -- MSInconsistentBranches
      ⊢⦉_∙_∙_⦊[_] : ∀ {Γ τ₁ τ₂}
        → Γ ⊢⇐ bool
        → Γ ⊢⇒ τ₁
        → Γ ⊢⇒ τ₂
        → τ₁ ~̸ τ₂
        → Γ ⊢⇒ unknown

    data Subsumable : {Γ : Ctx} {τ : Typ} → (ě : Γ ⊢⇒ τ) → Set where
      SuHole : ∀ {Γ}
        → {u : ℕ}
        → Subsumable {Γ} (⊢⦇-⦈^ u)

      SuVar : ∀ {Γ τ}
        → {∋x : Γ ∋ τ}
        → Subsumable {Γ} (⊢ ∋x)

      SuAp1 : ∀ {Γ τ τ₁ τ₂}
        → {ě₁ : Γ ⊢⇒ τ}
        → {ě₂ : Γ ⊢⇐ τ₁}
        → {τ▸ : τ ▸ τ₁ -→ τ₂}
        → Subsumable {Γ} (⊢ ě₁ ∙ ě₂ [ τ▸ ])

      SuAp2 : ∀ {Γ τ}
        → {ě₁ : Γ ⊢⇒ τ}
        → {ě₂ : Γ ⊢⇐ unknown}
        → {τ!▸ : τ !▸}
        → Subsumable {Γ} (⊢⸨ ě₁ ⸩∙ ě₂ [ τ!▸ ])

      SuNum : ∀ {Γ}
        → {n : ℕ}
        → Subsumable {Γ} (⊢ℕ n)

      SuPlus : ∀ {Γ}
        → {ě₁ : Γ ⊢⇐ num}
        → {ě₂ : Γ ⊢⇐ num}
        → Subsumable {Γ} (⊢ ě₁ + ě₂)

      SuTrue : ∀ {Γ}
        → Subsumable {Γ} (⊢tt)

      SuFalse : ∀ {Γ}
        → Subsumable {Γ} (⊢ff)

      SuUnbound : ∀ {Γ}
        → {x : FreeVar}
        → Subsumable {Γ} (⊢⟦ x ⟧)

      SuInconsistentBranches : ∀ {Γ τ₁ τ₂}
        → {ě₁ : Γ ⊢⇐ bool}
        → {ě₂ : Γ ⊢⇒ τ₁}
        → {ě₃ : Γ ⊢⇒ τ₂}
        → {τ₁~̸τ₂ : τ₁ ~̸ τ₂}
        → Subsumable {Γ} (⊢⦉ ě₁ ∙ ě₂ ∙ ě₃ ⦊[ τ₁~̸τ₂ ])

    -- analysis
    data _⊢⇐_ : (Γ : Ctx) (τ : Typ) → Set where
      -- MALam1
      ⊢λ∶_∙_[_∙_] : ∀ {Γ τ₁ τ₂ τ₃}
        → (τ : Typ)
        → Γ , τ ⊢⇐ τ₂
        → τ₃ ▸ τ₁ -→ τ₂
        → τ ~ τ₁
        → Γ ⊢⇐ τ₃

      -- MALam2
      ⊢⸨λ∶_∙_⸩[_] : ∀ {Γ τ′}
        → (τ : Typ)
        → Γ , τ ⊢⇐ unknown
        → τ′ !▸
        → Γ ⊢⇐ τ′

      -- MALam3
      ⊢λ∶⸨_⸩∙_[_∙_] : ∀ {Γ τ₁ τ₂ τ₃}
        → (τ : Typ)
        → Γ , τ ⊢⇐ τ₂
        → τ₃ ▸ τ₁ -→ τ₂
        → τ ~̸ τ₁
        → Γ ⊢⇐ τ₃

      -- MAIf
      ⊢_∙_∙_ : ∀ {Γ τ}
        → Γ ⊢⇐ bool
        → Γ ⊢⇐ τ
        → Γ ⊢⇐ τ
        → Γ ⊢⇐ τ

      -- MAInconsistentTypes
      ⊢⸨_⸩[_∙_] : ∀ {Γ τ τ′}
        → (ě : Γ ⊢⇒ τ′)
        → τ ~̸ τ′
        → Subsumable ě
        → Γ ⊢⇐ τ

      -- MASubsume
      ⊢∙_[_∙_] : ∀ {Γ τ τ′}
        → (ě : Γ ⊢⇒ τ′)
        → τ ~ τ′
        → Subsumable ě
        → Γ ⊢⇐ τ
