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
      ⊢_ : ∀ {Γ x τ}
        → (∋x : Γ ∋ x ∶ τ)
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
        → (τ!▸ : τ !▸-→)
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
        → (τ₁⊓τ₂ : τ₁ ⊓ τ₂ ⇒ τ)
        → Γ ⊢⇒ τ

      -- MSFree
      ⊢⟦_⟧ : ∀ {Γ y}
        → (∌y : Γ ∌ y)
        → Γ ⊢⇒ unknown

      -- MSInconsistentBranches
      ⊢⦉_∙_∙_⦊[_] : ∀ {Γ τ₁ τ₂}
        → (ě₁ : Γ ⊢⇐ bool)
        → (ě₂ : Γ ⊢⇒ τ₁)
        → (ě₃ : Γ ⊢⇒ τ₂)
        → (τ₁~̸τ₂ : τ₁ ~̸ τ₂)
        → Γ ⊢⇒ unknown

      -- MSPair
      ⊢⟨_,_⟩  : ∀ {Γ τ₁ τ₂}
        → (ě₁ : Γ ⊢⇒ τ₁)
        → (ě₂ : Γ ⊢⇒ τ₂)
        → Γ ⊢⇒ τ₁ -× τ₂

      -- MSProjL1
      ⊢π₁_[_] : ∀ {Γ τ τ₁ τ₂}
        → (ě : Γ ⊢⇒ τ)
        → (τ▸ : τ ▸ τ₁ -× τ₂)
        → Γ ⊢⇒ τ₁

      -- MSProjL2
      ⊢π₁⸨_⸩[_] : ∀ {Γ τ}
        → (ě : Γ ⊢⇒ τ)
        → (τ!▸ : τ !▸-×)
        → Γ ⊢⇒ unknown

      -- MSProjR1
      ⊢π₂_[_] : ∀ {Γ τ τ₁ τ₂}
        → (ě : Γ ⊢⇒ τ)
        → (τ▸ : τ ▸ τ₁ -× τ₂)
        → Γ ⊢⇒ τ₂

      -- MSProjL2
      ⊢π₂⸨_⸩[_] : ∀ {Γ τ}
        → (ě : Γ ⊢⇒ τ)
        → (τ!▸ : τ !▸-×)
        → Γ ⊢⇒ unknown

    data MSubsumable : {Γ : Ctx} {τ : Typ} → (ě : Γ ⊢⇒ τ) → Set where
      MSuHole : ∀ {Γ}
        → {u : Hole}
        → MSubsumable {Γ} (⊢⦇-⦈^ u)

      MSuVar : ∀ {Γ x τ}
        → {∋x : Γ ∋ x ∶ τ}
        → MSubsumable {Γ} (⊢ ∋x)

      MSuAp1 : ∀ {Γ τ τ₁ τ₂}
        → {ě₁ : Γ ⊢⇒ τ}
        → {ě₂ : Γ ⊢⇐ τ₁}
        → {τ▸ : τ ▸ τ₁ -→ τ₂}
        → MSubsumable {Γ} (⊢ ě₁ ∙ ě₂ [ τ▸ ])

      MSuAp2 : ∀ {Γ τ}
        → {ě₁ : Γ ⊢⇒ τ}
        → {ě₂ : Γ ⊢⇐ unknown}
        → {τ!▸ : τ !▸-→}
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

      MSuFree : ∀ {Γ y}
        → {∌y : Γ ∌ y}
        → MSubsumable {Γ} (⊢⟦ ∌y ⟧)

      MSuInconsistentBranches : ∀ {Γ τ₁ τ₂}
        → {ě₁ : Γ ⊢⇐ bool}
        → {ě₂ : Γ ⊢⇒ τ₁}
        → {ě₃ : Γ ⊢⇒ τ₂}
        → {τ₁~̸τ₂ : τ₁ ~̸ τ₂}
        → MSubsumable {Γ} (⊢⦉ ě₁ ∙ ě₂ ∙ ě₃ ⦊[ τ₁~̸τ₂ ])

      MSuProjL1 : ∀ {Γ τ τ₁ τ₂}
        → {ě : Γ ⊢⇒ τ}
        → {τ▸ : τ ▸ τ₁ -× τ₂}
        → MSubsumable {Γ} (⊢π₁ ě [ τ▸ ])

      MSuProjL2 : ∀ {Γ τ}
        → {ě : Γ ⊢⇒ τ}
        → {τ!▸ : τ !▸-×}
        → MSubsumable {Γ} (⊢π₁⸨ ě ⸩[ τ!▸ ])

      MSuProjR1 : ∀ {Γ τ τ₁ τ₂}
        → {ě : Γ ⊢⇒ τ}
        → {τ▸ : τ ▸ τ₁ -× τ₂}
        → MSubsumable {Γ} (⊢π₂ ě [ τ▸ ])

      MSuProjR2 : ∀ {Γ τ}
        → {ě : Γ ⊢⇒ τ}
        → {τ!▸ : τ !▸-×}
        → MSubsumable {Γ} (⊢π₂⸨ ě ⸩[ τ!▸ ])

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
        → (τ′!▸ : τ′ !▸-→)
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

      -- MAPair1
      ⊢⟨_,_⟩[_] : ∀ {Γ τ τ₁ τ₂}
        → (ě₁ : Γ ⊢⇐ τ₁)
        → (ě₂ : Γ ⊢⇐ τ₂)
        → (τ▸ : τ ▸ τ₁ -× τ₂)
        → Γ ⊢⇐ τ

      -- MAPair2
      ⊢⸨⟨_,_⟩⸩[_] : ∀ {Γ τ}
        → (ě₁ : Γ ⊢⇐ unknown)
        → (ě₂ : Γ ⊢⇐ unknown)
        → (τ!▸ : τ !▸-×)
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

  mutual
    data Markless⇒ : ∀ {Γ τ} → (ě : Γ ⊢⇒ τ) → Set where
      MLSHole : ∀ {Γ u}
        → Markless⇒ {Γ} (⊢⦇-⦈^ u)

      MLSVar : ∀ {Γ x τ}
        → {∋x : Γ ∋ x ∶ τ}
        → Markless⇒ {Γ} (⊢ ∋x)

      MLSLam : ∀ {Γ τ′ x τ}
        → {ě : Γ , x ∶ τ ⊢⇒ τ′}
        → (less : Markless⇒ ě)
        → Markless⇒ {Γ} (⊢λ x ∶ τ ∙ ě)

      MLSAp : ∀ {Γ τ τ₁ τ₂}
        → {ě₁ : Γ ⊢⇒ τ}
        → {ě₂ : Γ ⊢⇐ τ₁}
        → {τ▸ : τ ▸ τ₁ -→ τ₂}
        → (less₁ : Markless⇒ ě₁)
        → (less₂ : Markless⇐ ě₂)
        → Markless⇒ {Γ} (⊢ ě₁ ∙ ě₂ [ τ▸ ])

      MLSLet : ∀ {Γ τ₁ τ₂ x}
        → {ě₁ : Γ ⊢⇒ τ₁}
        → {ě₂ : Γ , x ∶ τ₁ ⊢⇒ τ₂}
        → (less₁ : Markless⇒ ě₁)
        → (less₂ : Markless⇒ ě₂)
        → Markless⇒ {Γ} (⊢ x ← ě₁ ∙ ě₂)

      MLSNum : ∀ {Γ n}
        → Markless⇒ {Γ} (⊢ℕ n)

      MLSPlus : ∀ {Γ}
        → {ě₁ : Γ ⊢⇐ num}
        → {ě₂ : Γ ⊢⇐ num}
        → (less₁ : Markless⇐ ě₁)
        → (less₂ : Markless⇐ ě₂)
        → Markless⇒ {Γ} (⊢ ě₁ + ě₂)

      MLSTrue : ∀ {Γ}
        → Markless⇒ {Γ} (⊢tt)

      MLSFalse : ∀ {Γ}
        → Markless⇒ {Γ} (⊢ff)

      MLSIf : ∀ {Γ τ₁ τ₂ τ}
        → {ě₁ : Γ ⊢⇐ bool}
        → {ě₂ : Γ ⊢⇒ τ₁}
        → {ě₃ : Γ ⊢⇒ τ₂}
        → {τ₁⊓τ₂ : τ₁ ⊓ τ₂ ⇒ τ}
        → (less₁ : Markless⇐ ě₁)
        → (less₂ : Markless⇒ ě₂)
        → (less₃ : Markless⇒ ě₃)
        → Markless⇒ {Γ} (⊢ ě₁ ∙ ě₂ ∙ ě₃ [ τ₁⊓τ₂ ])

      MLSPair : ∀ {Γ τ₁ τ₂}
        → {ě₁ : Γ ⊢⇒ τ₁}
        → {ě₂ : Γ ⊢⇒ τ₂}
        → (less₁ : Markless⇒ ě₁)
        → (less₂ : Markless⇒ ě₂)
        → Markless⇒ {Γ} (⊢⟨ ě₁ , ě₂ ⟩)

      MLSProjL : ∀ {Γ τ τ₁ τ₂}
        → {ě : Γ ⊢⇒ τ}
        → {τ▸ : τ ▸ τ₁ -× τ₂}
        → (less : Markless⇒ ě)
        → Markless⇒ {Γ} (⊢π₁ ě [ τ▸ ])

      MLSProjR : ∀ {Γ τ τ₁ τ₂}
        → {ě : Γ ⊢⇒ τ}
        → {τ▸ : τ ▸ τ₁ -× τ₂}
        → (less : Markless⇒ ě)
        → Markless⇒ {Γ} (⊢π₂ ě [ τ▸ ])

    data Markless⇐ : ∀ {Γ τ} → (ě : Γ ⊢⇐ τ) → Set where
      MLALam : ∀ {Γ τ₁ τ₂ τ₃ x τ}
        → {ě : Γ , x ∶ τ ⊢⇐ τ₂}
        → {τ₃▸ : τ₃ ▸ τ₁ -→ τ₂}
        → {τ~τ₁ : τ ~ τ₁}
        → (less : Markless⇐ ě)
        → Markless⇐ {Γ} (⊢λ x ∶ τ ∙ ě [ τ₃▸ ∙ τ~τ₁ ])

      -- MALet
      MLALet : ∀ {Γ τ₁ τ₂ x }
        → {ě₁ : Γ ⊢⇒ τ₁}
        → {ě₂ : Γ , x ∶ τ₁ ⊢⇐ τ₂}
        → (less₁ : Markless⇒ ě₁)
        → (less₂ : Markless⇐ ě₂)
        → Markless⇐ {Γ} (⊢ x ← ě₁ ∙ ě₂)

      -- MAIf
      MLAIf : ∀ {Γ τ}
        → {ě₁ : Γ ⊢⇐ bool}
        → {ě₂ : Γ ⊢⇐ τ}
        → {ě₃ : Γ ⊢⇐ τ}
        → (less₁ : Markless⇐ ě₁)
        → (less₂ : Markless⇐ ě₂)
        → (less₃ : Markless⇐ ě₃)
        → Markless⇐ {Γ} (⊢ ě₁ ∙ ě₂ ∙ ě₃)

      MLAPair : ∀ {Γ τ τ₁ τ₂}
        → {ě₁ : Γ ⊢⇐ τ₁}
        → {ě₂ : Γ ⊢⇐ τ₂}
        → {τ▸ : τ ▸ τ₁ -× τ₂}
        → (less₁ : Markless⇐ ě₁)
        → (less₂ : Markless⇐ ě₂)
        → Markless⇐ {Γ} (⊢⟨ ě₁ , ě₂ ⟩[ τ▸ ])

      MLASubsume : ∀ {Γ τ τ′}
        → {ě : Γ ⊢⇒ τ′}
        → {τ~τ′ : τ ~ τ′}
        → {su : MSubsumable ě}
        → (less : Markless⇒ ě)
        → Markless⇐ {Γ} (⊢∙ ě [ τ~τ′ ∙ su ])
