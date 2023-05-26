open import prelude

open import core.typ
open import core.var
open import core.ctx

open import patterned.ptyp

module patterned.mpat where
  infix  4 _⊢ₚ⇒_
  infix  4 _⊢ₚ⇐_⊣_

  mutual
    -- synthesis
    data _⊢ₚ⇒_ : (Γ : Ctx) (τ : PTyp) → Set where
      -- MSPWild
      ⊢- : ∀ {Γ}
        → Γ ⊢ₚ⇒ uswitch

      -- MSPVar
      ⊢_ : ∀ {Γ}
        → (x : Var)
        → Γ ⊢ₚ⇒ uswitch

      -- MSPPair
      ⊢⟨_,_⟩ : ∀ {Γ τ₁ τ₂}
        → (ṗ₁ : Γ ⊢ₚ⇒ τ₁)
        → (ṗ₂ : Γ ⊢ₚ⇒ τ₂)
        → Γ ⊢ₚ⇒ τ₁ -× τ₂

      -- MSPAnn
      ⊢_∶_ : ∀ {Γ Γ′}
        → (τ : Typ)
        → (ṗ : Γ ⊢ₚ⇐ τ ⊣ Γ′)
        → Γ ⊢ₚ⇒ Typ→PTyp τ

    -- analysis
    data _⊢ₚ⇐_⊣_ : (Γ : Ctx) (τ : Typ) (Γ′ : Ctx) → Set where
      -- MAPWild
      ⊢- : ∀ {Γ τ}
        → Γ ⊢ₚ⇐ τ ⊣ Γ

      -- MAPVar
      ⊢_ : ∀ {Γ τ}
        → (x : Var)
        → Γ ⊢ₚ⇐ τ ⊣ (Γ , x ∶ τ)

      -- MAPPair1
      ⊢⟨_,_⟩[_] : ∀ {Γ Γ₁ Γ₂ τ τ₁ τ₂}
        → (ṗ₁ : Γ ⊢ₚ⇐ τ₁ ⊣ Γ₁)
        → (ṗ₂ : Γ₁ ⊢ₚ⇐ τ₂ ⊣ Γ₂)
        → (τ▸ : τ ▸ τ₁ -× τ₂)
        → Γ ⊢ₚ⇐ τ ⊣ Γ₂

      -- MAPPair2
      ⊢⸨⟨_,_⟩⸩[_] : ∀ {Γ Γ₁ Γ₂ τ}
        → (ṗ₁ : Γ ⊢ₚ⇐ unknown ⊣ Γ₁)
        → (ṗ₂ : Γ₁ ⊢ₚ⇐ unknown ⊣ Γ₂)
        → (τ!▸ : τ !▸-×)
        → Γ ⊢ₚ⇐ τ ⊣ Γ₂

      -- MAPAnn1
      ⊢_∶_[_] : ∀ {Γ Γ′ τ}
        → (τ′ : Typ)
        → (ṗ : Γ ⊢ₚ⇐ τ′ ⊣ Γ′)
        → (τ~τ′ : τ ~ τ′)
        → Γ ⊢ₚ⇐ τ ⊣ Γ′

      -- MAPAnn2
      ⊢⸨_∶_⸩[_] : ∀ {Γ Γ′ τ}
        → (τ′ : Typ)
        → (ṗ : Γ ⊢ₚ⇐ τ′ ⊣ Γ′)
        → (τ~̸τ′ : τ ~̸ τ′)
        → Γ ⊢ₚ⇐ τ ⊣ Γ′
