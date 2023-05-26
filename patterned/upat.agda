open import prelude

open import core.typ
open import core.var
open import core.ctx

open import patterned.ptyp

-- unmarked patterns
module patterned.upat where
  infix  4 _⊢ₚ_⇒_
  infix  4 _⊢ₚ_⇐_⊣_

  data UPat : Set where
    ‵-      : UPat
    ‵_      : (x : Var) → UPat
    ‵⟨_,_⟩  : (p₁ : UPat) → (p₂ : UPat) → UPat
    ‵_∶_    : (p : UPat) → (τ : Typ) → UPat

  mutual
    -- synthesis
    data _⊢ₚ_⇒_ : (Γ : Ctx) (p : UPat) (τ : PTyp) → Set where
      USPWild : ∀ {Γ}
        → Γ ⊢ₚ ‵- ⇒ uswitch

      USPVar : ∀ {Γ x}
        → Γ ⊢ₚ ‵ x ⇒ uswitch 

      USPPair : ∀ {Γ p₁ p₂ τ₁ τ₂}
        → (p₁⇒τ₁ : Γ ⊢ₚ p₁ ⇒ τ₁)
        → (p₂⇒τ₂ : Γ ⊢ₚ p₂ ⇒ τ₂)
        → Γ ⊢ₚ ‵⟨ p₁ , p₂ ⟩ ⇒ τ₁ -× τ₂

      USPAnn : ∀ {Γ p τ Γ′}
        → (p⇐τ : Γ ⊢ₚ p ⇐ τ ⊣ Γ′)
        → Γ ⊢ₚ ‵ p ∶ τ ⇒ (Typ→PTyp τ)

    -- analysis
    data _⊢ₚ_⇐_⊣_ : (Γ : Ctx) (p : UPat) (τ : Typ) (Γ′ : Ctx) → Set where
      UAPWild : ∀ {Γ τ}
        → Γ ⊢ₚ ‵- ⇐ τ ⊣ Γ

      UAPVar : ∀ {Γ x τ}
        → (∋x : Γ ∋ x ∶ τ)
        → Γ ⊢ₚ ‵ x ⇐ τ ⊣ (Γ , x ∶ τ)

      UAPPair : ∀ {Γ Γ₁ Γ₂ p₁ p₂ τ τ₁ τ₂}
        → (p₁⇐τ₁ : Γ ⊢ₚ p₁ ⇐ τ₁ ⊣ Γ₁)
        → (p₂⇐τ₂ : Γ₁ ⊢ₚ p₂ ⇐ τ₁ ⊣ Γ₂)
        → (τ▸ : τ ▸ τ₁ -× τ₂)
        → Γ ⊢ₚ ‵⟨ p₁ , p₂ ⟩ ⇐ τ ⊣ Γ₂

      UAPAnn : ∀ {Γ p τ′ τ Γ′}
        → (p⇐τ′ : Γ ⊢ₚ p ⇐ τ′ ⊣ Γ′)
        → (τ~τ′ : τ ~ τ′)
        → Γ ⊢ₚ ‵ p ∶ τ′ ⇐ τ ⊣ Γ′
