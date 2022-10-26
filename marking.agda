open import prelude
open import typ
open import uexp renaming (Ctx to UCtx)
open import mexp renaming (Ctx to MCtx)

module marking where
  infix 4 _⊢_↬⇒_
  infix 4 _⊢_↬⇐_

  -- context conversion
  ctx : ∀ (Γ : UCtx) → MCtx
  ctx ∅ = ∅
  ctx (Γ , _ ∶ τ) = (ctx Γ) , τ

  ctx∋ : ∀ {Γ x τ} → Γ ∋ x ∶ τ → (ctx Γ) ∋ τ
  ctx∋ Z = Z
  ctx∋ (S x ∋x) = S (ctx∋ ∋x)

  -- mark insertion
  mutual
    -- synthesis
    data _⊢_↬⇒_ : {τ : Typ} (Γ : UCtx) → (e : UExp) → ((ctx Γ) ⊢⇒ τ) → Set where
      ISHole : ∀ {Γ u}
        → Γ ⊢ ‵⦇-⦈^ u ↬⇒ ⊢⦇-⦈^ u

      ISVar : ∀ {Γ x τ}
        → (∋x : Γ ∋ x ∶ τ)
        → Γ ⊢ ‵ x ↬⇒ ⊢ (ctx∋ ∋x)

      ISUnbound : ∀ {Γ x}
        → Γ ∌ x
        → Γ ⊢ ‵ x ↬⇒ ⊢⟦ x ⟧

      ISLam : ∀ {Γ x τ e τ₁}
        → {ě : (ctx (Γ , x ∶ τ)) ⊢⇒ τ₁}
        → Γ , x ∶ τ ⊢ e ↬⇒ ě
        → Γ ⊢ ‵λ x ∶ τ ∙ e ↬⇒ ⊢λ∶ τ ∙ ě

      ISAp1 : ∀ {Γ e₁ e₂ τ τ₁ τ₂}
        → {ě₁ : (ctx Γ) ⊢⇒ τ}
        → {ě₂ : (ctx Γ) ⊢⇐ τ₁}
        → Γ ⊢ e₁ ↬⇒ ě₁
        → (τ▸ : τ ▸ τ₁ -→ τ₂)
        → Γ ⊢ e₂ ↬⇐ ě₂
        → Γ ⊢ ‵ e₁ ∙ e₂ ↬⇒ ⊢ ě₁ ∙ ě₂ [ τ▸ ]

      ISAp2 : ∀ {Γ e₁ e₂ τ}
        → {ě₁ : (ctx Γ) ⊢⇒ τ}
        → {ě₂ : (ctx Γ) ⊢⇐ unknown}
        → Γ ⊢ e₁ ↬⇒ ě₁
        → (τ!▸ : τ !▸)
        → Γ ⊢ e₂ ↬⇐ ě₂
        → Γ ⊢ ‵ e₁ ∙ e₂ ↬⇒ ⊢⸨ ě₁ ⸩∙ ě₂ [ τ!▸ ]

      ISNum : ∀ {Γ n}
        → Γ ⊢ ‵ℕ n ↬⇒ ⊢ℕ n

      ISPlus : ∀ {Γ e₁ e₂}
        → {ě₁ : (ctx Γ) ⊢⇐ num}
        → {ě₂ : (ctx Γ) ⊢⇐ num}
        → Γ ⊢ e₁ ↬⇐ ě₁
        → Γ ⊢ e₂ ↬⇐ ě₂
        → Γ ⊢ ‵ e₁ + e₂ ↬⇒ ⊢ ě₁ + ě₂

      ISTrue : ∀ {Γ}
        → Γ ⊢ ‵tt ↬⇒ ⊢tt

      ISFalse : ∀ {Γ}
        → Γ ⊢ ‵ff ↬⇒ ⊢ff

      ISIf : ∀ {Γ e₁ e₂ e₃ τ₁ τ₂ τ}
        → {ě₁ : (ctx Γ) ⊢⇐ bool}
        → {ě₂ : (ctx Γ) ⊢⇒ τ₁} 
        → {ě₃ : (ctx Γ) ⊢⇒ τ₂} 
        → Γ ⊢ e₁ ↬⇐ ě₁
        → Γ ⊢ e₂ ↬⇒ ě₂
        → Γ ⊢ e₃ ↬⇒ ě₃
        → (τ₁⊔τ₂ : τ₁ ⊔ τ₂ ⇒ τ)
        → Γ ⊢ ‵ e₁ ∙ e₂ ∙ e₃ ↬⇒ ⊢ ě₁ ∙ ě₂ ∙ ě₃ [ τ₁⊔τ₂ ]

      ISInconsistentBranches : ∀ {Γ e₁ e₂ e₃ τ₁  τ₂}
        → {ě₁ : (ctx Γ) ⊢⇐ bool}
        → {ě₂ : (ctx Γ) ⊢⇒ τ₁} 
        → {ě₃ : (ctx Γ) ⊢⇒ τ₂} 
        → Γ ⊢ e₁ ↬⇐ ě₁
        → Γ ⊢ e₂ ↬⇒ ě₂
        → Γ ⊢ e₃ ↬⇒ ě₃
        → (τ₁~̸τ₂ : τ₁ ~̸ τ₂)
        → Γ ⊢ ‵ e₁ ∙ e₂ ∙ e₃ ↬⇒ ⊢⦉ ě₁ ∙ ě₂ ∙ ě₃ ⦊[ τ₁~̸τ₂ ]

    -- analysis
    data _⊢_↬⇐_ : {τ : Typ} (Γ : UCtx) → (e : UExp) → ((ctx Γ) ⊢⇐ τ) → Set where
      IALam : ∀ {Γ x τ e τ₁ τ₂ τ₃}
        → {ě : (ctx (Γ , x ∶ τ)) ⊢⇐ τ₂}
        → (τ₃▸ : τ₃ ▸ τ₁ -→ τ₂)
        → (τ~τ₁ : τ ~ τ₁)
        → Γ , x ∶ τ ⊢ e ↬⇐ ě
        → Γ ⊢ (‵λ x ∶ τ ∙ e) ↬⇐ (⊢λ∶ τ ∙ ě [ τ₃▸ ∙ τ~τ₁ ])

      IAIf : ∀ {Γ e₁ e₂ e₃ τ}
        → {ě₁ : (ctx Γ) ⊢⇐ bool}
        → {ě₂ : (ctx Γ) ⊢⇐ τ} 
        → {ě₃ : (ctx Γ) ⊢⇐ τ} 
        → Γ ⊢ e₁ ↬⇐ ě₁
        → Γ ⊢ e₂ ↬⇐ ě₂
        → Γ ⊢ e₃ ↬⇐ ě₃
        → Γ ⊢ ‵ e₁ ∙ e₂ ∙ e₃ ↬⇐ ⊢ ě₁ ∙ ě₂ ∙ ě₃

      IAInconsistentTypes : ∀ {Γ e τ τ′}
        → {ě : (ctx Γ) ⊢⇒ τ′}
        → Γ ⊢ e ↬⇒ ě
        → (τ~̸τ′ : τ ~̸ τ′)
        → Γ ⊢ e ↬⇐ ⊢⸨ ě ⸩[ τ~̸τ′ ]

      IASubsume : ∀ {Γ e τ τ′}
        → {ě : (ctx Γ) ⊢⇒ τ′}
        → Γ ⊢ e ↬⇒ ě
        → (τ~τ′ : τ ~ τ′)
        → Γ ⊢ e ↬⇐ ⊢∙ ě [ τ~τ′ ]
