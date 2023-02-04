open import prelude
open import typ
open import uexp renaming (Ctx to UCtx; Subsumable to USubsumable)
open import mexp renaming (Ctx to MCtx; Subsumable to MSubsumable)

module erasure where
  mutual
    _⇒□ : ∀ {Γ τ} → (ě : Γ ⊢⇒ τ) → UExp
    (⊢⦇-⦈^ u)                      ⇒□ = ‵⦇-⦈^ u
    (⊢ ∋x [ x ])                   ⇒□ = ‵ x
    (⊢λ∶ τ ∙ ě [ x ])              ⇒□ = ‵λ x ∶ τ ∙ (ě ⇒□)
    ⊢ ě₁ ∙ ě₂ [ τ▸ ]               ⇒□ = ‵ (ě₁ ⇒□) ∙ (ě₂ ⇐□)
    ⊢⸨ ě₁ ⸩∙ ě₂ [ τ!▸ ]            ⇒□ = ‵ (ě₁ ⇒□) ∙ (ě₂ ⇐□)
    (⊢ℕ n)                         ⇒□ = ‵ℕ n
    (⊢ ě₁ + ě₂)                    ⇒□ = ‵ (ě₁ ⇐□) + (ě₂ ⇐□)
    ⊢tt                            ⇒□ = ‵tt
    ⊢ff                            ⇒□ = ‵ff
    ⊢ ě₁ ∙ ě₂ ∙ ě₃ [ τ₁⊔τ₂ ]       ⇒□ = ‵ (ě₁ ⇐□) ∙ (ě₂ ⇒□) ∙ (ě₃ ⇒□)
    ⊢⟦ y ⟧                         ⇒□ = ‵ y
    ⊢⦉ ě₁ ∙ ě₂ ∙ ě₃ ⦊[ τ₁~̸τ₂ ]     ⇒□ = ‵ (ě₁ ⇐□) ∙ (ě₂ ⇒□) ∙ (ě₃ ⇒□)

    _⇐□ : ∀ {Γ τ} → (ě : Γ ⊢⇐ τ) → UExp
    ⊢λ∶ τ ∙ ě [ τ₃▸ ∙ τ~τ₁ ∙ x ]   ⇐□ = ‵λ x ∶ τ ∙ (ě ⇐□)
    ⊢⸨λ∶ τ ∙ ě ⸩[ τ′!▸ ∙ x ]       ⇐□ = ‵λ x ∶ τ ∙ (ě ⇐□)
    ⊢λ∶⸨ τ ⸩∙ ě [ τ₃▸ ∙ τ~̸τ₁ ∙ x ] ⇐□ = ‵λ x ∶ τ ∙ (ě ⇐□)
    (⊢ ě₁ ∙ ě₂ ∙ ě₃)               ⇐□ = ‵ (ě₁ ⇐□) ∙ (ě₂ ⇐□) ∙ (ě₃ ⇐□)
    ⊢⸨ ě ⸩[ τ~̸τ′ ∙ su ]            ⇐□ = ě ⇒□
    ⊢∙ ě [ τ~τ′ ∙ su ]             ⇐□ = ě ⇒□
