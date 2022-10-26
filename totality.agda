open import prelude
open import typ
open import uexp renaming (Ctx to UCtx)
open import mexp renaming (Ctx to MCtx)
open import marking

module totality where
  mutual
    ↬⇒-totality : ∀ (Γ : UCtx) → (e : UExp) → Σ[ τ ∈ Typ ] Σ[ ě ∈ ((ctx Γ) ⊢⇒ τ) ] (Γ ⊢ e ↬⇒ ě)
    ↬⇒-totality Γ (‵⦇-⦈^ x) = ⟨ unknown , ⟨ ⊢⦇-⦈^ x , ISHole ⟩ ⟩
    ↬⇒-totality Γ (‵ x) with Γ ∋?? x
    ...                    | yes (Z {Γ} {x} {τ}) = ⟨ τ , ⟨ ⊢ Z , ISVar Z ⟩ ⟩
    ...                    | yes (S {Γ} {x} {x′} {τ} {τ′} x≢x′ ∋x) = ⟨ τ , ⟨ ⊢ (S (ctx∋ ∋x)) , ISVar (S x≢x′ ∋x) ⟩ ⟩
    ...                    | no  ∌x = ⟨ unknown , ⟨ ⊢⟦ x ⟧ , ISUnbound ∌x ⟩ ⟩
    ↬⇒-totality Γ (‵λ x ∶ τ ∙ e) with ↬⇒-totality (Γ , x ∶ τ) e
    ...                             | ⟨ τ′ , ⟨ ě , e↬⇒ě ⟩ ⟩ = ⟨ τ -→ τ′ , ⟨ ⊢λ∶ τ ∙ ě , ISLam e↬⇒ě ⟩ ⟩
    ↬⇒-totality Γ (‵ e₁ ∙ e₂) with ↬⇒-totality Γ e₁
    ↬⇒-totality Γ (‵ e₁ ∙ e₂)    | ⟨ τ , ⟨ ě₁ , e₁↬⇒ě₁ ⟩ ⟩ with τ ▸?
    ↬⇒-totality Γ (‵ e₁ ∙ e₂)    | ⟨ τ , ⟨ ě₁ , e₁↬⇒ě₁ ⟩ ⟩    | no τ!▸ with ↬⇐-totality Γ unknown e₂
    ↬⇒-totality Γ (‵ e₁ ∙ e₂)    | ⟨ τ , ⟨ ě₁ , e₁↬⇒ě₁ ⟩ ⟩    | no τ!▸    | ⟨ ě₂ , e₂↬⇐ě₂ ⟩ = ⟨ unknown , ⟨ ⊢⸨ ě₁ ⸩∙ ě₂ [ τ!▸ ] , ISAp2 e₁↬⇒ě₁ τ!▸ e₂↬⇐ě₂ ⟩ ⟩
    ↬⇒-totality Γ (‵ e₁ ∙ e₂)    | ⟨ τ , ⟨ ě₁ , e₁↬⇒ě₁ ⟩ ⟩    | yes ⟨ τ₁ , ⟨ τ₂ , τ▸τ₁-→τ₂ ⟩ ⟩ with ↬⇐-totality Γ τ₁ e₂
    ↬⇒-totality Γ (‵ e₁ ∙ e₂)    | ⟨ τ , ⟨ ě₁ , e₁↬⇒ě₁ ⟩ ⟩    | yes ⟨ τ₁ , ⟨ τ₂ , τ▸τ₁-→τ₂ ⟩ ⟩    | ⟨ ě₂ , e₂↬⇐ě₂ ⟩ = ⟨ τ₂ , ⟨ ⊢ ě₁ ∙ ě₂ [ τ▸τ₁-→τ₂ ] , ISAp1 e₁↬⇒ě₁ τ▸τ₁-→τ₂ e₂↬⇐ě₂ ⟩ ⟩
    ↬⇒-totality Γ (‵ℕ n) = ⟨ num , ⟨ ⊢ℕ n , ISNum ⟩ ⟩
    ↬⇒-totality Γ (‵ e₁ + e₂) with ↬⇐-totality Γ num e₁ | ↬⇐-totality Γ num e₂
    ...                          | ⟨ ě₁ , e₁↬⇐ě₁ ⟩      | ⟨ ě₂ , e₂↬⇐ě₂ ⟩ = ⟨ num , ⟨ ⊢ ě₁ + ě₂ , ISPlus e₁↬⇐ě₁ e₂↬⇐ě₂ ⟩ ⟩
    ↬⇒-totality Γ ‵tt = ⟨ bool , ⟨ ⊢tt , ISTrue ⟩ ⟩
    ↬⇒-totality Γ ‵ff = ⟨ bool , ⟨ ⊢ff , ISFalse ⟩ ⟩
    ↬⇒-totality Γ (‵ e₁ ∙ e₂ ∙ e₃) with ↬⇐-totality Γ bool e₁ | ↬⇒-totality Γ e₂         | ↬⇒-totality Γ e₃
    ↬⇒-totality Γ (‵ e₁ ∙ e₂ ∙ e₃)    | ⟨ ě₁ , e₁↬⇐ě₁ ⟩       | ⟨ τ₁ , ⟨ ě₂ , e₂↬⇐ě₂ ⟩ ⟩ | ⟨ τ₂ , ⟨ ě₃ , e₃↬⇒ě₃ ⟩ ⟩ with τ₁ ~? τ₂
    ↬⇒-totality Γ (‵ e₁ ∙ e₂ ∙ e₃)    | ⟨ ě₁ , e₁↬⇐ě₁ ⟩       | ⟨ τ₁ , ⟨ ě₂ , e₂↬⇐ě₂ ⟩ ⟩ | ⟨ τ₂ , ⟨ ě₃ , e₃↬⇒ě₃ ⟩ ⟩    | yes τ₁~τ₂ with ~→⊔ τ₁~τ₂
    ↬⇒-totality Γ (‵ e₁ ∙ e₂ ∙ e₃)    | ⟨ ě₁ , e₁↬⇐ě₁ ⟩       | ⟨ τ₁ , ⟨ ě₂ , e₂↬⇐ě₂ ⟩ ⟩ | ⟨ τ₂ , ⟨ ě₃ , e₃↬⇒ě₃ ⟩ ⟩    | yes τ₁~τ₂    | ⟨ τ , ⊔⇒τ ⟩ = ⟨ τ , ⟨ ⊢ ě₁ ∙ ě₂ ∙ ě₃ [ ⊔⇒τ ] , ISIf e₁↬⇐ě₁ e₂↬⇐ě₂ e₃↬⇒ě₃ ⊔⇒τ ⟩ ⟩
    ↬⇒-totality Γ (‵ e₁ ∙ e₂ ∙ e₃)    | ⟨ ě₁ , e₁↬⇐ě₁ ⟩       | ⟨ τ₁ , ⟨ ě₂ , e₂↬⇐ě₂ ⟩ ⟩ | ⟨ τ₂ , ⟨ ě₃ , e₃↬⇒ě₃ ⟩ ⟩    | no  τ₁~̸τ₂                  = ⟨ unknown , ⟨ ⊢⦉ ě₁ ∙ ě₂ ∙ ě₃ ⦊[ τ₁~̸τ₂ ] , ISInconsistentBranches e₁↬⇐ě₁ e₂↬⇐ě₂ e₃↬⇒ě₃ τ₁~̸τ₂ ⟩ ⟩

    ↬⇐-totality : ∀ (Γ : UCtx) → (τ′ : Typ) → (e : UExp) → Σ[ ě ∈ ((ctx Γ) ⊢⇐ τ′) ] (Γ ⊢ e ↬⇐ ě)
    ↬⇐-totality Γ τ′ e = ↬⇐-subsume Γ τ′ e
      where
        ↬⇐-subsume : ∀ (Γ : UCtx) → (τ′ : Typ) → (e : UExp) → Σ[ ě ∈ ((ctx Γ) ⊢⇐ τ′) ] (Γ ⊢ e ↬⇐ ě)
        ↬⇐-subsume Γ τ′ e with ↬⇒-totality Γ e
        ... | ⟨ τ , ⟨ ě , e↬⇒ě ⟩ ⟩ with τ′ ~? τ
        ...   | yes τ′~τ = ⟨ ⊢∙ ě [ τ′~τ ] , IASubsume e↬⇒ě τ′~τ ⟩
        ...   | no  τ′~̸τ = ⟨ ⊢⸨ ě ⸩[ τ′~̸τ ] , IAInconsistentTypes e↬⇒ě τ′~̸τ ⟩
