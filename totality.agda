open import prelude
open import typ
open import uexp renaming (Ctx to UCtx; Subsumable to Subsumable)
open import mexp renaming (Ctx to MCtx; Subsumable to MSubsumable)
open import marking

module totality where
  mutual
    ↬⇒-totality : ∀ (Γ : UCtx) → (e : UExp) → Σ[ τ ∈ Typ ] Σ[ ě ∈ ⟦ Γ ⟧ ⊢⇒ τ ] (Γ ⊢ e ↬⇒ ě)
    ↬⇒-totality Γ (‵⦇-⦈^ x) = ⟨ unknown , ⟨ ⊢⦇-⦈^ x , ISHole ⟩ ⟩
    ↬⇒-totality Γ (‵ x) with Γ ∋?? x
    ...                    | yes (Z {Γ} {x} {τ}) = ⟨ τ , ⟨ ⊢ Z , ISVar Z ⟩ ⟩
    ...                    | yes (S {Γ} {x} {x′} {τ} {τ′} x≢x′ ∋x) = ⟨ τ , ⟨ ⊢ (S (⟦ ∋x ⟧∋)) , ISVar (S x≢x′ ∋x) ⟩ ⟩
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

    ↬⇐-subsume : ∀ {Γ e τ} → (ě : ⟦ Γ ⟧ ⊢⇒ τ) → (τ′ : Typ) → (Γ ⊢ e ↬⇒ ě) → (∙e : Subsumable e) → Σ[ ě ∈ ⟦ Γ ⟧ ⊢⇐ τ′ ] (Γ ⊢ e ↬⇐ ě)
    ↬⇐-subsume {Γ} {_} {τ} ě τ′ e↬⇒ě ∙e with τ′ ~? τ
    ...   | yes τ′~τ = ⟨ ⊢∙ ě  [ τ′~τ ∙ USu→MSu ∙e e↬⇒ě ] , IASubsume e↬⇒ě τ′~τ ∙e ⟩
    ...   | no  τ′~̸τ = ⟨ ⊢⸨ ě ⸩[ τ′~̸τ ∙ USu→MSu ∙e e↬⇒ě ] , IAInconsistentTypes e↬⇒ě τ′~̸τ ∙e ⟩

    ↬⇐-totality : ∀ (Γ : UCtx) → (τ′ : Typ) → (e : UExp) → Σ[ ě ∈ ⟦ Γ ⟧ ⊢⇐ τ′ ] (Γ ⊢ e ↬⇐ ě)
    ↬⇐-totality Γ τ′ e@(‵⦇-⦈^ u)
      with ↬⇒-totality Γ e
    ...  | ⟨ .unknown , ⟨ ě@(⊢⦇-⦈^ _) , e↬⇒ě ⟩ ⟩ = ↬⇐-subsume ě τ′ e↬⇒ě SuHole
    ↬⇐-totality Γ τ′ e@(‵ x)
      with ↬⇒-totality Γ e
    ...  | ⟨ .unknown , ⟨ ě@(⊢⟦ x ⟧) , e↬⇒ě ⟩ ⟩ = ↬⇐-subsume ě τ′ e↬⇒ě SuVar
    ...  | ⟨ τ        , ⟨ ě@(⊢ x)    , e↬⇒ě ⟩ ⟩ = ↬⇐-subsume ě τ′ e↬⇒ě SuVar
    ↬⇐-totality Γ τ′ e@(‵λ x ∶ τ ∙ e′)
      with τ′ ▸?
    ↬⇐-totality Γ τ′ e@(‵λ x ∶ τ ∙ e′) | yes ⟨ τ₁ , ⟨ τ₂ , τ′▸ ⟩ ⟩ with τ ~? τ₁
    ↬⇐-totality Γ τ′ e@(‵λ x ∶ τ ∙ e′) | yes ⟨ τ₁ , ⟨ τ₂ , τ′▸ ⟩ ⟩    | yes τ~τ₁ with ↬⇐-totality (Γ , x ∶ τ) τ₂ e′
    ↬⇐-totality Γ τ′ e@(‵λ x ∶ τ ∙ e′) | yes ⟨ τ₁ , ⟨ τ₂ , τ′▸ ⟩ ⟩    | yes τ~τ₁    | ⟨ ě′ , e′↬⇐ě′ ⟩ = ⟨ ⊢λ∶ τ ∙ ě′ [ τ′▸ ∙ τ~τ₁ ] , IALam1 τ′▸ τ~τ₁ e′↬⇐ě′ ⟩
    ↬⇐-totality Γ τ′ e@(‵λ x ∶ τ ∙ e′) | yes ⟨ τ₁ , ⟨ τ₂ , τ′▸ ⟩ ⟩    | no  τ~̸τ₁ with ↬⇐-totality (Γ , x ∶ τ) τ₂ e′
    ↬⇐-totality Γ τ′ e@(‵λ x ∶ τ ∙ e′) | yes ⟨ τ₁ , ⟨ τ₂ , τ′▸ ⟩ ⟩    | no  τ~̸τ₁    | ⟨ ě′ , e′↬⇐ě′ ⟩ = ⟨ ⊢λ∶⸨ τ ⸩∙ ě′ [ τ′▸ ∙ τ~̸τ₁ ] , IALam3 τ′▸ τ~̸τ₁ e′↬⇐ě′ ⟩
    ↬⇐-totality Γ τ′ e@(‵λ x ∶ τ ∙ e′) | no τ′!▸ with ↬⇐-totality (Γ , x ∶ τ) unknown e′
    ↬⇐-totality Γ τ′ e@(‵λ x ∶ τ ∙ e′) | no τ′!▸    | ⟨ ě′ , e′↬⇐ě′ ⟩ = ⟨ ⊢⸨λ∶ τ ∙ ě′ ⸩[ τ′!▸ ] , IALam2 τ′!▸ e′↬⇐ě′ ⟩
    ↬⇐-totality Γ τ′ e@(‵ _ ∙ _)
      with ↬⇒-totality Γ e
    ...  | ⟨ .unknown , ⟨ ě@(⊢⸨ _ ⸩∙ _ [ _ ]) , e↬⇒ě ⟩ ⟩ = ↬⇐-subsume ě τ′ e↬⇒ě SuAp
    ...  | ⟨ _        , ⟨ ě@(⊢  _  ∙ _ [ _ ]) , e↬⇒ě ⟩ ⟩ = ↬⇐-subsume ě τ′ e↬⇒ě SuAp
    ↬⇐-totality Γ τ′ e@(‵ℕ _)
      with ↬⇒-totality Γ e
    ...  | ⟨ _ , ⟨ ě@(⊢ℕ _) , e↬⇒ě ⟩ ⟩ = ↬⇐-subsume ě τ′ e↬⇒ě SuNum
    ↬⇐-totality Γ τ′ e@(‵ _ + _)
      with ↬⇒-totality Γ e
    ...  | ⟨ _ , ⟨ ě@(⊢ _ + _) , e↬⇒ě ⟩ ⟩ = ↬⇐-subsume ě τ′ e↬⇒ě SuPlus
    ↬⇐-totality Γ τ′ e@(‵tt)
      with ↬⇒-totality Γ e
    ...  | ⟨ _ , ⟨ ě@(⊢tt) , e↬⇒ě ⟩ ⟩ = ↬⇐-subsume ě τ′ e↬⇒ě SuTrue
    ↬⇐-totality Γ τ′ e@(‵ff)
      with ↬⇒-totality Γ e
    ...  | ⟨ _ , ⟨ ě@(⊢ff) , e↬⇒ě ⟩ ⟩ = ↬⇐-subsume ě τ′ e↬⇒ě SuFalse
    ↬⇐-totality Γ τ′ (‵ e₁ ∙ e₂ ∙ e₃)
      with ↬⇐-totality Γ bool e₁ | ↬⇐-totality Γ τ′ e₂ | ↬⇐-totality Γ τ′ e₃
    ...  | ⟨ ě₁ , e₁↬⇐ě₁ ⟩       | ⟨ ě₂ , e₂↬⇐ě₂ ⟩     | ⟨ ě₃ , e₃↬⇐ě₃ ⟩ = ⟨ ⊢ ě₁ ∙ ě₂ ∙ ě₃ , IAIf e₁↬⇐ě₁ e₂↬⇐ě₂ e₃↬⇐ě₃ ⟩
