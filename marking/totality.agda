open import prelude

open import core.typ
open import core.uexp
open import core.mexp

open import marking.marking

module marking.totality where
  mutual
    ↬⇒-totality : ∀ (Γ : UCtx) → (e : UExp) → Σ[ τ ∈ Typ ] Σ[ ě ∈ ⟦ Γ ⟧ ⊢⇒ τ ] (Γ ⊢ e ↬⇒ ě)
    ↬⇒-totality Γ (‵⦇-⦈^ x) = ⟨ unknown , ⟨ ⊢⦇-⦈^ x , ISHole ⟩ ⟩
    ↬⇒-totality Γ (‵ x)
      with Γ ∋?? x
    ...  | yes (Z {Γ} {x} {τ})                   = ⟨ τ       , ⟨ ⊢ Z [ x ]             , ISVar Z           ⟩ ⟩
    ...  | yes (S {Γ} {x} {x′} {τ} {τ′} x≢x′ ∋x) = ⟨ τ       , ⟨ ⊢ (S (⟦ ∋x ⟧∋)) [ x ] , ISVar (S x≢x′ ∋x) ⟩ ⟩
    ...  | no  ∌x                                = ⟨ unknown , ⟨ ⊢⟦ x ⟧                , ISUnbound ∌x      ⟩ ⟩
    ↬⇒-totality Γ (‵λ x ∶ τ ∙ e)
      with ⟨ τ′ , ⟨ ě , e↬⇒ě ⟩ ⟩ ← ↬⇒-totality (Γ , x ∶ τ) e
         = ⟨ τ -→ τ′ , ⟨ ⊢λ∶ τ ∙ ě [ x ] , ISLam e↬⇒ě ⟩ ⟩
    ↬⇒-totality Γ (‵ e₁ ∙ e₂)
      with ↬⇒-totality Γ e₁
    ...  | ⟨ τ , ⟨ ě₁ , e₁↬⇒ě₁ ⟩ ⟩
             with τ ▸?
    ...         | no τ!▸
                    with ⟨ ě₂ , e₂↬⇐ě₂ ⟩ ← ↬⇐-totality Γ unknown e₂
                       = ⟨ unknown , ⟨ ⊢⸨ ě₁ ⸩∙ ě₂ [ τ!▸ ] , ISAp2 e₁↬⇒ě₁ τ!▸ e₂↬⇐ě₂ ⟩ ⟩
    ...         | yes ⟨ τ₁ , ⟨ τ₂ , τ▸τ₁-→τ₂ ⟩ ⟩
                    with ⟨ ě₂ , e₂↬⇐ě₂ ⟩ ← ↬⇐-totality Γ τ₁ e₂
                       = ⟨ τ₂ , ⟨ ⊢ ě₁ ∙ ě₂ [ τ▸τ₁-→τ₂ ] , ISAp1 e₁↬⇒ě₁ τ▸τ₁-→τ₂ e₂↬⇐ě₂ ⟩ ⟩
    ↬⇒-totality Γ (‵ x ← e₁ ∙ e₂)
      with ⟨ τ₁ , ⟨ ě₁ , e₁↬⇒ě₁ ⟩ ⟩ ← ↬⇒-totality Γ e₁ 
      with ⟨ τ₂ , ⟨ ě₂ , e₂↬⇒ě₂ ⟩ ⟩ ← ↬⇒-totality (Γ , x ∶ τ₁) e₂
         = ⟨ τ₂ , ⟨ ⊢← ě₁ ∙ ě₂ [ x ] , ISLet e₁↬⇒ě₁ e₂↬⇒ě₂ ⟩ ⟩
    ↬⇒-totality Γ (‵ℕ n) = ⟨ num , ⟨ ⊢ℕ n , ISNum ⟩ ⟩
    ↬⇒-totality Γ (‵ e₁ + e₂)
      with ⟨ ě₁ , e₁↬⇐ě₁ ⟩ ← ↬⇐-totality Γ num e₁
         | ⟨ ě₂ , e₂↬⇐ě₂ ⟩ ← ↬⇐-totality Γ num e₂
         = ⟨ num , ⟨ ⊢ ě₁ + ě₂ , ISPlus e₁↬⇐ě₁ e₂↬⇐ě₂ ⟩ ⟩
    ↬⇒-totality Γ ‵tt = ⟨ bool , ⟨ ⊢tt , ISTrue ⟩ ⟩
    ↬⇒-totality Γ ‵ff = ⟨ bool , ⟨ ⊢ff , ISFalse ⟩ ⟩
    ↬⇒-totality Γ (‵ e₁ ∙ e₂ ∙ e₃)
      with ⟨ ě₁ , e₁↬⇐ě₁ ⟩ ← ↬⇐-totality Γ bool e₁
         | ⟨ τ₁ , ⟨ ě₂ , e₂↬⇐ě₂ ⟩ ⟩ ← ↬⇒-totality Γ e₂
         | ⟨ τ₂ , ⟨ ě₃ , e₃↬⇒ě₃ ⟩ ⟩ ← ↬⇒-totality Γ e₃
      with τ₁ ~? τ₂
    ...  | yes τ₁~τ₂
             with ⟨ τ , ⊔⇒τ ⟩ ← ~→⊔ τ₁~τ₂
                = ⟨ τ , ⟨ ⊢ ě₁ ∙ ě₂ ∙ ě₃ [ ⊔⇒τ ] , ISIf e₁↬⇐ě₁ e₂↬⇐ě₂ e₃↬⇒ě₃ ⊔⇒τ ⟩ ⟩
    ...  | no  τ₁~̸τ₂  = ⟨ unknown , ⟨ ⊢⦉ ě₁ ∙ ě₂ ∙ ě₃ ⦊[ τ₁~̸τ₂ ] , ISInconsistentBranches e₁↬⇐ě₁ e₂↬⇐ě₂ e₃↬⇒ě₃ τ₁~̸τ₂ ⟩ ⟩

    ↬⇐-subsume : ∀ {Γ e τ} → (ě : ⟦ Γ ⟧ ⊢⇒ τ) → (τ′ : Typ) → (Γ ⊢ e ↬⇒ ě) → (∙e : USubsumable e) → Σ[ ě ∈ ⟦ Γ ⟧ ⊢⇐ τ′ ] (Γ ⊢ e ↬⇐ ě)
    ↬⇐-subsume {_} {_} {τ} ě τ′ e↬⇒ě ∙e with τ′ ~? τ
    ...   | yes τ′~τ = ⟨ ⊢∙ ě  [ τ′~τ ∙ USu→MSu ∙e e↬⇒ě ] , IASubsume e↬⇒ě τ′~τ ∙e ⟩
    ...   | no  τ′~̸τ = ⟨ ⊢⸨ ě ⸩[ τ′~̸τ ∙ USu→MSu ∙e e↬⇒ě ] , IAInconsistentTypes e↬⇒ě τ′~̸τ ∙e ⟩

    ↬⇐-totality : ∀ (Γ : UCtx) → (τ′ : Typ) → (e : UExp) → Σ[ ě ∈ ⟦ Γ ⟧ ⊢⇐ τ′ ] (Γ ⊢ e ↬⇐ ě)
    ↬⇐-totality Γ τ′ e@(‵⦇-⦈^ u)
      with ⟨ .unknown , ⟨ ě@(⊢⦇-⦈^ _) , e↬⇒ě ⟩ ⟩ ← ↬⇒-totality Γ e
         = ↬⇐-subsume ě τ′ e↬⇒ě USuHole
    ↬⇐-totality Γ τ′ e@(‵ x)
      with ↬⇒-totality Γ e
    ...  | ⟨ .unknown , ⟨ ě@(⊢⟦ x ⟧) , e↬⇒ě ⟩ ⟩ = ↬⇐-subsume ě τ′ e↬⇒ě USuVar
    ...  | ⟨ τ        , ⟨ ě@(⊢ ∋x [ x ]) , e↬⇒ě ⟩ ⟩ = ↬⇐-subsume ě τ′ e↬⇒ě USuVar
    ↬⇐-totality Γ τ′ e@(‵λ x ∶ τ ∙ e′)
      with τ′ ▸?
    ...  | yes ⟨ τ₁ , ⟨ τ₂ , τ′▸ ⟩ ⟩
             with τ ~? τ₁
    ...         | yes τ~τ₁
                    with ⟨ ě′ , e′↬⇐ě′ ⟩ ← ↬⇐-totality (Γ , x ∶ τ) τ₂ e′
                       = ⟨ ⊢λ∶ τ ∙ ě′ [ τ′▸ ∙ τ~τ₁ ∙ x ] , IALam1 τ′▸ τ~τ₁ e′↬⇐ě′ ⟩
    ...         | no  τ~̸τ₁
                    with ⟨ ě′ , e′↬⇐ě′ ⟩ ← ↬⇐-totality (Γ , x ∶ τ) τ₂ e′
                       = ⟨ ⊢λ∶⸨ τ ⸩∙ ě′ [ τ′▸ ∙ τ~̸τ₁ ∙ x ] , IALam3 τ′▸ τ~̸τ₁ e′↬⇐ě′ ⟩
    ↬⇐-totality Γ τ′ e@(‵λ x ∶ τ ∙ e′)
         | no τ′!▸
             with ⟨ ě′ , e′↬⇐ě′ ⟩ ← ↬⇐-totality (Γ , x ∶ τ) unknown e′
                = ⟨ ⊢⸨λ∶ τ ∙ ě′ ⸩[ τ′!▸ ∙ x ] , IALam2 τ′!▸ e′↬⇐ě′ ⟩
    ↬⇐-totality Γ τ′ e@(‵ _ ∙ _)
      with ↬⇒-totality Γ e
    ...  | ⟨ .unknown , ⟨ ě@(⊢⸨ _ ⸩∙ _ [ _ ]) , e↬⇒ě ⟩ ⟩ = ↬⇐-subsume ě τ′ e↬⇒ě USuAp
    ...  | ⟨ _        , ⟨ ě@(⊢  _  ∙ _ [ _ ]) , e↬⇒ě ⟩ ⟩ = ↬⇐-subsume ě τ′ e↬⇒ě USuAp
    ↬⇐-totality Γ τ′ (‵ x ← e₁ ∙ e₂)
      with ⟨ τ₁ , ⟨ ě₁ , e₁↬⇒ě₁ ⟩ ⟩ ← ↬⇒-totality Γ e₁ 
      with ⟨ ě₂ , e₂↬⇐ě₂ ⟩ ← ↬⇐-totality (Γ , x ∶ τ₁) τ′ e₂
         = ⟨ ⊢← ě₁ ∙ ě₂ [ x ] , IALet e₁↬⇒ě₁ e₂↬⇐ě₂ ⟩
    ↬⇐-totality Γ τ′ e@(‵ℕ _)
      with ⟨ _ , ⟨ ě@(⊢ℕ _) , e↬⇒ě ⟩ ⟩ ← ↬⇒-totality Γ e
         = ↬⇐-subsume ě τ′ e↬⇒ě USuNum
    ↬⇐-totality Γ τ′ e@(‵ _ + _)
      with ⟨ _ , ⟨ ě@(⊢ _ + _) , e↬⇒ě ⟩ ⟩ ← ↬⇒-totality Γ e
         = ↬⇐-subsume ě τ′ e↬⇒ě USuPlus
    ↬⇐-totality Γ τ′ e@(‵tt)
      with ⟨ _ , ⟨ ě@(⊢tt) , e↬⇒ě ⟩ ⟩ ← ↬⇒-totality Γ e
         = ↬⇐-subsume ě τ′ e↬⇒ě USuTrue
    ↬⇐-totality Γ τ′ e@(‵ff)
      with ⟨ _ , ⟨ ě@(⊢ff) , e↬⇒ě ⟩ ⟩ ← ↬⇒-totality Γ e
         = ↬⇐-subsume ě τ′ e↬⇒ě USuFalse
    ↬⇐-totality Γ τ′ (‵ e₁ ∙ e₂ ∙ e₃)
      with ⟨ ě₁ , e₁↬⇐ě₁ ⟩ ← ↬⇐-totality Γ bool e₁
         | ⟨ ě₂ , e₂↬⇐ě₂ ⟩ ← ↬⇐-totality Γ τ′ e₂
         | ⟨ ě₃ , e₃↬⇐ě₃ ⟩ ← ↬⇐-totality Γ τ′ e₃
         = ⟨ ⊢ ě₁ ∙ ě₂ ∙ ě₃ , IAIf e₁↬⇐ě₁ e₂↬⇐ě₂ e₃↬⇐ě₃ ⟩
