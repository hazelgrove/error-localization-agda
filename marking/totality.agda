open import prelude
open import core

open import marking.marking

module marking.totality where
  mutual
    ↬⇒-totality : (Γ : Ctx)
                → (e : UExp)
                → Σ[ τ ∈ Typ ] Σ[ ě ∈ Γ ⊢⇒ τ ] (Γ ⊢ e ↬⇒ ě)
    ↬⇒-totality Γ (‵⦇-⦈^ x)        = ⟨ unknown , ⟨ ⊢⦇-⦈^ x , MKSHole ⟩ ⟩
    ↬⇒-totality Γ (‵ x)
      with Γ ∋?? x
    ...  | yes (Z {τ = τ})         = ⟨ τ       , ⟨ ⊢ Z           , MKSVar Z           ⟩ ⟩
    ...  | yes (S {τ = τ} x≢x′ ∋x) = ⟨ τ       , ⟨ ⊢ (S x≢x′ ∋x) , MKSVar (S x≢x′ ∋x) ⟩ ⟩
    ...  | no  ∌x                  = ⟨ unknown , ⟨ ⊢⟦ ∌x ⟧       , MKSFree ∌x         ⟩ ⟩
    ↬⇒-totality Γ (‵λ x ∶ τ ∙ e)
      with ⟨ τ′ , ⟨ ě , e↬⇒ě ⟩ ⟩ ← ↬⇒-totality (Γ , x ∶ τ) e
         = ⟨ τ -→ τ′ , ⟨ ⊢λ x ∶ τ ∙ ě , MKSLam e↬⇒ě ⟩ ⟩
    ↬⇒-totality Γ (‵ e₁ ∙ e₂)
      with ↬⇒-totality Γ e₁
    ...  | ⟨ τ , ⟨ ě₁ , e₁↬⇒ě₁ ⟩ ⟩
             with τ ▸-→?
    ...         | no τ!▸
                    with ⟨ ě₂ , e₂↬⇐ě₂ ⟩ ← ↬⇐-totality Γ unknown e₂
                       = ⟨ unknown , ⟨ ⊢⸨ ě₁ ⸩∙ ě₂ [ τ!▸ ] , MKSAp2 e₁↬⇒ě₁ τ!▸ e₂↬⇐ě₂ ⟩ ⟩
    ...         | yes ⟨ τ₁ , ⟨ τ₂ , τ▸τ₁-→τ₂ ⟩ ⟩
                    with ⟨ ě₂ , e₂↬⇐ě₂ ⟩ ← ↬⇐-totality Γ τ₁ e₂
                       = ⟨ τ₂ , ⟨ ⊢ ě₁ ∙ ě₂ [ τ▸τ₁-→τ₂ ] , MKSAp1 e₁↬⇒ě₁ τ▸τ₁-→τ₂ e₂↬⇐ě₂ ⟩ ⟩
    ↬⇒-totality Γ (‵ x ← e₁ ∙ e₂)
      with ⟨ τ₁ , ⟨ ě₁ , e₁↬⇒ě₁ ⟩ ⟩ ← ↬⇒-totality Γ e₁ 
      with ⟨ τ₂ , ⟨ ě₂ , e₂↬⇒ě₂ ⟩ ⟩ ← ↬⇒-totality (Γ , x ∶ τ₁) e₂
         = ⟨ τ₂ , ⟨ ⊢ x ← ě₁ ∙ ě₂ , MKSLet e₁↬⇒ě₁ e₂↬⇒ě₂ ⟩ ⟩
    ↬⇒-totality Γ (‵ℕ n) = ⟨ num , ⟨ ⊢ℕ n , MKSNum ⟩ ⟩
    ↬⇒-totality Γ (‵ e₁ + e₂)
      with ⟨ ě₁ , e₁↬⇐ě₁ ⟩ ← ↬⇐-totality Γ num e₁
         | ⟨ ě₂ , e₂↬⇐ě₂ ⟩ ← ↬⇐-totality Γ num e₂
         = ⟨ num , ⟨ ⊢ ě₁ + ě₂ , MKSPlus e₁↬⇐ě₁ e₂↬⇐ě₂ ⟩ ⟩
    ↬⇒-totality Γ ‵tt = ⟨ bool , ⟨ ⊢tt , MKSTrue ⟩ ⟩
    ↬⇒-totality Γ ‵ff = ⟨ bool , ⟨ ⊢ff , MKSFalse ⟩ ⟩
    ↬⇒-totality Γ (‵ e₁ ∙ e₂ ∙ e₃)
      with ⟨ ě₁ , e₁↬⇐ě₁ ⟩ ← ↬⇐-totality Γ bool e₁
         | ⟨ τ₁ , ⟨ ě₂ , e₂↬⇐ě₂ ⟩ ⟩ ← ↬⇒-totality Γ e₂
         | ⟨ τ₂ , ⟨ ě₃ , e₃↬⇒ě₃ ⟩ ⟩ ← ↬⇒-totality Γ e₃
      with τ₁ ~? τ₂
    ...  | yes τ₁~τ₂
             with ⟨ τ , ⊓⇒τ ⟩ ← ~→⊓ τ₁~τ₂
                = ⟨ τ , ⟨ ⊢ ě₁ ∙ ě₂ ∙ ě₃ [ ⊓⇒τ ] , MKSIf e₁↬⇐ě₁ e₂↬⇐ě₂ e₃↬⇒ě₃ ⊓⇒τ ⟩ ⟩
    ...  | no  τ₁~̸τ₂ = ⟨ unknown , ⟨ ⊢⦉ ě₁ ∙ ě₂ ∙ ě₃ ⦊[ τ₁~̸τ₂ ] , MKSInconsistentBranches e₁↬⇐ě₁ e₂↬⇐ě₂ e₃↬⇒ě₃ τ₁~̸τ₂ ⟩ ⟩
    ↬⇒-totality Γ ‵⟨ e₁ , e₂ ⟩
      with ⟨ τ₁ , ⟨ ě₁ , e₁↬⇒ě₁ ⟩ ⟩ ← ↬⇒-totality Γ e₁
      with ⟨ τ₂ , ⟨ ě₂ , e₂↬⇒ě₂ ⟩ ⟩ ← ↬⇒-totality Γ e₂
         = ⟨ τ₁ -× τ₂ , ⟨ ⊢⟨ ě₁ , ě₂ ⟩ , MKSPair e₁↬⇒ě₁ e₂↬⇒ě₂ ⟩ ⟩
    ↬⇒-totality Γ (‵π₁ e)
      with ⟨ τ , ⟨ ě , e↬⇒ě ⟩ ⟩ ← ↬⇒-totality Γ e
      with τ ▸-×?
    ...  | yes ⟨ τ₁ , ⟨ τ₂ , τ▸ ⟩ ⟩ = ⟨ τ₁ , ⟨ ⊢π₁ ě [ τ▸ ] , MKSProjL1 e↬⇒ě τ▸ ⟩ ⟩
    ...  | no  τ!▸                  = ⟨ unknown , ⟨ ⊢π₁⸨ ě ⸩[ τ!▸ ] , MKSProjL2 e↬⇒ě τ!▸ ⟩ ⟩
    ↬⇒-totality Γ (‵π₂ e)
      with ⟨ τ , ⟨ ě , e↬⇒ě ⟩ ⟩ ← ↬⇒-totality Γ e
      with τ ▸-×?
    ...  | yes ⟨ τ₁ , ⟨ τ₂ , τ▸ ⟩ ⟩ = ⟨ τ₂ , ⟨ ⊢π₂ ě [ τ▸ ] , MKSProjR1 e↬⇒ě τ▸ ⟩ ⟩
    ...  | no  τ!▸                  = ⟨ unknown , ⟨ ⊢π₂⸨ ě ⸩[ τ!▸ ] , MKSProjR2 e↬⇒ě τ!▸ ⟩ ⟩

    ↬⇐-subsume : ∀ {Γ e τ}
               → (ě : Γ ⊢⇒ τ)
               → (τ′ : Typ)
               → (Γ ⊢ e ↬⇒ ě)
               → (s : USubsumable e)
               → Σ[ ě ∈ Γ ⊢⇐ τ′ ] (Γ ⊢ e ↬⇐ ě)
    ↬⇐-subsume {τ = τ} ě τ′ e↬⇒ě s with τ′ ~? τ
    ...   | yes τ′~τ = ⟨ ⊢∙ ě  [ τ′~τ ∙ USu→MSu s e↬⇒ě ] , MKASubsume e↬⇒ě τ′~τ s ⟩
    ...   | no  τ′~̸τ = ⟨ ⊢⸨ ě ⸩[ τ′~̸τ ∙ USu→MSu s e↬⇒ě ] , MKAInconsistentTypes e↬⇒ě τ′~̸τ s ⟩

    ↬⇐-totality : (Γ : Ctx)
                → (τ′ : Typ)
                → (e : UExp)
                → Σ[ ě ∈ Γ ⊢⇐ τ′ ] (Γ ⊢ e ↬⇐ ě)
    ↬⇐-totality Γ τ′ e@(‵⦇-⦈^ u)
      with ⟨ .unknown , ⟨ ě@(⊢⦇-⦈^ _) , e↬⇒ě ⟩ ⟩ ← ↬⇒-totality Γ e
         = ↬⇐-subsume ě τ′ e↬⇒ě USuHole
    ↬⇐-totality Γ τ′ e@(‵ x)
      with ↬⇒-totality Γ e
    ...  | ⟨ .unknown , ⟨ ě@(⊢⟦ ∌x ⟧) , e↬⇒ě ⟩ ⟩ = ↬⇐-subsume ě τ′ e↬⇒ě USuVar
    ...  | ⟨ τ        , ⟨ ě@(⊢ ∋x) , e↬⇒ě ⟩ ⟩ = ↬⇐-subsume ě τ′ e↬⇒ě USuVar
    ↬⇐-totality Γ τ′ e@(‵λ x ∶ τ ∙ e′)
      with τ′ ▸-→?
    ...  | yes ⟨ τ₁ , ⟨ τ₂ , τ′▸ ⟩ ⟩
             with τ ~? τ₁
    ...         | yes τ~τ₁
                    with ⟨ ě′ , e′↬⇐ě′ ⟩ ← ↬⇐-totality (Γ , x ∶ τ) τ₂ e′
                       = ⟨ ⊢λ x ∶ τ ∙ ě′ [ τ′▸ ∙ τ~τ₁ ] , MKALam1 τ′▸ τ~τ₁ e′↬⇐ě′ ⟩
    ...         | no  τ~̸τ₁
                    with ⟨ ě′ , e′↬⇐ě′ ⟩ ← ↬⇐-totality (Γ , x ∶ τ) τ₂ e′
                       = ⟨ ⊢λ x ∶⸨ τ ⸩∙ ě′ [ τ′▸ ∙ τ~̸τ₁ ] , MKALam3 τ′▸ τ~̸τ₁ e′↬⇐ě′ ⟩
    ↬⇐-totality Γ τ′ e@(‵λ x ∶ τ ∙ e′)
         | no τ′!▸
             with ⟨ ě′ , e′↬⇐ě′ ⟩ ← ↬⇐-totality (Γ , x ∶ τ) unknown e′
                = ⟨ ⊢⸨λ x ∶ τ ∙ ě′ ⸩[ τ′!▸ ] , MKALam2 τ′!▸ e′↬⇐ě′ ⟩
    ↬⇐-totality Γ τ′ e@(‵ _ ∙ _)
      with ↬⇒-totality Γ e
    ...  | ⟨ .unknown , ⟨ ě@(⊢⸨ _ ⸩∙ _ [ _ ]) , e↬⇒ě ⟩ ⟩ = ↬⇐-subsume ě τ′ e↬⇒ě USuAp
    ...  | ⟨ _        , ⟨ ě@(⊢  _  ∙ _ [ _ ]) , e↬⇒ě ⟩ ⟩ = ↬⇐-subsume ě τ′ e↬⇒ě USuAp
    ↬⇐-totality Γ τ′ (‵ x ← e₁ ∙ e₂)
      with ⟨ τ₁ , ⟨ ě₁ , e₁↬⇒ě₁ ⟩ ⟩ ← ↬⇒-totality Γ e₁ 
      with ⟨ ě₂ , e₂↬⇐ě₂ ⟩ ← ↬⇐-totality (Γ , x ∶ τ₁) τ′ e₂
         = ⟨ ⊢ x ← ě₁ ∙ ě₂ , MKALet e₁↬⇒ě₁ e₂↬⇐ě₂ ⟩
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
         = ⟨ ⊢ ě₁ ∙ ě₂ ∙ ě₃ , MKAIf e₁↬⇐ě₁ e₂↬⇐ě₂ e₃↬⇐ě₃ ⟩
    ↬⇐-totality Γ τ′ ‵⟨ e₁ , e₂ ⟩
      with τ′ ▸-×?
    ...  | yes ⟨ τ₁ , ⟨ τ₂ , τ′▸ ⟩ ⟩
             with ⟨ ě₁ , e₁↬⇐ě₁ ⟩ ← ↬⇐-totality Γ τ₁ e₁
             with ⟨ ě₂ , e₂↬⇐ě₂ ⟩ ← ↬⇐-totality Γ τ₂ e₂
                = ⟨ ⊢⟨ ě₁ , ě₂ ⟩[ τ′▸ ] , MKAPair1 e₁↬⇐ě₁ e₂↬⇐ě₂ τ′▸ ⟩
    ...  | no  τ′!▸
             with ⟨ ě₁ , e₁↬⇐ě₁ ⟩ ← ↬⇐-totality Γ unknown e₁
             with ⟨ ě₂ , e₂↬⇐ě₂ ⟩ ← ↬⇐-totality Γ unknown e₂
                = ⟨ ⊢⸨⟨ ě₁ , ě₂ ⟩⸩[ τ′!▸ ] , MKAPair2 e₁↬⇐ě₁ e₂↬⇐ě₂ τ′!▸ ⟩
    ↬⇐-totality Γ τ′ e@(‵π₁ _)
      with ↬⇒-totality Γ e
    ...  | ⟨ _ , ⟨ ě@(⊢π₁ _ [ _ ])   , e↬⇒ě ⟩ ⟩ = ↬⇐-subsume ě τ′ e↬⇒ě USuProjL
    ...  | ⟨ _ , ⟨ ě@(⊢π₁⸨ _ ⸩[ _ ]) , e↬⇒ě ⟩ ⟩ = ↬⇐-subsume ě τ′ e↬⇒ě USuProjL
    ↬⇐-totality Γ τ′ e@(‵π₂ _)
      with ↬⇒-totality Γ e
    ...  | ⟨ _ , ⟨ ě@(⊢π₂ _ [ _ ])   , e↬⇒ě ⟩ ⟩ = ↬⇐-subsume ě τ′ e↬⇒ě USuProjR
    ...  | ⟨ _ , ⟨ ě@(⊢π₂⸨ _ ⸩[ _ ]) , e↬⇒ě ⟩ ⟩ = ↬⇐-subsume ě τ′ e↬⇒ě USuProjR
