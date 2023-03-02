open import prelude
open import core

open import hazelnut.action
open import hazelnut.untyped.zexp
open import hazelnut.untyped.action
open import hazelnut.untyped.erasure

module hazelnut.untyped.reachability where
  -- reach up for types
  reachup-τ : (τ^ : ZTyp) → ∃[ ᾱ ] ᾱ movements × τ^ + ᾱ +τ>* ▹ τ^ ◇τ ◃
  reachup-τ ▹ τ ◃ = ⟨ [] , ⟨ AMINil , ATIRefl ⟩ ⟩
  reachup-τ (τ^ -→₁ τ)
    with ⟨ ᾱ , ⟨ ᾱmv , τ^+>* ⟩ ⟩ ← reachup-τ τ^
       = ⟨ ᾱ ++ ∣[ move parent ] ,
         ⟨ movements-++ ᾱmv (AMICons parent AMINil) ,
           +τ>*-++ (ziplem-tarr1 τ^+>*) (ATITyp ATMArrParent1 ATIRefl) ⟩ ⟩
  reachup-τ (τ -→₂ τ^)
    with ⟨ ᾱ , ⟨ ᾱmv , τ^+>* ⟩ ⟩ ← reachup-τ τ^
       = ⟨ ᾱ ++ ∣[ move parent ] ,
         ⟨ movements-++ ᾱmv (AMICons parent AMINil) ,
           +τ>*-++ (ziplem-tarr2 τ^+>*) (ATITyp ATMArrParent2 ATIRefl) ⟩ ⟩
  reachup-τ (τ^ -×₁ τ)
    with ⟨ ᾱ , ⟨ ᾱmv , τ^+>* ⟩ ⟩ ← reachup-τ τ^
       = ⟨ ᾱ ++ ∣[ move parent ] ,
         ⟨ movements-++ ᾱmv (AMICons parent AMINil) ,
           +τ>*-++ (ziplem-tprod1 τ^+>*) (ATITyp ATMProdParent1 ATIRefl) ⟩ ⟩
  reachup-τ (τ -×₂ τ^)
    with ⟨ ᾱ , ⟨ ᾱmv , τ^+>* ⟩ ⟩ ← reachup-τ τ^
       = ⟨ ᾱ ++ ∣[ move parent ] ,
         ⟨ movements-++ ᾱmv (AMICons parent AMINil) ,
           +τ>*-++ (ziplem-tprod2 τ^+>*) (ATITyp ATMProdParent2 ATIRefl) ⟩ ⟩

  -- reach up for expressions
  reachup-e : (ê : ZExp) → ∃[ ᾱ ] ᾱ movements × ê + ᾱ +e>* ‵▹ ê ◇ ◃
  reachup-e ‵▹ e ◃ = ⟨ [] , ⟨ AMINil , AEIRefl ⟩ ⟩
  reachup-e (‵λ₁ x ∶ τ^ ∙ e)
    with ⟨ ᾱ , ⟨ ᾱmv , τ^+>* ⟩ ⟩ ← reachup-τ τ^
       = ⟨ ᾱ ++ ∣[ move parent ] ,
         ⟨ movements-++ ᾱmv (AMICons parent AMINil) ,
           +e>*-++ (ziplem-lam1 τ^+>*) (AEIExp AEMLamParent1 AEIRefl) ⟩ ⟩
  reachup-e (‵λ₂ x ∶ τ ∙ ê)
    with ⟨ ᾱ , ⟨ ᾱmv , ê+>* ⟩ ⟩ ← reachup-e ê
       = ⟨ ᾱ ++ ∣[ move parent ] ,
         ⟨ movements-++ ᾱmv (AMICons parent AMINil) ,
           +e>*-++ (ziplem-lam2 ê+>*) (AEIExp AEMLamParent2 AEIRefl) ⟩ ⟩
  reachup-e (‵ ê ∙₁ e)
    with ⟨ ᾱ , ⟨ ᾱmv , ê+>* ⟩ ⟩ ← reachup-e ê
       = ⟨ ᾱ ++ ∣[ move parent ] ,
         ⟨ movements-++ ᾱmv (AMICons parent AMINil) ,
           +e>*-++ (ziplem-ap1 ê+>*) (AEIExp AEMApParent1 AEIRefl) ⟩ ⟩
  reachup-e (‵ e ∙₂ ê)
    with ⟨ ᾱ , ⟨ ᾱmv , ê+>* ⟩ ⟩ ← reachup-e ê
       = ⟨ ᾱ ++ ∣[ move parent ] ,
         ⟨ movements-++ ᾱmv (AMICons parent AMINil) ,
           +e>*-++ (ziplem-ap2 ê+>*) (AEIExp AEMApParent2 AEIRefl) ⟩ ⟩
  reachup-e (‵ x ←₁ ê ∙ e)
    with ⟨ ᾱ , ⟨ ᾱmv , ê+>* ⟩ ⟩ ← reachup-e ê
       = ⟨ ᾱ ++ ∣[ move parent ] ,
         ⟨ movements-++ ᾱmv (AMICons parent AMINil) ,
           +e>*-++ (ziplem-let1 ê+>*) (AEIExp AEMLetParent1 AEIRefl) ⟩ ⟩
  reachup-e (‵ x ←₂ e ∙ ê)
    with ⟨ ᾱ , ⟨ ᾱmv , ê+>* ⟩ ⟩ ← reachup-e ê
       = ⟨ ᾱ ++ ∣[ move parent ] ,
         ⟨ movements-++ ᾱmv (AMICons parent AMINil) ,
           +e>*-++ (ziplem-let2 ê+>*) (AEIExp AEMLetParent2 AEIRefl) ⟩ ⟩
  reachup-e (‵ ê +₁ e)
    with ⟨ ᾱ , ⟨ ᾱmv , ê+>* ⟩ ⟩ ← reachup-e ê
       = ⟨ ᾱ ++ ∣[ move parent ] ,
         ⟨ movements-++ ᾱmv (AMICons parent AMINil) ,
           +e>*-++ (ziplem-plus1 ê+>*) (AEIExp AEMPlusParent1 AEIRefl) ⟩ ⟩
  reachup-e (‵ e +₂ ê)
    with ⟨ ᾱ , ⟨ ᾱmv , ê+>* ⟩ ⟩ ← reachup-e ê
       = ⟨ ᾱ ++ ∣[ move parent ] ,
         ⟨ movements-++ ᾱmv (AMICons parent AMINil) ,
           +e>*-++ (ziplem-plus2 ê+>*) (AEIExp AEMPlusParent2 AEIRefl) ⟩ ⟩
  reachup-e (‵ ê ∙₁ e₂ ∙ e₃)
    with ⟨ ᾱ , ⟨ ᾱmv , ê+>* ⟩ ⟩ ← reachup-e ê
       = ⟨ ᾱ ++ ∣[ move parent ] ,
         ⟨ movements-++ ᾱmv (AMICons parent AMINil) ,
           +e>*-++ (ziplem-if1 ê+>*) (AEIExp AEMIfParent1 AEIRefl) ⟩ ⟩
  reachup-e (‵ e₁ ∙₂ ê ∙ e₃)
    with ⟨ ᾱ , ⟨ ᾱmv , ê+>* ⟩ ⟩ ← reachup-e ê
       = ⟨ ᾱ ++ ∣[ move parent ] ,
         ⟨ movements-++ ᾱmv (AMICons parent AMINil) ,
           +e>*-++ (ziplem-if2 ê+>*) (AEIExp AEMIfParent2 AEIRefl) ⟩ ⟩
  reachup-e (‵ e₁ ∙₃ e₂ ∙ ê)
    with ⟨ ᾱ , ⟨ ᾱmv , ê+>* ⟩ ⟩ ← reachup-e ê
       = ⟨ ᾱ ++ ∣[ move parent ] ,
         ⟨ movements-++ ᾱmv (AMICons parent AMINil) ,
           +e>*-++ (ziplem-if3 ê+>*) (AEIExp AEMIfParent3 AEIRefl) ⟩ ⟩
  reachup-e (‵⟨ ê ,₁ e ⟩)
    with ⟨ ᾱ , ⟨ ᾱmv , ê+>* ⟩ ⟩ ← reachup-e ê
       = ⟨ ᾱ ++ ∣[ move parent ] ,
         ⟨ movements-++ ᾱmv (AMICons parent AMINil) ,
           +e>*-++ (ziplem-pair1 ê+>*) (AEIExp AEMPairParent1 AEIRefl) ⟩ ⟩
  reachup-e (‵⟨ e ,₂ ê ⟩)
    with ⟨ ᾱ , ⟨ ᾱmv , ê+>* ⟩ ⟩ ← reachup-e ê
       = ⟨ ᾱ ++ ∣[ move parent ] ,
         ⟨ movements-++ ᾱmv (AMICons parent AMINil) ,
           +e>*-++ (ziplem-pair2 ê+>*) (AEIExp AEMPairParent2 AEIRefl) ⟩ ⟩
  reachup-e (‵π₁ ê)
    with ⟨ ᾱ , ⟨ ᾱmv , ê+>* ⟩ ⟩ ← reachup-e ê
       = ⟨ ᾱ ++ ∣[ move parent ] ,
         ⟨ movements-++ ᾱmv (AMICons parent AMINil) ,
           +e>*-++ (ziplem-projl ê+>*) (AEIExp AEMProjLParent AEIRefl) ⟩ ⟩
  reachup-e (‵π₂ ê)
    with ⟨ ᾱ , ⟨ ᾱmv , ê+>* ⟩ ⟩ ← reachup-e ê
       = ⟨ ᾱ ++ ∣[ move parent ] ,
         ⟨ movements-++ ᾱmv (AMICons parent AMINil) ,
           +e>*-++ (ziplem-projr ê+>*) (AEIExp AEMProjRParent AEIRefl) ⟩ ⟩

  -- reach down for types
  reachdown-τ : (τ^ : ZTyp) → ∃[ ᾱ ] ᾱ movements ×  ▹ τ^ ◇τ ◃ + ᾱ +τ>* τ^
  reachdown-τ ▹ τ ◃ = ⟨ [] , ⟨ AMINil , ATIRefl ⟩ ⟩
  reachdown-τ (τ^ -→₁ τ)
    with ⟨ ᾱ , ⟨ ᾱmv , +>*τ^ ⟩ ⟩ ← reachdown-τ τ^
       = ⟨ move (child 1) ∷ ᾱ ,
         ⟨ AMICons (child 1) ᾱmv ,
           ATITyp ATMArrChild1 (ziplem-tarr1 +>*τ^) ⟩ ⟩
  reachdown-τ (τ -→₂ τ^)
    with ⟨ ᾱ , ⟨ ᾱmv , +>*τ^ ⟩ ⟩ ← reachdown-τ τ^
       = ⟨ move (child 2) ∷ ᾱ ,
         ⟨ AMICons (child 2) ᾱmv ,
           ATITyp ATMArrChild2 (ziplem-tarr2 +>*τ^) ⟩ ⟩
  reachdown-τ (τ^ -×₁ τ)
    with ⟨ ᾱ , ⟨ ᾱmv , +>*τ^ ⟩ ⟩ ← reachdown-τ τ^
       = ⟨ move (child 1) ∷ ᾱ ,
         ⟨ AMICons (child 1) ᾱmv ,
           ATITyp ATMProdChild1 (ziplem-tprod1 +>*τ^) ⟩ ⟩
  reachdown-τ (τ -×₂ τ^)
    with ⟨ ᾱ , ⟨ ᾱmv , +>*τ^ ⟩ ⟩ ← reachdown-τ τ^
       = ⟨ move (child 2) ∷ ᾱ ,
         ⟨ AMICons (child 2) ᾱmv ,
           ATITyp ATMProdChild2 (ziplem-tprod2 +>*τ^) ⟩ ⟩

  reachdown-e : (ê : ZExp) → ∃[ ᾱ ] ᾱ movements ×  ‵▹ ê ◇ ◃ + ᾱ +e>* ê
  reachdown-e ‵▹ e ◃ = ⟨ [] , ⟨ AMINil , AEIRefl ⟩ ⟩
  reachdown-e (‵λ₁ x ∶ τ^ ∙ e)
    with ⟨ ᾱ , ⟨ ᾱmv , +>*τ^ ⟩ ⟩ ← reachdown-τ τ^
       = ⟨ move (child 1) ∷ ᾱ ,
         ⟨ AMICons (child 1) ᾱmv ,
           AEIExp AEMLamChild1 (ziplem-lam1 +>*τ^) ⟩ ⟩
  reachdown-e (‵λ₂ x ∶ τ ∙ ê)
    with ⟨ ᾱ , ⟨ ᾱmv , +>*ê ⟩ ⟩ ← reachdown-e ê
       = ⟨ move (child 2) ∷ ᾱ ,
         ⟨ AMICons (child 2) ᾱmv ,
           AEIExp AEMLamChild2 (ziplem-lam2 +>*ê) ⟩ ⟩
  reachdown-e (‵ ê ∙₁ e)
    with ⟨ ᾱ , ⟨ ᾱmv , +>*ê ⟩ ⟩ ← reachdown-e ê
       = ⟨ move (child 1) ∷ ᾱ ,
         ⟨ AMICons (child 1) ᾱmv ,
           AEIExp AEMApChild1 (ziplem-ap1 +>*ê) ⟩ ⟩
  reachdown-e (‵ e ∙₂ ê)
    with ⟨ ᾱ , ⟨ ᾱmv , +>*ê ⟩ ⟩ ← reachdown-e ê
       = ⟨ move (child 2) ∷ ᾱ ,
         ⟨ AMICons (child 2) ᾱmv ,
           AEIExp AEMApChild2 (ziplem-ap2 +>*ê) ⟩ ⟩
  reachdown-e (‵ x ←₁ ê ∙ e)
    with ⟨ ᾱ , ⟨ ᾱmv , +>*ê ⟩ ⟩ ← reachdown-e ê
       = ⟨ move (child 1) ∷ ᾱ ,
         ⟨ AMICons (child 1) ᾱmv ,
           AEIExp AEMLetChild1 (ziplem-let1 +>*ê) ⟩ ⟩
  reachdown-e (‵ x ←₂ e ∙ ê)
    with ⟨ ᾱ , ⟨ ᾱmv , +>*ê ⟩ ⟩ ← reachdown-e ê
       = ⟨ move (child 2) ∷ ᾱ ,
         ⟨ AMICons (child 2) ᾱmv ,
           AEIExp AEMLetChild2 (ziplem-let2 +>*ê) ⟩ ⟩
  reachdown-e (‵ ê +₁ e)
    with ⟨ ᾱ , ⟨ ᾱmv , +>*ê ⟩ ⟩ ← reachdown-e ê
       = ⟨ move (child 1) ∷ ᾱ ,
         ⟨ AMICons (child 1) ᾱmv ,
           AEIExp AEMPlusChild1 (ziplem-plus1 +>*ê) ⟩ ⟩
  reachdown-e (‵ e +₂ ê)
    with ⟨ ᾱ , ⟨ ᾱmv , +>*ê ⟩ ⟩ ← reachdown-e ê
       = ⟨ move (child 2) ∷ ᾱ ,
         ⟨ AMICons (child 2) ᾱmv ,
           AEIExp AEMPlusChild2 (ziplem-plus2 +>*ê) ⟩ ⟩
  reachdown-e (‵ ê ∙₁ e₂ ∙ e₃)
    with ⟨ ᾱ , ⟨ ᾱmv , +>*ê ⟩ ⟩ ← reachdown-e ê
       = ⟨ move (child 1) ∷ ᾱ ,
         ⟨ AMICons (child 1) ᾱmv ,
           AEIExp AEMIfChild1 (ziplem-if1 +>*ê) ⟩ ⟩
  reachdown-e (‵ e₁ ∙₂ ê ∙ e₃)
    with ⟨ ᾱ , ⟨ ᾱmv , +>*ê ⟩ ⟩ ← reachdown-e ê
       = ⟨ move (child 2) ∷ ᾱ ,
         ⟨ AMICons (child 2) ᾱmv ,
           AEIExp AEMIfChild2 (ziplem-if2 +>*ê) ⟩ ⟩
  reachdown-e (‵ e₁ ∙₃ e₂ ∙ ê)
    with ⟨ ᾱ , ⟨ ᾱmv , +>*ê ⟩ ⟩ ← reachdown-e ê
       = ⟨ move (child 3) ∷ ᾱ ,
         ⟨ AMICons (child 3) ᾱmv ,
           AEIExp AEMIfChild3 (ziplem-if3 +>*ê) ⟩ ⟩
  reachdown-e (‵⟨ ê ,₁ e ⟩)
    with ⟨ ᾱ , ⟨ ᾱmv , +>*ê ⟩ ⟩ ← reachdown-e ê
       = ⟨ move (child 1) ∷ ᾱ ,
         ⟨ AMICons (child 1) ᾱmv ,
           AEIExp AEMPairChild1 (ziplem-pair1 +>*ê) ⟩ ⟩
  reachdown-e (‵⟨ e ,₂ ê ⟩)
    with ⟨ ᾱ , ⟨ ᾱmv , +>*ê ⟩ ⟩ ← reachdown-e ê
       = ⟨ move (child 2) ∷ ᾱ ,
         ⟨ AMICons (child 2) ᾱmv ,
           AEIExp AEMPairChild2 (ziplem-pair2 +>*ê) ⟩ ⟩
  reachdown-e (‵π₁ ê)
    with ⟨ ᾱ , ⟨ ᾱmv , +>*ê ⟩ ⟩ ← reachdown-e ê
       = ⟨ move (child 1) ∷ ᾱ ,
         ⟨ AMICons (child 1) ᾱmv ,
           AEIExp AEMProjLChild (ziplem-projl +>*ê) ⟩ ⟩
  reachdown-e (‵π₂ ê)
    with ⟨ ᾱ , ⟨ ᾱmv , +>*ê ⟩ ⟩ ← reachdown-e ê
       = ⟨ move (child 1) ∷ ᾱ ,
         ⟨ AMICons (child 1) ᾱmv ,
           AEIExp AEMProjRChild (ziplem-projr +>*ê) ⟩ ⟩

  reachability-τ : (τ₁^ τ₂^ : ZTyp) → τ₁^ ◇τ ≡ τ₂^ ◇τ → ∃[ ᾱ ] ᾱ movements × τ₁^ + ᾱ +τ>* τ₂^
  reachability-τ τ₁^ τ₂^ eq
    with ⟨ ᾱ₁ , ⟨ ᾱ₁mv , τ₁^+>*  ⟩ ⟩ ← reachup-τ τ₁^
       | ⟨ ᾱ₂ , ⟨ ᾱ₂mv , +>*τ₂^  ⟩ ⟩ ← reachdown-τ τ₂^
       = ⟨ ᾱ₁ ++ ᾱ₂ , ⟨ movements-++ ᾱ₁mv ᾱ₂mv , +τ>*-++ τ₁^+>* (transport (λ { τ → ▹ τ ◃ + ᾱ₂ +τ>* τ₂^ }) (≡-sym eq) +>*τ₂^) ⟩ ⟩

  reachability-e : (ê₁ ê₂ : ZExp) → ê₁ ◇ ≡ ê₂ ◇ → ∃[ ᾱ ] ᾱ movements × ê₁ + ᾱ +e>* ê₂
  reachability-e ê₁ ê₂ eq
    with ⟨ ᾱ₁ , ⟨ ᾱ₁mv , ê₁+>*  ⟩ ⟩ ← reachup-e ê₁
       | ⟨ ᾱ₂ , ⟨ ᾱ₂mv , +>*ê₂  ⟩ ⟩ ← reachdown-e ê₂
       = ⟨ ᾱ₁ ++ ᾱ₂ , ⟨ movements-++ ᾱ₁mv ᾱ₂mv , +e>*-++ ê₁+>* (transport (λ { e → ‵▹ e ◃ + ᾱ₂ +e>* ê₂ }) (≡-sym eq) +>*ê₂) ⟩ ⟩
