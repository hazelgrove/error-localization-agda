open import prelude
open import core

open import hazelnut.action
open import hazelnut.untyped.zexp
open import hazelnut.untyped.action
open import hazelnut.untyped.erasure

module hazelnut.untyped.reachability where
  -- reach up for types
  reachup-τ : (τ^ : ZTyp) → ∃[ ᾱ ] ᾱ movements × τ^ + ᾱ +τ>* ▹ τ^ ◇τ ◃
  reachup-τ ▹ τ ◃ = ⟨ [] , ⟨ AMINil , TIRefl ⟩ ⟩
  reachup-τ (τ^ -→₁ τ)
    with ⟨ ᾱ , ⟨ ᾱmv , τ^+>* ⟩ ⟩ ← reachup-τ τ^
       = ⟨ ᾱ ++ ∣[ move parent ] ,
         ⟨ movements-++ ᾱmv (AMICons parent AMINil) ,
           +τ>*-++ (ziplem-tarr1 τ^+>*) (TITyp TMArrParent1 TIRefl) ⟩ ⟩
  reachup-τ (τ -→₂ τ^)
    with ⟨ ᾱ , ⟨ ᾱmv , τ^+>* ⟩ ⟩ ← reachup-τ τ^
       = ⟨ ᾱ ++ ∣[ move parent ] ,
         ⟨ movements-++ ᾱmv (AMICons parent AMINil) ,
           +τ>*-++ (ziplem-tarr2 τ^+>*) (TITyp TMArrParent2 TIRefl) ⟩ ⟩
  reachup-τ (τ^ -×₁ τ)
    with ⟨ ᾱ , ⟨ ᾱmv , τ^+>* ⟩ ⟩ ← reachup-τ τ^
       = ⟨ ᾱ ++ ∣[ move parent ] ,
         ⟨ movements-++ ᾱmv (AMICons parent AMINil) ,
           +τ>*-++ (ziplem-tprod1 τ^+>*) (TITyp TMProdParent1 TIRefl) ⟩ ⟩
  reachup-τ (τ -×₂ τ^)
    with ⟨ ᾱ , ⟨ ᾱmv , τ^+>* ⟩ ⟩ ← reachup-τ τ^
       = ⟨ ᾱ ++ ∣[ move parent ] ,
         ⟨ movements-++ ᾱmv (AMICons parent AMINil) ,
           +τ>*-++ (ziplem-tprod2 τ^+>*) (TITyp TMProdParent2 TIRefl) ⟩ ⟩

  -- reach up for expressions
  reachup-e : (ê : ZExp) → ∃[ ᾱ ] ᾱ movements × ê + ᾱ +e>* ‵▹ ê ◇ ◃
  reachup-e ‵▹ e ◃ = ⟨ [] , ⟨ AMINil , EIRefl ⟩ ⟩
  reachup-e (‵λ₁ x ∶ τ^ ∙ e)
    with ⟨ ᾱ , ⟨ ᾱmv , τ^+>* ⟩ ⟩ ← reachup-τ τ^
       = ⟨ ᾱ ++ ∣[ move parent ] ,
         ⟨ movements-++ ᾱmv (AMICons parent AMINil) ,
           +e>*-++ (ziplem-lam1 τ^+>*) (EIExp EMLamParent1 EIRefl) ⟩ ⟩
  reachup-e (‵λ₂ x ∶ τ ∙ ê)
    with ⟨ ᾱ , ⟨ ᾱmv , ê+>* ⟩ ⟩ ← reachup-e ê
       = ⟨ ᾱ ++ ∣[ move parent ] ,
         ⟨ movements-++ ᾱmv (AMICons parent AMINil) ,
           +e>*-++ (ziplem-lam2 ê+>*) (EIExp EMLamParent2 EIRefl) ⟩ ⟩
  reachup-e (‵ ê ∙₁ e)
    with ⟨ ᾱ , ⟨ ᾱmv , ê+>* ⟩ ⟩ ← reachup-e ê
       = ⟨ ᾱ ++ ∣[ move parent ] ,
         ⟨ movements-++ ᾱmv (AMICons parent AMINil) ,
           +e>*-++ (ziplem-ap1 ê+>*) (EIExp EMApParent1 EIRefl) ⟩ ⟩
  reachup-e (‵ e ∙₂ ê)
    with ⟨ ᾱ , ⟨ ᾱmv , ê+>* ⟩ ⟩ ← reachup-e ê
       = ⟨ ᾱ ++ ∣[ move parent ] ,
         ⟨ movements-++ ᾱmv (AMICons parent AMINil) ,
           +e>*-++ (ziplem-ap2 ê+>*) (EIExp EMApParent2 EIRefl) ⟩ ⟩
  reachup-e (‵ x ←₁ ê ∙ e)
    with ⟨ ᾱ , ⟨ ᾱmv , ê+>* ⟩ ⟩ ← reachup-e ê
       = ⟨ ᾱ ++ ∣[ move parent ] ,
         ⟨ movements-++ ᾱmv (AMICons parent AMINil) ,
           +e>*-++ (ziplem-let1 ê+>*) (EIExp EMLetParent1 EIRefl) ⟩ ⟩
  reachup-e (‵ x ←₂ e ∙ ê)
    with ⟨ ᾱ , ⟨ ᾱmv , ê+>* ⟩ ⟩ ← reachup-e ê
       = ⟨ ᾱ ++ ∣[ move parent ] ,
         ⟨ movements-++ ᾱmv (AMICons parent AMINil) ,
           +e>*-++ (ziplem-let2 ê+>*) (EIExp EMLetParent2 EIRefl) ⟩ ⟩
  reachup-e (‵ ê +₁ e)
    with ⟨ ᾱ , ⟨ ᾱmv , ê+>* ⟩ ⟩ ← reachup-e ê
       = ⟨ ᾱ ++ ∣[ move parent ] ,
         ⟨ movements-++ ᾱmv (AMICons parent AMINil) ,
           +e>*-++ (ziplem-plus1 ê+>*) (EIExp EMPlusParent1 EIRefl) ⟩ ⟩
  reachup-e (‵ e +₂ ê)
    with ⟨ ᾱ , ⟨ ᾱmv , ê+>* ⟩ ⟩ ← reachup-e ê
       = ⟨ ᾱ ++ ∣[ move parent ] ,
         ⟨ movements-++ ᾱmv (AMICons parent AMINil) ,
           +e>*-++ (ziplem-plus2 ê+>*) (EIExp EMPlusParent2 EIRefl) ⟩ ⟩
  reachup-e (‵ ê ∙₁ e₂ ∙ e₃)
    with ⟨ ᾱ , ⟨ ᾱmv , ê+>* ⟩ ⟩ ← reachup-e ê
       = ⟨ ᾱ ++ ∣[ move parent ] ,
         ⟨ movements-++ ᾱmv (AMICons parent AMINil) ,
           +e>*-++ (ziplem-if1 ê+>*) (EIExp EMIfParent1 EIRefl) ⟩ ⟩
  reachup-e (‵ e₁ ∙₂ ê ∙ e₃)
    with ⟨ ᾱ , ⟨ ᾱmv , ê+>* ⟩ ⟩ ← reachup-e ê
       = ⟨ ᾱ ++ ∣[ move parent ] ,
         ⟨ movements-++ ᾱmv (AMICons parent AMINil) ,
           +e>*-++ (ziplem-if2 ê+>*) (EIExp EMIfParent2 EIRefl) ⟩ ⟩
  reachup-e (‵ e₁ ∙₃ e₂ ∙ ê)
    with ⟨ ᾱ , ⟨ ᾱmv , ê+>* ⟩ ⟩ ← reachup-e ê
       = ⟨ ᾱ ++ ∣[ move parent ] ,
         ⟨ movements-++ ᾱmv (AMICons parent AMINil) ,
           +e>*-++ (ziplem-if3 ê+>*) (EIExp EMIfParent3 EIRefl) ⟩ ⟩
  reachup-e (‵⟨ ê ,₁ e ⟩)
    with ⟨ ᾱ , ⟨ ᾱmv , ê+>* ⟩ ⟩ ← reachup-e ê
       = ⟨ ᾱ ++ ∣[ move parent ] ,
         ⟨ movements-++ ᾱmv (AMICons parent AMINil) ,
           +e>*-++ (ziplem-pair1 ê+>*) (EIExp EMPairParent1 EIRefl) ⟩ ⟩
  reachup-e (‵⟨ e ,₂ ê ⟩)
    with ⟨ ᾱ , ⟨ ᾱmv , ê+>* ⟩ ⟩ ← reachup-e ê
       = ⟨ ᾱ ++ ∣[ move parent ] ,
         ⟨ movements-++ ᾱmv (AMICons parent AMINil) ,
           +e>*-++ (ziplem-pair2 ê+>*) (EIExp EMPairParent2 EIRefl) ⟩ ⟩
  reachup-e (‵π₁ ê)
    with ⟨ ᾱ , ⟨ ᾱmv , ê+>* ⟩ ⟩ ← reachup-e ê
       = ⟨ ᾱ ++ ∣[ move parent ] ,
         ⟨ movements-++ ᾱmv (AMICons parent AMINil) ,
           +e>*-++ (ziplem-projl ê+>*) (EIExp EMProjLParent EIRefl) ⟩ ⟩
  reachup-e (‵π₂ ê)
    with ⟨ ᾱ , ⟨ ᾱmv , ê+>* ⟩ ⟩ ← reachup-e ê
       = ⟨ ᾱ ++ ∣[ move parent ] ,
         ⟨ movements-++ ᾱmv (AMICons parent AMINil) ,
           +e>*-++ (ziplem-projr ê+>*) (EIExp EMProjRParent EIRefl) ⟩ ⟩

  -- reach down for types
  reachdown-τ : (τ^ : ZTyp) → ∃[ ᾱ ] ᾱ movements ×  ▹ τ^ ◇τ ◃ + ᾱ +τ>* τ^
  reachdown-τ ▹ τ ◃ = ⟨ [] , ⟨ AMINil , TIRefl ⟩ ⟩
  reachdown-τ (τ^ -→₁ τ)
    with ⟨ ᾱ , ⟨ ᾱmv , +>*τ^ ⟩ ⟩ ← reachdown-τ τ^
       = ⟨ move (child 1) ∷ ᾱ ,
         ⟨ AMICons (child 1) ᾱmv ,
           TITyp TMArrChild1 (ziplem-tarr1 +>*τ^) ⟩ ⟩
  reachdown-τ (τ -→₂ τ^)
    with ⟨ ᾱ , ⟨ ᾱmv , +>*τ^ ⟩ ⟩ ← reachdown-τ τ^
       = ⟨ move (child 2) ∷ ᾱ ,
         ⟨ AMICons (child 2) ᾱmv ,
           TITyp TMArrChild2 (ziplem-tarr2 +>*τ^) ⟩ ⟩
  reachdown-τ (τ^ -×₁ τ)
    with ⟨ ᾱ , ⟨ ᾱmv , +>*τ^ ⟩ ⟩ ← reachdown-τ τ^
       = ⟨ move (child 1) ∷ ᾱ ,
         ⟨ AMICons (child 1) ᾱmv ,
           TITyp TMProdChild1 (ziplem-tprod1 +>*τ^) ⟩ ⟩
  reachdown-τ (τ -×₂ τ^)
    with ⟨ ᾱ , ⟨ ᾱmv , +>*τ^ ⟩ ⟩ ← reachdown-τ τ^
       = ⟨ move (child 2) ∷ ᾱ ,
         ⟨ AMICons (child 2) ᾱmv ,
           TITyp TMProdChild2 (ziplem-tprod2 +>*τ^) ⟩ ⟩

  reachdown-e : (ê : ZExp) → ∃[ ᾱ ] ᾱ movements ×  ‵▹ ê ◇ ◃ + ᾱ +e>* ê
  reachdown-e ‵▹ e ◃ = ⟨ [] , ⟨ AMINil , EIRefl ⟩ ⟩
  reachdown-e (‵λ₁ x ∶ τ^ ∙ e)
    with ⟨ ᾱ , ⟨ ᾱmv , +>*τ^ ⟩ ⟩ ← reachdown-τ τ^
       = ⟨ move (child 1) ∷ ᾱ ,
         ⟨ AMICons (child 1) ᾱmv ,
           EIExp EMLamChild1 (ziplem-lam1 +>*τ^) ⟩ ⟩
  reachdown-e (‵λ₂ x ∶ τ ∙ ê)
    with ⟨ ᾱ , ⟨ ᾱmv , +>*ê ⟩ ⟩ ← reachdown-e ê
       = ⟨ move (child 2) ∷ ᾱ ,
         ⟨ AMICons (child 2) ᾱmv ,
           EIExp EMLamChild2 (ziplem-lam2 +>*ê) ⟩ ⟩
  reachdown-e (‵ ê ∙₁ e)
    with ⟨ ᾱ , ⟨ ᾱmv , +>*ê ⟩ ⟩ ← reachdown-e ê
       = ⟨ move (child 1) ∷ ᾱ ,
         ⟨ AMICons (child 1) ᾱmv ,
           EIExp EMApChild1 (ziplem-ap1 +>*ê) ⟩ ⟩
  reachdown-e (‵ e ∙₂ ê)
    with ⟨ ᾱ , ⟨ ᾱmv , +>*ê ⟩ ⟩ ← reachdown-e ê
       = ⟨ move (child 2) ∷ ᾱ ,
         ⟨ AMICons (child 2) ᾱmv ,
           EIExp EMApChild2 (ziplem-ap2 +>*ê) ⟩ ⟩
  reachdown-e (‵ x ←₁ ê ∙ e)
    with ⟨ ᾱ , ⟨ ᾱmv , +>*ê ⟩ ⟩ ← reachdown-e ê
       = ⟨ move (child 1) ∷ ᾱ ,
         ⟨ AMICons (child 1) ᾱmv ,
           EIExp EMLetChild1 (ziplem-let1 +>*ê) ⟩ ⟩
  reachdown-e (‵ x ←₂ e ∙ ê)
    with ⟨ ᾱ , ⟨ ᾱmv , +>*ê ⟩ ⟩ ← reachdown-e ê
       = ⟨ move (child 2) ∷ ᾱ ,
         ⟨ AMICons (child 2) ᾱmv ,
           EIExp EMLetChild2 (ziplem-let2 +>*ê) ⟩ ⟩
  reachdown-e (‵ ê +₁ e)
    with ⟨ ᾱ , ⟨ ᾱmv , +>*ê ⟩ ⟩ ← reachdown-e ê
       = ⟨ move (child 1) ∷ ᾱ ,
         ⟨ AMICons (child 1) ᾱmv ,
           EIExp EMPlusChild1 (ziplem-plus1 +>*ê) ⟩ ⟩
  reachdown-e (‵ e +₂ ê)
    with ⟨ ᾱ , ⟨ ᾱmv , +>*ê ⟩ ⟩ ← reachdown-e ê
       = ⟨ move (child 2) ∷ ᾱ ,
         ⟨ AMICons (child 2) ᾱmv ,
           EIExp EMPlusChild2 (ziplem-plus2 +>*ê) ⟩ ⟩
  reachdown-e (‵ ê ∙₁ e₂ ∙ e₃)
    with ⟨ ᾱ , ⟨ ᾱmv , +>*ê ⟩ ⟩ ← reachdown-e ê
       = ⟨ move (child 1) ∷ ᾱ ,
         ⟨ AMICons (child 1) ᾱmv ,
           EIExp EMIfChild1 (ziplem-if1 +>*ê) ⟩ ⟩
  reachdown-e (‵ e₁ ∙₂ ê ∙ e₃)
    with ⟨ ᾱ , ⟨ ᾱmv , +>*ê ⟩ ⟩ ← reachdown-e ê
       = ⟨ move (child 2) ∷ ᾱ ,
         ⟨ AMICons (child 2) ᾱmv ,
           EIExp EMIfChild2 (ziplem-if2 +>*ê) ⟩ ⟩
  reachdown-e (‵ e₁ ∙₃ e₂ ∙ ê)
    with ⟨ ᾱ , ⟨ ᾱmv , +>*ê ⟩ ⟩ ← reachdown-e ê
       = ⟨ move (child 3) ∷ ᾱ ,
         ⟨ AMICons (child 3) ᾱmv ,
           EIExp EMIfChild3 (ziplem-if3 +>*ê) ⟩ ⟩
  reachdown-e (‵⟨ ê ,₁ e ⟩)
    with ⟨ ᾱ , ⟨ ᾱmv , +>*ê ⟩ ⟩ ← reachdown-e ê
       = ⟨ move (child 1) ∷ ᾱ ,
         ⟨ AMICons (child 1) ᾱmv ,
           EIExp EMPairChild1 (ziplem-pair1 +>*ê) ⟩ ⟩
  reachdown-e (‵⟨ e ,₂ ê ⟩)
    with ⟨ ᾱ , ⟨ ᾱmv , +>*ê ⟩ ⟩ ← reachdown-e ê
       = ⟨ move (child 2) ∷ ᾱ ,
         ⟨ AMICons (child 2) ᾱmv ,
           EIExp EMPairChild2 (ziplem-pair2 +>*ê) ⟩ ⟩
  reachdown-e (‵π₁ ê)
    with ⟨ ᾱ , ⟨ ᾱmv , +>*ê ⟩ ⟩ ← reachdown-e ê
       = ⟨ move (child 1) ∷ ᾱ ,
         ⟨ AMICons (child 1) ᾱmv ,
           EIExp EMProjLChild (ziplem-projl +>*ê) ⟩ ⟩
  reachdown-e (‵π₂ ê)
    with ⟨ ᾱ , ⟨ ᾱmv , +>*ê ⟩ ⟩ ← reachdown-e ê
       = ⟨ move (child 1) ∷ ᾱ ,
         ⟨ AMICons (child 1) ᾱmv ,
           EIExp EMProjRChild (ziplem-projr +>*ê) ⟩ ⟩

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
