open import prelude
open import core

open import hazelnut.action
open import hazelnut.untyped.zexp
open import hazelnut.untyped.action
open import hazelnut.untyped.erasure

module hazelnut.untyped.determinism where
  determinism-τ : ∀ {τ^ τ^′ τ^″ α} → τ^ + α +τ> τ^′ → τ^ + α +τ> τ^″ → τ^′ ≡ τ^″
  determinism-τ TMArrChild1        TMArrChild1   = refl
  determinism-τ TMArrChild2        TMArrChild2   = refl
  determinism-τ TMArrParent1       TMArrParent1  = refl
  determinism-τ TMArrParent1       (TZipArr1 ())
  determinism-τ TMArrParent2       TMArrParent2  = refl
  determinism-τ TMArrParent2       (TZipArr2 ())
  determinism-τ TMProdChild1       TMProdChild1  = refl
  determinism-τ TMProdChild2       TMProdChild2  = refl
  determinism-τ TMProdParent1      TMProdParent1 = refl
  determinism-τ TMProdParent1      (TZipProd1 ())
  determinism-τ TMProdParent2      TMProdParent2 = refl
  determinism-τ TMProdParent2      (TZipProd2 ())
  determinism-τ TDel               TDel          = refl
  determinism-τ TConArrow1         TConArrow1    = refl
  determinism-τ TConArrow2         TConArrow2    = refl
  determinism-τ TConProd1          TConProd1     = refl
  determinism-τ TConProd2          TConProd2     = refl
  determinism-τ TConNum            TConNum       = refl
  determinism-τ TConBool           TConBool      = refl
  determinism-τ (TZipArr1 ())      TMArrParent1
  determinism-τ (TZipArr1 τ^+>τ^′) (TZipArr1 τ^+>τ^″)
    rewrite determinism-τ τ^+>τ^′ τ^+>τ^″        = refl
  determinism-τ (TZipArr2 τ^+>τ^′) (TZipArr2 τ^+>τ^″)
    rewrite determinism-τ τ^+>τ^′ τ^+>τ^″        = refl
  determinism-τ (TZipProd1 τ^+>τ^′) (TZipProd1 τ^+>τ^″)
    rewrite determinism-τ τ^+>τ^′ τ^+>τ^″        = refl
  determinism-τ (TZipProd2 τ^+>τ^′) (TZipProd2 τ^+>τ^″)
    rewrite determinism-τ τ^+>τ^′ τ^+>τ^″        = refl

  determinism*-τ : ∀ {τ^ τ^′ τ^″ ᾱ} → τ^ + ᾱ +τ>* τ^′ → τ^ + ᾱ +τ>* τ^″ → τ^′ ≡ τ^″
  determinism*-τ TIRefl                     TIRefl = refl
  determinism*-τ (TITyp τ₁^+>τ₂^ τ₂^+>*τ₃^) (TITyp τ₁^+>τ₂^′ τ₂^+>*τ₃^′)
    rewrite determinism-τ τ₁^+>τ₂^ τ₁^+>τ₂^′
    rewrite determinism*-τ τ₂^+>*τ₃^ τ₂^+>*τ₃^′    = refl

  determinism-e : ∀ {ê ê′ ê″ α} → ê + α +e> ê′ → ê + α +e> ê″ → ê′ ≡ ê″
  determinism-e EMLamChild1        EMLamChild1   = refl
  determinism-e EMLamChild2        EMLamChild2   = refl
  determinism-e EMLamParent1       EMLamParent1  = refl
  determinism-e EMLamParent2       EMLamParent2  = refl
  determinism-e EMApChild1         EMApChild1    = refl
  determinism-e EMApChild2         EMApChild2    = refl
  determinism-e EMApParent1        EMApParent1   = refl
  determinism-e EMApParent2        EMApParent2   = refl
  determinism-e EMLetChild1        EMLetChild1   = refl
  determinism-e EMLetChild2        EMLetChild2   = refl
  determinism-e EMLetParent1       EMLetParent1  = refl
  determinism-e EMLetParent2       EMLetParent2  = refl
  determinism-e EMPlusChild1       EMPlusChild1  = refl
  determinism-e EMPlusChild2       EMPlusChild2  = refl
  determinism-e EMPlusParent1      EMPlusParent1 = refl
  determinism-e EMPlusParent2      EMPlusParent2 = refl
  determinism-e EMIfChild1         EMIfChild1    = refl
  determinism-e EMIfChild2         EMIfChild2    = refl
  determinism-e EMIfChild3         EMIfChild3    = refl
  determinism-e EMIfParent1        EMIfParent1   = refl
  determinism-e EMIfParent2        EMIfParent2   = refl
  determinism-e EMIfParent3        EMIfParent3   = refl
  determinism-e EMPairChild1       EMPairChild1  = refl
  determinism-e EMPairChild2       EMPairChild2  = refl
  determinism-e EMPairParent1      EMPairParent1 = refl
  determinism-e EMPairParent2      EMPairParent2 = refl
  determinism-e EMProjLChild       EMProjLChild  = refl
  determinism-e EMProjLParent      EMProjLParent = refl
  determinism-e EMProjRChild       EMProjRChild  = refl
  determinism-e EMProjRParent      EMProjRParent = refl
  determinism-e EDel               EDel          = refl
  determinism-e EConVar            EConVar       = refl
  determinism-e EConLam            EConLam       = refl
  determinism-e EConAp1            EConAp1       = refl
  determinism-e EConAp2            EConAp2       = refl
  determinism-e EConLet1           EConLet1      = refl
  determinism-e EConLet2           EConLet2      = refl
  determinism-e EConNum            EConNum       = refl
  determinism-e EConPlus1          EConPlus1     = refl
  determinism-e EConPlus2          EConPlus2     = refl
  determinism-e EConTrue           EConTrue      = refl
  determinism-e EConFalse          EConFalse     = refl
  determinism-e EConIf1            EConIf1       = refl
  determinism-e EConIf2            EConIf2       = refl
  determinism-e EConIf3            EConIf3       = refl
  determinism-e EConPair1          EConPair1     = refl
  determinism-e EConPair2          EConPair2     = refl
  determinism-e EConProjL          EConProjL     = refl
  determinism-e EConProjR          EConProjR     = refl
  determinism-e (EZipLam1 τ^+>τ^′) (EZipLam1 τ^+>τ^″)
    rewrite determinism-τ τ^+>τ^′ τ^+>τ^″        = refl
  determinism-e (EZipLam2 ê+>ê′)   (EZipLam2 ê+>ê″)
    rewrite determinism-e ê+>ê′ ê+>ê″            = refl
  determinism-e (EZipAp1 ê+>ê′)    (EZipAp1 ê+>ê″)
    rewrite determinism-e ê+>ê′ ê+>ê″            = refl
  determinism-e (EZipAp2 ê+>ê′)    (EZipAp2 ê+>ê″)
    rewrite determinism-e ê+>ê′ ê+>ê″            = refl
  determinism-e (EZipLet1 ê+>ê′)   (EZipLet1 ê+>ê″)
    rewrite determinism-e ê+>ê′ ê+>ê″            = refl
  determinism-e (EZipLet2 ê+>ê′)   (EZipLet2 ê+>ê″)
    rewrite determinism-e ê+>ê′ ê+>ê″            = refl
  determinism-e (EZipPlus1 ê+>ê′)  (EZipPlus1 ê+>ê″)
    rewrite determinism-e ê+>ê′ ê+>ê″            = refl
  determinism-e (EZipPlus2 ê+>ê′)  (EZipPlus2 ê+>ê″)
    rewrite determinism-e ê+>ê′ ê+>ê″            = refl
  determinism-e (EZipIf1 ê+>ê′)    (EZipIf1 ê+>ê″)
    rewrite determinism-e ê+>ê′ ê+>ê″            = refl
  determinism-e (EZipIf2 ê+>ê′)    (EZipIf2 ê+>ê″)
    rewrite determinism-e ê+>ê′ ê+>ê″            = refl
  determinism-e (EZipIf3 ê+>ê′)    (EZipIf3 ê+>ê″)
    rewrite determinism-e ê+>ê′ ê+>ê″            = refl
  determinism-e (EZipPair1 ê+>ê′)  (EZipPair1 ê+>ê″)
    rewrite determinism-e ê+>ê′ ê+>ê″            = refl
  determinism-e (EZipPair2 ê+>ê′)  (EZipPair2 ê+>ê″)
    rewrite determinism-e ê+>ê′ ê+>ê″            = refl
  determinism-e (EZipProjL ê+>ê′)  (EZipProjL ê+>ê″)
    rewrite determinism-e ê+>ê′ ê+>ê″            = refl
  determinism-e (EZipProjR ê+>ê′)  (EZipProjR ê+>ê″)
    rewrite determinism-e ê+>ê′ ê+>ê″            = refl

  determinism*-e : ∀ {ê ê′ ê″ ᾱ} → ê + ᾱ +e>* ê′ → ê + ᾱ +e>* ê″ → ê′ ≡ ê″
  determinism*-e EIRefl                 EIRefl = refl
  determinism*-e (EIExp ê₁+>ê₂ ê₂+>*ê₃) (EIExp ê₁+>ê₂′ ê₂+>*ê₃′)
    rewrite determinism-e ê₁+>ê₂ ê₁+>ê₂′
    rewrite determinism*-e ê₂+>*ê₃ ê₂+>*ê₃′    = refl
