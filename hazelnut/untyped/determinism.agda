open import prelude
open import core

open import hazelnut.action
open import hazelnut.untyped.zexp
open import hazelnut.untyped.action
open import hazelnut.untyped.erasure

module hazelnut.untyped.determinism where
  determinism-τ : ∀ {τ^ τ^′ τ^″ α} → τ^ + α +τ> τ^′ → τ^ + α +τ> τ^″ → τ^′ ≡ τ^″
  determinism-τ ATMArrChild1        ATMArrChild1   = refl
  determinism-τ ATMArrChild2        ATMArrChild2   = refl
  determinism-τ ATMArrParent1       ATMArrParent1  = refl
  determinism-τ ATMArrParent1       (ATZipArr1 ())
  determinism-τ ATMArrParent2       ATMArrParent2  = refl
  determinism-τ ATMArrParent2       (ATZipArr2 ())
  determinism-τ ATMProdChild1       ATMProdChild1  = refl
  determinism-τ ATMProdChild2       ATMProdChild2  = refl
  determinism-τ ATMProdParent1      ATMProdParent1 = refl
  determinism-τ ATMProdParent1      (ATZipProd1 ())
  determinism-τ ATMProdParent2      ATMProdParent2 = refl
  determinism-τ ATMProdParent2      (ATZipProd2 ())
  determinism-τ ATDel               ATDel          = refl
  determinism-τ ATConArrow1         ATConArrow1    = refl
  determinism-τ ATConArrow2         ATConArrow2    = refl
  determinism-τ ATConProd1          ATConProd1     = refl
  determinism-τ ATConProd2          ATConProd2     = refl
  determinism-τ ATConNum            ATConNum       = refl
  determinism-τ ATConBool           ATConBool      = refl
  determinism-τ (ATZipArr1 ())      ATMArrParent1
  determinism-τ (ATZipArr1 τ^+>τ^′) (ATZipArr1 τ^+>τ^″)
    rewrite determinism-τ τ^+>τ^′ τ^+>τ^″        = refl
  determinism-τ (ATZipArr2 τ^+>τ^′) (ATZipArr2 τ^+>τ^″)
    rewrite determinism-τ τ^+>τ^′ τ^+>τ^″        = refl
  determinism-τ (ATZipProd1 τ^+>τ^′) (ATZipProd1 τ^+>τ^″)
    rewrite determinism-τ τ^+>τ^′ τ^+>τ^″        = refl
  determinism-τ (ATZipProd2 τ^+>τ^′) (ATZipProd2 τ^+>τ^″)
    rewrite determinism-τ τ^+>τ^′ τ^+>τ^″        = refl

  determinism*-τ : ∀ {τ^ τ^′ τ^″ ᾱ} → τ^ + ᾱ +τ>* τ^′ → τ^ + ᾱ +τ>* τ^″ → τ^′ ≡ τ^″
  determinism*-τ ATIRefl                     ATIRefl = refl
  determinism*-τ (ATITyp τ₁^+>τ₂^ τ₂^+>*τ₃^) (ATITyp τ₁^+>τ₂^′ τ₂^+>*τ₃^′)
    rewrite determinism-τ τ₁^+>τ₂^ τ₁^+>τ₂^′
    rewrite determinism*-τ τ₂^+>*τ₃^ τ₂^+>*τ₃^′    = refl

  determinism-e : ∀ {ê ê′ ê″ α} → ê + α +e> ê′ → ê + α +e> ê″ → ê′ ≡ ê″
  determinism-e AEMLamChild1        AEMLamChild1   = refl
  determinism-e AEMLamChild2        AEMLamChild2   = refl
  determinism-e AEMLamParent1       AEMLamParent1  = refl
  determinism-e AEMLamParent2       AEMLamParent2  = refl
  determinism-e AEMApChild1         AEMApChild1    = refl
  determinism-e AEMApChild2         AEMApChild2    = refl
  determinism-e AEMApParent1        AEMApParent1   = refl
  determinism-e AEMApParent2        AEMApParent2   = refl
  determinism-e AEMLetChild1        AEMLetChild1   = refl
  determinism-e AEMLetChild2        AEMLetChild2   = refl
  determinism-e AEMLetParent1       AEMLetParent1  = refl
  determinism-e AEMLetParent2       AEMLetParent2  = refl
  determinism-e AEMPlusChild1       AEMPlusChild1  = refl
  determinism-e AEMPlusChild2       AEMPlusChild2  = refl
  determinism-e AEMPlusParent1      AEMPlusParent1 = refl
  determinism-e AEMPlusParent2      AEMPlusParent2 = refl
  determinism-e AEMIfChild1         AEMIfChild1    = refl
  determinism-e AEMIfChild2         AEMIfChild2    = refl
  determinism-e AEMIfChild3         AEMIfChild3    = refl
  determinism-e AEMIfParent1        AEMIfParent1   = refl
  determinism-e AEMIfParent2        AEMIfParent2   = refl
  determinism-e AEMIfParent3        AEMIfParent3   = refl
  determinism-e AEMPairChild1       AEMPairChild1  = refl
  determinism-e AEMPairChild2       AEMPairChild2  = refl
  determinism-e AEMPairParent1      AEMPairParent1 = refl
  determinism-e AEMPairParent2      AEMPairParent2 = refl
  determinism-e AEMProjLChild       AEMProjLChild  = refl
  determinism-e AEMProjLParent      AEMProjLParent = refl
  determinism-e AEMProjRChild       AEMProjRChild  = refl
  determinism-e AEMProjRParent      AEMProjRParent = refl
  determinism-e AEDel               AEDel          = refl
  determinism-e AEConVar            AEConVar       = refl
  determinism-e AEConLam            AEConLam       = refl
  determinism-e AEConAp1            AEConAp1       = refl
  determinism-e AEConAp2            AEConAp2       = refl
  determinism-e AEConLet1           AEConLet1      = refl
  determinism-e AEConLet2           AEConLet2      = refl
  determinism-e AEConNum            AEConNum       = refl
  determinism-e AEConPlus1          AEConPlus1     = refl
  determinism-e AEConPlus2          AEConPlus2     = refl
  determinism-e AEConTrue           AEConTrue      = refl
  determinism-e AEConFalse          AEConFalse     = refl
  determinism-e AEConIf1            AEConIf1       = refl
  determinism-e AEConIf2            AEConIf2       = refl
  determinism-e AEConIf3            AEConIf3       = refl
  determinism-e AEConPair1          AEConPair1     = refl
  determinism-e AEConPair2          AEConPair2     = refl
  determinism-e AEConProjL          AEConProjL     = refl
  determinism-e AEConProjR          AEConProjR     = refl
  determinism-e (AEZipLam1 τ^+>τ^′) (AEZipLam1 τ^+>τ^″)
    rewrite determinism-τ τ^+>τ^′ τ^+>τ^″        = refl
  determinism-e (AEZipLam2 ê+>ê′)   (AEZipLam2 ê+>ê″)
    rewrite determinism-e ê+>ê′ ê+>ê″            = refl
  determinism-e (AEZipAp1 ê+>ê′)    (AEZipAp1 ê+>ê″)
    rewrite determinism-e ê+>ê′ ê+>ê″            = refl
  determinism-e (AEZipAp2 ê+>ê′)    (AEZipAp2 ê+>ê″)
    rewrite determinism-e ê+>ê′ ê+>ê″            = refl
  determinism-e (AEZipLet1 ê+>ê′)   (AEZipLet1 ê+>ê″)
    rewrite determinism-e ê+>ê′ ê+>ê″            = refl
  determinism-e (AEZipLet2 ê+>ê′)   (AEZipLet2 ê+>ê″)
    rewrite determinism-e ê+>ê′ ê+>ê″            = refl
  determinism-e (AEZipPlus1 ê+>ê′)  (AEZipPlus1 ê+>ê″)
    rewrite determinism-e ê+>ê′ ê+>ê″            = refl
  determinism-e (AEZipPlus2 ê+>ê′)  (AEZipPlus2 ê+>ê″)
    rewrite determinism-e ê+>ê′ ê+>ê″            = refl
  determinism-e (AEZipIf1 ê+>ê′)    (AEZipIf1 ê+>ê″)
    rewrite determinism-e ê+>ê′ ê+>ê″            = refl
  determinism-e (AEZipIf2 ê+>ê′)    (AEZipIf2 ê+>ê″)
    rewrite determinism-e ê+>ê′ ê+>ê″            = refl
  determinism-e (AEZipIf3 ê+>ê′)    (AEZipIf3 ê+>ê″)
    rewrite determinism-e ê+>ê′ ê+>ê″            = refl
  determinism-e (AEZipPair1 ê+>ê′)  (AEZipPair1 ê+>ê″)
    rewrite determinism-e ê+>ê′ ê+>ê″            = refl
  determinism-e (AEZipPair2 ê+>ê′)  (AEZipPair2 ê+>ê″)
    rewrite determinism-e ê+>ê′ ê+>ê″            = refl
  determinism-e (AEZipProjL ê+>ê′)  (AEZipProjL ê+>ê″)
    rewrite determinism-e ê+>ê′ ê+>ê″            = refl
  determinism-e (AEZipProjR ê+>ê′)  (AEZipProjR ê+>ê″)
    rewrite determinism-e ê+>ê′ ê+>ê″            = refl

  determinism*-e : ∀ {ê ê′ ê″ ᾱ} → ê + ᾱ +e>* ê′ → ê + ᾱ +e>* ê″ → ê′ ≡ ê″
  determinism*-e AEIRefl                 AEIRefl = refl
  determinism*-e (AEIExp ê₁+>ê₂ ê₂+>*ê₃) (AEIExp ê₁+>ê₂′ ê₂+>*ê₃′)
    rewrite determinism-e ê₁+>ê₂ ê₁+>ê₂′
    rewrite determinism*-e ê₂+>*ê₃ ê₂+>*ê₃′    = refl
