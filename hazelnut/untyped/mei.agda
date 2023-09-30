open import prelude
open import core

open import hazelnut.action
open import hazelnut.untyped.zexp
open import hazelnut.untyped.action
open import hazelnut.untyped.erasure

module hazelnut.untyped.mei where
  -- movement erasure invariance
  movement-erasure-invariance-τ : ∀ {τ^ τ^′ δ} → τ^ + move δ +τ> τ^′ → τ^ ◇τ ≡ τ^′ ◇τ
  movement-erasure-invariance-τ ATMArrChild1      = refl
  movement-erasure-invariance-τ ATMArrChild2      = refl
  movement-erasure-invariance-τ ATMArrParent1     = refl
  movement-erasure-invariance-τ ATMArrParent2     = refl
  movement-erasure-invariance-τ (ATZipArr1 τ^+>τ^′)
    rewrite movement-erasure-invariance-τ τ^+>τ^′ = refl
  movement-erasure-invariance-τ (ATZipArr2 τ^+>τ^′)
    rewrite movement-erasure-invariance-τ τ^+>τ^′ = refl
  movement-erasure-invariance-τ ATMProdChild1     = refl
  movement-erasure-invariance-τ ATMProdChild2     = refl
  movement-erasure-invariance-τ ATMProdParent1    = refl
  movement-erasure-invariance-τ ATMProdParent2    = refl
  movement-erasure-invariance-τ (ATZipProd1 τ^+>τ^′)
    rewrite movement-erasure-invariance-τ τ^+>τ^′ = refl
  movement-erasure-invariance-τ (ATZipProd2 τ^+>τ^′)
    rewrite movement-erasure-invariance-τ τ^+>τ^′ = refl

  movement-erasure-invariance-e : ∀ {ê ê′ δ} → ê + move δ +e> ê′ → ê ◇ ≡ ê′ ◇
  movement-erasure-invariance-e AEMLamChild1      = refl
  movement-erasure-invariance-e AEMLamChild2      = refl
  movement-erasure-invariance-e AEMLamParent1     = refl
  movement-erasure-invariance-e AEMLamParent2     = refl
  movement-erasure-invariance-e AEMApChild1       = refl
  movement-erasure-invariance-e AEMApChild2       = refl
  movement-erasure-invariance-e AEMApParent1      = refl
  movement-erasure-invariance-e AEMApParent2      = refl
  movement-erasure-invariance-e AEMLetChild1      = refl
  movement-erasure-invariance-e AEMLetChild2      = refl
  movement-erasure-invariance-e AEMLetParent1     = refl
  movement-erasure-invariance-e AEMLetParent2     = refl
  movement-erasure-invariance-e AEMPlusChild1     = refl
  movement-erasure-invariance-e AEMPlusChild2     = refl
  movement-erasure-invariance-e AEMPlusParent1    = refl
  movement-erasure-invariance-e AEMPlusParent2    = refl
  movement-erasure-invariance-e AEMIfChild1       = refl
  movement-erasure-invariance-e AEMIfChild2       = refl
  movement-erasure-invariance-e AEMIfChild3       = refl
  movement-erasure-invariance-e AEMIfParent1      = refl
  movement-erasure-invariance-e AEMIfParent2      = refl
  movement-erasure-invariance-e AEMIfParent3      = refl
  movement-erasure-invariance-e AEMPairChild1     = refl
  movement-erasure-invariance-e AEMPairChild2     = refl
  movement-erasure-invariance-e AEMPairParent1    = refl
  movement-erasure-invariance-e AEMPairParent2    = refl
  movement-erasure-invariance-e AEMProjLChild     = refl
  movement-erasure-invariance-e AEMProjLParent    = refl
  movement-erasure-invariance-e AEMProjRChild     = refl
  movement-erasure-invariance-e AEMProjRParent    = refl
  movement-erasure-invariance-e (AEZipLam1 τ^+>τ^′)
    rewrite movement-erasure-invariance-τ τ^+>τ^′ = refl
  movement-erasure-invariance-e (AEZipLam2 ê+>ê′)
    rewrite movement-erasure-invariance-e ê+>ê′   = refl
  movement-erasure-invariance-e (AEZipAp1 ê+>ê′) 
    rewrite movement-erasure-invariance-e ê+>ê′   = refl
  movement-erasure-invariance-e (AEZipAp2 ê+>ê′) 
    rewrite movement-erasure-invariance-e ê+>ê′   = refl
  movement-erasure-invariance-e (AEZipLet1 ê+>ê′) 
    rewrite movement-erasure-invariance-e ê+>ê′   = refl
  movement-erasure-invariance-e (AEZipLet2 ê+>ê′) 
    rewrite movement-erasure-invariance-e ê+>ê′   = refl
  movement-erasure-invariance-e (AEZipPlus1 ê+>ê′) 
    rewrite movement-erasure-invariance-e ê+>ê′   = refl
  movement-erasure-invariance-e (AEZipPlus2 ê+>ê′) 
    rewrite movement-erasure-invariance-e ê+>ê′   = refl
  movement-erasure-invariance-e (AEZipIf1 ê+>ê′) 
    rewrite movement-erasure-invariance-e ê+>ê′   = refl
  movement-erasure-invariance-e (AEZipIf2 ê+>ê′) 
    rewrite movement-erasure-invariance-e ê+>ê′   = refl
  movement-erasure-invariance-e (AEZipIf3 ê+>ê′)
    rewrite movement-erasure-invariance-e ê+>ê′   = refl
  movement-erasure-invariance-e (AEZipPair1 ê+>ê′) 
    rewrite movement-erasure-invariance-e ê+>ê′   = refl
  movement-erasure-invariance-e (AEZipPair2 ê+>ê′) 
    rewrite movement-erasure-invariance-e ê+>ê′   = refl
  movement-erasure-invariance-e (AEZipProjL ê+>ê′) 
    rewrite movement-erasure-invariance-e ê+>ê′   = refl
  movement-erasure-invariance-e (AEZipProjR ê+>ê′) 
    rewrite movement-erasure-invariance-e ê+>ê′   = refl
