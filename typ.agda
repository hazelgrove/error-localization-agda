open import prelude

-- types
module typ where
  data Typ : Set where
    num     : Typ
    bool    : Typ
    unknown : Typ
    _-→_    : Typ → Typ → Typ

  infixr 25  _-→_

  -- base types
  data _base : (τ : Typ) → Set where
    BNum  : num base
    BBool : bool base

  -- consistency
  data _~_ : (τ₁ τ₂ : Typ) → Set where
    TCRefl     : {τ : Typ} → τ ~ τ
    TCUnknown1 : {τ : Typ} → τ ~ unknown
    TCUnknown2 : {τ : Typ} → unknown ~ τ
    TCArr      : {τ₁ τ₂ τ₁′ τ₂′ : Typ}
                → τ₁ ~ τ₁′
                → τ₂ ~ τ₂′
                → τ₁ -→ τ₂ ~ τ₁′ -→ τ₂′

  _~̸_ : (τ₁ : Typ) → (τ₂ : Typ) → Set
  τ₁ ~̸ τ₂ = ¬ (τ₁ ~ τ₂)

  -- matched arrow
  data _▸_-→_ : (τ τ₁ τ₂ : Typ) → Set where
    TMAHole : unknown ▸ unknown -→ unknown
    TMAArr  : {τ₁ τ₂ : Typ} → τ₁ -→ τ₂ ▸ τ₁ -→ τ₂

  _!▸ : Typ → Set
  τ !▸ = ¬ (∃[ τ₁ ] ∃[ τ₂ ] τ ▸ τ₁ -→ τ₂)

  -- lub join
  data _⊔_⇒_ : (τ₁ τ₂ τ : Typ) → Set where
    TJUnknown1 : {τ : Typ} → τ ⊔ unknown ⇒ unknown
    TJUnknown2 : {τ : Typ} → unknown ⊔ τ ⇒ unknown
    TJNum      : num ⊔ num ⇒ num
    TJBool     : bool ⊔ bool ⇒ bool
    TJArr      : {τ₁ τ₂ τ₁′ τ₂′ τ₁″ τ₂″ : Typ}
                → τ₁ ⊔ τ₁′ ⇒ τ₁″
                → τ₂ ⊔ τ₂′ ⇒ τ₂″
                → τ₁ -→ τ₂ ⊔ τ₁′ -→ τ₂′ ⇒ τ₁″ -→ τ₂″

  -- arrow type equality
  -→≡ : ∀ {τ₁ τ₂ τ₁′ τ₂′} → τ₁ ≡ τ₁′ → τ₂ ≡ τ₂′ → τ₁ -→ τ₂ ≡ τ₁′ -→ τ₂′
  -→≡ refl refl = refl

  -- inverted arrow type equality
  ≡-→ : ∀ {τ₁ τ₂ τ₁′ τ₂′} → τ₁ -→ τ₂ ≡ τ₁′ -→ τ₂′ → τ₁ ≡ τ₁′ × τ₂ ≡ τ₂′
  ≡-→ refl = ⟨ refl , refl ⟩

  -- arrow type inequalities
  -→≢₁ : ∀ {τ₁ τ₂ τ₁′ τ₂′} → τ₁ ≢ τ₁′ → τ₁ -→ τ₂ ≢ τ₁′ -→ τ₂′
  -→≢₁ τ₁≢τ₁′ refl = τ₁≢τ₁′ refl

  -→≢₂ : ∀ {τ₁ τ₂ τ₁′ τ₂′} → τ₂ ≢ τ₂′ → τ₁ -→ τ₂ ≢ τ₁′ -→ τ₂′
  -→≢₂ τ₂≢τ₂′ refl = τ₂≢τ₂′ refl

  -- decidable equality
  _≡?_ : (τ : Typ) → (τ′ : Typ) → Dec (τ ≡ τ′)
  num        ≡? num      = yes refl
  num        ≡? bool     = no (λ ())
  num        ≡? unknown  = no (λ ())
  num        ≡? (_ -→ _) = no (λ ())
  bool       ≡? num      = no (λ ())
  bool       ≡? bool     = yes refl
  bool       ≡? unknown  = no (λ ())
  bool       ≡? (_ -→ _) = no (λ ())
  unknown    ≡? num      = no (λ ())
  unknown    ≡? bool     = no (λ ())
  unknown    ≡? unknown  = yes refl
  unknown    ≡? (_ -→ _) = no (λ ())
  (_ -→ _)   ≡? num      = no (λ ())
  (_ -→ _)   ≡? bool     = no (λ ())
  (_ -→ _)   ≡? unknown  = no (λ ())
  (τ₁ -→ τ₂) ≡? (τ₁′ -→ τ₂′) with τ₁ ≡? τ₁′  | τ₂ ≡? τ₂′
  ...                           | yes τ₁≡τ₁′ | yes τ₂≡τ₂′ = yes (-→≡ τ₁≡τ₁′ τ₂≡τ₂′)
  ...                           | _          | no τ₂≢τ₂′  = no (-→≢₂ τ₂≢τ₂′)
  ...                           | no τ₁≢τ₁′  | _          = no (-→≢₁ τ₁≢τ₁′)

  -- arrow type inconsistencies
  -→~̸₁ : ∀ {τ₁ τ₂ τ₁′ τ₂′} → τ₁ ~̸ τ₁′ → τ₁ -→ τ₂ ~̸ τ₁′ -→ τ₂′
  -→~̸₁ τ₁~̸τ₁′ = λ { TCRefl → τ₁~̸τ₁′ TCRefl ; (TCArr τ₁~τ₁′ _) → τ₁~̸τ₁′ τ₁~τ₁′ }

  -→~̸₂ : ∀ {τ₁ τ₂ τ₁′ τ₂′} → τ₂ ~̸ τ₂′ → τ₁ -→ τ₂ ~̸ τ₁′ -→ τ₂′
  -→~̸₂ τ₂~̸τ₂′ = λ { TCRefl → τ₂~̸τ₂′ TCRefl ; (TCArr _ τ₂~τ₂′) → τ₂~̸τ₂′ τ₂~τ₂′ }

  -- decidable consistency
  _~?_ : (τ : Typ) → (τ′ : Typ) → Dec (τ ~ τ′)
  unknown    ~? _        = yes TCUnknown2
  _          ~? unknown  = yes TCUnknown1
  num        ~? num      = yes TCRefl
  num        ~? bool     = no (λ ())
  num        ~? (_ -→ _) = no (λ ())
  bool       ~? num      = no (λ ())
  bool       ~? bool     = yes TCRefl
  bool       ~? (_ -→ _) = no (λ ())
  (_ -→ _)   ~? num      = no (λ ())
  (_ -→ _)   ~? bool     = no (λ ())
  (τ₁ -→ τ₂) ~? (τ₁′ -→ τ₂′) with τ₁ ~? τ₁′  | τ₂ ~? τ₂′
  ...                           | yes τ₁~τ₁′ | yes τ₂~τ₂′ = yes (TCArr τ₁~τ₁′ τ₂~τ₂′)
  ...                           | _          | no ¬τ₂~τ₂′ = no λ { TCRefl → ¬τ₂~τ₂′ TCRefl ; (TCArr _ τ₂~τ₂′) → ¬τ₂~τ₂′ τ₂~τ₂′ }
  ...                           | no ¬τ₁~τ₁′ | _          = no λ { TCRefl → ¬τ₁~τ₁′ TCRefl ; (TCArr τ₁~τ₁′ _) → ¬τ₁~τ₁′ τ₁~τ₁′ }

  -- decidable matched arrow
  _▸? : (τ : Typ) → Dec (∃[ τ₁ ] ∃[ τ₂ ] τ ▸ τ₁ -→ τ₂)
  num ▸? = no (λ ())
  bool ▸? = no (λ ())
  unknown ▸? = yes ⟨ unknown , ⟨ unknown , TMAHole ⟩ ⟩
  (τ₁ -→ τ₂) ▸? = yes ⟨ τ₁ , ⟨ τ₂ , TMAArr ⟩ ⟩

  -- consistency is symmetric
  ~-sym : ∀ {τ₁ τ₂} → τ₁ ~ τ₂ → τ₂ ~ τ₁
  ~-sym TCRefl                = TCRefl
  ~-sym TCUnknown1            = TCUnknown2
  ~-sym TCUnknown2            = TCUnknown1
  ~-sym (TCArr τ₁~τ₁′ τ₂~τ₂′) = TCArr (~-sym τ₁~τ₁′) (~-sym τ₂~τ₂′)

  -- matched arrow is unique
  ▸-→-unicity : ∀ {τ τ₁ τ₂ τ₃ τ₄} → τ ▸ τ₁ -→ τ₂ → τ ▸ τ₃ -→ τ₄ → τ₁ -→ τ₂ ≡ τ₃ -→ τ₄
  ▸-→-unicity TMAHole TMAHole = refl
  ▸-→-unicity TMAArr TMAArr = refl

  -- equal types produce same matched arrow type
  ≡▸-→→≡ : ∀ {τ τ₁ τ₂ τ′ τ₁′ τ₂′} → τ ≡ τ′ → τ ▸ τ₁ -→ τ₂ → τ′ ▸ τ₁′ -→ τ₂′ → τ₁ ≡ τ₁′ × τ₂ ≡ τ₂′
  ≡▸-→→≡ refl τ▸ τ′▸ = ≡-→ (▸-→-unicity τ▸ τ′▸)

  -- only consistent types arrow match
  ▸-→→~ : ∀ {τ τ₁ τ₂} → τ ▸ τ₁ -→ τ₂ → τ ~ τ₁ -→ τ₂
  ▸-→→~ TMAHole = TCUnknown2
  ▸-→→~ TMAArr = TCRefl

  ▸-→~̸₁ : ∀ {τ τ₁ τ₂ τ₁′} → τ ▸ τ₁ -→ τ₂ → τ₁′ ~̸ τ₁ → τ ~̸ τ₁′ -→ τ₂
  ▸-→~̸₁ τ▸      τ₁′~̸τ₁ TCRefl with ▸-→→~ τ▸
  ...                            | TCRefl         = τ₁′~̸τ₁ TCRefl
  ...                            | TCArr τ₁′~τ₁ _ = τ₁′~̸τ₁ τ₁′~τ₁
  ▸-→~̸₁ TMAHole τ₁′~̸τ₁ TCUnknown2                 = τ₁′~̸τ₁ TCUnknown1
  ▸-→~̸₁ TMAArr  τ₁′~̸τ₁ (TCArr τ₁~τ₁′ _)           = τ₁′~̸τ₁ (~-sym τ₁~τ₁′)

  ▸-→~̸₂ : ∀ {τ τ₁ τ₂ τ₂′} → τ ▸ τ₁ -→ τ₂ → τ₂′ ~̸ τ₂ → τ ~̸ τ₁ -→ τ₂′
  ▸-→~̸₂ τ▸      τ₂′~̸τ₂ TCRefl with ▸-→→~ τ▸
  ...                            | TCRefl         = τ₂′~̸τ₂ TCRefl
  ...                            | TCArr _ τ₂′~τ₂ = τ₂′~̸τ₂ τ₂′~τ₂
  ▸-→~̸₂ TMAHole τ₂′~̸τ₂ TCUnknown2                 = τ₂′~̸τ₂ TCUnknown1
  ▸-→~̸₂ TMAArr  τ₂′~̸τ₂ (TCArr _ τ₂~τ₂′)           = τ₂′~̸τ₂ (~-sym τ₂~τ₂′)

  -- decidable join
  _⊔?_ : (τ₁ : Typ) → (τ₂ : Typ) → Dec (∃[ τ ] τ₁ ⊔ τ₂ ⇒ τ)
  unknown ⊔? _ = yes ⟨ unknown , TJUnknown2 ⟩
  _ ⊔? unknown = yes ⟨ unknown , TJUnknown1 ⟩
  num ⊔? num = yes ⟨ num , TJNum ⟩
  num ⊔? bool = no (λ ())
  num ⊔? (_ -→ _) = no (λ ())
  bool ⊔? num = no (λ ())
  bool ⊔? bool = yes ⟨ bool , TJBool ⟩
  bool ⊔? (_ -→ _) = no (λ ())
  (_ -→ _) ⊔? num = no (λ ())
  (_ -→ _) ⊔? bool = no (λ ())
  (τ₁ -→ τ₂) ⊔? (τ₁′ -→ τ₂′) with τ₁ ⊔? τ₁′            | τ₂ ⊔? τ₂′
  ...                           | yes ⟨ τ , τ₁⊔τ₁′⇒τ ⟩ | yes ⟨ τ′ , τ₂⊔τ₂′⇒τ′ ⟩ = yes ⟨ τ -→ τ′ , TJArr τ₁⊔τ₁′⇒τ τ₂⊔τ₂′⇒τ′ ⟩
  ...                           | _                    | no ¬τ₂⊔τ₂′ = no λ { ⟨ .(_ -→ _) , TJArr {τ₂″ = τ₂″} τ₁⊔τ₁′⇒τ₁″ τ₂⊔τ₂′⇒τ₂″ ⟩ → ¬τ₂⊔τ₂′ ⟨ τ₂″ , τ₂⊔τ₂′⇒τ₂″ ⟩ }
  ...                           | no ¬τ₁⊔τ₁′           | _ = no λ { ⟨ .(_ -→ _) , TJArr {τ₁″ = τ₁″} τ₁⊔τ₁′⇒τ₁″ τ₂⊔τ₂′⇒τ₂″ ⟩ → ¬τ₁⊔τ₁′ ⟨ τ₁″ , τ₁⊔τ₁′⇒τ₁″ ⟩ }

  -- join is symmetric
  ⊔-sym : ∀ {τ₁ τ₂ τ} → τ₁ ⊔ τ₂ ⇒ τ → τ₂ ⊔ τ₁ ⇒ τ
  ⊔-sym TJUnknown1          = TJUnknown2
  ⊔-sym TJUnknown2          = TJUnknown1
  ⊔-sym TJNum               = TJNum
  ⊔-sym TJBool              = TJBool
  ⊔-sym (TJArr ⊔⇒τ₁″ ⊔⇒τ₂″) = TJArr (⊔-sym ⊔⇒τ₁″) (⊔-sym ⊔⇒τ₂″)

  -- join is a function
  ⊔-unicity : ∀ {τ₁ τ₂ τ τ′} → τ₁ ⊔ τ₂ ⇒ τ → τ₁ ⊔ τ₂ ⇒ τ′ → τ ≡ τ′ 
  ⊔-unicity TJUnknown1 TJUnknown1                         = refl
  ⊔-unicity TJUnknown1 TJUnknown2                         = refl
  ⊔-unicity TJUnknown2 TJUnknown1                         = refl
  ⊔-unicity TJUnknown2 TJUnknown2                         = refl
  ⊔-unicity TJNum TJNum                                   = refl
  ⊔-unicity TJBool TJBool                                 = refl
  ⊔-unicity (TJArr τ₁⊔τ₁′ τ₂⊔τ₂′) (TJArr τ₁⊔τ₁′′ τ₂⊔τ₂′′) = -→≡ (⊔-unicity τ₁⊔τ₁′ τ₁⊔τ₁′′) (⊔-unicity τ₂⊔τ₂′ τ₂⊔τ₂′′)

  -- join existence means that types are consistent
  ⊔→~ : ∀ {τ τ₁ τ₂} → τ₁ ⊔ τ₂ ⇒ τ → τ₁ ~ τ₂
  ⊔→~ TJUnknown1            = TCUnknown1
  ⊔→~ TJUnknown2            = TCUnknown2
  ⊔→~ TJNum                 = TCRefl
  ⊔→~ TJBool                = TCRefl
  ⊔→~ (TJArr τ₁⊔τ₁′ τ₂⊔τ₂′) = TCArr (⊔→~ τ₁⊔τ₁′) (⊔→~ τ₂⊔τ₂′)

  -- consistent types have a join
  ~→⊔ : ∀ {τ₁ τ₂} → τ₁ ~ τ₂ → ∃[ τ ] τ₁ ⊔ τ₂ ⇒ τ
  ~→⊔ {num}      TCRefl                                            = ⟨ num , TJNum ⟩
  ~→⊔ {bool}     TCRefl                                            = ⟨ bool , TJBool ⟩
  ~→⊔ {unknown}  TCRefl                                            = ⟨ unknown , TJUnknown1 ⟩
  ~→⊔ {τ₁ -→ τ₂} TCRefl     with ~→⊔ {τ₁} TCRefl | ~→⊔ {τ₂} TCRefl
  ...                          | ⟨ τ₁′ , ⊔⇒τ₁′ ⟩ | ⟨ τ₂′ , ⊔⇒τ₂′ ⟩ = ⟨ τ₁′ -→ τ₂′ , TJArr ⊔⇒τ₁′ ⊔⇒τ₂′ ⟩
  ~→⊔ TCUnknown1                                                   = ⟨ unknown , TJUnknown1 ⟩
  ~→⊔ TCUnknown2                                                   = ⟨ unknown , TJUnknown2 ⟩
  ~→⊔ (TCArr τ₁~τ₁′ τ₂~τ₂′) with ~→⊔ τ₁~τ₁′ | ~→⊔ τ₂~τ₂′
  ...                          | ⟨ τ₁″ , ⊔⇒τ₁″ ⟩ | ⟨ τ₂″ , ⊔⇒τ₂″ ⟩ = ⟨ τ₁″ -→ τ₂″ , TJArr ⊔⇒τ₁″ ⊔⇒τ₂″ ⟩
