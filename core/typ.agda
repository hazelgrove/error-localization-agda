open import prelude

-- types
module core.typ where
  data Typ : Set where
    num     : Typ
    bool    : Typ
    unknown : Typ
    _-→_    : Typ → Typ → Typ
    _-×_     : Typ → Typ → Typ

  infixr 25  _-→_
  infixr 24  _-×_

  module equality where
    -- arrow type equality
    -→-≡ : ∀ {τ₁ τ₂ τ₁′ τ₂′} → (τ₁ ≡ τ₁′) → (τ₂ ≡ τ₂′) → τ₁ -→ τ₂ ≡ τ₁′ -→ τ₂′
    -→-≡ refl refl = refl

    -- inverted arrow type equality
    -→-inj : ∀ {τ₁ τ₂ τ₁′ τ₂′} → (τ₁ -→ τ₂ ≡ τ₁′ -→ τ₂′) → τ₁ ≡ τ₁′ × τ₂ ≡ τ₂′
    -→-inj refl = ⟨ refl , refl ⟩

    -- arrow type inequalities
    -→-≢₁ : ∀ {τ₁ τ₂ τ₁′ τ₂′} → (τ₁ ≢ τ₁′) → τ₁ -→ τ₂ ≢ τ₁′ -→ τ₂′
    -→-≢₁ τ₁≢τ₁′ refl = τ₁≢τ₁′ refl

    -→-≢₂ : ∀ {τ₁ τ₂ τ₁′ τ₂′} → (τ₂ ≢ τ₂′) → τ₁ -→ τ₂ ≢ τ₁′ -→ τ₂′
    -→-≢₂ τ₂≢τ₂′ refl = τ₂≢τ₂′ refl

    -- product type equality
    -×-≡ : ∀ {τ₁ τ₂ τ₁′ τ₂′} → (τ₁ ≡ τ₁′) → (τ₂ ≡ τ₂′) → τ₁ -× τ₂ ≡ τ₁′ -× τ₂′
    -×-≡ refl refl = refl

    -- inverted product type equality
    -×-inj : ∀ {τ₁ τ₂ τ₁′ τ₂′} → (τ₁ -× τ₂ ≡ τ₁′ -× τ₂′) → τ₁ ≡ τ₁′ × τ₂ ≡ τ₂′
    -×-inj refl = ⟨ refl , refl ⟩

    -- product type inequalities
    -×-≢₁ : ∀ {τ₁ τ₂ τ₁′ τ₂′} → (τ₁ ≢ τ₁′) → τ₁ -× τ₂ ≢ τ₁′ -× τ₂′
    -×-≢₁ τ₁≢τ₁′ refl = τ₁≢τ₁′ refl

    -×-≢₂ : ∀ {τ₁ τ₂ τ₁′ τ₂′} → (τ₂ ≢ τ₂′) → τ₁ -× τ₂ ≢ τ₁′ -× τ₂′
    -×-≢₂ τ₂≢τ₂′ refl = τ₂≢τ₂′ refl

    -- decidable equality
    _≡τ?_ : (τ : Typ) → (τ′ : Typ) → Dec (τ ≡ τ′)
    num        ≡τ? num      = yes refl
    num        ≡τ? bool     = no (λ ())
    num        ≡τ? unknown  = no (λ ())
    num        ≡τ? (_ -→ _) = no (λ ())
    num        ≡τ? (_ -× _) = no (λ ())
    bool       ≡τ? num      = no (λ ())
    bool       ≡τ? bool     = yes refl
    bool       ≡τ? unknown  = no (λ ())
    bool       ≡τ? (_ -→ _) = no (λ ())
    bool       ≡τ? (_ -× _) = no (λ ())
    unknown    ≡τ? num      = no (λ ())
    unknown    ≡τ? bool     = no (λ ())
    unknown    ≡τ? unknown  = yes refl
    unknown    ≡τ? (_ -→ _) = no (λ ())
    unknown    ≡τ? (_ -× _) = no (λ ())
    (_ -→ _)   ≡τ? num      = no (λ ())
    (_ -→ _)   ≡τ? bool     = no (λ ())
    (_ -→ _)   ≡τ? unknown  = no (λ ())
    (τ₁ -→ τ₂) ≡τ? (τ₁′ -→ τ₂′) with τ₁ ≡τ? τ₁′ | τ₂ ≡τ? τ₂′
    ...                           | yes refl    | yes refl  = yes refl
    ...                           | _           | no τ₂≢τ₂′ = no  (-→-≢₂ τ₂≢τ₂′)
    ...                           | no τ₁≢τ₁′   | _         = no  (-→-≢₁ τ₁≢τ₁′)
    (_ -→ _)   ≡τ? (_ -× _) = no (λ ())
    (_ -× _)   ≡τ? num      = no (λ ())
    (_ -× _)   ≡τ? bool     = no (λ ())
    (_ -× _)   ≡τ? unknown  = no (λ ())
    (_ -× _)   ≡τ? (_ -→ _) = no (λ ())
    (τ₁ -× τ₂) ≡τ? (τ₁′ -× τ₂′) with τ₁ ≡τ? τ₁′ | τ₂ ≡τ? τ₂′
    ...                           | yes refl    | yes refl  = yes refl
    ...                           | _           | no τ₂≢τ₂′ = no  (-×-≢₂ τ₂≢τ₂′)
    ...                           | no τ₁≢τ₁′   | _         = no  (-×-≢₁ τ₁≢τ₁′)

  module base where
    -- base types
    data _base : (τ : Typ) → Set where
      TBNum  : num base
      TBBool : bool base

    -- decidable base
    _base? : (τ : Typ) → Dec (τ base)
    num      base? = yes TBNum
    bool     base? = yes TBBool
    unknown  base? = no (λ ())
    (_ -→ _) base? = no (λ ())
    (_ -× _) base? = no (λ ())

    -- base judgment equality
    base-≡ : ∀ {τ} → (b₁ : τ base) → (b₂ : τ base) → b₁ ≡ b₂
    base-≡ TBNum TBNum = refl
    base-≡ TBBool TBBool = refl

  module consistency where
    open base

    -- consistency
    data _~_ : (τ₁ τ₂ : Typ) → Set where
      TCUnknown     : unknown ~ unknown
      TCBase        : {τ : Typ} → (b : τ base) → τ ~ τ
      TCUnknownBase : {τ : Typ} → (b : τ base) → unknown ~ τ
      TCBaseUnknown : {τ : Typ} → (b : τ base) → τ ~ unknown
      TCArr         : {τ₁ τ₂ τ₁′ τ₂′ : Typ}
                    → (τ₁~τ₁′ : τ₁ ~ τ₁′)
                    → (τ₂~τ₂′ : τ₂ ~ τ₂′)
                    → τ₁ -→ τ₂ ~ τ₁′ -→ τ₂′
      TCUnknownArr  : {τ₁ τ₂ : Typ}
                    → unknown ~ τ₁ -→ τ₂
      TCArrUnknown  : {τ₁ τ₂ : Typ}
                    → τ₁ -→ τ₂ ~ unknown
      TCProd        : {τ₁ τ₂ τ₁′ τ₂′ : Typ}
                    → (τ₁~τ₁′ : τ₁ ~ τ₁′)
                    → (τ₂~τ₂′ : τ₂ ~ τ₂′)
                    → τ₁ -× τ₂ ~ τ₁′ -× τ₂′
      TCUnknownProd : {τ₁ τ₂ : Typ}
                    → unknown ~ τ₁ -× τ₂
      TCProdUnknown : {τ₁ τ₂ : Typ}
                    → τ₁ -× τ₂ ~ unknown

    -- inconsistency
    _~̸_ : (τ₁ : Typ) → (τ₂ : Typ) → Set
    τ₁ ~̸ τ₂ = ¬ (τ₁ ~ τ₂)

    -- consistency reflexivity
    ~-refl : ∀ {τ} → τ ~ τ
    ~-refl {num}      = TCBase TBNum
    ~-refl {bool}     = TCBase TBBool
    ~-refl {unknown}  = TCUnknown
    ~-refl {τ₁ -→ τ₂} = TCArr ~-refl ~-refl
    ~-refl {τ₁ -× τ₂} = TCProd ~-refl ~-refl

    -- consistency symmetry
    ~-sym : ∀ {τ₁ τ₂} → τ₁ ~ τ₂ → τ₂ ~ τ₁
    ~-sym TCUnknown              = TCUnknown
    ~-sym (TCBase b)             = TCBase b
    ~-sym (TCUnknownBase b)      = TCBaseUnknown b
    ~-sym (TCBaseUnknown b)      = TCUnknownBase b
    ~-sym TCUnknownArr           = TCArrUnknown
    ~-sym TCArrUnknown           = TCUnknownArr
    ~-sym (TCArr τ₁~τ₁′ τ₂~τ₂′)  = TCArr (~-sym τ₁~τ₁′) (~-sym τ₂~τ₂′)
    ~-sym (TCProd τ₁~τ₁′ τ₂~τ₂′) = TCProd (~-sym τ₁~τ₁′) (~-sym τ₂~τ₂′)
    ~-sym TCUnknownProd          = TCProdUnknown
    ~-sym TCProdUnknown          = TCUnknownProd

    -- consistency with unknown type
    ~-unknown₁ : ∀ {τ} → unknown ~ τ
    ~-unknown₁ {num}     = TCUnknownBase TBNum
    ~-unknown₁ {bool}    = TCUnknownBase TBBool
    ~-unknown₁ {unknown} = TCUnknown
    ~-unknown₁ {_ -→ _}  = TCUnknownArr
    ~-unknown₁ {_ -× _}  = TCUnknownProd

    ~-unknown₂ : ∀ {τ} → τ ~ unknown
    ~-unknown₂ {num}     = TCBaseUnknown TBNum
    ~-unknown₂ {bool}    = TCBaseUnknown TBBool
    ~-unknown₂ {unknown} = TCUnknown
    ~-unknown₂ {_ -→ _}  = TCArrUnknown
    ~-unknown₂ {_ -× _}  = TCProdUnknown

    -- consistency derivation equality
    ~-≡ : ∀ {τ₁ τ₂} → (τ₁~τ₂ : τ₁ ~ τ₂) → (τ₁~τ₂′ : τ₁ ~ τ₂) → τ₁~τ₂ ≡ τ₁~τ₂′
    ~-≡ TCUnknown             TCUnknown               = refl
    ~-≡ (TCBase b)            (TCBase b′)
      rewrite base-≡ b b′                             = refl
    ~-≡ (TCUnknownBase b)     (TCUnknownBase b′)
      rewrite base-≡ b b′                             = refl
    ~-≡ (TCBaseUnknown b)     (TCBaseUnknown b′)
      rewrite base-≡ b b′                             = refl
    ~-≡ (TCArr τ₁~τ₁′ τ₂~τ₂′) (TCArr τ₁~τ₁′′ τ₂~τ₂′′)
      rewrite ~-≡ τ₁~τ₁′ τ₁~τ₁′′ | ~-≡ τ₂~τ₂′ τ₂~τ₂′′ = refl
    ~-≡ TCUnknownArr          TCUnknownArr            = refl
    ~-≡ TCArrUnknown          TCArrUnknown            = refl
    ~-≡ (TCProd τ₁~τ₁′ τ₂~τ₂′) (TCProd τ₁~τ₁′′ τ₂~τ₂′′)
      rewrite ~-≡ τ₁~τ₁′ τ₁~τ₁′′ | ~-≡ τ₂~τ₂′ τ₂~τ₂′′ = refl
    ~-≡ TCUnknownProd          TCUnknownProd          = refl
    ~-≡ TCProdUnknown          TCProdUnknown          = refl

    -- inconsistency derivation equality
    ~̸-≡ : ∀ {τ₁ τ₂} → (τ₁~̸τ₂ : τ₁ ~̸ τ₂) → (τ₁~̸τ₂′ : τ₁ ~̸ τ₂) → τ₁~̸τ₂ ≡ τ₁~̸τ₂′
    ~̸-≡ τ₁~̸τ₂ τ₁~̸τ₂′ rewrite ¬-≡ τ₁~̸τ₂ τ₁~̸τ₂′ = refl

    -- arrow type inconsistencies
    -→-~̸₁ : ∀ {τ₁ τ₂ τ₁′ τ₂′} → τ₁ ~̸ τ₁′ → τ₁ -→ τ₂ ~̸ τ₁′ -→ τ₂′
    -→-~̸₁ τ₁~̸τ₁′ = λ { (TCBase ()) ; (TCArr τ₁~τ₁′ _) → τ₁~̸τ₁′ τ₁~τ₁′ }

    -→-~̸₂ : ∀ {τ₁ τ₂ τ₁′ τ₂′} → τ₂ ~̸ τ₂′ → τ₁ -→ τ₂ ~̸ τ₁′ -→ τ₂′
    -→-~̸₂ τ₂~̸τ₂′ = λ { (TCBase ()) ; (TCArr _ τ₂~τ₂′) → τ₂~̸τ₂′ τ₂~τ₂′ }

    -- decidable consistency
    _~?_ : (τ : Typ) → (τ′ : Typ) → Dec (τ ~ τ′)
    unknown    ~? num      = yes (TCUnknownBase TBNum)
    unknown    ~? bool     = yes (TCUnknownBase TBBool)
    unknown    ~? unknown  = yes TCUnknown
    unknown    ~? (_ -→ _) = yes TCUnknownArr
    unknown    ~? (_ -× _) = yes TCUnknownProd
    num        ~? num      = yes (TCBase TBNum)
    num        ~? bool     = no  (λ ())
    num        ~? unknown  = yes (TCBaseUnknown TBNum)
    num        ~? (_ -→ _) = no  (λ ())
    num        ~? (_ -× _) = no  (λ ())
    bool       ~? num      = no  (λ ())
    bool       ~? bool     = yes (TCBase TBBool)
    bool       ~? unknown  = yes (TCBaseUnknown TBBool)
    bool       ~? (_ -→ _) = no  (λ ())
    bool       ~? (_ -× _) = no  (λ ())
    (_ -→ _)   ~? num      = no  (λ ())
    (_ -→ _)   ~? bool     = no  (λ ())
    (_ -→ _)   ~? unknown  = yes TCArrUnknown
    (τ₁ -→ τ₂) ~? (τ₁′ -→ τ₂′) with τ₁ ~? τ₁′  | τ₂ ~? τ₂′
    ...                           | yes τ₁~τ₁′ | yes τ₂~τ₂′ = yes (TCArr τ₁~τ₁′ τ₂~τ₂′)
    ...                           | _          | no ¬τ₂~τ₂′ = no λ { (TCBase ()) ; (TCArr _ τ₂~τ₂′) → ¬τ₂~τ₂′ τ₂~τ₂′ }
    ...                           | no ¬τ₁~τ₁′ | _          = no λ { (TCBase ()) ; (TCArr τ₁~τ₁′ _) → ¬τ₁~τ₁′ τ₁~τ₁′ }
    (_ -→ _)   ~? (_ -× _) = no  (λ ())
    (_ -× _)   ~? num      = no  (λ ())
    (_ -× _)   ~? bool     = no  (λ ())
    (_ -× _)   ~? unknown  = yes TCProdUnknown
    (_ -× _)   ~? (_ -→ _) = no  (λ ())
    (τ₁ -× τ₂) ~? (τ₁′ -× τ₂′) with τ₁ ~? τ₁′  | τ₂ ~? τ₂′
    ...                           | yes τ₁~τ₁′ | yes τ₂~τ₂′ = yes (TCProd τ₁~τ₁′ τ₂~τ₂′)
    ...                           | _          | no ¬τ₂~τ₂′ = no λ { (TCBase ()) ; (TCProd _ τ₂~τ₂′) → ¬τ₂~τ₂′ τ₂~τ₂′ }
    ...                           | no ¬τ₁~τ₁′ | _          = no λ { (TCBase ()) ; (TCProd τ₁~τ₁′ _) → ¬τ₁~τ₁′ τ₁~τ₁′ }

    module formalism where
      data _~′_ : (τ₁ τ₂ : Typ) → Set where
        TCUnknown1 : {τ : Typ} → unknown ~′ τ
        TCUnknown2 : {τ : Typ} → τ ~′ unknown
        TCRefl     : {τ : Typ} → τ ~′ τ
        TCArr      : {τ₁ τ₁′ τ₂ τ₂′ : Typ}
                   → (τ₁~τ₁′ : τ₁ ~′ τ₁′)
                   → (τ₂~τ₂′ : τ₂ ~′ τ₂′)
                   → τ₁ -→ τ₂ ~′ τ₁′ -→ τ₂′
        TCProd     : {τ₁ τ₁′ τ₂ τ₂′ : Typ}
                   → (τ₁~τ₁′ : τ₁ ~′ τ₁′)
                   → (τ₂~τ₂′ : τ₂ ~′ τ₂′)
                   → τ₁ -× τ₂ ~′ τ₁′ -× τ₂′

      ~→~′ : ∀ {τ₁ τ₂ : Typ} → τ₁ ~ τ₂ → τ₁ ~′ τ₂
      ~→~′ TCUnknown               = TCRefl
      ~→~′ (TCBase TBNum)          = TCRefl
      ~→~′ (TCBase TBBool)         = TCRefl
      ~→~′ (TCUnknownBase b)       = TCUnknown1
      ~→~′ (TCBaseUnknown b)       = TCUnknown2
      ~→~′ (TCArr τ₁~τ₁′ τ₂~τ₂′)
        with τ₁~τ₁′′ ← ~→~′ τ₁~τ₁′
           | τ₂~τ₂′′ ← ~→~′ τ₂~τ₂′ = TCArr τ₁~τ₁′′ τ₂~τ₂′′
      ~→~′ TCUnknownArr            = TCUnknown1
      ~→~′ TCArrUnknown            = TCUnknown2
      ~→~′ (TCProd τ₁~τ₁′ τ₂~τ₂′)
        with τ₁~τ₁′′ ← ~→~′ τ₁~τ₁′
           | τ₂~τ₂′′ ← ~→~′ τ₂~τ₂′ = TCProd τ₁~τ₁′′ τ₂~τ₂′′
      ~→~′ TCUnknownProd           = TCUnknown1
      ~→~′ TCProdUnknown           = TCUnknown2

      ~′→~ : ∀ {τ₁ τ₂ : Typ} → τ₁ ~′ τ₂ → τ₁ ~ τ₂
      ~′→~ {τ₂ = num} TCUnknown1 = TCUnknownBase TBNum
      ~′→~ {τ₂ = bool} TCUnknown1 = TCUnknownBase TBBool
      ~′→~ {τ₂ = unknown} TCUnknown1 = TCUnknown
      ~′→~ {τ₂ = _ -→ _} TCUnknown1 = TCUnknownArr
      ~′→~ {τ₂ = _ -× _} TCUnknown1 = TCUnknownProd
      ~′→~ {τ₁ = num} TCUnknown2 = TCBaseUnknown TBNum
      ~′→~ {τ₁ = bool} TCUnknown2 = TCBaseUnknown TBBool
      ~′→~ {τ₁ = unknown} TCUnknown2 = TCUnknown
      ~′→~ {τ₁ = _ -→ _} TCUnknown2 = TCArrUnknown
      ~′→~ {τ₁ = _ -× _} TCUnknown2 = TCProdUnknown
      ~′→~ {τ₁ = num} TCRefl = TCBase TBNum
      ~′→~ {τ₁ = bool} TCRefl = TCBase TBBool
      ~′→~ {τ₁ = unknown} TCRefl = TCUnknown
      ~′→~ {τ₁ = _ -→ _} TCRefl = TCArr (~′→~ TCRefl) (~′→~ TCRefl)
      ~′→~ {τ₁ = _ -× _} TCRefl = TCProd (~′→~ TCRefl) (~′→~ TCRefl)
      ~′→~ (TCArr τ₁~τ₁′ τ₂~τ₂′) = TCArr (~′→~ τ₁~τ₁′) (~′→~ τ₂~τ₂′)
      ~′→~ (TCProd τ₁~τ₁′ τ₂~τ₂′) = TCProd (~′→~ τ₁~τ₁′) (~′→~ τ₂~τ₂′)

      ~⇔~′ : ∀ {τ₁ τ₂ : Typ} → (τ₁ ~ τ₂) ⇔ (τ₁ ~′ τ₂)
      ~⇔~′ =
        record
          { to   = ~→~′
          ; from = ~′→~
          }
      
  module matched where
    open equality
    open consistency

    -- matched arrow
    data _▸_-→_ : (τ τ₁ τ₂ : Typ) → Set where
      TMAUnknown : unknown ▸ unknown -→ unknown
      TMAArr  : {τ₁ τ₂ : Typ} → τ₁ -→ τ₂ ▸ τ₁ -→ τ₂

    -- no matched
    _!▸-→ : Typ → Set
    τ !▸-→ = ¬ (∃[ τ₁ ] ∃[ τ₂ ] τ ▸ τ₁ -→ τ₂)

    -- decidable matched arrow
    _▸-→? : (τ : Typ) → Dec (∃[ τ₁ ] ∃[ τ₂ ] τ ▸ τ₁ -→ τ₂)
    num        ▸-→? = no (λ ())
    bool       ▸-→? = no (λ ())
    unknown    ▸-→? = yes ⟨ unknown , ⟨ unknown , TMAUnknown ⟩ ⟩
    (τ₁ -→ τ₂) ▸-→? = yes ⟨ τ₁      , ⟨ τ₂      , TMAArr     ⟩ ⟩
    (τ₁ -× τ₂) ▸-→? = no (λ ())

    -- matched arrow derivation equality
    ▸-→-≡ : ∀ {τ τ₁ τ₂} → (τ▸ : τ ▸ τ₁ -→ τ₂) → (τ▸′ : τ ▸ τ₁ -→ τ₂) → τ▸ ≡ τ▸′
    ▸-→-≡ TMAUnknown TMAUnknown = refl
    ▸-→-≡ TMAArr     TMAArr     = refl

    -- matched arrow unicity
    ▸-→-unicity : ∀ {τ τ₁ τ₂ τ₃ τ₄} → (τ ▸ τ₁ -→ τ₂) → (τ ▸ τ₃ -→ τ₄) → τ₁ -→ τ₂ ≡ τ₃ -→ τ₄
    ▸-→-unicity TMAUnknown TMAUnknown = refl
    ▸-→-unicity TMAArr     TMAArr     = refl

    -- no matched arrow derivation equality
    !▸-→-≡ : ∀ {τ} → (τ!▸ : τ !▸-→) → (τ!▸′ : τ !▸-→) → τ!▸ ≡ τ!▸′
    !▸-→-≡ τ!▸ τ!▸′ = ¬-≡ τ!▸ τ!▸′

    -- only consistent types arrow match
    ▸-→→~ : ∀ {τ τ₁ τ₂} → τ ▸ τ₁ -→ τ₂ → τ ~ τ₁ -→ τ₂
    ▸-→→~ TMAUnknown = TCUnknownArr
    ▸-→→~ TMAArr     = ~-refl

    ▸-→-~̸₁ : ∀ {τ τ₁ τ₂ τ₁′} → τ ▸ τ₁ -→ τ₂ → τ₁′ ~̸ τ₁ → τ ~̸ τ₁′ -→ τ₂
    ▸-→-~̸₁ TMAArr     τ₁′~̸τ₁ (TCArr τ₁~τ₁′ _) = τ₁′~̸τ₁ (~-sym τ₁~τ₁′)
    ▸-→-~̸₁ TMAUnknown τ₁′~̸τ₁ TCUnknownArr     = τ₁′~̸τ₁ ~-unknown₂

    ▸-→-~̸₂ : ∀ {τ τ₁ τ₂ τ₂′} → τ ▸ τ₁ -→ τ₂ → τ₂′ ~̸ τ₂ → τ ~̸ τ₁ -→ τ₂′
    ▸-→-~̸₂ TMAUnknown τ₂′~̸τ₂ TCUnknownArr     = τ₂′~̸τ₂ ~-unknown₂
    ▸-→-~̸₂ TMAArr     τ₂′~̸τ₂ (TCArr _ τ₂~τ₂′) = τ₂′~̸τ₂ (~-sym τ₂~τ₂′)

    -- consistency with an arrow type implies existence of a matched arrow type
    ~→▸-→ : ∀ {τ τ₁ τ₂} → τ ~ τ₁ -→ τ₂ → ∃[ τ₁′ ] ∃[ τ₂′ ] τ ▸ τ₁′ -→ τ₂′
    ~→▸-→ (TCArr {τ₁ = τ₁} {τ₂ = τ₂} τ₁~ τ₂~) = ⟨ τ₁      , ⟨ τ₂      , TMAArr ⟩ ⟩
    ~→▸-→ TCUnknownArr                        = ⟨ unknown , ⟨ unknown , TMAUnknown ⟩ ⟩

    ~-▸-→→~ : ∀ {τ τ₁ τ₂ τ₁′ τ₂′} → τ ~ τ₁ -→ τ₂ → τ ▸ τ₁′ -→ τ₂′ → τ₁ -→ τ₂ ~ τ₁′ -→ τ₂′
    ~-▸-→→~ (TCArr τ₁~ τ₂~) TMAArr     = TCArr (~-sym τ₁~) (~-sym τ₂~)
    ~-▸-→→~ TCUnknownArr    TMAUnknown = TCArr ~-unknown₂ ~-unknown₂

    -- matched product
    data _▸_-×_ : (τ τ₁ τ₂ : Typ) → Set where
      TMPUnknown : unknown ▸ unknown -× unknown
      TMPProd  : {τ₁ τ₂ : Typ} → τ₁ -× τ₂ ▸ τ₁ -× τ₂

    -- no matched
    _!▸-× : Typ → Set
    τ !▸-× = ¬ (∃[ τ₁ ] ∃[ τ₂ ] τ ▸ τ₁ -× τ₂)

    -- decidable matched product
    _▸-×? : (τ : Typ) → Dec (∃[ τ₁ ] ∃[ τ₂ ] τ ▸ τ₁ -× τ₂)
    num        ▸-×? = no (λ ())
    bool       ▸-×? = no (λ ())
    unknown    ▸-×? = yes ⟨ unknown , ⟨ unknown , TMPUnknown ⟩ ⟩
    (τ₁ -→ τ₂) ▸-×? = no (λ ())
    (τ₁ -× τ₂) ▸-×? = yes ⟨ τ₁      , ⟨ τ₂      , TMPProd    ⟩ ⟩

    -- matched product derivation equality
    ▸-×-≡ : ∀ {τ τ₁ τ₂} → (τ▸ : τ ▸ τ₁ -× τ₂) → (τ▸′ : τ ▸ τ₁ -× τ₂) → τ▸ ≡ τ▸′
    ▸-×-≡ TMPUnknown TMPUnknown = refl
    ▸-×-≡ TMPProd    TMPProd    = refl

    -- matched product unicity
    ▸-×-unicity : ∀ {τ τ₁ τ₂ τ₃ τ₄} → (τ ▸ τ₁ -× τ₂) → (τ ▸ τ₃ -× τ₄) → τ₁ -× τ₂ ≡ τ₃ -× τ₄
    ▸-×-unicity TMPUnknown TMPUnknown = refl
    ▸-×-unicity TMPProd    TMPProd    = refl

    -- no matched product derivation equality
    !▸-×-≡ : ∀ {τ} → (τ!▸ : τ !▸-×) → (τ!▸′ : τ !▸-×) → τ!▸ ≡ τ!▸′
    !▸-×-≡ τ!▸ τ!▸′ = ¬-≡ τ!▸ τ!▸′

    -- only consistent types product match
    ▸-×→~ : ∀ {τ τ₁ τ₂} → τ ▸ τ₁ -× τ₂ → τ ~ τ₁ -× τ₂
    ▸-×→~ TMPUnknown = TCUnknownProd
    ▸-×→~ TMPProd    = ~-refl

    ▸-×-~̸₁ : ∀ {τ τ₁ τ₂ τ₁′} → τ ▸ τ₁ -× τ₂ → τ₁′ ~̸ τ₁ → τ ~̸ τ₁′ -× τ₂
    ▸-×-~̸₁ TMPProd    τ₁′~̸τ₁ (TCProd τ₁~τ₁′ _) = τ₁′~̸τ₁ (~-sym τ₁~τ₁′)
    ▸-×-~̸₁ TMPUnknown τ₁′~̸τ₁ TCUnknownProd     = τ₁′~̸τ₁ ~-unknown₂

    ▸-×-~̸₂ : ∀ {τ τ₁ τ₂ τ₂′} → τ ▸ τ₁ -× τ₂ → τ₂′ ~̸ τ₂ → τ ~̸ τ₁ -× τ₂′
    ▸-×-~̸₂ TMPUnknown  τ₂′~̸τ₂ TCUnknownProd     = τ₂′~̸τ₂ ~-unknown₂
    ▸-×-~̸₂ TMPProd     τ₂′~̸τ₂ (TCProd _ τ₂~τ₂′) = τ₂′~̸τ₂ (~-sym τ₂~τ₂′)

    -- consistency with an product type implies existence of a matched product type
    ~→▸-× : ∀ {τ τ₁ τ₂} → τ ~ τ₁ -× τ₂ → ∃[ τ₁′ ] ∃[ τ₂′ ] τ ▸ τ₁′ -× τ₂′
    ~→▸-× (TCProd {τ₁ = τ₁} {τ₂ = τ₂} τ₁~ τ₂~) = ⟨ τ₁      , ⟨ τ₂      , TMPProd ⟩ ⟩
    ~→▸-× TCUnknownProd                        = ⟨ unknown , ⟨ unknown , TMPUnknown ⟩ ⟩

    ~-▸-×→~ : ∀ {τ τ₁ τ₂ τ₁′ τ₂′} → τ ~ τ₁ -× τ₂ → τ ▸ τ₁′ -× τ₂′ → τ₁ -× τ₂ ~ τ₁′ -× τ₂′
    ~-▸-×→~ (TCProd τ₁~ τ₂~) TMPProd    = TCProd (~-sym τ₁~) (~-sym τ₂~)
    ~-▸-×→~ TCUnknownProd    TMPUnknown = TCProd ~-unknown₂ ~-unknown₂

  module meet where
    open base
    open equality
    open consistency

    -- greatest lower bound (where the unknown type is the top of the imprecision partial order)
    data _⊔_⇒_ : (τ₁ τ₂ τ : Typ) → Set where
      TJBase        : {τ : Typ} → (b : τ base) → τ ⊔ τ ⇒ τ
      TJUnknown     : unknown ⊔ unknown ⇒ unknown
      TJUnknownBase : {τ : Typ} → (b : τ base) → unknown ⊔ τ ⇒ τ
      TJBaseUnknown : {τ : Typ} → (b : τ base) → τ ⊔ unknown ⇒ τ
      TJArr         : {τ₁ τ₂ τ₁′ τ₂′ τ₁″ τ₂″ : Typ}
                     → (τ₁⊔τ₁′ : τ₁ ⊔ τ₁′ ⇒ τ₁″)
                     → (τ₂⊔τ₂′ : τ₂ ⊔ τ₂′ ⇒ τ₂″)
                     → τ₁ -→ τ₂ ⊔ τ₁′ -→ τ₂′ ⇒ τ₁″ -→ τ₂″
      TJUnknownArr  : {τ₁ τ₂ : Typ}
                     → unknown ⊔ τ₁ -→ τ₂ ⇒ τ₁ -→ τ₂
      TJArrUnknown  : {τ₁ τ₂ : Typ}
                     → τ₁ -→ τ₂ ⊔ unknown ⇒ τ₁ -→ τ₂
      TJProd        : {τ₁ τ₂ τ₁′ τ₂′ τ₁″ τ₂″ : Typ}
                     → (τ₁⊔τ₁′ : τ₁ ⊔ τ₁′ ⇒ τ₁″)
                     → (τ₂⊔τ₂′ : τ₂ ⊔ τ₂′ ⇒ τ₂″)
                     → τ₁ -× τ₂ ⊔ τ₁′ -× τ₂′ ⇒ τ₁″ -× τ₂″
      TJUnknownProd : {τ₁ τ₂ : Typ}
                     → unknown ⊔ τ₁ -× τ₂ ⇒ τ₁ -× τ₂
      TJProdUnknown : {τ₁ τ₂ : Typ}
                     → τ₁ -× τ₂ ⊔ unknown ⇒ τ₁ -× τ₂

    -- decidable meet
    _⊔?_ : (τ₁ : Typ) → (τ₂ : Typ) → Dec (∃[ τ ] τ₁ ⊔ τ₂ ⇒ τ)
    num        ⊔? num          = yes ⟨ num , TJBase TBNum ⟩
    num        ⊔? bool         = no λ()
    num        ⊔? unknown      = yes ⟨ num , TJBaseUnknown TBNum ⟩
    num        ⊔? (_ -→ _)     = no λ()
    num        ⊔? (_ -× _)     = no λ()
    bool       ⊔? num          = no λ()
    bool       ⊔? bool         = yes ⟨ bool , TJBase TBBool ⟩
    bool       ⊔? unknown      = yes ⟨ bool , TJBaseUnknown TBBool ⟩
    bool       ⊔? (_ -→ _)     = no λ()
    bool       ⊔? (_ -× _)     = no λ()
    unknown    ⊔? num          = yes ⟨ num      , TJUnknownBase TBNum ⟩
    unknown    ⊔? bool         = yes ⟨ bool     , TJUnknownBase TBBool ⟩
    unknown    ⊔? unknown      = yes ⟨ unknown  , TJUnknown ⟩
    unknown    ⊔? (τ₁ -→ τ₂)   = yes ⟨ τ₁ -→ τ₂ , TJUnknownArr ⟩
    unknown    ⊔? (τ₁ -× τ₂)   = yes ⟨ τ₁ -× τ₂ , TJUnknownProd ⟩
    (τ₁ -→ τ₂) ⊔? num          = no λ()
    (τ₁ -→ τ₂) ⊔? bool         = no λ()
    (τ₁ -→ τ₂) ⊔? unknown      = yes ⟨ τ₁ -→ τ₂ , TJArrUnknown ⟩
    (τ₁ -→ τ₂) ⊔? (τ₁′ -→ τ₂′)
      with τ₁ ⊔? τ₁′          | τ₂ ⊔? τ₂′
    ...  | yes ⟨ τ , τ₁⊔τ₁′ ⟩ | yes ⟨ τ′ , τ₂⊔τ₂′′ ⟩ = yes ⟨ τ -→ τ′ , TJArr τ₁⊔τ₁′ τ₂⊔τ₂′′ ⟩
    ...  | _                  | no ¬τ₂⊔τ₂′           = no λ { ⟨ .(_ -→ _) , TJArr {τ₂″ = τ₂″} τ₁⊔τ₁′″ τ₂⊔τ₂′″ ⟩ → ¬τ₂⊔τ₂′ ⟨ τ₂″ , τ₂⊔τ₂′″ ⟩ }
    ...  | no ¬τ₁⊔τ₁′         | _                    = no λ { ⟨ .(_ -→ _) , TJArr {τ₁″ = τ₁″} τ₁⊔τ₁′″ τ₂⊔τ₂′″ ⟩ → ¬τ₁⊔τ₁′ ⟨ τ₁″ , τ₁⊔τ₁′″ ⟩ }
    (τ₁ -→ τ₂) ⊔? (τ₁′ -× τ₂′) = no λ()
    (τ₁ -× τ₂) ⊔? num          = no λ()
    (τ₁ -× τ₂) ⊔? bool         = no λ()
    (τ₁ -× τ₂) ⊔? unknown      = yes ⟨ τ₁ -× τ₂ , TJProdUnknown ⟩
    (τ₁ -× τ₂) ⊔? (τ₁′ -→ τ₂′) = no λ()
    (τ₁ -× τ₂) ⊔? (τ₁′ -× τ₂′)
      with τ₁ ⊔? τ₁′          | τ₂ ⊔? τ₂′
    ...  | yes ⟨ τ , τ₁⊔τ₁′ ⟩ | yes ⟨ τ′ , τ₂⊔τ₂′′ ⟩ = yes ⟨ τ -× τ′ , TJProd τ₁⊔τ₁′ τ₂⊔τ₂′′ ⟩
    ...  | _                  | no ¬τ₂⊔τ₂′           = no λ { ⟨ .(_ -× _) , TJProd {τ₂″ = τ₂″} τ₁⊔τ₁′″ τ₂⊔τ₂′″ ⟩ → ¬τ₂⊔τ₂′ ⟨ τ₂″ , τ₂⊔τ₂′″ ⟩ }
    ...  | no ¬τ₁⊔τ₁′         | _                    = no λ { ⟨ .(_ -× _) , TJProd {τ₁″ = τ₁″} τ₁⊔τ₁′″ τ₂⊔τ₂′″ ⟩ → ¬τ₁⊔τ₁′ ⟨ τ₁″ , τ₁⊔τ₁′″ ⟩ }

    -- meet of same type
    ⊔-refl : ∀ {τ} → τ ⊔ τ ⇒ τ
    ⊔-refl {num}     = TJBase TBNum
    ⊔-refl {bool}    = TJBase TBBool
    ⊔-refl {unknown} = TJUnknown
    ⊔-refl {τ₁ -→ τ₂}
      with τ₁⊔τ₁ ← ⊔-refl {τ₁}
         | τ₂⊔τ₂ ← ⊔-refl {τ₂}
         = TJArr τ₁⊔τ₁ τ₂⊔τ₂
    ⊔-refl {τ₁ -× τ₂}
      with τ₁⊔τ₁ ← ⊔-refl {τ₁}
         | τ₂⊔τ₂ ← ⊔-refl {τ₂}
         = TJProd τ₁⊔τ₁ τ₂⊔τ₂

    -- meet is symmetric
    ⊔-sym : ∀ {τ₁ τ₂ τ} → τ₁ ⊔ τ₂ ⇒ τ → τ₂ ⊔ τ₁ ⇒ τ
    ⊔-sym (TJBase b)           = TJBase b
    ⊔-sym TJUnknown            = TJUnknown
    ⊔-sym (TJUnknownBase b)    = TJBaseUnknown b
    ⊔-sym (TJBaseUnknown b)    = TJUnknownBase b
    ⊔-sym TJUnknownArr         = TJArrUnknown
    ⊔-sym TJArrUnknown         = TJUnknownArr
    ⊔-sym (TJArr ⊔⇒τ₁″ ⊔⇒τ₂″)  = TJArr (⊔-sym ⊔⇒τ₁″) (⊔-sym ⊔⇒τ₂″)
    ⊔-sym TJUnknownProd        = TJProdUnknown
    ⊔-sym TJProdUnknown        = TJUnknownProd
    ⊔-sym (TJProd ⊔⇒τ₁″ ⊔⇒τ₂″) = TJProd (⊔-sym ⊔⇒τ₁″) (⊔-sym ⊔⇒τ₂″)

    -- meet with unknown
    ⊔-unknown₁ : ∀ {τ} → unknown ⊔ τ ⇒ τ
    ⊔-unknown₁ {num}     = TJUnknownBase TBNum
    ⊔-unknown₁ {bool}    = TJUnknownBase TBBool
    ⊔-unknown₁ {unknown} = TJUnknown
    ⊔-unknown₁ {_ -→ _}  = TJUnknownArr
    ⊔-unknown₁ {_ -× _}  = TJUnknownProd

    ⊔-unknown₂ : ∀ {τ} → τ ⊔ unknown ⇒ τ
    ⊔-unknown₂ {num}     = TJBaseUnknown TBNum
    ⊔-unknown₂ {bool}    = TJBaseUnknown TBBool
    ⊔-unknown₂ {unknown} = TJUnknown
    ⊔-unknown₂ {_ -→ _}  = TJArrUnknown
    ⊔-unknown₂ {_ -× _}  = TJProdUnknown

    -- meet unicity
    ⊔-unicity : ∀ {τ₁ τ₂ τ τ′} → τ₁ ⊔ τ₂ ⇒ τ → τ₁ ⊔ τ₂ ⇒ τ′ → τ ≡ τ′ 
    ⊔-unicity (TJBase _)            (TJBase _)                = refl
    ⊔-unicity TJUnknown             TJUnknown                 = refl
    ⊔-unicity (TJUnknownBase _)     (TJUnknownBase _)         = refl
    ⊔-unicity (TJBaseUnknown _)     (TJBaseUnknown _)         = refl
    ⊔-unicity TJUnknownArr          TJUnknownArr              = refl
    ⊔-unicity TJArrUnknown          TJArrUnknown              = refl
    ⊔-unicity (TJArr _ _)           (TJBase ())
    ⊔-unicity (TJArr τ₁⊔τ₁′ τ₂⊔τ₂′) (TJArr τ₁⊔τ₁′′ τ₂⊔τ₂′′)   = -→-≡ (⊔-unicity τ₁⊔τ₁′ τ₁⊔τ₁′′) (⊔-unicity τ₂⊔τ₂′ τ₂⊔τ₂′′)
    ⊔-unicity TJUnknownProd         TJUnknownProd             = refl
    ⊔-unicity TJProdUnknown         TJProdUnknown             = refl
    ⊔-unicity (TJProd _ _)          (TJBase ())
    ⊔-unicity (TJProd τ₁⊔τ₁′ τ₂⊔τ₂′) (TJProd τ₁⊔τ₁′′ τ₂⊔τ₂′′) = -×-≡ (⊔-unicity τ₁⊔τ₁′ τ₁⊔τ₁′′) (⊔-unicity τ₂⊔τ₂′ τ₂⊔τ₂′′)

    -- meet derivation equality
    ⊔-≡ : ∀ {τ₁ τ₂ τ} → (τ₁⊔τ₂ : τ₁ ⊔ τ₂ ⇒ τ) → (τ₁⊔τ₂′ : τ₁ ⊔ τ₂ ⇒ τ) → τ₁⊔τ₂ ≡ τ₁⊔τ₂′
    ⊔-≡ (TJBase b) (TJBase b′) 
      rewrite base-≡ b b′           = refl
    ⊔-≡ TJUnknown TJUnknown         = refl
    ⊔-≡ (TJUnknownBase b) (TJUnknownBase b′)
      rewrite base-≡ b b′           = refl
    ⊔-≡ (TJBaseUnknown b) (TJBaseUnknown b′)
      rewrite base-≡ b b′           = refl
    ⊔-≡ (TJArr τ₁⊔τ₁′ τ₂⊔τ₂′) (TJArr τ₁⊔τ₁′′ τ₂⊔τ₂′′)
      rewrite ⊔-≡ τ₁⊔τ₁′ τ₁⊔τ₁′′
            | ⊔-≡ τ₂⊔τ₂′ τ₂⊔τ₂′′    = refl
    ⊔-≡ TJUnknownArr TJUnknownArr   = refl
    ⊔-≡ TJArrUnknown TJArrUnknown   = refl
    ⊔-≡ (TJProd τ₁⊔τ₁′ τ₂⊔τ₂′) (TJProd τ₁⊔τ₁′′ τ₂⊔τ₂′′)
      rewrite ⊔-≡ τ₁⊔τ₁′ τ₁⊔τ₁′′
            | ⊔-≡ τ₂⊔τ₂′ τ₂⊔τ₂′′    = refl
    ⊔-≡ TJUnknownProd TJUnknownProd = refl
    ⊔-≡ TJProdUnknown TJProdUnknown = refl

    -- meet existence means that types are consistent
    ⊔→~ : ∀ {τ τ₁ τ₂} → τ₁ ⊔ τ₂ ⇒ τ → τ₁ ~ τ₂
    ⊔→~ (TJBase b)             = TCBase b
    ⊔→~ TJUnknown              = TCUnknown
    ⊔→~ (TJUnknownBase b)      = TCUnknownBase b
    ⊔→~ (TJBaseUnknown b)      = TCBaseUnknown b
    ⊔→~ TJUnknownArr           = TCUnknownArr
    ⊔→~ TJArrUnknown           = TCArrUnknown
    ⊔→~ (TJArr τ₁⊔τ₁′ τ₂⊔τ₂′)  = TCArr (⊔→~ τ₁⊔τ₁′) (⊔→~ τ₂⊔τ₂′)
    ⊔→~ TJUnknownProd          = TCUnknownProd
    ⊔→~ TJProdUnknown          = TCProdUnknown
    ⊔→~ (TJProd τ₁⊔τ₁′ τ₂⊔τ₂′) = TCProd (⊔→~ τ₁⊔τ₁′) (⊔→~ τ₂⊔τ₂′)

    -- consistent types have a meet
    ~→⊔ : ∀ {τ₁ τ₂} → τ₁ ~ τ₂ → ∃[ τ ] τ₁ ⊔ τ₂ ⇒ τ
    ~→⊔           TCUnknown         = ⟨ unknown , TJUnknown       ⟩
    ~→⊔ {τ₁ = τ } (TCBase b)        = ⟨ τ       , TJBase b        ⟩
    ~→⊔ {τ₂ = τ₂} (TCUnknownBase b) = ⟨ τ₂      , TJUnknownBase b ⟩
    ~→⊔ {τ₁ = τ₁} (TCBaseUnknown b) = ⟨ τ₁      , TJBaseUnknown b ⟩
    ~→⊔ {τ₂ = τ₂} TCUnknownArr      = ⟨ τ₂      , TJUnknownArr    ⟩
    ~→⊔ {τ₁ = τ₁} TCArrUnknown      = ⟨ τ₁      , TJArrUnknown    ⟩
    ~→⊔     (TCArr τ₁~τ₁′ τ₂~τ₂′)
      with ⟨ τ₁″ , ⊔⇒τ₁″ ⟩ ← ~→⊔ τ₁~τ₁′
         | ⟨ τ₂″ , ⊔⇒τ₂″ ⟩ ← ~→⊔ τ₂~τ₂′
         = ⟨ τ₁″ -→ τ₂″ , TJArr ⊔⇒τ₁″ ⊔⇒τ₂″ ⟩
    ~→⊔ {τ₂ = τ₂} TCUnknownProd     = ⟨ τ₂ , TJUnknownProd    ⟩
    ~→⊔ {τ₁ = τ₁} TCProdUnknown     = ⟨ τ₁ , TJProdUnknown    ⟩
    ~→⊔     (TCProd τ₁~τ₁′ τ₂~τ₂′)
      with ⟨ τ₁″ , ⊔⇒τ₁″ ⟩ ← ~→⊔ τ₁~τ₁′
         | ⟨ τ₂″ , ⊔⇒τ₂″ ⟩ ← ~→⊔ τ₂~τ₂′
         = ⟨ τ₁″ -× τ₂″ , TJProd ⊔⇒τ₁″ ⊔⇒τ₂″ ⟩

    -- meet nonexistence means types are inconsistent
    ¬⊔→~̸ : ∀ {τ₁ τ₂} → ¬ (∃[ τ ] τ₁ ⊔ τ₂ ⇒ τ) → τ₁ ~̸ τ₂
    ¬⊔→~̸ ¬τ₁⊔τ₂ = λ { τ₁~τ₂ → ¬τ₁⊔τ₂ (~→⊔ τ₁~τ₂) }

    -- inconsistent types have no meet
    ~̸→¬⊔ : ∀ {τ₁ τ₂} → τ₁ ~̸ τ₂ → ¬ (∃[ τ ] τ₁ ⊔ τ₂ ⇒ τ)
    ~̸→¬⊔ τ₁~̸τ₂ = λ { ⟨ τ , τ₁⊔τ₂ ⟩ → τ₁~̸τ₂ (⊔→~ τ₁⊔τ₂) }

    -- types are consistent with their meet
    ⊔⇒→~ : ∀ {τ₁ τ₂ τ} → τ₁ ⊔ τ₂ ⇒ τ → τ₁ ~ τ × τ₂ ~ τ
    ⊔⇒→~ (TJBase b) = ⟨ TCBase b , TCBase b ⟩
    ⊔⇒→~ TJUnknown = ⟨ TCUnknown , TCUnknown ⟩
    ⊔⇒→~ (TJUnknownBase b) = ⟨ TCUnknownBase b , TCBase b ⟩
    ⊔⇒→~ (TJBaseUnknown b) = ⟨ TCBase b , TCUnknownBase b ⟩
    ⊔⇒→~ (TJArr τ₁⊔τ₁′ τ₂⊔τ₂′)
      with ⟨ τ₁~ , τ₁′~ ⟩ ← ⊔⇒→~ τ₁⊔τ₁′
         | ⟨ τ₂~ , τ₂′~ ⟩ ← ⊔⇒→~ τ₂⊔τ₂′
         = ⟨ TCArr τ₁~ τ₂~ , TCArr τ₁′~ τ₂′~ ⟩
    ⊔⇒→~ TJUnknownArr = ⟨ TCUnknownArr , TCArr ~-refl ~-refl ⟩
    ⊔⇒→~ TJArrUnknown = ⟨ TCArr ~-refl ~-refl , TCUnknownArr ⟩
    ⊔⇒→~ (TJProd τ₁⊔τ₁′ τ₂⊔τ₂′)
      with ⟨ τ₁~ , τ₁′~ ⟩ ← ⊔⇒→~ τ₁⊔τ₁′
         | ⟨ τ₂~ , τ₂′~ ⟩ ← ⊔⇒→~ τ₂⊔τ₂′
         = ⟨ TCProd τ₁~ τ₂~ , TCProd τ₁′~ τ₂′~ ⟩
    ⊔⇒→~ TJUnknownProd = ⟨ TCUnknownProd , TCProd ~-refl ~-refl ⟩
    ⊔⇒→~ TJProdUnknown = ⟨ TCProd ~-refl ~-refl , TCUnknownProd ⟩

    -- types are consistent with types consistent to their meet
    ⊔⇒-~→~ : ∀ {τ₁ τ₂ τ τ′} → τ₁ ⊔ τ₂ ⇒ τ → τ ~ τ′ → τ₁ ~ τ′ × τ₂ ~ τ′
    ⊔⇒-~→~ (TJBase b)        τ~τ′ = ⟨ τ~τ′ , τ~τ′ ⟩
    ⊔⇒-~→~ TJUnknown         τ~τ′ = ⟨ τ~τ′ , τ~τ′ ⟩
    ⊔⇒-~→~ (TJUnknownBase b) τ~τ′ = ⟨ ~-unknown₁ , τ~τ′ ⟩
    ⊔⇒-~→~ (TJBaseUnknown b) τ~τ′ = ⟨ τ~τ′ , ~-unknown₁ ⟩
    ⊔⇒-~→~ {τ = .(_ -→ _)} {unknown} (TJArr τ₁⊔τ₁′ τ₂⊔τ₂′) τ~τ′
         = ⟨ TCArrUnknown , TCArrUnknown ⟩
    ⊔⇒-~→~ {τ = .(_ -→ _)} {τ₁″ -→ τ₂″} (TJArr τ₁⊔τ₁′ τ₂⊔τ₂′) (TCArr τ₁″~τ₁‴ τ₂″~τ₂‴)
      with ⟨ τ₁~τ₁″ , τ₁′~τ₁″ ⟩ ← ⊔⇒-~→~ τ₁⊔τ₁′ τ₁″~τ₁‴
      with ⟨ τ₂~τ₂″ , τ₂′~τ₂″ ⟩ ← ⊔⇒-~→~ τ₂⊔τ₂′ τ₂″~τ₂‴
         = ⟨ TCArr τ₁~τ₁″ τ₂~τ₂″ , TCArr τ₁′~τ₁″ τ₂′~τ₂″ ⟩
    ⊔⇒-~→~ {τ = .(_ -→ _)} TJUnknownArr τ~τ′
         = ⟨ ~-unknown₁ , τ~τ′ ⟩
    ⊔⇒-~→~ {τ = .(_ -→ _)} TJArrUnknown τ~τ′
         = ⟨ τ~τ′ , ~-unknown₁ ⟩
    ⊔⇒-~→~ {τ = .(_ -× _)} {unknown} (TJProd τ₁⊔τ₁′ τ₂⊔τ₂′) τ~τ′
         = ⟨ TCProdUnknown , TCProdUnknown ⟩
    ⊔⇒-~→~ {τ = .(_ -× _)} {τ′} (TJProd τ₁⊔τ₁′ τ₂⊔τ₂′) (TCProd τ₁″~τ₁‴ τ₂″~τ₂‴)
      with ⟨ τ₁~τ₁″ , τ₁′~τ₁″ ⟩ ← ⊔⇒-~→~ τ₁⊔τ₁′ τ₁″~τ₁‴
      with ⟨ τ₂~τ₂″ , τ₂′~τ₂″ ⟩ ← ⊔⇒-~→~ τ₂⊔τ₂′ τ₂″~τ₂‴
         = ⟨ TCProd τ₁~τ₁″ τ₂~τ₂″ , TCProd τ₁′~τ₁″ τ₂′~τ₂″ ⟩
    ⊔⇒-~→~ {τ = .(_ -× _)} TJUnknownProd τ~τ′
         = ⟨ ~-unknown₁ , τ~τ′ ⟩
    ⊔⇒-~→~ {τ = .(_ -× _)} TJProdUnknown τ~τ′
         = ⟨ τ~τ′ , ~-unknown₁ ⟩

  open equality public
  open base public
  open consistency public
  open matched public
  open meet public
