module STLC where
-- ma look no imports

{-

   Semantics of Simply Typed Lambda Calculus in Agda
   Zhenya Vinogradov · 6 July 2020

   We describe operational semantics for simply typed lambda calculus by defining a function
   which describes a single computation step (sections 1-11). Then we prove that operational
   semantics are terminating by providing denotational-style semantics, i.e. interpreting
   types of our calculus as corresponding meta-language types (sections 12-19). As the
   termination proof is constructive, it allows us to define an interpreter for the calculus,
   which computes resulting value for a term (section 20).

   This file has 20 sections (also listed in the navigation bar in the rendered version):

   Part I. Operational semantics
     1. Standard library definitions
     2. Types
     3. Introduction and elimination rules
     4. Boilerplate utensils for introduction and elimination rules
     5. Terms
     6. Examples of terms
     7. Compiled term representation
     8. Compilation
     9. Run-time term representation
     10. Operational semantics for elimination rules
     11. Operational semantics for the whole calculus
   Part II. Denotational semantics
     12. Locality lemma
     13. Examples of values
     14. Definition of a computation trace
     15. Definition of denotation for values
     16. Definition of denotation for other objects
     17. Denotational semantics for introduction rules
     18. Denotational semantics for elimination rules
     19. Denotational semantics for the whole calculus
     20. Interpreter

   This file is available in two versions:
   * rendered: https://zhenyavinogradov.github.io/stlc/
   * raw code on github: https://github.com/zhenyavinogradov/stlc/blob/barin/STLC.agda

-}



module 1:Library where
  {-
     1. Standard library definitions
  -}

  -- Pair
  infixr 15 _×_
  infixr 5 _,_
  record _×_ (X Y : Set) : Set where
    constructor _,_
    field
      fst : X
      snd : Y

  -- Dependent sum
  infixr 5 _,,_
  record Σ (Ω : Set) (X : Ω → Set) : Set where
    constructor _,,_
    field
      first  : Ω
      second : X first

  -- Equality
  data Eq {X : Set} (x : X) : X → Set where
    refl : Eq x x

  -- Synonym for 'Eq'
  _≡_ = Eq

  -- List
  infixr 5 _∷_
  data List (X : Set) : Set where
    ε   : List X
    _∷_ : X → List X → List X

  -- Heterogeneous list
  data All {Ω : Set} (X : Ω → Set) : List Ω → Set where
    ε   : All X ε
    _∷_ : ∀ {ω ωs} → X ω → All X ωs → All X (ω ∷ ωs)

  -- Heterogeneous list for Set₁
  data All₁ {Ω : Set} (X : Ω → Set₁) : List Ω → Set₁ where
    ε   : All₁ X ε
    _∷_ : ∀ {ω ωs} → X ω → All₁ X ωs → All₁ X (ω ∷ ωs)

  -- 'Any X ωs' states that 'X' holds for some element of 'ωs'
  data Any {Ω : Set} (X : Ω → Set) : List Ω → Set where
    here  : ∀ {ω ωs} → X ω → Any X (ω ∷ ωs)
    there : ∀ {ω ωs} → Any X ωs → Any X (ω ∷ ωs)

  -- 'Has ωs ω' points at a position of 'ω' in 'ωs'
  Has : {Ω : Set} → List Ω → Ω → Set
  Has ωs ω = Any (Eq ω) ωs

  -- 'All× X Y (ω , ψ)' states that 'X' holds for 'ω' and 'Y' holds for 'ψ'
  data All× {Ω Ψ : Set} (X : Ω → Set) (Y : Ψ → Set) : Ω × Ψ → Set where
    _,_ : ∀ {ω ψ} → X ω → Y ψ → All× X Y (ω , ψ)

  -- 'AllΣ P (ω ,, x)' states that 'P' holds for 'x'
  data AllΣ {Ω : Set} {X : Ω → Set} (P : ∀ ω → X ω → Set) : Σ Ω X → Set where
    _,,_ : (ω : Ω) → {x : X ω} → P ω x → AllΣ P (ω ,, x)

  -- 'All2 P ωs xs' states that 'P' holds for all elements of 'xs'
  data All2 {Ω : Set} {X : Ω → Set} (P : ∀ ω → X ω → Set) : ∀ ωs → All X ωs → Set where
    ε   : All2 P ε ε
    _∷_ : ∀ {ω ωs x xs} → P ω x → All2 P ωs xs → All2 P (ω ∷ ωs) (x ∷ xs)

  -- 'AllAny P ωs xᵢ' states that 'P' holds for the value which 'xᵢ' points to
  data AllAny {Ω : Set} {X : Ω → Set} (P : ∀ ω → X ω → Set) : ∀ ωs → Any X ωs → Set where
    here  : ∀ {ω ωs x} → P ω x → AllAny P (ω ∷ ωs) (here x)
    there : ∀ {ω ωs xᵢ} → AllAny P ωs xᵢ → AllAny P (ω ∷ ωs) (there xᵢ)

  -- Functorial map for List
  mapList : {X Y : Set} → (X → Y) → (List X → List Y)
  mapList f  ε       = ε
  mapList f (x ∷ xs) = f x ∷ mapList f xs

  -- Functorial map for All
  mapAll : {Ω : Set} {X Y : Ω → Set} → (∀ {ω} → X ω → Y ω) → (∀ {ωs} → All X ωs → All Y ωs)
  mapAll f  ε       = ε
  mapAll f (x ∷ xs) = f x ∷ mapAll f xs

  -- Functorial map for Any
  mapAny : {Ω : Set} {X Y : Ω → Set} → (∀ {ω} → X ω → Y ω) → (∀ {ωs} → Any X ωs → Any Y ωs)
  mapAny f (here x)   = here (f x)
  mapAny f (there xᵢ) = there (mapAny f xᵢ)

  -- Functorial map for All2
  mapAll2
      : {Ω : Set} {X Y : Ω → Set} {AllX : ∀ ω → X ω → Set} {AllY : ∀ ω → Y ω → Set}
      → (f : ∀ {ω} → X ω → Y ω)
      → (allF : ∀ {ω x} → AllX ω x → AllY ω (f x))
      → ∀ {ωs xs} → All2 AllX ωs xs → All2 AllY ωs (mapAll f xs)
  mapAll2 f allF  ε       = ε
  mapAll2 f allF (p ∷ ps) = allF p ∷ mapAll2 f allF ps

  -- Functorial map for AllAny
  mapAllAny
      : {Ω : Set} {X Y : Ω → Set} {AllX : ∀ ω → X ω → Set} {AllY : ∀ ω → Y ω → Set}
      → (f : ∀ {ω} → X ω → Y ω)
      → (allF : ∀ {ω x} → AllX ω x → AllY ω (f x))
      → ∀ {ωs xs} → AllAny AllX ωs xs → AllAny AllY ωs (mapAny f xs)
  mapAllAny f allF (here p)   = here (allF p)
  mapAllAny f allF (there pᵢ) = there (mapAllAny f allF pᵢ)

  -- Identity function
  identity : {X : Set} → X → X
  identity x = x

  -- Proves that function application preserves equality
  cong : {X Y : Set} → (f : X → Y) → ∀ {x x'} → x ≡ x' → f x ≡ f x'
  cong f refl = refl

  -- Proves that index of a predicate can be replaced with an equal one
  transport : {Ω : Set} → (X : Ω → Set) → ∀ {ω ω'} → ω ≡ ω' → X ω → X ω'
  transport X refl x = x

  -- Shorthands for 'Has' for several first elements
  $0 : ∀ {Ω ω₀ ωs}             → Has {Ω} (ω₀ ∷ ωs) ω₀
  $1 : ∀ {Ω ω₀ ω₁ ωs}          → Has {Ω} (ω₀ ∷ ω₁ ∷ ωs) ω₁
  $2 : ∀ {Ω ω₀ ω₁ ω₂ ωs}       → Has {Ω} (ω₀ ∷ ω₁ ∷ ω₂ ∷ ωs) ω₂
  $3 : ∀ {Ω ω₀ ω₁ ω₂ ω₃ ωs}    → Has {Ω} (ω₀ ∷ ω₁ ∷ ω₂ ∷ ω₃ ∷ ωs) ω₃
  $4 : ∀ {Ω ω₀ ω₁ ω₂ ω₃ ω₄ ωs} → Has {Ω} (ω₀ ∷ ω₁ ∷ ω₂ ∷ ω₃ ∷ ω₄ ∷ ωs) ω₄
  $0 = here refl
  $1 = there $0
  $2 = there $1
  $3 = there $2
  $4 = there $3

  -- Returns ith element of 'All'
  get : {Ω : Set} {X : Ω → Set} → ∀ {ω ωs} → All X ωs → Has ωs ω → X ω
  get (x ∷ xs) (here refl) = x
  get (x ∷ xs) (there i)   = get xs i

  -- Returns ith element of 'All2'
  get2 : {Ω : Set} {X : Ω → Set} {P : ∀ ω → X ω → Set} → ∀ {ω ωs xs} → All2 P ωs xs → (i : Has ωs ω) → P ω (get xs i)
  get2 (p ∷ ps) (here refl) = p
  get2 (p ∷ ps) (there i)   = get2 ps i

  -- List concatenation
  infixr 5 _++_
  _++_ : {X : Set} → List X → List X → List X
  ε        ++ ys = ys
  (x ∷ xs) ++ ys = x ∷ (xs ++ ys)


  {-
     Some properties of 'Has'
  -}

  has-skip : {Ω : Set} → {τs : List Ω} → {τ : Ω} → (ρs : List Ω) → Has τs τ → Has (ρs ++ τs) τ
  has-skip  ε       i = i
  has-skip (ρ ∷ ρs) i = there (has-skip ρs i)

  has-append : {Ω : Set} → {τs : List Ω} → {τ : Ω} → (ρs : List Ω) → Has τs τ → Has (τs ++ ρs) τ
  has-append ρs (here e)  = here e
  has-append ρs (there i) = there (has-append ρs i)

  has-splice : {Ω : Set} → {τ : Ω} → (τs τs' ρs : List Ω) → Has (τs ++ τs') τ → Has (τs ++ ρs ++ τs') τ
  has-splice  ε       τs' ρs  i        = has-skip ρs i
  has-splice (τ ∷ τs) τs' ρs (here e)  = here e
  has-splice (τ ∷ τs) τs' ρs (there i) = there (has-splice τs τs' ρs i)

  has-abs : {Ω : Set} → {τ : Ω} → (τ' : Ω) → (τs ρs : List Ω) → Has (τ' ∷ τs) τ → Has (τ' ∷ ρs ++ τs) τ
  has-abs τ' τs ρs i = has-splice (τ' ∷ ε) τs ρs i

  has-cons : {Ω : Set} → {τs : List Ω} → {τ' τ : Ω} → Has τs τ' → Has (τ' ∷ τs) τ → Has τs τ
  has-cons i (here refl) = i
  has-cons i (there j)   = j

  has-prepend : {Ω : Set} → {τs τs' : List Ω} → (∀ {τ} → Has τs τ → Has τs' τ) → (σs : List Ω) → (∀ {τ} → Has (σs ++ τs) τ → Has (σs ++ τs') τ)
  has-prepend f  ε        x        = f x
  has-prepend f (σ ∷ σs) (here x)  = here x
  has-prepend f (σ ∷ σs) (there x) = there (has-prepend f σs x)

open 1:Library



module 2:Types where
  {-
     2. Types
  -}

  -- Types defined in our calculus. We have functions, finite coproducts, finite products, and
  -- a couple of inductive and coinductive types
  infixr 5 _⇒_
  data Type : Set where
    _⇒_      : Type → Type → Type -- function
    #Sum     : List Type → Type   -- sum of a list of types
    #Product : List Type → Type   -- product of a list of types
    #Nat     : Type               -- natural number
    #Conat   : Type               -- conatural number (potentially infinite number)
    #Stream  : Type → Type        -- stream (infinite sequence)

  -- Empty sum
  #Void : Type
  #Void = #Sum ε

  -- Empty product
  #Unit : Type
  #Unit = #Product ε

  -- Sum of two types
  #Either : Type → Type → Type
  #Either σ τ = #Sum (σ ∷ τ ∷ ε)

  -- Product of two types
  #Pair : Type → Type → Type
  #Pair σ τ = #Product (σ ∷ τ ∷ ε)

  -- Bool
  #Bool : Type
  #Bool = #Either #Unit #Unit

  -- Maybe
  #Maybe : Type → Type
  #Maybe τ = #Either #Unit τ

open 2:Types



module 3:Rules where
  {-
     3. Introduction and elimination rules
  -}

  {-
     We define introduction and elimination rules for our calculus, parameterized by two
     special types: '%Abstraction' and '%Value'. In next sections we use different
     instantiatons of these two types to define different representations for terms
     of our calculus.
  -}

  -- Introduction rules
  data Intr (%Abstraction : Type → Type → Set) (%Value : Type → Set) : Type → Set where
    -- A function is defined by a lambda abstraction
    intrArrow : ∀ {ρ τ} → %Abstraction ρ τ → Intr %Abstraction %Value (ρ ⇒ τ)

    -- To construct '#Sum τs', provide a value for one of the types in τs
    intrSum : ∀ {τs} → Any %Value τs → Intr %Abstraction %Value (#Sum τs)

    -- To construct '#Product τs', provide a value for each type in τs
    intrProduct : ∀ {τs} → All %Value τs → Intr %Abstraction %Value (#Product τs)

    -- To construct '#Nat', provide a value of type '#Maybe #Nat'. 'nothing' corresponds to
    -- zero, 'just n' corresponds to the successor of 'n'
    intrNat : %Value (#Maybe #Nat) → Intr %Abstraction %Value #Nat

    -- Conatural number is defined by a triple '(ρ ,, v , f)', where ρ is a type, 'v' is a
    -- value of type ρ and 'f' is a function of type 'ρ ⇒ #Maybe ρ'. 'v' represents current
    -- state, 'f' returns 'nothing' if the number is zero, or 'just u' if the number is the
    -- successor of 'u'
    intrConat : Σ Type (\ρ → %Value ρ × %Value (ρ ⇒ #Maybe ρ)) → Intr %Abstraction %Value #Conat

    -- Stream of elements of type τ is defined by a triple (ρ ,, v , f), where ρ is a type,
    -- 'v' is a value of type ρ and 'f' is a function of type 'ρ ⇒ #Pair τ ρ'. 'v' represents
    -- current state, 'f' returns a pair containing stream head and stream tail
    intrStream : ∀ {τ} → Σ Type (\ρ → %Value ρ × %Value (ρ ⇒ #Pair τ ρ)) → Intr %Abstraction %Value (#Stream τ)

  -- Elimination rules
  data Elim (%Value : Type → Set) : Type → Type → Set where
    -- To eliminate 'ρ ⇒ τ', provide a value of type ρ; the result will be of type τ
    elimArrow : ∀ {ρ τ} → %Value ρ → Elim %Value (ρ ⇒ τ) τ

    -- To eliminate '#Sum τs', provide a function 'τ ⇒ ϕ' for each type τ in τs; the result
    -- will be of type ϕ
    elimSum : ∀ {τs ϕ} → All (\τ → %Value (τ ⇒ ϕ)) τs → Elim %Value (#Sum τs) ϕ

    -- If τ is a member of τs, we can eliminate '#Product τs' to get a value of type τ
    elimProduct : ∀ {τs τ} → Has τs τ → Elim %Value (#Product τs) τ

    -- Elimination for '#Nat' is recursion
    elimNat : ∀ {ϕ} → %Value (#Maybe ϕ ⇒ ϕ) → Elim %Value #Nat ϕ

    -- '#Conat' can be deconstructed into '#Maybe #Conat', giving 'nothing' for zero, or
    -- 'just n' for the successor of 'n'
    elimConat : Elim %Value #Conat (#Maybe #Conat)

    -- '#Stream τ' can be deconstructed into '#Pair τ (#Stream τ)', giving a pair containing
    -- stream head and stream tail
    elimStream : ∀ {τ} → Elim %Value (#Stream τ) (#Pair τ (#Stream τ))

  -- An expression is either an introduction rule, or an elimination rule with a value it applies to
  data Expr (%Abstraction : Type → Type → Set) (%Value : Type → Set) (τ : Type) : Set where
    intr : Intr %Abstraction %Value τ         → Expr %Abstraction %Value τ
    elim : ∀ {ϕ} → %Value ϕ → Elim %Value ϕ τ → Expr %Abstraction %Value τ

open 3:Rules



module 4:Utensils where
  {-
     4. Boilerplate utensils for introduction and elimination rules
  -}

  -- Functorial map for Intr
  mapIntr
      : ∀ {%A1 %A2 %V1 %V2}
      → (%mapA : ∀ {ρ τ} → %A1 ρ τ → %A2 ρ τ) → (%mapV : ∀ {τ} → %V1 τ → %V2 τ) → (∀ {τ} → Intr %A1 %V1 τ → Intr %A2 %V2 τ)
  mapIntr %mapA %mapV (intrArrow abs)           = intrArrow (%mapA abs) 
  mapIntr %mapA %mapV (intrSum vᵢ)              = intrSum (mapAny %mapV vᵢ)
  mapIntr %mapA %mapV (intrProduct vs)          = intrProduct (mapAll %mapV vs)
  mapIntr %mapA %mapV (intrNat v)               = intrNat (%mapV v)
  mapIntr %mapA %mapV (intrConat (ρ ,, v , f))  = intrConat (ρ ,, %mapV v , %mapV f)
  mapIntr %mapA %mapV (intrStream (ρ ,, v , f)) = intrStream (ρ ,, %mapV v , %mapV f)

  -- Functorial map for Elim
  mapElim : ∀ {%V1 %V2} → (%mapV : ∀ {τ} → %V1 τ → %V2 τ) → (∀ {τ ϕ} → Elim %V1 τ ϕ → Elim %V2 τ ϕ)
  mapElim %mapV (elimArrow v)   = elimArrow (%mapV v)
  mapElim %mapV (elimSum fs)    = elimSum (mapAll %mapV fs)
  mapElim %mapV (elimProduct i) = elimProduct i
  mapElim %mapV (elimNat f)     = elimNat (%mapV f)
  mapElim %mapV  elimConat      = elimConat
  mapElim %mapV  elimStream     = elimStream

  -- Functorial map for Expr
  mapExpr
      : ∀ {%A1 %A2 %V1 %V2}
      → (%mapA : ∀ {ρ τ} → %A1 ρ τ → %A2 ρ τ) → (%mapV : ∀ {τ} → %V1 τ → %V2 τ) → (∀ {τ} → Expr %A1 %V1 τ → Expr %A2 %V2 τ)
  mapExpr %mapA %mapV (intr rule)       = intr (mapIntr %mapA %mapV rule)
  mapExpr %mapA %mapV (elim value rule) = elim (%mapV value) (mapElim %mapV rule)

  -- 'AllIntr %AllA %AllV τ rule' states that:
  -- 1. all instances of '%A' in 'rule' satisfy '%AllA'
  -- 2. all instances of '%V' in 'rule' satisfy '%AllV'
  data AllIntr
      {%A : Type → Type → Set} {%V : Type → Set}
      (%AllA : (ρ τ : Type) → %A ρ τ → Set) (%AllV : (τ : Type) → %V τ → Set)
      : ∀ τ → Intr %A %V τ → Set where
    mkAllIntrArrow   : ∀ {ρ τ abs} → %AllA ρ τ abs                                        → AllIntr _ _ (ρ ⇒ τ)       (intrArrow abs)
    mkAllIntrSum     : ∀ {τs vᵢ}   → AllAny %AllV τs vᵢ                                   → AllIntr _ _ (#Sum τs)     (intrSum vᵢ)
    mkAllIntrProduct : ∀ {τs vs}   → All2 %AllV τs vs                                     → AllIntr _ _ (#Product τs) (intrProduct vs)
    mkAllIntrNat     : ∀ {v}       → %AllV (#Maybe #Nat) v                                → AllIntr _ _  #Nat         (intrNat v)
    mkAllIntrConat   : ∀ {r}       → AllΣ (\ρ → All× (%AllV ρ) (%AllV (ρ ⇒ #Maybe ρ))) r  → AllIntr _ _  #Conat       (intrConat r)
    mkAllIntrStream  : ∀ {τ r}     → AllΣ (\ρ → All× (%AllV ρ) (%AllV (ρ ⇒ #Pair τ ρ))) r → AllIntr _ _ (#Stream τ)   (intrStream r)

  -- 'AllElim %AllV τ ϕ rule' states that all instances of '%V' in 'rule' satisfy '%AllV'
  data AllElim {%V : Type → Set} (%AllV : (τ : Type) → %V τ → Set) : ∀ τ ϕ → Elim %V τ ϕ → Set where
    mkAllElimArrow   : ∀ {ρ τ v}   → %AllV ρ v                        → AllElim _ (ρ ⇒ τ)       τ                   (elimArrow v)
    mkAllElimSum     : ∀ {τs ϕ fs} → All2 (\τ → %AllV (τ ⇒ ϕ)) τs fs  → AllElim _ (#Sum τs)     ϕ                   (elimSum fs)
    mkAllElimProduct : ∀ {τs τ}    → (i : Has τs τ)                   → AllElim _ (#Product τs) τ                   (elimProduct i)
    mkAllElimNat     : ∀ {ϕ f}     → %AllV (#Maybe ϕ ⇒ ϕ) f           → AllElim _  #Nat         ϕ                   (elimNat f)
    mkAllElimConat   :                                                  AllElim _  #Conat      (#Maybe #Conat)       elimConat
    mkAllElimStream  : ∀ {τ}                                          → AllElim _ (#Stream τ)  (#Pair τ (#Stream τ)) elimStream

  -- Functorial map for AllIntr
  mapAllIntr
      : {%A1 %A2 : Type → Type → Set} → {%V1 %V2 : Type → Set}
      → {%AllA1 : ∀ ρ τ → %A1 ρ τ → Set} {%AllA2 : ∀ ρ τ → %A2 ρ τ → Set} {%AllV1 : ∀ τ → %V1 τ → Set} {%AllV2 : ∀ τ → %V2 τ → Set}
      → (%mapA : ∀ {ρ τ} → %A1 ρ τ → %A2 ρ τ)
      → (%mapV : ∀ {τ} → %V1 τ → %V2 τ)
      → (%mapAllA : ∀ {ρ τ abs} → %AllA1 ρ τ abs → %AllA2 ρ τ (%mapA abs))
      → (%mapAllV : ∀ {τ v} → %AllV1 τ v → %AllV2 τ (%mapV v))
      → ∀ {τ rule} → AllIntr %AllA1 %AllV1 τ rule → AllIntr %AllA2 %AllV2 τ (mapIntr %mapA %mapV rule)
  mapAllIntr %mapA %mapV %mapAllA %mapAllV (mkAllIntrArrow abs)           = mkAllIntrArrow (%mapAllA abs)
  mapAllIntr %mapA %mapV %mapAllA %mapAllV (mkAllIntrSum vᵢ)              = mkAllIntrSum (mapAllAny %mapV %mapAllV vᵢ)
  mapAllIntr %mapA %mapV %mapAllA %mapAllV (mkAllIntrProduct vs)          = mkAllIntrProduct (mapAll2 %mapV %mapAllV vs)
  mapAllIntr %mapA %mapV %mapAllA %mapAllV (mkAllIntrNat v)               = mkAllIntrNat (%mapAllV v)
  mapAllIntr %mapA %mapV %mapAllA %mapAllV (mkAllIntrConat (ρ ,, v , f))  = mkAllIntrConat (ρ ,, %mapAllV v , %mapAllV f)
  mapAllIntr %mapA %mapV %mapAllA %mapAllV (mkAllIntrStream (ρ ,, v , f)) = mkAllIntrStream (ρ ,, %mapAllV v , %mapAllV f)

  -- Functorial map for AllElim
  mapAllElim
      : {%V1 %V2 : Type → Set} {%AllV1 : ∀ τ → %V1 τ → Set} {%AllV2 : ∀ τ → %V2 τ → Set}
      → (%mapV : ∀ {τ} → %V1 τ → %V2 τ)
      → (%mapAllV : ∀ {τ v} → %AllV1 τ v → %AllV2 τ (%mapV v))
      → ∀ {τ ϕ rule} → AllElim %AllV1 τ ϕ rule → AllElim %AllV2 τ ϕ (mapElim %mapV rule)
  mapAllElim %mapV %mapAllV (mkAllElimArrow v)   = mkAllElimArrow (%mapAllV v)
  mapAllElim %mapV %mapAllV (mkAllElimSum fs)    = mkAllElimSum (mapAll2 %mapV %mapAllV fs)
  mapAllElim %mapV %mapAllV (mkAllElimProduct i) = mkAllElimProduct i
  mapAllElim %mapV %mapAllV (mkAllElimNat f)     = mkAllElimNat (%mapAllV f)
  mapAllElim %mapV %mapAllV  mkAllElimConat      = mkAllElimConat
  mapAllElim %mapV %mapAllV  mkAllElimStream     = mkAllElimStream

open 4:Utensils



module 5:Term where
  {-
     5. Terms
  -}

  mutual
    -- Regular de Bruijn representation of a term
    data Term (Γ : List Type) (τ : Type) : Set where
      -- a variable
      var  : Has Γ τ → Term Γ τ

      -- an expression recursively containing other terms
      wrap : Expr (AbsTerm Γ) (Term Γ) τ → Term Γ τ

    AbsTerm : List Type → (Type → Type → Set)
    AbsTerm Γ ρ τ = Term (ρ ∷ Γ) τ

  -- Maps a function to each variable in a term
  {-# TERMINATING #-} -- terminating because it preserves structure, inlining 'mapExpr' would convince Agda
  mapTerm : ∀ {Γ Δ} → (∀ {τ} → Has Γ τ → Has Δ τ) → (∀ {τ} → Term Γ τ → Term Δ τ)
  mapTerm f (var x)     = var (f x)
  mapTerm f (wrap expr) = wrap (mapExpr (mapTerm (has-prepend f _)) (mapTerm f) expr)

  -- Expands context with one ignored variable
  ↑_ : ∀ {Γ ρ τ} → Term Γ τ → Term (ρ ∷ Γ) τ
  ↑ term = mapTerm there term

open 5:Term



module 6:SomeTerms where
  {-
     6. Examples of terms
  -}

  #lambda : ∀ {Γ σ τ} → Term (σ ∷ Γ) τ → Term Γ (σ ⇒ τ)
  #lambda f = wrap (intr (intrArrow f))

  #apply : ∀ {Γ σ τ} → Term Γ (σ ⇒ τ) → Term Γ σ → Term Γ τ
  #apply f v = wrap (elim f (elimArrow v))

  #compose : ∀ {Γ ρ σ τ} → Term Γ (σ ⇒ τ) → Term Γ (ρ ⇒ σ) → Term Γ (ρ ⇒ τ)
  #compose f g = #lambda (#apply (↑ f) (#apply (↑ g) (var $0)))

  #inl : ∀ {Γ σ τ} → Term Γ σ → Term Γ (#Either σ τ)
  #inl v = wrap (intr (intrSum (here v)))

  #inr : ∀ {Γ σ τ} → Term Γ τ → Term Γ (#Either σ τ)
  #inr v = wrap (intr (intrSum (there (here v))))

  #either : ∀ {Γ σ τ ϕ} → Term Γ (σ ⇒ ϕ) → Term Γ (τ ⇒ ϕ) → Term Γ (#Either σ τ) → Term Γ ϕ
  #either f₁ f₂ v = wrap (elim v (elimSum (f₁ ∷ f₂ ∷ ε)))

  #unit : ∀ {Γ} → Term Γ #Unit
  #unit = wrap (intr (intrProduct ε))

  #pair : ∀ {Γ σ τ} → Term Γ σ → Term Γ τ → Term Γ (#Pair σ τ)
  #pair v₁ v₂ = wrap (intr (intrProduct (v₁ ∷ v₂ ∷ ε)))

  #fst : ∀ {Γ σ τ} → Term Γ (#Pair σ τ) → Term Γ σ
  #fst v = wrap (elim v (elimProduct $0))

  #snd : ∀ {Γ σ τ} → Term Γ (#Pair σ τ) → Term Γ τ
  #snd v = wrap (elim v (elimProduct $1))

  #mapPair : ∀ {Γ ρ σ τ} → Term Γ (σ ⇒ τ) → Term Γ (#Pair ρ σ ⇒ #Pair ρ τ)
  #mapPair f = #lambda (#pair (#fst (var $0)) (#apply (↑ f) (#snd (var $0))))

  #nothing : ∀ {Γ τ} → Term Γ (#Maybe τ)
  #nothing = #inl #unit

  #just : ∀ {Γ τ} → Term Γ τ → Term Γ (#Maybe τ)
  #just v = #inr v

  #maybe : ∀ {Γ τ ϕ} → Term Γ ϕ → Term Γ (τ ⇒ ϕ) → Term Γ (#Maybe τ) → Term Γ ϕ
  #maybe f₁ f₂ v = #either (#lambda (↑ f₁)) f₂ v

  #mapMaybe : ∀ {Γ σ τ} → Term Γ (σ ⇒ τ) → Term Γ (#Maybe σ ⇒ #Maybe τ)
  #mapMaybe f = #lambda (#maybe #nothing (#lambda (#just (#apply (↑ ↑ f) (var $0)))) (var $0))

  #elimNat : ∀ {Γ ϕ} → Term Γ (#Maybe ϕ ⇒ ϕ) → Term Γ (#Nat ⇒ ϕ)
  #elimNat f = #lambda (wrap (elim (var $0) (elimNat (↑ f))))

  #buildConat : ∀ {Γ ρ} → Term Γ (ρ ⇒ #Maybe ρ) → Term Γ (ρ ⇒ #Conat)
  #buildConat f = #lambda (wrap (intr (intrConat (_ ,, var $0 , ↑ f))))

  #buildStream : ∀ {Γ τ ρ} → Term Γ (ρ ⇒ #Pair τ ρ) → Term Γ (ρ ⇒ #Stream τ)
  #buildStream f = #lambda (wrap (intr (intrStream (_ ,, var $0 , ↑ f))))

open 6:SomeTerms



module 7:CompiledTerm where
  {-
     7. Compiled term representation
  -}

  infixr 5 _▸_
  mutual
    -- Compiled representation of a term
    data TermC (Γ : List Type) (τ : Type) : Set where
      -- 'return x': return the value of variable 'x'
      return : Has Γ τ → TermC Γ τ

      -- 'expr ▸ term': compute 'expr', push the result, then proceed to compute 'term'
      _▸_    : ∀ {ρ} → Expr (AbsTermC Γ) (Has Γ) ρ → TermC (ρ ∷ Γ) τ → TermC Γ τ

    AbsTermC : List Type → (Type → Type → Set)
    AbsTermC Γ σ τ = TermC (σ ∷ Γ) τ

  -- Compile-time introduction rule
  IntrC : List Type → Type → Set
  IntrC Γ τ = Intr (AbsTermC Γ) (Has Γ) τ

  -- Compile-time elimination rule
  ElimC : List Type → Type → Type → Set
  ElimC Γ τ ϕ = Elim (Has Γ) τ ϕ

  -- Maps a function to each variable in a term
  {-# TERMINATING #-} -- terminating because it preserves structure, inlining 'mapExpr' would convince Agda
  mapTermC : ∀ {Γ Δ τ} → (∀ {ϕ} → Has Γ ϕ → Has Δ ϕ) → (TermC Γ τ → TermC Δ τ)
  mapTermC f (return x) = return (f x)
  mapTermC f (expr ▸ term) = mapExpr (mapTermC (has-prepend f _)) f expr ▸ mapTermC (has-prepend f _) term

  -- Term computing a single expression
  pure : ∀ {Γ τ} → Expr (AbsTermC Γ) (Has Γ) τ → TermC Γ τ
  pure expr = expr ▸ return $0

open 7:CompiledTerm



module 8:Compilation where
  {-
     8. Compilation
  -}

  infixr 5 _∷ₗ_
  data Linear {Ω : Set} (%V : Ω → Set) (%E : List Ω → Set) : List Ω → Set where
    εₗ   : ∀ {ρs} → %E ρs → Linear %V %E ρs
    _∷ₗ_ : ∀ {ρ ρs} → %V ρ → Linear %V %E (ρ ∷ ρs) → Linear %V %E ρs

  mapLinear
      : {Ω : Set} {%V : Ω → Set} {%E1 %E2 : List Ω → Set}
      → (∀ {τs} → %E1 τs → %E2 τs) → (∀ {τs} → Linear %V %E1 τs → Linear %V %E2 τs)
  mapLinear f (εₗ x)   = εₗ (f x)
  mapLinear f (v ∷ₗ l) = v ∷ₗ mapLinear f l

  mapLinear'
      : {Ω : Set} {%V : Ω → Set} {%E1 %E2 : List Ω → Set} {Γ : List Ω}
      → (∀ {τs} → %E1 τs → %E2 (τs ++ Γ)) → (∀ {τs} → Linear %V %E1 τs → Linear %V %E2 (τs ++ Γ))
  mapLinear' f (εₗ x)   = εₗ (f x)
  mapLinear' f (v ∷ₗ l) = v ∷ₗ mapLinear' f l

  linizeAny
      : {Ω : Set} {%V : Ω → Set} {τs : List Ω}
      → (κ : Ω → Ω) → Any (\τ → %V (κ τ)) τs → Linear %V (\ρs → Any (\τ → Has ρs (κ τ)) τs) ε
  linizeAny κ (here v)   = v ∷ₗ εₗ (here $0)
  linizeAny κ (there vᵢ) = mapLinear there (linizeAny κ vᵢ)

  linizeAll
      : {Ω : Set} {%V : Ω → Set} {τs : List Ω}
      → (κ : Ω → Ω) → All (\τ → %V (κ τ)) τs → Linear %V (\ρs → All (\τ → Has ρs (κ τ)) τs) ε
  linizeAll κ  ε       = εₗ ε
  linizeAll κ (v ∷ vs) = v ∷ₗ mapLinear' (\vs' → has-skip _ $0 ∷ mapAll (has-append _) vs') (linizeAll κ vs)

  linizeIntr : ∀ {%A %V τ} → Intr %A %V τ → Linear %V (\ρs → Intr %A (Has ρs) τ) ε
  linizeIntr (intrArrow e)             = εₗ (intrArrow e)
  linizeIntr (intrSum vᵢ)              = mapLinear intrSum (linizeAny identity vᵢ)
  linizeIntr (intrProduct vs)          = mapLinear intrProduct (linizeAll identity vs)
  linizeIntr (intrNat v)               = v ∷ₗ εₗ (intrNat $0)
  linizeIntr (intrConat (ρ ,, v , f))  = v ∷ₗ f ∷ₗ εₗ (intrConat (ρ ,, $1 , $0))
  linizeIntr (intrStream (ρ ,, v , f)) = v ∷ₗ f ∷ₗ εₗ (intrStream (ρ ,, $1 , $0))

  linizeElim : ∀ {%V τ ϕ} → Elim %V τ ϕ → Linear %V (\ρs → Elim (Has ρs) τ ϕ) ε
  linizeElim (elimArrow v)   = v ∷ₗ εₗ (elimArrow $0)
  linizeElim (elimSum f)     = mapLinear elimSum (linizeAll (\τ → τ ⇒ _) f)
  linizeElim (elimProduct i) = εₗ (elimProduct i)
  linizeElim (elimNat v)     = v ∷ₗ εₗ (elimNat $0)
  linizeElim  elimConat      = εₗ elimConat
  linizeElim  elimStream     = εₗ elimStream

  linizeExpr : ∀ {%A %V τ} → Expr %A %V τ → Linear %V (\ρs → Expr %A (Has ρs) τ) ε
  linizeExpr (intr rule)       = mapLinear intr (linizeIntr rule)
  linizeExpr (elim value rule) = value ∷ₗ mapLinear' (\rule' → elim (has-skip _ $0) (mapElim (has-append _) rule')) (linizeElim rule)

  combine2 : ∀ {Γ ρ τ} → TermC Γ ρ → TermC (ρ ∷ Γ) τ → TermC Γ τ
  combine2 (return x)     term2 = mapTermC (has-cons x) term2
  combine2 (expr ▸ term1) term2 = expr ▸ combine2 term1 (mapTermC (has-abs _ _ _) term2)

  combineL : ∀ {Γ Δ τ} → Linear (TermC Γ) (\ρs → Expr (AbsTermC Γ) (Has ρs) τ) Δ → TermC (Δ ++ Γ) τ
  combineL (εₗ expr)   = pure (mapExpr (mapTermC (has-abs _ _ _)) (has-append _) expr)
  combineL (term ∷ₗ l) = combine2 (mapTermC (has-skip _) term) (combineL l)

  seqize : ∀ {Γ τ} → Expr (AbsTermC Γ) (TermC Γ) τ → TermC Γ τ
  seqize expr = combineL (linizeExpr expr)

  -- Transforms regular representation of a term into compiled representation
  {-# TERMINATING #-} -- terminating because 'mapExpr' preserves structure, inlining 'mapExpr' would convince Agda
  compile : ∀ {Γ τ} → Term Γ τ → TermC Γ τ
  compile (var x)     = return x
  compile (wrap expr) = seqize (mapExpr compile compile expr)

open 8:Compilation



module 9:Runtime where
  {-
     9. Run-time term representation
  -}

  mutual
    -- Result of a computation. Simillar to 'Term', but constructed using only introduction rules
    data Value (τ : Type) : Set where
      construct : Intr Closure Value τ → Value τ

    -- Run-time representation of a function 'ρ ⇒ τ'. Consists of a term in context 'ρ ∷ Γ' and
    -- a list of values for all types in Γ
    data Closure (ρ τ : Type) : Set where
      _&_ : ∀ {Γ} → Env Γ → TermC (ρ ∷ Γ) τ → Closure ρ τ

    -- A list containing a value for each type in Γ
    Env : List Type → Set
    Env Γ = All Value Γ

  -- Run-time introduction rule
  IntrR : Type → Set
  IntrR τ = Intr Closure Value τ

  -- Run-time elimination rule
  ElimR : Type → Type → Set
  ElimR τ ϕ = Elim Value τ ϕ

  -- Unevaluated thunk. Consists of a term and a list of values for all variables of the term
  data Thunk (τ : Type) : Set where
    _&_ : ∀ {Γ} → Env Γ → TermC Γ τ → Thunk τ

  -- A composable sequence of closures
  data CallStack : Type → Type → Set where
    ε   : ∀ {τ}     → CallStack τ τ
    _∷_ : ∀ {ρ σ τ} → Closure ρ σ → CallStack σ τ → CallStack ρ τ

  -- Computation state
  -- * a thunk that is currently being evaluated
  -- * and a continuation which will be applied when we finish evaluating the thunk
  data Machine : Type → Set where
    _▹_ : ∀ {σ τ} → Thunk σ → CallStack σ τ → Machine τ

  -- Result of a single computation step
  -- * final value if the computation finishes
  -- * next computation state if it doesn't
  data Step (τ : Type) : Set where
    finish   : Value τ → Step τ
    continue : Machine τ → Step τ

  -- Plugs a value into a closure, producing a thunk
  composeValueClosure : ∀ {σ τ} → Value σ → Closure σ τ → Thunk τ
  composeValueClosure value (env & term) = (value ∷ env) & term

  -- Composes two callstacks
  composeStackStack : ∀ {ρ σ τ} → CallStack ρ σ → CallStack σ τ → CallStack ρ τ
  composeStackStack  ε                 stack2 = stack2
  composeStackStack (closure ∷ stack1) stack2 = closure ∷ composeStackStack stack1 stack2

  -- Appends a callstack to the current callstack of a machine
  composeMachineStack : ∀ {σ τ} → Machine σ → CallStack σ τ → Machine τ
  composeMachineStack (thunk ▹ stack1) stack2 = thunk ▹ composeStackStack stack1 stack2

  -- Applies a value to a callstack
  composeValueStack : ∀ {σ τ} → Value σ → CallStack σ τ → Step τ
  composeValueStack value  ε                = finish value
  composeValueStack value (closure ∷ stack) = continue (composeValueClosure value closure ▹ stack)

  -- Composes a computation step and a callstack
  -- * for a finished computation: applies the callstack to the result
  -- * for an unfinished computation: append the callstack to the current callstack of the machine
  composeStepStack : ∀ {σ τ} → Step σ → CallStack σ τ → Step τ
  composeStepStack (finish value)     stack = composeValueStack value stack
  composeStepStack (continue machine) stack = continue (composeMachineStack machine stack)

  -- Transforms compiled representation of a closed term into run-time representation
  -- * initial environment is empty
  -- * initial continuation is empty as well
  load : ∀ {τ} → TermC ε τ → Machine τ
  load term = (ε & term) ▹ ε

open 9:Runtime



module 10:OperationalElimination where
  {-
     10. Operational semantics for elimination rules
  -}

  -- Arrow elimination: plug the supplied value into the closure describing the function
  eliminateArrow : ∀ {ρ τ ϕ} → Elim Value (ρ ⇒ τ) ϕ → Value (ρ ⇒ τ) → Thunk ϕ
  eliminateArrow (elimArrow value) (construct (intrArrow closure)) = composeValueClosure value closure

  -- Sum elimination: apply corresponding function to the contained element
  eliminateSum : ∀ {τs ϕ} → Elim Value (#Sum τs) ϕ → Value (#Sum τs) → Thunk ϕ
  eliminateSum (elimSum (f ∷ fs)) (construct (intrSum (here v))) = (f ∷ v ∷ ε) & compile (#apply (var $0) (var $1))
  eliminateSum (elimSum (f ∷ fs)) (construct (intrSum (there vᵢ))) = eliminateSum (elimSum fs) (construct (intrSum vᵢ))

  -- Product elimination: extract the element with the corresponding index
  eliminateProduct : ∀ {τs ϕ} → Elim Value (#Product τs) ϕ → Value (#Product τs) → Thunk ϕ
  eliminateProduct (elimProduct i) (construct (intrProduct vs)) = (get vs i ∷ ε) & compile (var $0)

  -- Natural number elimination: given 'f : #Maybe ϕ ⇒ ϕ' and 'w : #Nat', unpack 'w' to get
  -- 'v : #Maybe #Nat', apply elimination to 'v' recursively to get a value of type '#Maybe ϕ',
  -- then apply 'f' to the result
  eliminateNat : ∀ {ϕ} → Elim Value #Nat ϕ → Value #Nat → Thunk ϕ
  eliminateNat (elimNat f) (construct (intrNat v)) =
      (f ∷ v ∷ ε) & compile (#apply (#compose (var $0) (#mapMaybe (#elimNat (var $0)))) (var $1))

  -- Conatural number elimination: given 'w : #Conat', unpack it to get
  -- '(ρ : Type) × (v : ρ) × (f : ρ ⇒ #Maybe ρ)', apply 'f' to 'v' to get a value
  -- of type '#Maybe ρ', and pack the result into a new Conat
  eliminateConat : ∀ {ϕ} → Elim Value #Conat ϕ → Value #Conat → Thunk ϕ
  eliminateConat elimConat (construct (intrConat (ρ ,, v , f))) =
      (f ∷ v ∷ ε) & compile (#apply (#compose (#mapMaybe (#buildConat (var $0))) (var $0)) (var $1))

  -- Stream elimination: given 'w : #Stream τ', unpack it to get
  -- '(ρ : Type) × (v : ρ) × (f : ρ ⇒ #Pair τ ρ)', apply 'f' to 'v' to get a value
  -- of type '#Pair τ ρ', and pack the result into a new Stream
  eliminateStream : ∀ {τ ϕ} → Elim Value (#Stream τ) ϕ → Value (#Stream τ) → Thunk ϕ
  eliminateStream elimStream (construct (intrStream (ρ ,, v , f))) =
      (f ∷ v ∷ ε) & compile (#apply (#compose (#mapPair (#buildStream (var $0))) (var $0)) (var $1))

  {-
     We don't actually use 'eliminate' definitions for Nat, Conat and Stream given above,
     because they make typechecking in next sections unbearingly slow. Instead we use
     optimized equivalent definitions given below, which compute to the same value but in
     less steps.
  -}

  eliminateNat' : ∀ {ϕ} → Elim Value #Nat ϕ → Value #Nat → Thunk ϕ
  eliminateNat' (elimNat f) (construct (intrNat v)) =
      (f ∷ v ∷ ε) &
      ( intr (intrArrow (intr (intrProduct ε) ▸ pure (intr (intrSum (here $0)))))
      ▸ intr (intrArrow (elim $0 (elimNat $2) ▸ pure (intr (intrSum (there (here $0))))))
      ▸ elim $3 (elimSum ($1 ∷ $0 ∷ ε))
      ▸ pure (elim $3 (elimArrow $0))
      )

  eliminateConat' : ∀ {ϕ} → Elim Value #Conat ϕ → Value #Conat → Thunk ϕ
  eliminateConat' elimConat (construct (intrConat (ρ ,, v , f))) =
      (f ∷ v ∷ ε) &
      ( elim $0 (elimArrow $1)
      ▸ intr (intrArrow (intr (intrProduct ε) ▸ pure (intr (intrSum (here $0)))))
      ▸ intr (intrArrow (intr (intrConat (ρ ,, $0 , $3)) ▸ pure (intr (intrSum (there (here $0))))))
      ▸ pure (elim $2 (elimSum ($1 ∷ $0 ∷ ε)))
      )

  eliminateStream' : ∀ {τ ϕ} → Elim Value (#Stream τ) ϕ → Value (#Stream τ) → Thunk ϕ
  eliminateStream' elimStream (construct (intrStream (ρ ,, v , f))) =
      (f ∷ v ∷ ε) &
      ( elim $0 (elimArrow $1)
      ▸ elim $0 (elimProduct $0)
      ▸ elim $1 (elimProduct $1)
      ▸ intr (intrStream (ρ ,, $0 , $3))
      ▸ pure (intr (intrProduct ($2 ∷ $0 ∷ ε)))
      )

  -- Given a run-time elimination rule and a value, produces a thunk computing the result
  -- of applying the rule to the value
  eliminate : ∀ {τ ϕ} → Elim Value τ ϕ → Value τ → Thunk ϕ
  eliminate {ρ ⇒ τ}       = eliminateArrow
  eliminate {#Sum τs}     = eliminateSum
  eliminate {#Product τs} = eliminateProduct
  eliminate {#Nat}        = eliminateNat'
  eliminate {#Conat}      = eliminateConat'
  eliminate {#Stream τ}   = eliminateStream'

open 10:OperationalElimination



module 11:Operational where
  {-
     11. Operational semantics for the whole calculus
  -}

  -- Given an environment, transforms compile-time introduction rule into a run-time introduction rule
  plugEnvIntr : ∀ {Γ τ} → Env Γ → Intr (AbsTermC Γ) (Has Γ) τ → Intr Closure Value τ
  plugEnvIntr env rule = mapIntr (\term → env & term) (\x → get env x) rule

  -- Given an environment, transforms compile-time elimination rule into a run-time elimination rule
  plugEnvElim : ∀ {Γ τ ϕ} → Env Γ → Elim (Has Γ) τ ϕ → Elim Value τ ϕ
  plugEnvElim env rule = mapElim (\x → get env x) rule


  -- Performs a single computation step by matching on the current term
  reduce : ∀ {τ} → Machine τ → Step τ
  -- * 'return x': supply value of variable 'x' to the continuation stack
  reduce ((env & return x) ▹ stack) = composeValueStack (get env x) stack
  -- * introduction rule: compute value constructed by the introduction rule, push it into
  --   the environment, and continue with computing the rest of the term
  reduce ((env & (intr rule ▸ term')) ▹ stack) = continue (((value ∷ env) & term') ▹ stack)
    where
      value : Value _
      value = construct (plugEnvIntr env rule)
  -- * elimination rule: build a thunk computing the result of the elimination rule, push
  --   current computation into the continuation stack, and start evaluating the new thunk
  reduce ((env & (elim x rule ▸ term')) ▹ stack) = continue (thunk ▹ ((env & term') ∷ stack))
    where
      thunk : Thunk _
      thunk = eliminate (plugEnvElim env rule) (get env x)

open 11:Operational



module 12:Locality where
  {-
     12. Locality lemma
  -}

  -- We can append a callstack to a machine either before, or after performing a reduction
  -- step, the result will be the same
  locality-lem
      : ∀ {σ τ} → (machine : Machine σ) → (stack : CallStack σ τ)
      → composeStepStack (reduce machine) stack ≡ reduce (composeMachineStack machine stack)
  locality-lem ((env & return x)              ▹ ε)                 stack' = refl
  locality-lem ((env & return x)              ▹ (closure ∷ stack)) stack' = refl
  locality-lem ((env & (intr rule   ▸ term')) ▹ stack)             stack' = refl
  locality-lem ((env & (elim x rule ▸ term')) ▹ stack)             stack' = refl

open 12:Locality



module 13:SomeValues where
  {-
     13. Examples of values
  -}

  ^apply : ∀ {τ ϕ} → Value (τ ⇒ ϕ) → Value τ → Thunk ϕ
  ^apply f v = eliminateArrow (elimArrow v) f

  ^here : ∀ {τ τs} → Value τ → Value (#Sum (τ ∷ τs))
  ^here v = construct (intrSum (here v))

  ^there : ∀ {τ τs} → Value (#Sum τs) → Value (#Sum (τ ∷ τs))
  ^there (construct (intrSum vᵢ)) = construct (intrSum (there vᵢ))

  ^nil : Value (#Product ε)
  ^nil = construct (intrProduct ε)

  ^cons : ∀ {τ τs} → Value τ → Value (#Product τs) → Value (#Product (τ ∷ τs))
  ^cons v (construct (intrProduct vs)) = construct (intrProduct (v ∷ vs))

  ^pair : ∀ {σ τ} → Value σ → Value τ → Value (#Pair σ τ)
  ^pair v₁ v₂ = construct (intrProduct (v₁ ∷ v₂ ∷ ε))

  ^nothing : ∀ {τ} → Value (#Maybe τ)
  ^nothing = construct (intrSum (here ^nil))

  ^just : ∀ {τ} → Value τ → Value (#Maybe τ)
  ^just v = construct (intrSum (there (here v)))

  ^mkNat : Value (#Maybe #Nat) → Value #Nat
  ^mkNat v = construct (intrNat v)

  ^mkConat : (ρ : Type) → Value ρ → Value (ρ ⇒ #Maybe ρ) → Value #Conat
  ^mkConat ρ v f = construct (intrConat (ρ ,, v , f))

  ^mkStream : ∀ {τ} → (ρ : Type) → Value ρ → Value (ρ ⇒ #Pair τ ρ) → Value (#Stream τ)
  ^mkStream ρ v f = construct (intrStream (ρ ,, v , f))

open 13:SomeValues



module 14:Trace where
  {-
     14. Definition of a computation trace
  -}

  {-
     As a convention, we prefix names related to denotational semantics with '!'.
  -}

  -- 'TraceStep !τ step' states that 'step' is either a value satisfying
  -- predicate '!τ', or 'step' is a machine, and applying 'reduce' repeatedly
  -- to that machine will eventually terminate with a value satisfying '!τ'
  data TraceStep {τ} (!τ : Value τ → Set) : Step τ → Set where
    !finish   : {value : Value τ} → !τ value → TraceStep !τ (finish value)
    !continue : {machine : Machine τ} → TraceStep !τ (reduce machine) → TraceStep !τ (continue machine)

  -- 'TraceMachine !τ machine' states that applying 'reduce' repeatedly to
  -- 'machine' will eventually terminate, and the final value will satisfy '!τ'
  data TraceMachine {τ} (!τ : Value τ → Set) : Machine τ → Set where
    !continueM : {machine : Machine τ} → TraceStep !τ (reduce machine) → TraceMachine !τ machine

  -- Trace for a thunk is a trace for the machine consisting of this thunk and
  -- an empty continuation
  TraceThunk : ∀ {τ} → (!τ : Value τ → Set) → Thunk τ → Set
  TraceThunk !τ thunk = TraceMachine !τ (thunk ▹ ε)

  -- Functorial map for TraceStep
  mapTraceStep
      : ∀ {τ} { !τ !τ' : Value τ → Set }
      → (∀ {value} → !τ value → !τ' value) → (∀ {step} → TraceStep !τ step → TraceStep !τ' step)
  mapTraceStep f (!finish !v)      = !finish (f !v)
  mapTraceStep f (!continue !step) = !continue (mapTraceStep f !step)

  -- Functorial map for TraceMachine
  mapTraceMachine
      : ∀ {τ} { !τ !τ' : Value τ → Set }
      → (∀ {value} → !τ value → !τ' value) → (∀ {machine} → TraceMachine !τ machine → TraceMachine !τ' machine)
  mapTraceMachine f (!continueM !step) = !continueM (mapTraceStep f !step)

  -- Neat aliases for !finish, !continue and !continueM
  infix 10 ◽_ ∗_ ∗ₘ_

  ◽_ : ∀ {τ value} { !τ : Value τ → Set } → !τ value → TraceStep !τ (finish value)
  ◽_ = !finish

  ∗_ : ∀ {τ machine} { !τ : Value τ → Set } → TraceStep !τ (reduce machine) → TraceStep !τ (continue machine)
  ∗_ = !continue

  ∗ₘ_ : ∀ {τ machine} { !τ : Value τ → Set } → TraceStep !τ (reduce machine) → TraceMachine !τ machine
  ∗ₘ_ = !continueM

  -- Composes trace of a step and trace of a callstack
  !composeStepStack
      : ∀ {σ τ step stack} { !σ : Value σ → Set } { !τ : Value τ → Set }
      → TraceStep !σ step
      → (∀ {value} → !σ value → TraceStep !τ (composeValueStack value stack))
      → TraceStep !τ (composeStepStack step stack)
  !composeStepStack {σ} {τ} {finish value}     {stack} { !σ } { !τ } (!finish !value)   !stack = !stack !value
  !composeStepStack {σ} {τ} {continue machine} {stack} { !σ } { !τ } (!continue !step') !stack =
      !continue (transport (TraceStep !τ) (locality-lem machine stack) (!composeStepStack !step' !stack))

  -- Composes trace of a thunk and trace of a callstack
  _▹!_
      : ∀ {σ τ thunk stack} { !σ : Value σ → Set } { !τ : Value τ → Set }
      → TraceThunk !σ thunk
      → (∀ {value} → !σ value → TraceStep !τ (composeValueStack value stack))
      → TraceStep !τ (reduce (thunk ▹ stack))
  _▹!_ {σ} {τ} {thunk} {stack} { !σ } { !τ } (!continueM !step) !stack =
      transport (TraceStep !τ) (locality-lem (thunk ▹ ε) stack) (!composeStepStack !step !stack)

  -- Returns final value for TraceStep
  resultStep : ∀ {τ step} → { !τ : Value τ → Set } → TraceStep !τ step → Value τ
  resultStep {step = finish value}     (!finish _)        = value
  resultStep {step = continue machine} (!continue trace') = resultStep trace'

  -- Returns final value for TraceMachine
  result : ∀ {τ machine} → { !τ : Value τ → Set } → TraceMachine !τ machine → Value τ
  result (!continueM traceStep) = resultStep traceStep

open 14:Trace



module 15:DenotationValue where
  {-
     15. Definition of denotation for values
  -}

  -- We define denotations on type τ as predicates on values of type τ
  Val : Type → Set₁
  Val τ = Value τ → Set

  -- Denotations for a list of types
  Vals : List Type → Set₁
  Vals τs = All₁ Val τs

  -- Denotation for a function is a function transforming denotation of a value to a denotation
  -- of the application result
  data !Arrow {ρ τ} (!ρ : Val ρ) (!τ : Val τ) : Val (ρ ⇒ τ) where
    !mkArrow : ∀ {f} → (∀ {v} → !ρ v → TraceThunk !τ (^apply f v)) → !Arrow !ρ !τ f

  -- Denotation for a sum is a denotation for the value selected by the sum
  data !Sum : ∀ {τs} → Vals τs → Val (#Sum τs) where
    !here  : ∀ {τ τs v}  { !τ : Val τ } { !τs : All₁ Val τs } → !τ v        → !Sum (!τ ∷ !τs) (^here v)
    !there : ∀ {τ τs vᵢ} { !τ : Val τ } { !τs : All₁ Val τs } → !Sum !τs vᵢ → !Sum (!τ ∷ !τs) (^there vᵢ)

  -- Denotation for a product is a product of denotations
  infixr 5 _∷!_
  data !Product : ∀ {τs} → Vals τs → Val (#Product τs) where
    !ε   : !Product ε ^nil
    _∷!_ : ∀ {τ τs v vs} { !τ : Val τ } { !τs : All₁ Val τs }
         → !τ v → !Product !τs vs → !Product (!τ ∷ !τs) (^cons v vs)

  -- Denotation for a pair is a pair of denotations
  data !Pair {σ τ} (!σ : Val σ) (!τ : Val τ) : Val (#Pair σ τ) where
    _,_ : ∀ {v₁ v₂} → !σ v₁ → !τ v₂ → !Pair !σ !τ (^pair v₁ v₂)

  -- Denotation for Maybe is a meta-language Maybe
  data !Maybe {τ} (!τ : Val τ) : Val (#Maybe τ) where
    !nothing : !Maybe !τ ^nothing
    !just    : ∀ {v} → !τ v → !Maybe !τ (^just v)

  -- Denotation for a natural number is a denotation for the value wrapped by the constructor
  data !Nat : Val #Nat where
    !mkNat : ∀ {n} → !Maybe !Nat n → !Nat (^mkNat n)

  -- Helper type for defining denotation for Conat
  record !ConatU {ρ} (f : Value (ρ ⇒ #Maybe ρ)) (v : Value ρ) : Set where
    coinductive
    field !forceConat : TraceThunk (!Maybe (!ConatU f)) (^apply f v)
  open !ConatU public

  -- Denotation for a conatural number described by a triple (ρ ,, v , f) is a stream of
  -- denotations for all successive applications of 'f' to 'v'
  data !Conat : Val #Conat where
    !mkConat : ∀ {ρ v f} → !ConatU f v → !Conat (^mkConat ρ v f)

  -- Helper type for defining denotation for Stream
  record !StreamU {τ ρ} (!τ : Val τ) (f : Value (ρ ⇒ #Pair τ ρ)) (v : Value ρ) : Set where
    coinductive
    field !forceStream : TraceThunk (!Pair !τ (!StreamU !τ f)) (^apply f v)
  open !StreamU public

  -- Denotation for a stream described by a triple (ρ ,, v , f) is a stream of
  -- denotations for all successive applications of 'f' to 'v'
  data !Stream {τ} (!τ : Val τ) : Val (#Stream τ) where
    !mkStream : ∀ {ρ v f} → !StreamU !τ f v → !Stream !τ (^mkStream ρ v f)

  mutual
    -- Denotation for a value
    !Value : (τ : Type) → Val τ
    !Value (ρ ⇒ τ)       = !Arrow (!Value ρ) (!Value τ)
    !Value (#Sum τs)     = !Sum (!Values τs)
    !Value (#Product τs) = !Product (!Values τs)
    !Value (#Nat)        = !Nat
    !Value (#Conat)      = !Conat
    !Value (#Stream τ)   = !Stream (!Value τ)

    -- A list of denotations for a list of types
    !Values : (τs : List Type) → Vals τs
    !Values  ε       = ε
    !Values (τ ∷ τs) = !Value τ ∷ !Values τs

open 15:DenotationValue



module 16:DenotationRest where
  {-
     16. Definition of denotation for other objects
  -}

  -- Denotation for a step is a trace for the step with a denotation for the final value
  !Step : ∀ τ → Step τ → Set
  !Step τ = TraceStep (!Value τ)

  -- Denotation for a machine is a trace for the machine with a denotation for the final value
  !Machine : ∀ τ → Machine τ → Set
  !Machine τ = TraceMachine (!Value τ)

  -- We also call denotations for machines simply traces
  Trace : ∀ {τ} → Machine τ → Set
  Trace {τ} machine = !Machine τ machine

  -- Denotation for a thunk is a trace for the thunk with a denotation for the final value
  !Thunk : ∀ τ → Thunk τ → Set
  !Thunk τ = TraceThunk (!Value τ)

  -- Denotation for an environment consists of denotations for each value in the environment
  !Env : ∀ Γ → Env Γ → Set
  !Env Γ env = All2 !Value Γ env

  -- Denotation for a closure is a function transforming denotation of a value to a denotation
  -- of the result of applying the closure to the value
  !Closure : ∀ σ τ → (closure : Closure σ τ) → Set
  !Closure σ τ closure = ∀ {value} → !Value σ value → !Thunk τ (composeValueClosure value closure)

  -- Denotation for a callstack is a function transforming denotation of a value to a
  -- denotation of the result of applying the callstack to the value
  !CallStack : ∀ σ τ → CallStack σ τ → Set
  !CallStack σ τ stack = ∀ {value} → !Value σ value → !Step τ (composeValueStack value stack)

  -- Denotation for a term is a function computing denotation for any machine containing
  -- this term
  !TermC : ∀ Γ τ → (term : TermC Γ τ) → Set
  !TermC Γ τ term = ∀ {ϕ env stack} → !Env Γ env → !CallStack τ ϕ stack → !Machine ϕ ((env & term) ▹ stack)

  -- Denotation for 'AbsTermC' is the same as denotation for 'TermC'
  !AbsTermC : ∀ Γ ρ τ → (term : AbsTermC Γ ρ τ) → Set
  !AbsTermC Γ ρ τ term = !TermC (ρ ∷ Γ) τ term

  -- Applies function denotation to a value denotation
  !apply : ∀ {σ τ f v} → !Value (σ ⇒ τ) f → !Value σ v → !Thunk τ (^apply f v)
  !apply (!mkArrow !f) !v = !f !v

open 16:DenotationRest



module 17:DenotationalIntroduction where
  {-
     17. Denotational semantics for introduction rules
  -}

  !constructArrow : ∀ {ρ τ rule} → AllIntr !Closure !Value (ρ ⇒ τ) rule → !Value (ρ ⇒ τ) (construct rule)
  !constructArrow (mkAllIntrArrow !closure) = !mkArrow !closure

  !constructSum : ∀ {τs rule} → AllIntr !Closure !Value (#Sum τs) rule → !Value (#Sum τs) (construct rule)
  !constructSum (mkAllIntrSum (here !v))   = !here !v
  !constructSum (mkAllIntrSum (there !vᵢ)) = !there (!constructSum (mkAllIntrSum !vᵢ))

  !constructProduct : ∀ {τs rule} → AllIntr !Closure !Value (#Product τs) rule → !Value (#Product τs) (construct rule)
  !constructProduct (mkAllIntrProduct ε)          = !ε
  !constructProduct (mkAllIntrProduct (!v ∷ !vs)) = !v ∷! !constructProduct (mkAllIntrProduct !vs)

  !constructNat : ∀ {rule} → AllIntr !Closure !Value #Nat rule → !Value #Nat (construct rule)
  !constructNat (mkAllIntrNat (!here !ε))          = !mkNat !nothing
  !constructNat (mkAllIntrNat (!there (!here !v))) = !mkNat (!just !v)

  !constructConatU : ∀ {ρ f v} → !Value (ρ ⇒ #Maybe ρ) f → !Value ρ v → !ConatU f v
  !forceConat (!constructConatU {ρ} {f} {v} !f !v) = mapConstructMachine (!apply !f !v)
    where
      mapConstructMaybe : ∀ {value} → !Value (#Maybe ρ) value → !Maybe (!ConatU f) value
      mapConstructMaybe (!here !ε)           = !nothing
      mapConstructMaybe (!there (!here !v')) = !just (!constructConatU !f !v')

      mapConstructStep : ∀ {step} → TraceStep (!Value (#Maybe ρ)) step → TraceStep (!Maybe (!ConatU f)) step
      mapConstructStep (!finish !v')     = !finish (mapConstructMaybe !v')
      mapConstructStep (!continue trace) = !continue (mapConstructStep trace)

      mapConstructMachine : ∀ {machine} → TraceMachine (!Value (#Maybe ρ)) machine → TraceMachine (!Maybe (!ConatU f)) machine
      mapConstructMachine (!continueM s) = !continueM (mapConstructStep s)

  !constructConat : ∀ {rule} → AllIntr !Closure !Value #Conat rule → !Value #Conat (construct rule)
  !constructConat (mkAllIntrConat (ρ ,, !v , !f)) = !mkConat (!constructConatU !f !v)

  !constructStreamU : ∀ {τ ρ f v} → !Value (ρ ⇒ #Pair τ ρ) f → !Value ρ v → !StreamU (!Value τ) f v
  !forceStream (!constructStreamU {τ} {ρ} {f} {v} !f !v) = mapConstructMachine (!apply !f !v)
    where
      mapConstructPair : ∀ {value} → !Value (#Pair τ ρ) value → !Pair (!Value τ) (!StreamU (!Value τ) f) value
      mapConstructPair (!u ∷! !v' ∷! !ε) = !u , !constructStreamU !f !v'

      mapConstructStep : ∀ {step} → TraceStep (!Value (#Pair τ ρ)) step → TraceStep (!Pair (!Value τ) (!StreamU (!Value τ) f)) step
      mapConstructStep (!finish !v')     = !finish (mapConstructPair !v')
      mapConstructStep (!continue trace) = !continue (mapConstructStep trace)

      mapConstructMachine : ∀ {machine} → TraceMachine (!Value (#Pair τ ρ)) machine → TraceMachine (!Pair (!Value τ) (!StreamU (!Value τ) f)) machine
      mapConstructMachine (!continueM s) = !continueM (mapConstructStep s)

  !constructStream : ∀ {τ rule} → AllIntr !Closure !Value (#Stream τ) rule → !Value (#Stream τ) (construct rule)
  !constructStream {τ} (mkAllIntrStream (ρ ,, !v , !f)) = !mkStream (!constructStreamU !f !v)

  -- Given denotations for all components of a run-time introduction rule, returns denotation
  -- for the value produced by the rule
  !construct : ∀ {τ rule} → AllIntr !Closure !Value τ rule → !Value τ (construct rule)
  !construct {ρ ⇒ τ}       = !constructArrow
  !construct {#Sum τs}     = !constructSum
  !construct {#Product τs} = !constructProduct
  !construct {#Nat}        = !constructNat
  !construct {#Conat}      = !constructConat
  !construct {#Stream τ}   = !constructStream

open 17:DenotationalIntroduction



module 18:DenotationalElimination where
  {-
     18. Denotational semantics for elimination rules
  -}

  !eliminateArrow : ∀ {ρ τ ϕ rule value} → AllElim !Value (ρ ⇒ τ) ϕ rule → !Value (ρ ⇒ τ) value → !Thunk ϕ (eliminate rule value)
  !eliminateArrow (mkAllElimArrow !v) (!mkArrow !f) = !f !v

  !eliminateSum : ∀ {τs ϕ rule value} → AllElim !Value (#Sum τs) ϕ rule → !Value (#Sum τs) value → !Thunk ϕ (eliminate rule value)
  !eliminateSum (mkAllElimSum (!f ∷ !fs)) (!here !v) = ∗ₘ ∗ (!apply !f !v) ▹! \ !v' → ∗ ◽ !v'
  !eliminateSum (mkAllElimSum (!f ∷ !fs)) (!there {vᵢ = construct (intrSum _)} !vᵢ) = !eliminateSum (mkAllElimSum !fs) !vᵢ

  !eliminateProduct : ∀ {τs ϕ rule value} → AllElim !Value (#Product τs) ϕ rule → !Value (#Product τs) value → !Thunk ϕ (eliminate rule value)
  !eliminateProduct (mkAllElimProduct (here refl)) (_∷!_ {vs = construct (intrProduct _)} !v !vs) = ∗ₘ ◽ !v
  !eliminateProduct (mkAllElimProduct (there i)) (_∷!_ {vs = construct (intrProduct _)} !v !vs) = !eliminateProduct (mkAllElimProduct i) !vs

  !eliminateNat : ∀ {ϕ rule value} → AllElim !Value #Nat ϕ rule → !Value #Nat value → !Thunk ϕ (eliminate rule value)
  !eliminateNat (mkAllElimNat !f) (!mkNat !nothing) =
      ∗ₘ ∗ ∗ ∗ ∗ ∗ ∗ ∗ ∗ ∗ (!apply !f (!here !ε)) ▹! \ !v' →
      ∗ ◽ !v'
  !eliminateNat (mkAllElimNat !f) (!mkNat (!just !n)) =
      ∗ₘ ∗ ∗ ∗ ∗ ∗ (!eliminateNat (mkAllElimNat !f) !n) ▹! \ !v' →
      ∗ ∗ ∗ ∗ ∗    (!apply !f (!there (!here !v')))     ▹! \ !v'' →
      ∗ ◽ !v''

  !eliminateConat : ∀ {ϕ rule value} → AllElim !Value #Conat ϕ rule → !Value #Conat value → !Thunk ϕ (eliminate rule value)
  !eliminateConat mkAllElimConat (!mkConat !v) =
      ∗ₘ ∗ (!forceConat !v) ▹! \
      {  !nothing   → ∗ ∗ ∗ ∗ ∗ ∗ ∗ ∗ ∗ ◽ (!here !ε)
      ; (!just !v') → ∗ ∗ ∗ ∗ ∗ ∗ ∗ ∗ ∗ ◽ (!there (!here (!mkConat !v')))
      }

  !eliminateStream : ∀ {τ ϕ rule value} → AllElim !Value (#Stream τ) ϕ rule → !Value (#Stream τ) value → !Thunk ϕ (eliminate rule value)
  !eliminateStream mkAllElimStream (!mkStream !v) =
      ∗ₘ ∗ (!forceStream !v) ▹! \
      { (!u , !v') → ∗ ∗ ∗ ∗ ∗ ∗ ∗ ◽ (!u ∷! !mkStream !v' ∷! !ε) }

  -- Given denotations for all components of a run-time elimination rule and denotation for
  -- a value, returns denotation for the result of applying the rule to the value
  !eliminate : ∀ {τ ϕ rule value} → AllElim !Value τ ϕ rule → !Value τ value → !Thunk ϕ (eliminate rule value)
  !eliminate {ρ ⇒ τ}       = !eliminateArrow
  !eliminate {#Sum τs}     = !eliminateSum
  !eliminate {#Product τs} = !eliminateProduct
  !eliminate {#Nat}        = !eliminateNat
  !eliminate {#Conat}      = !eliminateConat
  !eliminate {#Stream τ}   = !eliminateStream

open 18:DenotationalElimination



module 19:Denotational where
  {-
     19. Denotational semantics for the whole calculus
  -}

  -- Placeholder predicate with a single constructor
  data !Has (Γ : List Type) (τ : Type) : Has Γ τ → Set where
    !mkHas : (x : Has Γ τ) → !Has Γ τ x

  -- 'AllTerm %P Γ τ term' states that each subterm of 'term' satisfies '%P'
  data AllTerm (%P : ∀ Γ τ → TermC Γ τ → Set) : ∀ Γ τ → TermC Γ τ → Set where
    mkAllTermReturn : ∀ {Γ τ} → (x : Has Γ τ) → AllTerm %P Γ τ (return x)
    mkAllTermIntr
        : ∀ {Γ σ τ rule term}
        → AllIntr (\ρ τ → %P (ρ ∷ Γ) τ) (!Has Γ) σ rule → AllTerm %P (σ ∷ Γ) τ term → AllTerm %P Γ τ (intr rule ▸ term)
    mkAllTermElim
        : ∀ {Γ ρ σ τ rule term}
        → (x : Has Γ ρ) → AllElim (!Has Γ) ρ σ rule → AllTerm %P (σ ∷ Γ) τ term → AllTerm %P Γ τ (elim x rule ▸ term)

  -- Denotational variant of 'plugEnvIntr' function from section 11
  !plugEnvIntr
      : ∀ {Γ τ env rule}
      → !Env Γ env → AllIntr (!AbsTermC Γ) (!Has Γ) τ rule → AllIntr !Closure !Value τ (plugEnvIntr env rule)
  !plugEnvIntr {Γ} {τ} {env} {rule} !env !rule =
      mapAllIntr (\term → env & term) (\x → get env x)
        (\{_} !term {_} !v → !term (!v ∷ !env) !finish)
        (\{ (!mkHas x) → get2 !env x })
        !rule

  -- Denotational variant of 'plugEnvElim' function from section 11
  !plugEnvElim : ∀ {Γ τ ϕ env rule} → !Env Γ env → AllElim (!Has Γ) τ ϕ rule → AllElim !Value τ ϕ (plugEnvElim env rule)
  !plugEnvElim {Γ} {τ} {ϕ} {env} !env !rule = mapAllElim (\x → get env x) (\{ (!mkHas x) → get2 !env x }) !rule

  -- Denotational variant of 'reduce' function from section 11
  !reduce
      : ∀ {Γ τ ϕ env term stack}
      → !Env Γ env → AllTerm !TermC Γ τ term → !CallStack τ ϕ stack
      → !Step ϕ (reduce ((env & term) ▹ stack))
  !reduce !env (mkAllTermReturn x) !stack = !stack (get2 !env x)
  !reduce !env (mkAllTermIntr !rule !term') !stack = !continue (!reduce (!value ∷ !env) !term' !stack)
    where
      !value : !Value _ _
      !value = !construct (!plugEnvIntr !env !rule)
  !reduce !env (mkAllTermElim x !rule !term') !stack = !continue (!thunk ▹! \ !v → ∗ !reduce (!v ∷ !env) !term' !stack)
    where
      !thunk : !Thunk _ _
      !thunk = !eliminate (!plugEnvElim !env !rule) (get2 !env x)

  {-
     Now we define functions that compute denotations for different objects.
  -}

  mutual
    -- Plugs placeholder '!mkHas' into 'Any'
    runAnyC : ∀ {Γ τs} → (κ : Type → Type) → (vᵢ : Any (\τ → Has Γ (κ τ)) τs) → AllAny (\τ → !Has Γ (κ τ)) τs vᵢ
    runAnyC κ (here v)   = here (!mkHas v)
    runAnyC κ (there vᵢ) = there (runAnyC κ vᵢ)

    -- Plugs placeholder '!mkHas' into 'All'
    runAllC : ∀ {Γ τs} → (κ : Type → Type) → (vs : All (\τ → Has Γ (κ τ)) τs) → All2 (\τ → !Has Γ (κ τ)) τs vs
    runAllC κ  ε       = ε
    runAllC κ (v ∷ vs) = !mkHas v ∷ runAllC κ vs

    -- Computes denotation for each subterm of a compile-time introduction rule
    runIntrC : ∀ {Γ τ} → (rule : Intr (AbsTermC Γ) (Has Γ) τ) → AllIntr (!AbsTermC Γ) (!Has Γ) τ rule
    runIntrC (intrArrow term)          = mkAllIntrArrow (runTerm term)
    runIntrC (intrSum vᵢ)              = mkAllIntrSum (runAnyC identity vᵢ)
    runIntrC (intrProduct vs)          = mkAllIntrProduct (runAllC identity vs)
    runIntrC (intrNat v)               = mkAllIntrNat (!mkHas v)
    runIntrC (intrConat (ρ ,, v , f))  = mkAllIntrConat (ρ ,, !mkHas v , !mkHas f)
    runIntrC (intrStream (ρ ,, v , f)) = mkAllIntrStream (ρ ,, !mkHas v , !mkHas f)

    -- Plugs placeholder '!mkHas' into compile-time elimination rule
    runElimC : ∀ {Γ τ ϕ} → (rule : Elim (Has Γ) τ ϕ) → AllElim (!Has Γ) τ ϕ rule
    runElimC (elimArrow v)   = mkAllElimArrow (!mkHas v)
    runElimC (elimSum fs)    = mkAllElimSum (runAllC (\τ → τ ⇒ _) fs)
    runElimC (elimProduct i) = mkAllElimProduct i
    runElimC (elimNat f)     = mkAllElimNat (!mkHas f)
    runElimC  elimConat      = mkAllElimConat
    runElimC  elimStream     = mkAllElimStream

    -- Computes denotation for each subterm of a term
    runAllTerm : ∀ {Γ τ} → (term : TermC Γ τ) → AllTerm !TermC Γ τ term
    runAllTerm (return x)            = mkAllTermReturn x
    runAllTerm (intr rule   ▸ term') = mkAllTermIntr (runIntrC rule) (runAllTerm term')
    runAllTerm (elim x rule ▸ term') = mkAllTermElim x (runElimC rule) (runAllTerm term')

    -- Computes denotation for 'Any Value'
    runAnyR : ∀ {τs} → (vᵢ : Any Value τs) → AllAny !Value τs vᵢ
    runAnyR (here v)   = here (runValue v)
    runAnyR (there vᵢ) = there (runAnyR vᵢ)

    -- Computes denotation for 'All Value'
    runAllR : ∀ {τs} → (vs : All Value τs) → All2 !Value τs vs
    runAllR  ε       = ε
    runAllR (v ∷ vs) = runValue v ∷ runAllR vs

    -- Computes denotation for each component of a run-time introduction rule
    runIntrR : ∀ {τ} → (rule : Intr Closure Value τ) → AllIntr !Closure !Value τ rule
    runIntrR (intrArrow closure)       = mkAllIntrArrow (runClosure closure)
    runIntrR (intrSum vᵢ)              = mkAllIntrSum (runAnyR vᵢ)
    runIntrR (intrProduct vs)          = mkAllIntrProduct (runAllR vs)
    runIntrR (intrNat v)               = mkAllIntrNat (runValue v)
    runIntrR (intrConat (ρ ,, v , f))  = mkAllIntrConat (ρ ,, runValue v , runValue f)
    runIntrR (intrStream (ρ ,, v , f)) = mkAllIntrStream (ρ ,, runValue v , runValue f)

    -- Computes denotation for a term
    runTerm : ∀ {Γ τ} → (term : TermC Γ τ) → !TermC Γ τ term
    runTerm term !env !stack = !continueM (!reduce !env (runAllTerm term) !stack)

    -- Computes denotation for a value
    runValue : ∀ {τ} → (value : Value τ) → !Value τ value
    runValue (construct x) = !construct (runIntrR x)

    -- Computes denotation for a closure
    runClosure : ∀ {ρ τ} → (closure : Closure ρ τ) → !Closure ρ τ closure
    runClosure (env & term) !value = runTerm term (!value ∷ runEnv env) !finish

    -- Computes denotation for an environment
    runEnv : ∀ {τs} → (env : Env τs) → !Env τs env
    runEnv = runAllR

    -- Computes denotation for a thunk
    runThunk : ∀ {τ} → (thunk : Thunk τ) → !Thunk τ thunk
    runThunk (env & term) = runTerm term (runEnv env) !finish

    -- Computes denotation for a callstack
    runStack : ∀ {ρ τ} → (stack : CallStack ρ τ) → !CallStack ρ τ stack
    runStack  ε                !value = !finish !value
    runStack (closure ∷ stack) !value = !continue (runClosure closure !value ▹! runStack stack)

    -- Computes denotation for a machine
    runMachine : ∀ {τ} → (machine : Machine τ) → !Machine τ machine
    runMachine (thunk ▹ stack) = !continueM (runThunk thunk ▹! runStack stack)

  -- Returns computation trace for a machine, proving that it terminates (alias for 'runMachine')
  run : ∀ {τ} → (machine : Machine τ) → Trace machine
  run = runMachine

open 19:Denotational



module 20:Interpreter where
  {-
     20. Interpreter
  -}

  -- Evaluates closed term to a value
  evaluate : ∀ {τ} → Term ε τ → Value τ
  evaluate term = result (run (load (compile term)))

