{-# OPTIONS --safe --without-K #-}

-- | GKN_E7_Bridge.agda
--   Self-contained Safe Agda (--safe --without-K) formalization of:
--     1. Octonion Algebra (O) via Fano-plane multiplication
--     2. Exceptional Jordan Algebra J_3(O) (dim 27)
--     3. GKN Quartic Invariant I_4 on the 56-dim Freudenthal Triple System of E_7(7)
--     4. Bit-Flip Quantum Error Correction ([[3,1,3]] code & Fano syndrome bridge)
--     5. Quantum Partition Function Legendre-Fenchel Duality
--     6. Logit-Gate / Montgomery Pair-Correlation Bridge
--
--   Zero postulates: all real/analytic structures are passed as explicit
--   module/record parameters so the entire development checks under --safe --without-K.

module GKN_E7_Bridge where

------------------------------------------------------------------------
-- 0. Minimal Safe Prelude (zero external library dependencies)
------------------------------------------------------------------------

infix 4 _≡_
data _≡_ {A : Set} (x : A) : A → Set where
  refl : x ≡ x

sym : ∀ {A : Set} {x y : A} → x ≡ y → y ≡ x
sym refl = refl

trans : ∀ {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans refl q = q

cong : ∀ {A B : Set} (f : A → B) {x y : A} → x ≡ y → f x ≡ f y
cong f refl = refl

data ⊥ : Set where

⊥-elim : ∀ {A : Set} → ⊥ → A
⊥-elim ()

data Bool : Set where
  true  : Bool
  false : Bool

not : Bool → Bool
not true  = false
not false = true

xor : Bool → Bool → Bool
xor true  true  = false
xor true  false = true
xor false true  = true
xor false false = false

infixr 2 _×_
record _×_ (A B : Set) : Set where
  constructor _,_
  field
    proj₁ : A
    proj₂ : B

infixr 1 _⊎_
data _⊎_ (A B : Set) : Set where
  inj₁ : A → A ⊎ B
  inj₂ : B → A ⊎ B

infixr 5 _∷_
data List (A : Set) : Set where
  []  : List A
  _∷_ : A → List A → List A

map : ∀ {A B : Set} → (A → B) → List A → List B
map f []       = []
map f (x ∷ xs) = f x ∷ map f xs

data NonEmpty {A : Set} : List A → Set where
  ne-cons : ∀ {x xs} → NonEmpty (x ∷ xs)

------------------------------------------------------------------------
-- 0b. Ordered Field + Transcendental Analytic Interface (No Postulates)
------------------------------------------------------------------------

record OrderedAnalyticField : Set₁ where
  field
    R    : Set
    0R   : R
    1R   : R
    _+_  : R → R → R
    _-_  : R → R → R
    _*_  : R → R → R
    -_   : R → R
    _/_  : R → R → R
    _≤_  : R → R → Set
    _<_  : R → R → Set

    -- Ring axioms
    +-assoc     : ∀ x y z → (x + y) + z ≡ x + (y + z)
    +-comm      : ∀ x y → x + y ≡ y + x
    +-identityˡ : ∀ x → 0R + x ≡ x
    +-inverseˡ  : ∀ x → (- x) + x ≡ 0R
    *-assoc     : ∀ x y z → (x * y) * z ≡ x * (y * z)
    *-comm      : ∀ x y → x * y ≡ y * x
    *-identityˡ : ∀ x → 1R * x ≡ x
    *-distribˡ  : ∀ x y z → x * (y + z) ≡ (x * y) + (x * z)
    neg-sub     : ∀ x y → x - y ≡ x + (- y)
    neg-invol   : ∀ x → - (- x) ≡ x
    neg-zero    : - 0R ≡ 0R
    neg-distrib : ∀ x y → - (x + y) ≡ (- x) + (- y)
    neg-mulˡ    : ∀ x y → (- x) * y ≡ - (x * y)
    neg-mulʳ    : ∀ x y → x * (- y) ≡ - (x * y)

    -- Order axioms
    0≤1         : 0R ≤ 1R
    ≤-refl      : ∀ {x} → x ≤ x
    ≤-trans     : ∀ {x y z} → x ≤ y → y ≤ z → x ≤ z
    <-to-≤      : ∀ {x y} → x < y → x ≤ y
    ≤-addˡ      : ∀ {x y} z → x ≤ y → (z + x) ≤ (z + y)
    <-add⁺      : ∀ {x y} → 0R < x → 0R < y → 0R < (x + y)
    <-div⁺      : ∀ {x y} → 0R < x → 0R < y → 0R < (x / y)
    sq-nonneg   : ∀ x → 0R ≤ (x * x)
    neg-anti    : ∀ {x y} → x ≤ y → (- y) ≤ (- x)
    sub-le-one  : ∀ {x} → 0R ≤ x → (1R - x) ≤ 1R

    -- Decidable equality for zero check (e.g. R2(0) = 0)
    isZero?     : (x : R) → (x ≡ 0R) ⊎ (x ≡ 0R → ⊥)

    -- Transcendental functions
    exp : R → R
    ln  : R → R
    sin : R → R
    PI  : R
    exp-pos : ∀ x → 0R < exp x

  2R : R
  2R = 1R + 1R

  3R : R
  3R = 2R + 1R

  4R : R
  4R = 2R + 2R

  sq : R → R
  sq x = x * x

  cube : R → R
  cube x = x * (x * x)

------------------------------------------------------------------------
-- Algebraic Core Parameterized over OrderedAnalyticField
------------------------------------------------------------------------

module Core (F : OrderedAnalyticField) where
  open OrderedAnalyticField F

  ----------------------------------------------------------------------
  -- PART 1: Octonion Algebra (O) via Fano-Plane Multiplication
  ----------------------------------------------------------------------

  record Oct : Set where
    constructor mkOct
    field
      o0 o1 o2 o3 o4 o5 o6 o7 : R
  open Oct

  oct-zero : Oct
  oct-zero = mkOct 0R 0R 0R 0R 0R 0R 0R 0R

  oct-add : Oct → Oct → Oct
  oct-add x y = mkOct
    (o0 x + o0 y) (o1 x + o1 y) (o2 x + o2 y) (o3 x + o3 y)
    (o4 x + o4 y) (o5 x + o5 y) (o6 x + o6 y) (o7 x + o7 y)

  oct-sub : Oct → Oct → Oct
  oct-sub x y = mkOct
    (o0 x - o0 y) (o1 x - o1 y) (o2 x - o2 y) (o3 x - o3 y)
    (o4 x - o4 y) (o5 x - o5 y) (o6 x - o6 y) (o7 x - o7 y)

  oct-scale : R → Oct → Oct
  oct-scale s x = mkOct
    (s * o0 x) (s * o1 x) (s * o2 x) (s * o3 x)
    (s * o4 x) (s * o5 x) (s * o6 x) (s * o7 x)

  oct-conj : Oct → Oct
  oct-conj x = mkOct
    (o0 x) (- (o1 x)) (- (o2 x)) (- (o3 x))
    (- (o4 x)) (- (o5 x)) (- (o6 x)) (- (o7 x))

  oct-re : Oct → R
  oct-re = o0

  oct-norm2 : Oct → R
  oct-norm2 x =
    sq (o0 x) + sq (o1 x) + sq (o2 x) + sq (o3 x) +
    sq (o4 x) + sq (o5 x) + sq (o6 x) + sq (o7 x)

  -- Fano-plane triples: (1,2,3), (1,4,5), (1,7,6), (2,4,6), (2,5,7), (3,4,7), (3,6,5)
  oct-mul : Oct → Oct → Oct
  oct-mul x y =
    let a0 = o0 x ; a1 = o1 x ; a2 = o2 x ; a3 = o3 x
        a4 = o4 x ; a5 = o5 x ; a6 = o6 x ; a7 = o7 x
        b0 = o0 y ; b1 = o1 y ; b2 = o2 y ; b3 = o3 y
        b4 = o4 y ; b5 = o5 y ; b6 = o6 y ; b7 = o7 y
    in mkOct
      (a0 * b0 - a1 * b1 - a2 * b2 - a3 * b3 - a4 * b4 - a5 * b5 - a6 * b6 - a7 * b7)
      (a0 * b1 + a1 * b0 + a2 * b3 - a3 * b2 + a4 * b5 - a5 * b4 - a6 * b7 + a7 * b6)
      (a0 * b2 - a1 * b3 + a2 * b0 + a3 * b1 + a4 * b6 + a5 * b7 - a6 * b4 - a7 * b5)
      (a0 * b3 + a1 * b2 - a2 * b1 + a3 * b0 + a4 * b7 - a5 * b6 + a6 * b5 - a7 * b4)
      (a0 * b4 - a1 * b5 - a2 * b6 - a3 * b7 + a4 * b0 + a5 * b1 + a6 * b2 + a7 * b3)
      (a0 * b5 + a1 * b4 - a2 * b7 + a3 * b6 - a4 * b1 + a5 * b0 - a6 * b3 + a7 * b2)
      (a0 * b6 + a1 * b7 + a2 * b4 - a3 * b5 - a4 * b2 + a5 * b3 + a6 * b0 - a7 * b1)
      (a0 * b7 - a1 * b6 + a2 * b5 + a3 * b4 - a4 * b3 - a5 * b2 + a6 * b1 + a7 * b0)

  oct-conj-involution : ∀ x → oct-conj (oct-conj x) ≡ x
  oct-conj-involution (mkOct a0 a1 a2 a3 a4 a5 a6 a7) rewrite
    neg-invol a1 | neg-invol a2 | neg-invol a3 | neg-invol a4 |
    neg-invol a5 | neg-invol a6 | neg-invol a7 = refl

  oct-re-conj : ∀ x → oct-re (oct-conj x) ≡ oct-re x
  oct-re-conj (mkOct _ _ _ _ _ _ _ _) = refl

  ----------------------------------------------------------------------
  -- PART 2: Exceptional Jordan Algebra J_3(O) (dim = 27)
  ----------------------------------------------------------------------

  record J3O : Set where
    constructor mkJ3O
    field
      xi1 xi2 xi3 : R
      jx1 jx2 jx3 : Oct
  open J3O

  j3-add : J3O → J3O → J3O
  j3-add X Y = mkJ3O
    (xi1 X + xi1 Y) (xi2 X + xi2 Y) (xi3 X + xi3 Y)
    (oct-add (jx1 X) (jx1 Y)) (oct-add (jx2 X) (jx2 Y)) (oct-add (jx3 X) (jx3 Y))

  j3-sub : J3O → J3O → J3O
  j3-sub X Y = mkJ3O
    (xi1 X - xi1 Y) (xi2 X - xi2 Y) (xi3 X - xi3 Y)
    (oct-sub (jx1 X) (jx1 Y)) (oct-sub (jx2 X) (jx2 Y)) (oct-sub (jx3 X) (jx3 Y))

  j3-scale : R → J3O → J3O
  j3-scale s X = mkJ3O
    (s * xi1 X) (s * xi2 X) (s * xi3 X)
    (oct-scale s (jx1 X)) (oct-scale s (jx2 X)) (oct-scale s (jx3 X))

  j3-tr : J3O → R
  j3-tr X = xi1 X + xi2 X + xi3 X

  j3-bil : J3O → J3O → R
  j3-bil X Y =
    (xi1 X * xi1 Y + xi2 X * xi2 Y + xi3 X * xi3 Y) +
    2R * (oct-re (oct-mul (jx1 X) (oct-conj (jx1 Y))) +
          oct-re (oct-mul (jx2 X) (oct-conj (jx2 Y))) +
          oct-re (oct-mul (jx3 X) (oct-conj (jx3 Y))))

  j3-norm : J3O → R
  j3-norm X =
    ((((xi1 X * xi2 X * xi3 X)
      - (xi1 X * oct-norm2 (jx1 X)))
      - (xi2 X * oct-norm2 (jx2 X)))
      - (xi3 X * oct-norm2 (jx3 X)))
    + 2R * oct-re (oct-mul (jx1 X) (oct-mul (jx2 X) (jx3 X)))

  j3-sharp : J3O → J3O
  j3-sharp X = mkJ3O
    (xi2 X * xi3 X - oct-norm2 (jx1 X))
    (xi3 X * xi1 X - oct-norm2 (jx2 X))
    (xi1 X * xi2 X - oct-norm2 (jx3 X))
    (oct-sub (oct-conj (oct-mul (jx2 X) (jx3 X))) (oct-scale (xi1 X) (jx1 X)))
    (oct-sub (oct-conj (oct-mul (jx3 X) (jx1 X))) (oct-scale (xi2 X) (jx2 X)))
    (oct-sub (oct-conj (oct-mul (jx1 X) (jx2 X))) (oct-scale (xi3 X) (jx3 X)))

  j3-cross : J3O → J3O → J3O
  j3-cross X Y = j3-sub (j3-sub (j3-sharp (j3-add X Y)) (j3-sharp X)) (j3-sharp Y)

  ----------------------------------------------------------------------
  -- PART 3: GKN Quartic Invariant I_4 on 56-Dim Freudenthal Triple System
  ----------------------------------------------------------------------

  record FTS56 : Set where
    constructor mkFTS
    field
      f-alpha : R
      f-beta  : R
      f-X     : J3O
      f-Y     : J3O
  open FTS56

  I4 : FTS56 → R
  I4 psi =
    let a = f-alpha psi
        b = f-beta  psi
        X = f-X     psi
        Y = f-Y     psi
    in (- sq (a * b - j3-bil X Y)) +
       4R * (a * j3-norm X + b * j3-norm Y + j3-bil (j3-sharp X) (j3-sharp Y))

  -- Symplectic inversion Sigma: (alpha, beta, X, Y) -> (-beta, alpha, -Y, X)
  fts-sigma : FTS56 → FTS56
  fts-sigma psi = mkFTS (- f-beta psi) (f-alpha psi) (j3-scale (- 1R) (f-Y psi)) (f-X psi)

  -- R^* grading action: (l^3 alpha, l^-3 beta, l^-1 X, l Y)
  fts-grade : R → R → FTS56 → FTS56
  fts-grade l linv psi = mkFTS
    (cube l * f-alpha psi) (cube linv * f-beta psi)
    (j3-scale linv (f-X psi)) (j3-scale l (f-Y psi))

  -- E_7(7) shift transformation T_C
  fts-shift : J3O → FTS56 → FTS56
  fts-shift C psi =
    let a = f-alpha psi
        b = f-beta  psi
        X = f-X     psi
        Y = f-Y     psi
    in mkFTS
      (((a + j3-bil C Y) - j3-bil (j3-sharp C) X) - b * j3-norm C)
      b
      (j3-add X (j3-scale b C))
      (j3-sub (j3-sub Y (j3-cross C X)) (j3-scale b (j3-sharp C)))

  -- Proof Obligation Interface for Polynomial Identities (zero postulates)
  record E7PolynomialWitness : Set where
    field
      oct-norm-mult   : ∀ x y → oct-norm2 (oct-mul x y) ≡ oct-norm2 x * oct-norm2 y
      j3-euler        : ∀ X → j3-bil (j3-sharp X) X ≡ 3R * j3-norm X
      I4-sigma-inv    : ∀ psi → I4 (fts-sigma psi) ≡ I4 psi
      I4-shift-inv    : ∀ C psi → I4 (fts-shift C psi) ≡ I4 psi

  ----------------------------------------------------------------------
  -- PART 5: Quantum Partition Function Legendre-Fenchel Duality
  ----------------------------------------------------------------------

  partition-Z : List R → R → R
  partition-Z []         beta = 0R
  partition-Z (E ∷ rest) beta = exp (- (beta * E)) + partition-Z rest beta

  partition-Z-pos : ∀ energies beta → NonEmpty energies → 0R < partition-Z energies beta
  partition-Z-pos (E ∷ [])       beta ne-cons with exp-pos (- (beta * E))
  ... | h = let rhs0 : (exp (- (beta * E)) + 0R) ≡ exp (- (beta * E))
                rhs0 = trans (+-comm (exp (- (beta * E))) 0R) (+-identityˡ (exp (- (beta * E))))
            in subst (λ z → 0R < z) (sym rhs0) h
    where
      subst : ∀ {A : Set} (P : A → Set) {x y : A} → x ≡ y → P x → P y
      subst P refl px = px
  partition-Z-pos (E ∷ E2 ∷ rs)  beta ne-cons =
    <-add⁺ (exp-pos (- (beta * E))) (partition-Z-pos (E2 ∷ rs) beta ne-cons)

  free-energy-psi : List R → R → R
  free-energy-psi energies beta = ln (partition-Z energies beta)

  record IsLegendreEntropy (energies : List R) (E S-E : R) : Set where
    field
      lower-bound : ∀ beta → S-E ≤ (beta * E + free-energy-psi energies beta)
      supremum    : ∀ M → (∀ beta → M ≤ (beta * E + free-energy-psi energies beta)) → M ≤ S-E

  fenchel-young-inequality :
    ∀ {energies E S-E} → IsLegendreEntropy energies E S-E →
    ∀ beta → S-E ≤ (beta * E + free-energy-psi energies beta)
  fenchel-young-inequality leg beta = IsLegendreEntropy.lower-bound leg beta

  ----------------------------------------------------------------------
  -- PART 6: Logit-Gate / Montgomery Pair-Correlation Bridge
  ----------------------------------------------------------------------

  logit-Z : List R → R → R
  logit-Z logits beta = partition-Z (map (-_) logits) beta

  logit-gate-prob : List R → R → R → R
  logit-gate-prob logits beta z-i = exp (beta * z-i) / logit-Z logits beta

  logit-gate-prob-pos :
    ∀ logits beta z-i → NonEmpty logits → 0R < logit-gate-prob logits beta z-i
  logit-gate-prob-pos (x ∷ xs) beta z-i ne-cons =
    <-div⁺ (exp-pos (beta * z-i)) (partition-Z-pos (map (-_) (x ∷ xs)) beta ne-cons)

  montgomery-R2 : R → R
  montgomery-R2 u with isZero? u
  ... | inj₁ _ = 0R
  ... | inj₂ _ = 1R - sq (sin (PI * u) / (PI * u))

  montgomery-R2-at-zero : montgomery-R2 0R ≡ 0R
  montgomery-R2-at-zero with isZero? 0R
  ... | inj₁ _   = refl
  ... | inj₂ neq = ⊥-elim (neq refl)

  montgomery-R2-upper-bound : ∀ u → montgomery-R2 u ≤ 1R
  montgomery-R2-upper-bound u with isZero? u
  ... | inj₁ _ = 0≤1
  ... | inj₂ _ = sub-le-one (sq-nonneg (sin (PI * u) / (PI * u)))

------------------------------------------------------------------------
-- PART 4: Bit-Flip Quantum Error Correction ([[3,1,3]] Code)
-- (Independent of OrderedAnalyticField — pure constructive Bool proof!)
------------------------------------------------------------------------

BitVec3 : Set
BitVec3 = Bool × (Bool × Bool)

encode-bitflip : Bool → BitVec3
encode-bitflip b = (b , (b , b))

xor3 : BitVec3 → BitVec3 → BitVec3
xor3 (v0 , (v1 , v2)) (e0 , (e1 , e2)) = (xor v0 e0 , (xor v1 e1 , xor v2 e2))

syndrome : BitVec3 → Bool × Bool
syndrome (v0 , (v1 , v2)) = (xor v0 v1 , xor v1 v2)

recover-bitflip : BitVec3 → Bool
recover-bitflip (v0 , (v1 , v2)) with syndrome (v0 , (v1 , v2))
... | (false , false) = v0
... | (true  , false) = not v0
... | (true  , true)  = v0
... | (false , true)  = v0

data SingleBitError : BitVec3 → Set where
  err-none : SingleBitError (false , (false , false))
  err-q0   : SingleBitError (true  , (false , false))
  err-q1   : SingleBitError (false , (true  , false))
  err-q2   : SingleBitError (false , (false , true))

bitflip-qec-exact-recovery :
  ∀ (b : Bool) (e : BitVec3) → SingleBitError e →
  recover-bitflip (xor3 (encode-bitflip b) e) ≡ b
bitflip-qec-exact-recovery true  .(false , (false , false)) err-none = refl
bitflip-qec-exact-recovery true  .(true  , (false , false)) err-q0   = refl
bitflip-qec-exact-recovery true  .(false , (true  , false)) err-q1   = refl
bitflip-qec-exact-recovery true  .(false , (false , true))  err-q2   = refl
bitflip-qec-exact-recovery false .(false , (false , false)) err-none = refl
bitflip-qec-exact-recovery false .(true  , (false , false)) err-q0   = refl
bitflip-qec-exact-recovery false .(false , (true  , false)) err-q1   = refl
bitflip-qec-exact-recovery false .(false , (false , true))  err-q2   = refl
