import Mathlib.Data.Bool.Basic
import Mathlib.Data.Fin.Basic

namespace BitFlipCode

-- ══════════════════════════════════════════════════════════════
-- 1. ENCODING
-- Logical |b⟩_L → |bbb⟩  (three physical qubits all equal b)
-- ══════════════════════════════════════════════════════════════

/-- Encode logical bit b into 3 physical qubits -/
def encode (b : Bool) : Fin 3 → Bool := fun _ => b

theorem encode_false : encode false = fun _ => false := rfl
theorem encode_true  : encode true  = fun _ => true  := rfl

-- ══════════════════════════════════════════════════════════════
-- 2. X ERROR MODEL
-- X_i flips qubit i, leaves others unchanged
-- ══════════════════════════════════════════════════════════════

/-- Apply X (bit-flip) on qubit i -/
def xError (i : Fin 3) (s : Fin 3 → Bool) : Fin 3 → Bool :=
  fun j => if j = i then !s j else s j

theorem xError_flips_target (i : Fin 3) (s : Fin 3 → Bool) :
    xError i s i = !s i := by simp [xError]

theorem xError_preserves_others (i j : Fin 3) (h : i ≠ j) (s : Fin 3 → Bool) :
    xError i s j = s j := by simp [xError, h.symm]

theorem xError_involution (i : Fin 3) (s : Fin 3 → Bool) :
    xError i (xError i s) = s := by
  funext j; simp [xError]; split <;> simp_all

-- ══════════════════════════════════════════════════════════════
-- 3. SYNDROME MEASUREMENT
-- Stabilizers Z₀Z₁ and Z₁Z₂
-- parity q0 q1 = true  iff q0 = q1  (ZZ eigenvalue +1, no error on this pair)
-- parity q0 q1 = false iff q0 ≠ q1  (ZZ eigenvalue −1, error detected)
-- ══════════════════════════════════════════════════════════════

/-- Parity: true = same (even parity), false = different (odd parity) -/
def parity (q0 q1 : Bool) : Bool := q0 == q1

def syndrome (s : Fin 3 → Bool) : Bool × Bool :=
  (parity (s ⟨0, by omega⟩) (s ⟨1, by omega⟩),
   parity (s ⟨1, by omega⟩) (s ⟨2, by omega⟩))

-- Syndrome table (matches QuantumSyndrome.apl and quantum.rs exactly):
--   No error → (true,  true)   APL: [0,0]
--   X on q0  → (false, true)   APL: [1,0]
--   X on q1  → (false, false)  APL: [1,1]
--   X on q2  → (true,  false)  APL: [0,1]

theorem syndrome_no_error (b : Bool) :
    syndrome (encode b) = (true, true) := by
  cases b <;> simp [syndrome, encode, parity]

theorem syndrome_x0 (b : Bool) :
    syndrome (xError ⟨0, by omega⟩ (encode b)) = (false, true) := by
  cases b <;> simp [syndrome, xError, encode, parity]

theorem syndrome_x1 (b : Bool) :
    syndrome (xError ⟨1, by omega⟩ (encode b)) = (false, false) := by
  cases b <;> simp [syndrome, xError, encode, parity]

theorem syndrome_x2 (b : Bool) :
    syndrome (xError ⟨2, by omega⟩ (encode b)) = (true, false) := by
  cases b <;> simp [syndrome, xError, encode, parity]

-- ══════════════════════════════════════════════════════════════
-- 4. SYNDROME UNIQUENESS
-- All four syndrome values are distinct → unambiguous correction
-- ══════════════════════════════════════════════════════════════

theorem syndrome_unique_no_x0 (b : Bool) :
    syndrome (encode b) ≠ syndrome (xError ⟨0, by omega⟩ (encode b)) := by
  cases b <;> simp [syndrome_no_error, syndrome_x0]

theorem syndrome_unique_x0_x1 (b : Bool) :
    syndrome (xError ⟨0, by omega⟩ (encode b)) ≠
    syndrome (xError ⟨1, by omega⟩ (encode b)) := by
  cases b <;> simp [syndrome_x0, syndrome_x1]

theorem syndrome_unique_x1_x2 (b : Bool) :
    syndrome (xError ⟨1, by omega⟩ (encode b)) ≠
    syndrome (xError ⟨2, by omega⟩ (encode b)) := by
  cases b <;> simp [syndrome_x1, syndrome_x2]

-- ══════════════════════════════════════════════════════════════
-- 5. CORRECTION AND DECODE
-- ══════════════════════════════════════════════════════════════

/-- Lookup correction qubit from syndrome -/
def correctionIdx (syn : Bool × Bool) : Option (Fin 3) :=
  match syn with
  | (true,  true)  => none
  | (false, true)  => some ⟨0, by omega⟩
  | (false, false) => some ⟨1, by omega⟩
  | (true,  false) => some ⟨2, by omega⟩

/-- Apply correction: flip the guilty qubit if syndrome is non-trivial -/
def correct (syn : Bool × Bool) (s : Fin 3 → Bool) : Fin 3 → Bool :=
  match correctionIdx syn with
  | none   => s
  | some i => xError i s

/-- Majority vote decode: at least 2 of 3 must agree -/
def decode (s : Fin 3 → Bool) : Bool :=
  let q0 := s ⟨0, by omega⟩
  let q1 := s ⟨1, by omega⟩
  let q2 := s ⟨2, by omega⟩
  (q0 && q1) || (q1 && q2) || (q0 && q2)

-- ══════════════════════════════════════════════════════════════
-- 6. THE MASTER THEOREM
-- ══════════════════════════════════════════════════════════════

/-- For any logical bit b and any single-qubit X error on qubit i,
    ENCODE → INJECT → SYNDROME → CORRECT → DECODE recovers b.
    Proof: finite enumeration over {false,true} × {0,1,2} via decide. -/
theorem recover_single_x (b : Bool) (i : Fin 3) :
    decode (correct (syndrome (xError i (encode b)))
                    (xError i (encode b))) = b := by
  fin_cases i <;> cases b <;>
    simp [encode, xError, syndrome, parity, correctionIdx, correct, decode]

/-- No correction needed when no error is injected -/
theorem recover_no_error (b : Bool) :
    decode (correct (syndrome (encode b)) (encode b)) = b := by
  cases b <;> simp [encode, syndrome, parity, correctionIdx, correct, decode]

-- ══════════════════════════════════════════════════════════════
-- 7. EXHAUSTIVE VERIFICATION (all 8 cases)
-- ══════════════════════════════════════════════════════════════

theorem all_cases_false : ∀ i : Fin 3,
    decode (correct (syndrome (xError i (encode false)))
                    (xError i (encode false))) = false := by
  intro i; fin_cases i <;>
    simp [encode, xError, syndrome, parity, correctionIdx, correct, decode]

theorem all_cases_true : ∀ i : Fin 3,
    decode (correct (syndrome (xError i (encode true)))
                    (xError i (encode true))) = true := by
  intro i; fin_cases i <;>
    simp [encode, xError, syndrome, parity, correctionIdx, correct, decode]

end BitFlipCode
