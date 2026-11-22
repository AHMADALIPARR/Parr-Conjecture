# Theorem Index — Parr Conjecture (GKN–E7 Bridge)

Complete registry of every theorem, lemma, axiom, and formal definition in this repository, generated from the source text. Each entry gives the exact identifier, the source file and line, the kind of declaration, and the verbatim formal statement as written in the file. Implementation source files are the authority; this index describes them and changes nothing in them.

Source tree inspected: the implementation files at remote HEAD `d342fb9` (AHMADALIPARR/Parr-Conjecture). Counts are counts of declarations in the source text, obtained by reading every file. The word "proved" below means the file contains a proof term or tactic proof for the statement; it is not a claim that a build or verifier run was performed. No local build was run while writing this documentation. The twelve unnamed `example` declarations in `ParrDSL/Examples.lean` have no identifiers and are described in the README, Section 4.6; they do not appear in this registry. Record fields other than the four `E7PolynomialWitness` obligations are part of their record type entries and are not listed individually. Twelve identifiers are declared in two files each, the same name in two proof systems (`I4_homogeneous`, `j3_norm_homogeneous`, `j3_sharp_homogeneous`, `I4_shift_invariant`, `bitflip_qec_exact_recovery`, `partition_Z_pos`, `montgomery_R2_at_zero`, `montgomery_R2_upper_bound`, `logit_gate_prob_pos`, `I4`, `IsLegendreEntropy`, `SingleBitError`); those entries are distinguished by their source lines, so the registry has 275 entries for 263 distinct identifiers.

## Lean 4 — 71 theorems, 57 lemmas, 6 axioms

### `smul_c`

- Source: `GKN/I4_CommRing.lean:36`
- Kind: lemma
- Evidence: term-mode proof

```lean
@[simp] lemma smul_c (r : R) (a : Octonion R) (i : Fin 8) :
    (r • a).c i = r * a.c i := rfl
```

### `zero_c`

- Source: `GKN/I4_CommRing.lean:38`
- Kind: lemma
- Evidence: term-mode proof

```lean
@[simp] lemma zero_c (i : Fin 8) : (0 : Octonion R).c i = 0 := rfl
```

### `realPart_zero`

- Source: `GKN/I4_CommRing.lean:43`
- Kind: lemma
- Evidence: term-mode proof

```lean
@[simp] lemma realPart_zero : realPart (0 : Octonion R) = 0 := rfl
```

### `normSq_zero`

- Source: `GKN/I4_CommRing.lean:44`
- Kind: lemma
- Evidence: tactic proof (by)

```lean
@[simp] lemma normSq_zero : normSq (0 : Octonion R) = 0 := by
  simp [normSq]
```

### `smul_zero_octs`

- Source: `GKN/I4_CommRing.lean:47`
- Kind: lemma
- Evidence: tactic proof (by)

```lean
@[simp] lemma smul_zero_octs (r : R) : r • (0 : Octonion R) = 0 := by
  ext i; simp
```

### `normSq_smul`

- Source: `GKN/I4_CommRing.lean:50`
- Kind: lemma
- Evidence: tactic proof (by)

```lean
@[simp] lemma normSq_smul (r : R) (a : Octonion R) :
    normSq (r • a) = r ^ 2 * normSq a := by
  simp [normSq, Finset.mul_sum]; congr 1; ext i; ring
```

### `realPart_smul`

- Source: `GKN/I4_CommRing.lean:54`
- Kind: lemma
- Evidence: tactic proof (by)

```lean
@[simp] lemma realPart_smul (r : R) (a : Octonion R) :
    realPart (r • a) = r * realPart a := by simp [realPart]
```

### `smul_d`

- Source: `GKN/I4_CommRing.lean:77`
- Kind: lemma
- Evidence: term-mode proof

```lean
@[simp] lemma smul_d (r : R) (M : J3O R) (i : Fin 3) : (r • M).d i = r * M.d i := rfl
```

### `smul_o`

- Source: `GKN/I4_CommRing.lean:78`
- Kind: lemma
- Evidence: term-mode proof

```lean
@[simp] lemma smul_o (r : R) (M : J3O R) (k : Fin 3) : (r • M).o k = r • M.o k := rfl
```

### `add_d`

- Source: `GKN/I4_CommRing.lean:79`
- Kind: lemma
- Evidence: term-mode proof

```lean
@[simp] lemma add_d  (M N : J3O R) (i : Fin 3) : (M + N).d i = M.d i + N.d i := rfl
```

### `add_o`

- Source: `GKN/I4_CommRing.lean:80`
- Kind: lemma
- Evidence: term-mode proof

```lean
@[simp] lemma add_o  (M N : J3O R) (k : Fin 3) : (M + N).o k = M.o k + N.o k := rfl
```

### `neg_d`

- Source: `GKN/I4_CommRing.lean:81`
- Kind: lemma
- Evidence: term-mode proof

```lean
@[simp] lemma neg_d  (M : J3O R) (i : Fin 3) : (-M).d i = -M.d i := rfl
```

### `neg_o_c`

- Source: `GKN/I4_CommRing.lean:82`
- Kind: lemma
- Evidence: term-mode proof

```lean
@[simp] lemma neg_o_c (M : J3O R) (k : Fin 3) (i : Fin 8) :
    ((-M).o k).c i = -(M.o k).c i := rfl
```

### `zero_d`

- Source: `GKN/I4_CommRing.lean:84`
- Kind: lemma
- Evidence: term-mode proof

```lean
@[simp] lemma zero_d (i : Fin 3) : (0 : J3O R).d i = 0 := rfl
```

### `zero_o`

- Source: `GKN/I4_CommRing.lean:85`
- Kind: lemma
- Evidence: term-mode proof

```lean
@[simp] lemma zero_o (k : Fin 3) : (0 : J3O R).o k = (0 : Octonion R) := rfl
```

### `sub_d`

- Source: `GKN/I4_CommRing.lean:87`
- Kind: lemma
- Evidence: tactic proof (by)

```lean
@[simp] lemma sub_d (M N : J3O R) (i : Fin 3) : (M - N).d i = M.d i - N.d i := by
  show M.d i + -N.d i = M.d i - N.d i; ring
```

### `smul_zero_j3o`

- Source: `GKN/I4_CommRing.lean:90`
- Kind: lemma
- Evidence: tactic proof (by)

```lean
@[simp] lemma smul_zero_j3o (r : R) : r • (0 : J3O R) = 0 := by
  ext i <;> simp
```

### `cubicNorm_smul`

- Source: `GKN/I4_CommRing.lean:117`
- Kind: lemma
- Evidence: tactic proof (by)

```lean
lemma cubicNorm_smul (r : R) (M : J3O R) :
    cubicNorm (r • M) = r ^ 3 * cubicNorm M := by
  simp only [cubicNorm, smul_d, smul_o,
             Octonion.normSq_smul, Octonion.realPart_smul]
  ring
```

### `adjoint_d0`

- Source: `GKN/I4_CommRing.lean:123`
- Kind: lemma
- Evidence: term-mode proof

```lean
@[simp] lemma adjoint_d0 (M : J3O R) :
    (adjoint M).d ⟨0, by omega⟩ = M.d 1 * M.d 2 - Octonion.normSq (M.o 1) := rfl
```

### `adjoint_d1`

- Source: `GKN/I4_CommRing.lean:125`
- Kind: lemma
- Evidence: term-mode proof

```lean
@[simp] lemma adjoint_d1 (M : J3O R) :
    (adjoint M).d ⟨1, by omega⟩ = M.d 0 * M.d 2 - Octonion.normSq (M.o 2) := rfl
```

### `adjoint_d2`

- Source: `GKN/I4_CommRing.lean:127`
- Kind: lemma
- Evidence: term-mode proof

```lean
@[simp] lemma adjoint_d2 (M : J3O R) :
    (adjoint M).d ⟨2, by omega⟩ = M.d 0 * M.d 1 - Octonion.normSq (M.o 0) := rfl
```

### `adjoint_o`

- Source: `GKN/I4_CommRing.lean:129`
- Kind: lemma
- Evidence: term-mode proof

```lean
@[simp] lemma adjoint_o (M : J3O R) (k : Fin 3) :
    (adjoint M).o k = 0 := rfl
```

### `adjoint_smul`

- Source: `GKN/I4_CommRing.lean:132`
- Kind: lemma
- Evidence: tactic proof (by)

```lean
lemma adjoint_smul (r : R) (M : J3O R) :
    adjoint (r • M) = r ^ 2 • adjoint M := by
  apply J3O.ext
  · funext i
    fin_cases i <;> simp [adjoint, Octonion.normSq_smul] <;> ring
  · funext k
    simp only [adjoint_o, smul_o, adjoint_o, Octonion.smul_zero_octs]
```

### `trace_smul_left`

- Source: `GKN/I4_CommRing.lean:141`
- Kind: lemma
- Evidence: tactic proof (by)

```lean
lemma trace_smul_left (r : R) (M N : J3O R) :
    trace (r • M) N = r * trace M N := by
  simp only [trace, smul_d]
  have hosum : ∑ k : Fin 3, Octonion.realPart ((r • M).o k) * Octonion.realPart (N.o k) =
      r * ∑ k : Fin 3, Octonion.realPart (M.o k) * Octonion.realPart (N.o k) := by
    simp_rw [smul_o, Octonion.realPart_smul]
    rw [Finset.mul_sum]; congr 1; ext; ring
  rw [hosum]; ring
```

### `trace_smul_right`

- Source: `GKN/I4_CommRing.lean:151`
- Kind: lemma
- Evidence: tactic proof (by)

```lean
lemma trace_smul_right (r : R) (M N : J3O R) :
    trace M (r • N) = r * trace M N := by
  simp only [trace, smul_d]
  have hosum : ∑ k : Fin 3, Octonion.realPart (M.o k) * Octonion.realPart ((r • N).o k) =
      r * ∑ k : Fin 3, Octonion.realPart (M.o k) * Octonion.realPart (N.o k) := by
    simp_rw [smul_o, Octonion.realPart_smul]
    rw [Finset.mul_sum]; congr 1; ext; ring
  rw [hosum]; ring
```

### `trace_smul_smul`

- Source: `GKN/I4_CommRing.lean:161`
- Kind: lemma
- Evidence: tactic proof (by)

```lean
lemma trace_smul_smul (r s : R) (M N : J3O R) :
    trace (r • M) (s • N) = r * s * trace M N := by
  rw [trace_smul_left, trace_smul_right]; ring
```

### `cubicNorm_zero`

- Source: `GKN/I4_CommRing.lean:165`
- Kind: lemma
- Evidence: tactic proof (by)

```lean
@[simp] lemma cubicNorm_zero : cubicNorm (0 : J3O R) = 0 := by
  simp [cubicNorm, Octonion.normSq, Octonion.realPart]
```

### `adjoint_zero`

- Source: `GKN/I4_CommRing.lean:168`
- Kind: lemma
- Evidence: tactic proof (by)

```lean
@[simp] lemma adjoint_zero : adjoint (0 : J3O R) = 0 := by
  apply J3O.ext
  · funext i; fin_cases i <;> simp [adjoint, Octonion.normSq]
  · funext k; simp [adjoint]
```

### `trace_zero_left`

- Source: `GKN/I4_CommRing.lean:173`
- Kind: lemma
- Evidence: tactic proof (by)

```lean
@[simp] lemma trace_zero_left (N : J3O R) : trace 0 N = 0 := by simp [trace]
```

### `trace_zero_right`

- Source: `GKN/I4_CommRing.lean:174`
- Kind: lemma
- Evidence: tactic proof (by)

```lean
@[simp] lemma trace_zero_right (M : J3O R) : trace M 0 = 0 := by simp [trace]
```

### `trace_comm`

- Source: `GKN/I4_CommRing.lean:176`
- Kind: lemma
- Evidence: tactic proof (by)

```lean
lemma trace_comm (M N : J3O R) : trace M N = trace N M := by
  simp only [trace]
  have hsum : ∑ k : Fin 3, Octonion.realPart (M.o k) * Octonion.realPart (N.o k) =
              ∑ k : Fin 3, Octonion.realPart (N.o k) * Octonion.realPart (M.o k) :=
    Finset.sum_congr rfl fun k _ => mul_comm _ _
```

### `smul_α`

- Source: `GKN/I4_CommRing.lean:199`
- Kind: lemma
- Evidence: term-mode proof

```lean
@[simp] lemma smul_α (r : R) (s : FTS56 R) : (r • s).α = r * s.α := rfl
```

### `smul_β`

- Source: `GKN/I4_CommRing.lean:200`
- Kind: lemma
- Evidence: term-mode proof

```lean
@[simp] lemma smul_β (r : R) (s : FTS56 R) : (r • s).β = r * s.β := rfl
```

### `smul_X`

- Source: `GKN/I4_CommRing.lean:201`
- Kind: lemma
- Evidence: term-mode proof

```lean
@[simp] lemma smul_X (r : R) (s : FTS56 R) : (r • s).X = r • s.X := rfl
```

### `smul_Y`

- Source: `GKN/I4_CommRing.lean:202`
- Kind: lemma
- Evidence: term-mode proof

```lean
@[simp] lemma smul_Y (r : R) (s : FTS56 R) : (r • s).Y = r • s.Y := rfl
```

### `alpha_zero`

- Source: `GKN/I4_CommRing.lean:203`
- Kind: lemma
- Evidence: term-mode proof

```lean
@[simp] lemma alpha_zero : (0 : FTS56 R).α = 0 := rfl
```

### `beta_zero`

- Source: `GKN/I4_CommRing.lean:204`
- Kind: lemma
- Evidence: term-mode proof

```lean
@[simp] lemma beta_zero  : (0 : FTS56 R).β = 0 := rfl
```

### `X_zero`

- Source: `GKN/I4_CommRing.lean:205`
- Kind: lemma
- Evidence: term-mode proof

```lean
@[simp] lemma X_zero     : (0 : FTS56 R).X = 0 := rfl
```

### `Y_zero`

- Source: `GKN/I4_CommRing.lean:206`
- Kind: lemma
- Evidence: term-mode proof

```lean
@[simp] lemma Y_zero     : (0 : FTS56 R).Y = 0 := rfl
```

### `I4_homogeneous`

- Source: `GKN/I4_CommRing.lean:215`
- Kind: theorem
- Evidence: tactic proof (by)

```lean
theorem I4_homogeneous (c : R) (s : FTS56 R) :
    I4 (c • s) = c ^ 4 * I4 s := by
  simp only [I4, smul_α, smul_β, smul_X, smul_Y]
  rw [J3O.trace_smul_smul]
  rw [J3O.cubicNorm_smul c s.X, J3O.cubicNorm_smul c s.Y]
  rw [J3O.adjoint_smul c s.X, J3O.adjoint_smul c s.Y, J3O.trace_smul_smul]
  ring
```

### `I4_scale2`

- Source: `GKN/I4_CommRing.lean:224`
- Kind: theorem
- Evidence: tactic proof (by)

```lean
theorem I4_scale2 (s : FTS56 R) : I4 ((2 : R) • s) = 16 * I4 s := by
  rw [I4_homogeneous]; norm_num
```

### `I4_zero`

- Source: `GKN/I4_CommRing.lean:228`
- Kind: theorem
- Evidence: tactic proof (by)

```lean
theorem I4_zero : I4 (0 : FTS56 R) = 0 := by
  simp [I4]
```

### `I4_symplectic_swap`

- Source: `GKN/I4_CommRing.lean:233`
- Kind: theorem
- Evidence: tactic proof (by)

```lean
theorem I4_symplectic_swap (α β : R) (X Y : J3O R) :
    I4 ⟨α, β, X, Y⟩ = I4 ⟨β, α, Y, X⟩ := by
  simp only [I4]
  rw [J3O.trace_comm X Y, J3O.trace_comm (J3O.adjoint X) (J3O.adjoint Y)]
  ring
```

### `I4_neg`

- Source: `GKN/I4_CommRing.lean:243`
- Kind: theorem
- Evidence: tactic proof (by)

```lean
theorem I4_neg (s : FTS56 R) : I4 ((-1 : R) • s) = I4 s := by
  have h := I4_homogeneous (-1 : R) s
```

### `I4_gl1`

- Source: `GKN/I4_CommRing.lean:250`
- Kind: theorem
- Evidence: term-mode proof

```lean
theorem I4_gl1 (c : R) (s : FTS56 R) : I4 (c • s) = c ^ 4 * I4 s :=
  I4_homogeneous c s
```

### `cubicNorm_diag`

- Source: `GKN/I4_CommRing.lean:265`
- Kind: lemma
- Evidence: tactic proof (by)

```lean
lemma cubicNorm_diag {M : J3O R} (h : IsDiag M) :
    cubicNorm M = M.d 0 * M.d 1 * M.d 2 := by
  simp only [cubicNorm]
  have h0 := h 0
```

### `adjoint_diag`

- Source: `GKN/I4_CommRing.lean:274`
- Kind: lemma
- Evidence: term-mode proof

```lean
lemma adjoint_diag {M : J3O R} (_h : IsDiag M) : IsDiag (adjoint M) :=
  fun k => adjoint_o M k
```

### `adjoint_adjoint_d_diag`

- Source: `GKN/I4_CommRing.lean:279`
- Kind: lemma
- Evidence: tactic proof (by)

```lean
lemma adjoint_adjoint_d_diag {M : J3O R} (h : IsDiag M) (i : Fin 3) :
    (adjoint (adjoint M)).d i = cubicNorm M * M.d i := by
  have h0 := h 0
```

### `freudenthal_double_adjoint_diag`

- Source: `GKN/I4_CommRing.lean:291`
- Kind: theorem
- Evidence: tactic proof (by)

```lean
theorem freudenthal_double_adjoint_diag {M : J3O R} (h : IsDiag M) :
    adjoint (adjoint M) = cubicNorm M • M := by
  apply J3O.ext
  · funext i
    rw [adjoint_adjoint_d_diag h i]
    simp [smul_d]
  · funext k
    simp [adjoint_o, smul_o, h k]
```

### `I4_α_zero`

- Source: `GKN/I4_CommRing.lean:311`
- Kind: theorem
- Evidence: tactic proof (by)

```lean
theorem I4_α_zero (β : R) (X Y : J3O R) :
    I4 ⟨0, β, X, Y⟩ =
      (J3O.trace X Y) ^ 2
      - 4 * β * J3O.cubicNorm Y
      + 4 * J3O.trace (J3O.adjoint X) (J3O.adjoint Y) := by
  simp only [I4]; ring
```

### `I4_β_zero`

- Source: `GKN/I4_CommRing.lean:319`
- Kind: theorem
- Evidence: tactic proof (by)

```lean
theorem I4_β_zero (α : R) (X Y : J3O R) :
    I4 ⟨α, 0, X, Y⟩ =
      (J3O.trace X Y) ^ 2
      - 4 * α * J3O.cubicNorm X
      + 4 * J3O.trace (J3O.adjoint X) (J3O.adjoint Y) := by
  simp only [I4]; ring
```

### `symp_self`

- Source: `GKN/I4_CommRing.lean:336`
- Kind: theorem
- Evidence: tactic proof (by)

```lean
theorem symp_self (s : FTS56 R) : symp s s = 0 := by
  simp only [symp]; ring
```

### `symp_antisym`

- Source: `GKN/I4_CommRing.lean:340`
- Kind: theorem
- Evidence: tactic proof (by)

```lean
theorem symp_antisym (s t : FTS56 R) : symp s t = -(symp t s) := by
  simp only [symp]; ring
```

### `I4_fourth_difference`

- Source: `GKN/I4_CommRing.lean:353`
- Kind: theorem
- Evidence: tactic proof (by)

```lean
theorem I4_fourth_difference (s : FTS56 R) :
    I4 ((4 : R) • s) - 4 * I4 ((3 : R) • s) + 6 * I4 ((2 : R) • s)
      - 4 * I4 ((1 : R) • s) + I4 ((0 : R) • s) = 24 * I4 s := by
  have h4 := I4_homogeneous (4 : R) s
```

### `fanoTriples_count`

- Source: `GKN/VerifyE7Bridge.lean:65`
- Kind: theorem
- Evidence: term-mode proof

```lean
theorem fanoTriples_count : fanoTriples.length = 7 := rfl
```

### `oct_normSq_nonneg_real`

- Source: `GKN/VerifyE7Bridge.lean:68`
- Kind: theorem
- Evidence: tactic proof (by)

```lean
theorem oct_normSq_nonneg_real (a : Octonion ℝ) :
    0 ≤ Octonion.normSq a := by
  simp only [Octonion.normSq]
  exact Finset.sum_nonneg fun i _ => mul_self_nonneg _
```

### `oct_normSq_homogeneous`

- Source: `GKN/VerifyE7Bridge.lean:74`
- Kind: theorem
- Evidence: term-mode proof

```lean
theorem oct_normSq_homogeneous (r : R) (a : Octonion R) :
    Octonion.normSq (r • a) = r ^ 2 * Octonion.normSq a :=
  Octonion.normSq_smul r a
```

### `oct_realPart_linear`

- Source: `GKN/VerifyE7Bridge.lean:79`
- Kind: theorem
- Evidence: term-mode proof

```lean
theorem oct_realPart_linear (r : R) (a : Octonion R) :
    Octonion.realPart (r • a) = r * Octonion.realPart a :=
  Octonion.realPart_smul r a
```

### `j3_norm_homogeneous`

- Source: `GKN/VerifyE7Bridge.lean:88`
- Kind: theorem
- Evidence: term-mode proof

```lean
theorem j3_norm_homogeneous (s : R) (X : J3O R) :
    J3O.cubicNorm (s • X) = s ^ 3 * J3O.cubicNorm X :=
  J3O.cubicNorm_smul s X
```

### `j3_sharp_homogeneous`

- Source: `GKN/VerifyE7Bridge.lean:93`
- Kind: theorem
- Evidence: term-mode proof

```lean
theorem j3_sharp_homogeneous (s : R) (X : J3O R) :
    J3O.adjoint (s • X) = s ^ 2 • J3O.adjoint X :=
  J3O.adjoint_smul s X
```

### `j3_euler_identity_diag`

- Source: `GKN/VerifyE7Bridge.lean:98`
- Kind: theorem
- Evidence: tactic proof (by)

```lean
theorem j3_euler_identity_diag {X : J3O R} (h : J3O.IsDiag X) :
    J3O.trace (J3O.adjoint X) X = 3 * J3O.cubicNorm X := by
  have h0 := h 0; have h1 := h 1; have h2 := h 2
```

### `j3_springer_identity_diag`

- Source: `GKN/VerifyE7Bridge.lean:106`
- Kind: theorem
- Evidence: term-mode proof

```lean
theorem j3_springer_identity_diag {X : J3O R} (h : J3O.IsDiag X) :
    J3O.adjoint (J3O.adjoint X) = J3O.cubicNorm X • X :=
  J3O.freudenthal_double_adjoint_diag h
```

### `I4_sigma_invariant'`

- Source: `GKN/VerifyE7Bridge.lean:119`
- Kind: theorem
- Evidence: term-mode proof

```lean
theorem I4_sigma_invariant' (α β : R) (X Y : J3O R) :
    FTS56.I4 ⟨α, β, X, Y⟩ = FTS56.I4 ⟨β, α, Y, X⟩ :=
  FTS56.I4_symplectic_swap α β X Y
```

### `I4_neg_invariant`

- Source: `GKN/VerifyE7Bridge.lean:124`
- Kind: theorem
- Evidence: term-mode proof

```lean
theorem I4_neg_invariant (s : FTS56 R) :
    FTS56.I4 ((-1 : R) • s) = FTS56.I4 s :=
  FTS56.I4_neg s
```

### `I4_scale_invariant`

- Source: `GKN/VerifyE7Bridge.lean:129`
- Kind: theorem
- Evidence: term-mode proof

```lean
theorem I4_scale_invariant (λ : R) (s : FTS56 R) :
    FTS56.I4 (λ • s) = λ ^ 4 * FTS56.I4 s :=
  FTS56.I4_homogeneous λ s
```

### `I4_scale2_witness`

- Source: `GKN/VerifyE7Bridge.lean:134`
- Kind: theorem
- Evidence: term-mode proof

```lean
theorem I4_scale2_witness (s : FTS56 R) :
    FTS56.I4 ((2 : R) • s) = 16 * FTS56.I4 s :=
  FTS56.I4_scale2 s
```

### `shift_zero`

- Source: `GKN/VerifyE7Bridge.lean:153`
- Kind: theorem
- Evidence: tactic proof (by)

```lean
theorem shift_zero (s : FTS56 R) : shift (0 : J3O R) s = s := by
  simp only [shift, J3O.trace_zero_left, J3O.adjoint_zero,
             J3O.cubicNorm_zero, J3O.smul_zero_j3o, sub_zero, add_zero]
  cases s; rfl
```

### `I4_shift_invariant`

- Source: `GKN/VerifyE7Bridge.lean:159`
- Kind: axiom
- Evidence: axiom (assumed, not proved)

```lean
axiom I4_shift_invariant (C : J3O R) (s : FTS56 R) :
    FTS56.I4 (shift C s) = FTS56.I4 s
```

### `bitflip_qec_exact_recovery`

- Source: `GKN/VerifyE7Bridge.lean:167`
- Kind: theorem
- Evidence: term-mode proof

```lean
theorem bitflip_qec_exact_recovery (b : Bool) (i : Fin 3) :
    BitFlipCode.decode
      (BitFlipCode.correct
        (BitFlipCode.syndrome (BitFlipCode.xError i (BitFlipCode.encode b)))
        (BitFlipCode.xError i (BitFlipCode.encode b))) = b :=
  BitFlipCode.recover_single_x b i
```

### `bitflip_no_error_recovery`

- Source: `GKN/VerifyE7Bridge.lean:175`
- Kind: theorem
- Evidence: term-mode proof

```lean
theorem bitflip_no_error_recovery (b : Bool) :
    BitFlipCode.decode
      (BitFlipCode.correct
        (BitFlipCode.syndrome (BitFlipCode.encode b))
        (BitFlipCode.encode b)) = b :=
  BitFlipCode.recover_no_error b
```

### `bitflip_syndrome_unique_x0_x1`

- Source: `GKN/VerifyE7Bridge.lean:183`
- Kind: theorem
- Evidence: term-mode proof

```lean
theorem bitflip_syndrome_unique_x0_x1 (b : Bool) :
    BitFlipCode.syndrome (BitFlipCode.xError ⟨0, by omega⟩ (BitFlipCode.encode b)) ≠
    BitFlipCode.syndrome (BitFlipCode.xError ⟨1, by omega⟩ (BitFlipCode.encode b)) :=
  BitFlipCode.syndrome_unique_x0_x1 b
```

### `steaneH_cols_nonzero`

- Source: `GKN/VerifyE7Bridge.lean:199`
- Kind: theorem
- Evidence: tactic proof (by)

```lean
theorem steaneH_cols_nonzero (j : Fin 7) :
    steaneH j ≠ fun _ => false := by
  fin_cases j <;> decide
```

### `partition_Z_pos`

- Source: `GKN/VerifyE7Bridge.lean:212`
- Kind: theorem
- Evidence: tactic proof (by)

```lean
theorem partition_Z_pos (E : List ℝ) (β : ℝ) (h : E ≠ []) :
    0 < partZ E β := by
  simp only [partZ]
  cases E with
  | nil => exact (h rfl).elim
  | cons e es =>
    simp only [List.map_cons, List.sum_cons]
    exact add_pos_of_pos_of_nonneg (Real.exp_pos _) (List.sum_nonneg fun x hx => by
      obtain ⟨z, _, rfl⟩ := List.mem_map.mp hx
```

### `log_sum_exp_lower`

- Source: `GKN/VerifyE7Bridge.lean:228`
- Kind: theorem
- Evidence: tactic proof (by)

```lean
theorem log_sum_exp_lower (x : ℝ) (xs : List ℝ) :
    x ≤ Real.log ((x :: xs).map Real.exp).sum := by
  have hpos : 0 < ((x :: xs).map Real.exp).sum := by
    simp only [List.map_cons, List.sum_cons]
    exact add_pos_of_pos_of_nonneg (Real.exp_pos _) (List.sum_nonneg fun y hy => by
      obtain ⟨z, _, rfl⟩ := List.mem_map.mp hy; exact le_of_lt (Real.exp_pos _))
```

### `montgomery_R2_at_zero`

- Source: `GKN/VerifyE7Bridge.lean:250`
- Kind: theorem
- Evidence: tactic proof (by)

```lean
theorem montgomery_R2_at_zero : montgomeryR2 0 = 0 := by
  simp [montgomeryR2]
```

### `montgomery_R2_upper_bound`

- Source: `GKN/VerifyE7Bridge.lean:254`
- Kind: theorem
- Evidence: tactic proof (by)

```lean
theorem montgomery_R2_upper_bound (u : ℝ) : montgomeryR2 u ≤ 1 := by
  simp only [montgomeryR2]
  split_ifs with h
  · norm_num
  · have : 0 ≤ (Real.sin (Real.pi * u) / (Real.pi * u)) ^ 2 := sq_nonneg _
```

### `montgomery_R2_nonneg_at_zero`

- Source: `GKN/VerifyE7Bridge.lean:262`
- Kind: theorem
- Evidence: tactic proof (by)

```lean
theorem montgomery_R2_nonneg_at_zero : 0 ≤ montgomeryR2 0 := by
  simp [montgomeryR2]
```

### `logit_gate_sum_one`

- Source: `GKN/VerifyE7Bridge.lean:266`
- Kind: theorem
- Evidence: term-mode proof

```lean
theorem logit_gate_sum_one (g : RiemannMetatron.LogitGate) :
    ∑ i : Fin g.vocab_size, RiemannMetatron.logitSimplex g i = 1 :=
  RiemannMetatron.logit_simplex_sums_to_one g
```

### `logit_gate_prob_pos`

- Source: `GKN/VerifyE7Bridge.lean:271`
- Kind: theorem
- Evidence: term-mode proof

```lean
theorem logit_gate_prob_pos (g : RiemannMetatron.LogitGate) (i : Fin g.vocab_size) :
    0 < Real.exp (g.logits i) :=
  Real.exp_pos _
```

### `all_closed_checks`

- Source: `GKN/VerifyE7Bridge.lean:280`
- Kind: theorem
- Evidence: tactic proof (by)

```lean
theorem all_closed_checks
    (s : FTS56 R) (c : R) (X : J3O R) (hX : J3O.IsDiag X)
    (b : Bool) (i : Fin 3) (g : RiemannMetatron.LogitGate) :
    (J3O.cubicNorm (c • X) = c ^ 3 * J3O.cubicNorm X) ∧
    (J3O.adjoint (c • X) = c ^ 2 • J3O.adjoint X) ∧
    (J3O.adjoint (J3O.adjoint X) = J3O.cubicNorm X • X) ∧
    (FTS56.I4 (c • s) = c ^ 4 * FTS56.I4 s) ∧
    (FTS56.I4 ((-1 : R) • s) = FTS56.I4 s) ∧
    (BitFlipCode.decode
      (BitFlipCode.correct
        (BitFlipCode.syndrome (BitFlipCode.xError i (BitFlipCode.encode b)))
        (BitFlipCode.xError i (BitFlipCode.encode b))) = b) ∧
    (montgomeryR2 0 = 0) ∧
    (montgomeryR2 0 ≤ 1) ∧
    (∑ j : Fin g.vocab_size, RiemannMetatron.logitSimplex g j = 1) := by
  refine ⟨j3_norm_homogeneous c X,
          j3_sharp_homogeneous c X,
          j3_springer_identity_diag hX,
          I4_scale_invariant c s,
          I4_neg_invariant s,
          bitflip_qec_exact_recovery b i,
          montgomery_R2_at_zero,
          montgomery_R2_upper_bound 0,
          logit_gate_sum_one g⟩
```

### `encode_false`

- Source: `BitFlipCode/BitFlipCode.lean:23`
- Kind: theorem
- Evidence: term-mode proof

```lean
theorem encode_false : encode false = fun _ => false := rfl
```

### `encode_true`

- Source: `BitFlipCode/BitFlipCode.lean:24`
- Kind: theorem
- Evidence: term-mode proof

```lean
theorem encode_true  : encode true  = fun _ => true  := rfl
```

### `xError_flips_target`

- Source: `BitFlipCode/BitFlipCode.lean:35`
- Kind: theorem
- Evidence: tactic proof (by)

```lean
theorem xError_flips_target (i : Fin 3) (s : Fin 3 → Bool) :
    xError i s i = !s i := by simp [xError]
```

### `xError_preserves_others`

- Source: `BitFlipCode/BitFlipCode.lean:38`
- Kind: theorem
- Evidence: tactic proof (by)

```lean
theorem xError_preserves_others (i j : Fin 3) (h : i ≠ j) (s : Fin 3 → Bool) :
    xError i s j = s j := by simp [xError, h.symm]
```

### `xError_involution`

- Source: `BitFlipCode/BitFlipCode.lean:41`
- Kind: theorem
- Evidence: tactic proof (by)

```lean
theorem xError_involution (i : Fin 3) (s : Fin 3 → Bool) :
    xError i (xError i s) = s := by
  funext j; simp [xError]; split <;> simp_all
```

### `syndrome_no_error`

- Source: `BitFlipCode/BitFlipCode.lean:65`
- Kind: theorem
- Evidence: tactic proof (by)

```lean
theorem syndrome_no_error (b : Bool) :
    syndrome (encode b) = (true, true) := by
  cases b <;> simp [syndrome, encode, parity]
```

### `syndrome_x0`

- Source: `BitFlipCode/BitFlipCode.lean:69`
- Kind: theorem
- Evidence: tactic proof (by)

```lean
theorem syndrome_x0 (b : Bool) :
    syndrome (xError ⟨0, by omega⟩ (encode b)) = (false, true) := by
  cases b <;> simp [syndrome, xError, encode, parity]
```

### `syndrome_x1`

- Source: `BitFlipCode/BitFlipCode.lean:73`
- Kind: theorem
- Evidence: tactic proof (by)

```lean
theorem syndrome_x1 (b : Bool) :
    syndrome (xError ⟨1, by omega⟩ (encode b)) = (false, false) := by
  cases b <;> simp [syndrome, xError, encode, parity]
```

### `syndrome_x2`

- Source: `BitFlipCode/BitFlipCode.lean:77`
- Kind: theorem
- Evidence: tactic proof (by)

```lean
theorem syndrome_x2 (b : Bool) :
    syndrome (xError ⟨2, by omega⟩ (encode b)) = (true, false) := by
  cases b <;> simp [syndrome, xError, encode, parity]
```

### `syndrome_unique_no_x0`

- Source: `BitFlipCode/BitFlipCode.lean:86`
- Kind: theorem
- Evidence: tactic proof (by)

```lean
theorem syndrome_unique_no_x0 (b : Bool) :
    syndrome (encode b) ≠ syndrome (xError ⟨0, by omega⟩ (encode b)) := by
  rw [syndrome_no_error, syndrome_x0]; decide
```

### `syndrome_unique_x0_x1`

- Source: `BitFlipCode/BitFlipCode.lean:90`
- Kind: theorem
- Evidence: tactic proof (by)

```lean
theorem syndrome_unique_x0_x1 (b : Bool) :
    syndrome (xError ⟨0, by omega⟩ (encode b)) ≠
    syndrome (xError ⟨1, by omega⟩ (encode b)) := by
  rw [syndrome_x0, syndrome_x1]; decide
```

### `syndrome_unique_x1_x2`

- Source: `BitFlipCode/BitFlipCode.lean:95`
- Kind: theorem
- Evidence: tactic proof (by)

```lean
theorem syndrome_unique_x1_x2 (b : Bool) :
    syndrome (xError ⟨1, by omega⟩ (encode b)) ≠
    syndrome (xError ⟨2, by omega⟩ (encode b)) := by
  rw [syndrome_x1, syndrome_x2]; decide
```

### `recover_single_x`

- Source: `BitFlipCode/BitFlipCode.lean:132`
- Kind: theorem
- Evidence: tactic proof (by)

```lean
theorem recover_single_x (b : Bool) (i : Fin 3) :
    decode (correct (syndrome (xError i (encode b)))
                    (xError i (encode b))) = b := by
  fin_cases i <;> cases b <;>
    simp [encode, xError, syndrome, parity, correctionIdx, correct, decode]
```

### `recover_no_error`

- Source: `BitFlipCode/BitFlipCode.lean:139`
- Kind: theorem
- Evidence: tactic proof (by)

```lean
theorem recover_no_error (b : Bool) :
    decode (correct (syndrome (encode b)) (encode b)) = b := by
  cases b <;> simp [encode, syndrome, parity, correctionIdx, correct, decode]
```

### `all_cases_false`

- Source: `BitFlipCode/BitFlipCode.lean:147`
- Kind: theorem
- Evidence: tactic proof (by)

```lean
theorem all_cases_false : ∀ i : Fin 3,
    decode (correct (syndrome (xError i (encode false)))
                    (xError i (encode false))) = false := by
  intro i; fin_cases i <;>
    simp [encode, xError, syndrome, parity, correctionIdx, correct, decode]
```

### `all_cases_true`

- Source: `BitFlipCode/BitFlipCode.lean:153`
- Kind: theorem
- Evidence: tactic proof (by)

```lean
theorem all_cases_true : ∀ i : Fin 3,
    decode (correct (syndrome (xError i (encode true)))
                    (xError i (encode true))) = true := by
  intro i; fin_cases i <;>
    simp [encode, xError, syndrome, parity, correctionIdx, correct, decode]
```

### `partZ_pos`

- Source: `Quantum/QuantumPartitionBridge.lean:26`
- Kind: lemma
- Evidence: tactic proof (by)

```lean
lemma partZ_pos {n : ℕ} (hn : 0 < n) (H : Fin n → ℝ) (β : ℝ) :
    0 < partZ H β := by
  have i₀ : Fin n := ⟨0, hn⟩
```

### `log_div_exp`

- Source: `Quantum/QuantumPartitionBridge.lean:52`
- Kind: lemma
- Evidence: term-mode proof

```lean
private lemma log_div_exp (a b : ℝ) (ha : 0 < a) (hb : b ≠ 0) :
    Real.log (a / b) = Real.log a - Real.log b :=
  Real.log_div ha.ne' hb
```

### `entropy_eq`

- Source: `Quantum/QuantumPartitionBridge.lean:57`
- Kind: lemma
- Evidence: tactic proof (by)

```lean
lemma entropy_eq {n : ℕ} (hn : 0 < n) (H : Fin n → ℝ) (β : ℝ) :
    SvN (gibbs H β) = β * expH H (gibbs H β) + Real.log (partZ H β) := by
  have hZpos : 0 < partZ H β := partZ_pos hn H β
```

### `free_energy_legendre`

- Source: `Quantum/QuantumPartitionBridge.lean:108`
- Kind: theorem
- Evidence: tactic proof (by)

```lean
theorem free_energy_legendre {n : ℕ} (hn : 0 < n) (H : Fin n → ℝ) (β : ℝ) (hβ : 0 < β) :
    freeE H β = expH H (gibbs H β) - (1 / β) * SvN (gibbs H β) := by
  rw [freeE, entropy_eq hn H β]
  have hβne : (β : ℝ) ≠ 0 := ne_of_gt hβ
```

### `zeta_ne_zero_of_re_gt_one`

- Source: `RiemannMetatron/RiemannMetatron.lean:21`
- Kind: theorem
- Evidence: term-mode proof

```lean
theorem zeta_ne_zero_of_re_gt_one (s : ℂ) (hs : 1 < s.re) : riemannZeta s ≠ 0 :=
  riemannZeta_ne_zero_of_one_le_re hs.le
```

### `completedZeta_functional_eq`

- Source: `RiemannMetatron/RiemannMetatron.lean:27`
- Kind: theorem
- Evidence: term-mode proof

```lean
theorem completedZeta_functional_eq (s : ℂ) :
    completedRiemannZeta (1 - s) = completedRiemannZeta s :=
  completedRiemannZeta_one_sub s
```

### `critical_strip_is_open`

- Source: `RiemannMetatron/RiemannMetatron.lean:38`
- Kind: theorem
- Evidence: tactic proof (by)

```lean
theorem critical_strip_is_open : IsOpen criticalStrip := by
  have heq : criticalStrip = Complex.re ⁻¹' Set.Ioo 0 1 := by
    ext s; simp [criticalStrip, Set.mem_Ioo]
  rw [heq]
  exact isOpen_Ioo.preimage Complex.continuous_re
```

### `vonMangoldt_sum_pos`

- Source: `RiemannMetatron/RiemannMetatron.lean:54`
- Kind: theorem
- Evidence: tactic proof (by)

```lean
theorem vonMangoldt_sum_pos (N : ℕ) (hN : 3 ≤ N) : 0 < vonMangoldt_sum N := by
  simp only [vonMangoldt_sum]
  have h2 : (2 : ℕ) ∈ Finset.range N := Finset.mem_range.mpr (by omega)
```

### `gue_conjecture`

- Source: `RiemannMetatron/RiemannMetatron.lean:120`
- Kind: theorem
- Evidence: term-mode proof

```lean
theorem gue_conjecture (_g : LogitGate) : True := trivial
```

### `logit_simplex_sums_to_one`

- Source: `RiemannMetatron/RiemannMetatron.lean:129`
- Kind: theorem
- Evidence: term-mode proof

```lean
theorem logit_simplex_sums_to_one (g : LogitGate) :
    ∑ i : Fin g.vocab_size, logitSimplex g i = 1 :=
  g.sum_one
```

### `models_certified`

- Source: `ParrDSL/AMPL.lean:269`
- Kind: theorem
- Evidence: tactic proof (by)

```lean
theorem models_certified :
    model_I4_scale |>.isCertified = true ∧
    model_free_energy |>.isCertified = true ∧
    model_bitflip_recovery |>.isCertified = true ∧
    model_spectral_gap |>.isCertified = true ∧
    model_BPS_I4 |>.isCertified = true := by
  native_decide
```

### `interpret_I4_scale`

- Source: `ParrDSL/AMPL.lean:282`
- Kind: theorem
- Evidence: term-mode proof

```lean
theorem interpret_I4_scale {R : Type*} [CommRing R] (λ : R) (s : FTS56 R) :
    FTS56.I4 (λ • s) = λ ^ 4 * FTS56.I4 s :=
  I4_scale_invariant λ s
```

### `interpret_Z_pos`

- Source: `ParrDSL/AMPL.lean:287`
- Kind: theorem
- Evidence: term-mode proof

```lean
theorem interpret_Z_pos (E : List ℝ) (β : ℝ) (h : E ≠ []) :
    0 < partZ E β :=
  partition_Z_pos E β h
```

### `interpret_bitflip`

- Source: `ParrDSL/AMPL.lean:292`
- Kind: theorem
- Evidence: term-mode proof

```lean
theorem interpret_bitflip (b : Bool) (i : Fin 3) :
    BitFlipCode.decode
      (BitFlipCode.correct
        (BitFlipCode.syndrome (BitFlipCode.xError i (BitFlipCode.encode b)))
        (BitFlipCode.xError i (BitFlipCode.encode b))) = b :=
  bitflip_qec_exact_recovery b i
```

### `interpret_gates`

- Source: `ParrDSL/AMPL.lean:300`
- Kind: theorem
- Evidence: term-mode proof

```lean
theorem interpret_gates (g : RiemannMetatron.LogitGate) :
    ∑ i : Fin g.vocab_size, RiemannMetatron.logitSimplex g i = 1 :=
  logit_gate_sum_one g
```

### `interpret_R2_zero`

- Source: `ParrDSL/AMPL.lean:305`
- Kind: theorem
- Evidence: term-mode proof

```lean
theorem interpret_R2_zero : montgomeryR2 0 = 0 :=
  montgomery_R2_at_zero
```

### `ampl_grounded_in_master`

- Source: `ParrDSL/AMPL.lean:363`
- Kind: theorem
- Evidence: tactic proof (by)

```lean
theorem ampl_grounded_in_master
    {R : Type*} [CommRing R]
    (s : FTS56 R) (c : R) (X : J3O R) (hX : J3O.IsDiag X)
    (b : Bool) (i : Fin 3) (g : RiemannMetatron.LogitGate) :
    (model_I4_scale.isCertified = true) ∧
    (model_bitflip_recovery.isCertified = true) ∧
    (model_free_energy.isCertified = true) ∧
    (model_spectral_gap.isCertified = true) ∧
    (model_BPS_I4.isCertified = true) ∧
    -- semantic core
    (FTS56.I4 (c • s) = c ^ 4 * FTS56.I4 s) ∧
    (BitFlipCode.decode
      (BitFlipCode.correct
        (BitFlipCode.syndrome (BitFlipCode.xError i (BitFlipCode.encode b)))
        (BitFlipCode.xError i (BitFlipCode.encode b))) = b) ∧
    (montgomeryR2 0 = 0) ∧
    (∑ j : Fin g.vocab_size, RiemannMetatron.logitSimplex g j = 1) := by
  refine ⟨?cert1, ?cert2, ?cert3, ?cert4, ?cert5, ?h1, ?h2, ?h3, ?h4⟩
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · exact I4_scale_invariant c s
  · exact bitflip_qec_exact_recovery b i
  · exact montgomery_R2_at_zero
  · exact logit_gate_sum_one g
```

### `parr_j3o_simps_smul_d`

- Source: `ParrDSL/Automation.lean:37`
- Kind: lemma
- Evidence: term-mode proof

```lean
lemma parr_j3o_simps_smul_d {R : Type*} [CommRing R] (r : R) (M : J3O R) (i : Fin 3) :
    (r • M).d i = r * M.d i := J3O.smul_d r M i
```

### `parr_j3o_simps_smul_o`

- Source: `ParrDSL/Automation.lean:40`
- Kind: lemma
- Evidence: term-mode proof

```lean
lemma parr_j3o_simps_smul_o {R : Type*} [CommRing R] (r : R) (M : J3O R) (k : Fin 3) :
    (r • M).o k = r • M.o k := J3O.smul_o r M k
```

### `parr_j3o_simps_normSq_smul`

- Source: `ParrDSL/Automation.lean:43`
- Kind: lemma
- Evidence: term-mode proof

```lean
lemma parr_j3o_simps_normSq_smul {R : Type*} [CommRing R] (r : R) (a : Octonion R) :
    Octonion.normSq (r • a) = r ^ 2 * Octonion.normSq a := Octonion.normSq_smul r a
```

### `parr_j3o_simps_realPart_smul`

- Source: `ParrDSL/Automation.lean:46`
- Kind: lemma
- Evidence: term-mode proof

```lean
lemma parr_j3o_simps_realPart_smul {R : Type*} [CommRing R] (r : R) (a : Octonion R) :
    Octonion.realPart (r • a) = r * Octonion.realPart a := Octonion.realPart_smul r a
```

### `parr_cubicNorm_homog`

- Source: `ParrDSL/Automation.lean:50`
- Kind: lemma
- Evidence: term-mode proof

```lean
lemma parr_cubicNorm_homog {R : Type*} [CommRing R] (r : R) (M : J3O R) :
    J3O.cubicNorm (r • M) = r ^ 3 * J3O.cubicNorm M := J3O.cubicNorm_smul r M
```

### `parr_adjoint_homog`

- Source: `ParrDSL/Automation.lean:54`
- Kind: lemma
- Evidence: term-mode proof

```lean
lemma parr_adjoint_homog {R : Type*} [CommRing R] (r : R) (M : J3O R) :
    J3O.adjoint (r • M) = r ^ 2 • J3O.adjoint M := J3O.adjoint_smul r M
```

### `parr_I4_homog`

- Source: `ParrDSL/Automation.lean:58`
- Kind: lemma
- Evidence: term-mode proof

```lean
lemma parr_I4_homog {R : Type*} [CommRing R] (c : R) (s : FTS56 R) :
    FTS56.I4 (c • s) = c ^ 4 * FTS56.I4 s := FTS56.I4_homogeneous c s
```

### `parr_symp_alt`

- Source: `ParrDSL/Automation.lean:62`
- Kind: lemma
- Evidence: term-mode proof

```lean
lemma parr_symp_alt {R : Type*} [CommRing R] (s : FTS56 R) :
    FTS56.symp s s = 0 := FTS56.symp_self s
```

### `parr_symp_antisym`

- Source: `ParrDSL/Automation.lean:66`
- Kind: lemma
- Evidence: term-mode proof

```lean
lemma parr_symp_antisym {R : Type*} [CommRing R] (s t : FTS56 R) :
    FTS56.symp s t = -(FTS56.symp t s) := FTS56.symp_antisym s t
```

### `parr_bitflip_recover`

- Source: `ParrDSL/Automation.lean:70`
- Kind: lemma
- Evidence: term-mode proof

```lean
lemma parr_bitflip_recover (b : Bool) (i : Fin 3) :
    BitFlipCode.decode
      (BitFlipCode.correct
        (BitFlipCode.syndrome (BitFlipCode.xError i (BitFlipCode.encode b)))
        (BitFlipCode.xError i (BitFlipCode.encode b))) = b :=
  BitFlipCode.recover_single_x b i
```

### `parr_gates_norm`

- Source: `ParrDSL/Automation.lean:78`
- Kind: lemma
- Evidence: term-mode proof

```lean
lemma parr_gates_norm (g : RiemannMetatron.LogitGate) :
    ∑ i : Fin g.vocab_size, RiemannMetatron.logitSimplex g i = 1 :=
  RiemannMetatron.logit_simplex_sums_to_one g
```

### `parr_critical_strip_open`

- Source: `ParrDSL/Automation.lean:83`
- Kind: lemma
- Evidence: term-mode proof

```lean
lemma parr_critical_strip_open : IsOpen RiemannMetatron.criticalStrip :=
  RiemannMetatron.critical_strip_is_open
```

### `parr_I4_surface`

- Source: `ParrDSL/Examples.lean:95`
- Kind: theorem
- Evidence: tactic proof (by)

```lean
theorem parr_I4_surface (c : R) (s : FTS56 R) :
    I₄(c ·ₚ s) = c ^ 4 * I₄(s) := by
  parr_homog
```

### `parr_fourth_diff`

- Source: `ParrDSL/Examples.lean:100`
- Kind: theorem
- Evidence: tactic proof (by)

```lean
theorem parr_fourth_diff (s : FTS56 R) :
    I₄((4 : R) ·ₚ s) - 4 * I₄((3 : R) ·ₚ s) + 6 * I₄((2 : R) ·ₚ s)
      - 4 * I₄((1 : R) ·ₚ s) + I₄((0 : R) ·ₚ s) = 24 * I₄(s) := by
  simpa using FTS56.I4_fourth_difference s
```

### `I4_56_homogeneous`

- Source: `S_AUTOCODE/MTheory.lean:214`
- Kind: axiom
- Evidence: axiom (assumed, not proved)

```lean
axiom I4_56_homogeneous (s : State56) (r : Float) :
    I4_56 (s56Scale r s) = HMul.hMul (HMul.hMul (HMul.hMul r r) (HMul.hMul r r)) (I4_56 s)
```

### `Pipeline_Relocate_Axiom`

- Source: `S_AUTOCODE/MTheory.lean:347`
- Kind: axiom
- Evidence: axiom (assumed, not proved)

```lean
axiom Pipeline_Relocate_Axiom (pipe : CompilerPipeline) :
  pipe.relocateInitialState = relocate pipe.drumLayout pipe.siliconState
```

### `I4_homogeneous`

- Source: `S_AUTOCODE/MTheory.lean:354`
- Kind: axiom
- Evidence: axiom (assumed, not proved)

```lean
axiom I4_homogeneous (Psi : State108) (r : Float) :
    I4 (stateScale r Psi) =
      HMul.hMul (HMul.hMul (HMul.hMul r r) (HMul.hMul r r))
        (HMul.hMul (HMul.hMul r r) (I4 Psi))
```

### `I4_E7_Invariant`

- Source: `S_AUTOCODE/MTheory.lean:361`
- Kind: axiom
- Evidence: axiom (assumed, not proved)

```lean
axiom I4_E7_Invariant (R : RelocationPerm) (Psi : State108) :
    I4 (relocate R Psi) = I4 Psi
```

### `I4_Unique`

- Source: `S_AUTOCODE/MTheory.lean:365`
- Kind: axiom
- Evidence: axiom (assumed, not proved)

```lean
axiom I4_Unique : forall (F : State108 -> Float),
  (forall (R : RelocationPerm) (Psi : State108), F (relocate R Psi) = F Psi) ->
  exists c : Float, forall (Psi : State108), F Psi = HMul.hMul c (I4 Psi)
```

### `drumOptimizerEOM`

- Source: `S_AUTOCODE/MTheory.lean:370`
- Kind: theorem
- Evidence: tactic proof (by)

```lean
theorem drumOptimizerEOM
    (C : CausalSet) (Psi : Nat -> State108) (R_opt : RelocationPerm)
    (_h_opt : forall (R : RelocationPerm),
      discreteAction C (fun x => relocate R_opt (Psi x)) <=
      discreteAction C (fun x => relocate R (Psi x))) :
    0.0 = 0.0 := by
  rfl
```

### `Sovereign_Compiler_Correct`

- Source: `S_AUTOCODE/MTheory.lean:379`
- Kind: theorem
- Evidence: tactic proof (by)

```lean
theorem Sovereign_Compiler_Correct (pipe : CompilerPipeline) :
    I4 pipe.siliconState = I4 pipe.relocateInitialState := by
  have h1 := I4_E7_Invariant pipe.drumLayout pipe.siliconState
```

## Rocq — 11 theorems, 9 lemmas, 1 axiom

### `oct_norm2_nonneg`

- Source: `Rocq/GKN_E7_Bridge.v:73`
- Kind: lemma
- Evidence: tactic proof, closed with Qed

```coq
Lemma oct_norm2_nonneg : forall x : Oct, 0 <= oct_norm2 x.
Proof.
  intros [a0 a1 a2 a3 a4 a5 a6 a7]. unfold oct_norm2; simpl.
  repeat apply Rplus_le_le_0_compat; apply pow2_ge_0.
Qed.
```

### `oct_conj_involution`

- Source: `Rocq/GKN_E7_Bridge.v:79`
- Kind: lemma
- Evidence: tactic proof, closed with Qed

```coq
Lemma oct_conj_involution : forall x : Oct, oct_conj (oct_conj x) = x.
Proof.
  intros [a0 a1 a2 a3 a4 a5 a6 a7]. unfold oct_conj; simpl.
  f_equal; ring.
Qed.
```

### `oct_re_conj`

- Source: `Rocq/GKN_E7_Bridge.v:85`
- Kind: lemma
- Evidence: tactic proof, closed with Qed

```coq
Lemma oct_re_conj : forall x : Oct, oct_re (oct_conj x) = oct_re x.
Proof.
  intros [a0 a1 a2 a3 a4 a5 a6 a7]; reflexivity.
Qed.
```

### `oct_norm_multiplicative`

- Source: `Rocq/GKN_E7_Bridge.v:90`
- Kind: theorem
- Evidence: tactic proof, closed with Qed

```coq
Theorem oct_norm_multiplicative : forall x y : Oct,
  oct_norm2 (oct_mul x y) = oct_norm2 x * oct_norm2 y.
Proof.
  intros [a0 a1 a2 a3 a4 a5 a6 a7] [b0 b1 b2 b3 b4 b5 b6 b7].
  unfold oct_norm2, oct_mul; simpl.
  ring.
Qed.
```

### `oct_left_alternative`

- Source: `Rocq/GKN_E7_Bridge.v:98`
- Kind: theorem
- Evidence: tactic proof, closed with Qed

```coq
Theorem oct_left_alternative : forall x y : Oct,
  oct_mul (oct_mul x x) y = oct_mul x (oct_mul x y).
Proof.
  intros [a0 a1 a2 a3 a4 a5 a6 a7] [b0 b1 b2 b3 b4 b5 b6 b7].
  unfold oct_mul; simpl.
  f_equal; ring.
Qed.
```

### `oct_right_alternative`

- Source: `Rocq/GKN_E7_Bridge.v:106`
- Kind: theorem
- Evidence: tactic proof, closed with Qed

```coq
Theorem oct_right_alternative : forall x y : Oct,
  oct_mul (oct_mul y x) x = oct_mul y (oct_mul x x).
Proof.
  intros [a0 a1 a2 a3 a4 a5 a6 a7] [b0 b1 b2 b3 b4 b5 b6 b7].
  unfold oct_mul; simpl.
  f_equal; ring.
Qed.
```

### `j3_norm_homogeneous`

- Source: `Rocq/GKN_E7_Bridge.v:162`
- Kind: theorem
- Evidence: tactic proof, closed with Qed

```coq
Theorem j3_norm_homogeneous : forall (s : R) (X : J3O),
  j3_norm (j3_scale s X) = s^3 * j3_norm X.
Proof.
  intros s [d1 d2 d3 [a0 a1 a2 a3 a4 a5 a6 a7]
                   [b0 b1 b2 b3 b4 b5 b6 b7]
                   [c0 c1 c2 c3 c4 c5 c6 c7]].
  unfold j3_norm, j3_scale, oct_scale, oct_norm2, oct_re, oct_mul; simpl.
  ring.
Qed.
```

### `j3_sharp_homogeneous`

- Source: `Rocq/GKN_E7_Bridge.v:172`
- Kind: theorem
- Evidence: tactic proof, closed with Qed

```coq
Theorem j3_sharp_homogeneous : forall (s : R) (X : J3O),
  j3_sharp (j3_scale s X) = j3_scale (s^2) (j3_sharp X).
Proof.
  intros s [d1 d2 d3 [a0 a1 a2 a3 a4 a5 a6 a7]
                   [b0 b1 b2 b3 b4 b5 b6 b7]
                   [c0 c1 c2 c3 c4 c5 c6 c7]].
  unfold j3_sharp, j3_scale, oct_scale, oct_sub, oct_conj, oct_norm2, oct_mul; simpl.
  f_equal; try ring; f_equal; ring.
Qed.
```

### `j3_euler_identity`

- Source: `Rocq/GKN_E7_Bridge.v:182`
- Kind: theorem
- Evidence: tactic proof, closed with Qed

```coq
Theorem j3_euler_identity : forall X : J3O,
  j3_bil (j3_sharp X) X = 3 * j3_norm X.
Proof.
  intros [d1 d2 d3 [a0 a1 a2 a3 a4 a5 a6 a7]
                 [b0 b1 b2 b3 b4 b5 b6 b7]
                 [c0 c1 c2 c3 c4 c5 c6 c7]].
  unfold j3_bil, j3_sharp, j3_norm, oct_sub, oct_conj, oct_scale, oct_norm2, oct_re, oct_mul; simpl.
  ring.
Qed.
```

### `j3_bil_sym`

- Source: `Rocq/GKN_E7_Bridge.v:232`
- Kind: lemma
- Evidence: tactic proof, closed with Qed

```coq
Lemma j3_bil_sym : forall X Y : J3O, j3_bil X Y = j3_bil Y X.
Proof.
  intros [d1 d2 d3 [a0 a1 a2 a3 a4 a5 a6 a7] [b0 b1 b2 b3 b4 b5 b6 b7] [c0 c1 c2 c3 c4 c5 c6 c7]]
         [e1 e2 e3 [u0 u1 u2 u3 u4 u5 u6 u7] [v0 v1 v2 v3 v4 v5 v6 v7] [w0 w1 w2 w3 w4 w5 w6 w7]].
  unfold j3_bil, oct_re, oct_mul, oct_conj; simpl. ring.
Qed.
```

### `j3_norm_neg`

- Source: `Rocq/GKN_E7_Bridge.v:239`
- Kind: lemma
- Evidence: tactic proof, closed with Qed

```coq
Lemma j3_norm_neg : forall X : J3O, j3_norm (j3_scale (-1) X) = - j3_norm X.
Proof.
  intro X. rewrite j3_norm_homogeneous. ring.
Qed.
```

### `j3_sharp_neg`

- Source: `Rocq/GKN_E7_Bridge.v:244`
- Kind: lemma
- Evidence: tactic proof, closed with Qed

```coq
Lemma j3_sharp_neg : forall X : J3O, j3_sharp (j3_scale (-1) X) = j3_sharp X.
Proof.
  intro X. rewrite j3_sharp_homogeneous.
  destruct X as [d1 d2 d3 [a0 a1 a2 a3 a4 a5 a6 a7] [b0 b1 b2 b3 b4 b5 b6 b7] [c0 c1 c2 c3 c4 c5 c6 c7]].
  unfold j3_sharp, j3_scale, oct_scale; simpl. f_equal; try ring; f_equal; ring.
Qed.
```

### `j3_bil_neg_left`

- Source: `Rocq/GKN_E7_Bridge.v:251`
- Kind: lemma
- Evidence: tactic proof, closed with Qed

```coq
Lemma j3_bil_neg_left : forall X Y : J3O, j3_bil (j3_scale (-1) X) Y = - j3_bil X Y.
Proof.
  intros [d1 d2 d3 [a0 a1 a2 a3 a4 a5 a6 a7] [b0 b1 b2 b3 b4 b5 b6 b7] [c0 c1 c2 c3 c4 c5 c6 c7]]
         [e1 e2 e3 [u0 u1 u2 u3 u4 u5 u6 u7] [v0 v1 v2 v3 v4 v5 v6 v7] [w0 w1 w2 w3 w4 w5 w6 w7]].
  unfold j3_bil, j3_scale, oct_scale, oct_re, oct_mul, oct_conj; simpl. ring.
Qed.
```

### `I4_sigma_invariant`

- Source: `Rocq/GKN_E7_Bridge.v:258`
- Kind: theorem
- Evidence: tactic proof, closed with Qed

```coq
Theorem I4_sigma_invariant : forall psi : FTS56,
  I4 (fts_sigma psi) = I4 psi.
Proof.
  intros [a b X Y]. unfold I4, fts_sigma; simpl.
  rewrite j3_bil_neg_left, j3_norm_neg, j3_sharp_neg.
  rewrite (j3_bil_sym (j3_sharp Y) (j3_sharp X)).
  ring.
Qed.
```

### `I4_shift_invariant`

- Source: `Rocq/GKN_E7_Bridge.v:269`
- Kind: axiom
- Evidence: axiom (assumed, not proved)

```coq
Axiom I4_shift_invariant : forall (C : J3O) (psi : FTS56),
  I4 (fts_shift C psi) = I4 psi.
```

### `bitflip_qec_exact_recovery`

- Source: `Rocq/GKN_E7_Bridge.v:305`
- Kind: theorem
- Evidence: tactic proof, closed with Qed

```coq
Theorem bitflip_qec_exact_recovery : forall (b : bool) (e : BitVec3),
  single_bit_error e ->
  recover_bitflip (xor3 (encode_bitflip b) e) = b.
Proof.
  intros b e He.
  destruct b; destruct He as [-> | [-> | [-> | ->]]]; reflexivity.
Qed.
```

### `partition_Z_pos`

- Source: `Rocq/GKN_E7_Bridge.v:324`
- Kind: lemma
- Evidence: tactic proof, closed with Qed

```coq
Lemma partition_Z_pos : forall (energies : list R) (beta : R),
  energies <> [] -> 0 < partition_Z energies beta.
Proof.
  intros energies beta Hne.
  induction energies as [| E rest IH].
  - contradiction.
  - simpl. destruct rest as [| E2 rest2].
    + simpl. rewrite Rplus_0_r. apply exp_pos.
    + apply Rplus_lt_0_compat.
      * apply exp_pos.
      * apply IH. discriminate.
Qed.
```

### `fenchel_young_inequality`

- Source: `Rocq/GKN_E7_Bridge.v:345`
- Kind: theorem
- Evidence: tactic proof, closed with Qed

```coq
Theorem fenchel_young_inequality : forall (energies : list R) (E S_E beta : R),
  is_legendre_entropy energies E S_E ->
  S_E <= beta * E + free_energy_psi energies beta.
Proof.
  intros energies E S_E beta [Hlb _]. apply Hlb.
Qed.
```

### `logit_gate_prob_pos`

- Source: `Rocq/GKN_E7_Bridge.v:362`
- Kind: lemma
- Evidence: tactic proof, closed with Qed

```coq
Lemma logit_gate_prob_pos : forall (logits : list R) (beta z_i : R),
  logits <> [] -> 0 < logit_gate_prob logits beta z_i.
Proof.
  intros logits beta z_i Hne.
  unfold logit_gate_prob, logit_Z.
  apply Rdiv_lt_0_compat.
  - apply exp_pos.
  - apply partition_Z_pos. destruct logits; [contradiction | discriminate].
Qed.
```

### `montgomery_R2_at_zero`

- Source: `Rocq/GKN_E7_Bridge.v:377`
- Kind: theorem
- Evidence: tactic proof, closed with Qed

```coq
Theorem montgomery_R2_at_zero : montgomery_R2 0 = 0.
Proof.
  unfold montgomery_R2.
  destruct (Req_EM_T 0 0) as [H|H]; [reflexivity | lra].
Qed.
```

### `montgomery_R2_upper_bound`

- Source: `Rocq/GKN_E7_Bridge.v:383`
- Kind: theorem
- Evidence: tactic proof, closed with Qed

```coq
Theorem montgomery_R2_upper_bound : forall u : R, montgomery_R2 u <= 1.
Proof.
  intro u. unfold montgomery_R2.
  destruct (Req_EM_T u 0).
  - lra.
  - assert (0 <= (sin (PI * u) / (PI * u))^2) by apply pow2_ge_0.
    lra.
Qed.
```

## Agda — 80 entries: top-level declarations, data and record types, and the four E7PolynomialWitness obligations

### `_≡_`

- Source: `Agda/GKN_E7_Bridge.agda:28`
- Kind: data type
- Evidence: type declaration

```agda
data _≡_ {A : Set} (x : A) : A → Set where
```

### `refl`

- Source: `Agda/GKN_E7_Bridge.agda:29`
- Kind: constructor
- Evidence: constructor of a data type

```agda
  refl : x ≡ x
```

### `sym`

- Source: `Agda/GKN_E7_Bridge.agda:31`
- Kind: proved proposition
- Evidence: proof term (Agda term of the stated type)

```agda
sym : ∀ {A : Set} {x y : A} → x ≡ y → y ≡ x
sym refl = refl
```

### `trans`

- Source: `Agda/GKN_E7_Bridge.agda:34`
- Kind: proved proposition
- Evidence: proof term (Agda term of the stated type)

```agda
trans : ∀ {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans refl q = q
```

### `cong`

- Source: `Agda/GKN_E7_Bridge.agda:37`
- Kind: proved proposition
- Evidence: proof term (Agda term of the stated type)

```agda
cong : ∀ {A B : Set} (f : A → B) {x y : A} → x ≡ y → f x ≡ f y
cong f refl = refl
```

### `⊥`

- Source: `Agda/GKN_E7_Bridge.agda:40`
- Kind: data type
- Evidence: type declaration

```agda
data ⊥ : Set where
```

### `⊥-elim`

- Source: `Agda/GKN_E7_Bridge.agda:42`
- Kind: definition
- Evidence: definition

```agda
⊥-elim : ∀ {A : Set} → ⊥ → A
⊥-elim ()
```

### `Bool`

- Source: `Agda/GKN_E7_Bridge.agda:45`
- Kind: data type
- Evidence: type declaration

```agda
data Bool : Set where
```

### `true`

- Source: `Agda/GKN_E7_Bridge.agda:46`
- Kind: constructor
- Evidence: constructor of a data type

```agda
  true  : Bool
```

### `false`

- Source: `Agda/GKN_E7_Bridge.agda:47`
- Kind: constructor
- Evidence: constructor of a data type

```agda
  false : Bool
```

### `not`

- Source: `Agda/GKN_E7_Bridge.agda:49`
- Kind: definition
- Evidence: definition

```agda
not : Bool → Bool
not true  = false
not false = true
```

### `xor`

- Source: `Agda/GKN_E7_Bridge.agda:53`
- Kind: definition
- Evidence: definition

```agda
xor : Bool → Bool → Bool
xor true  true  = false
xor true  false = true
xor false true  = true
xor false false = false
```

### `_×_`

- Source: `Agda/GKN_E7_Bridge.agda:60`
- Kind: record type
- Evidence: type declaration

```agda
record _×_ (A B : Set) : Set where
```

### `_⊎_`

- Source: `Agda/GKN_E7_Bridge.agda:67`
- Kind: data type
- Evidence: type declaration

```agda
data _⊎_ (A B : Set) : Set where
```

### `inj₁`

- Source: `Agda/GKN_E7_Bridge.agda:68`
- Kind: constructor
- Evidence: constructor of a data type

```agda
  inj₁ : A → A ⊎ B
```

### `inj₂`

- Source: `Agda/GKN_E7_Bridge.agda:69`
- Kind: constructor
- Evidence: constructor of a data type

```agda
  inj₂ : B → A ⊎ B
```

### `List`

- Source: `Agda/GKN_E7_Bridge.agda:72`
- Kind: data type
- Evidence: type declaration

```agda
data List (A : Set) : Set where
```

### `[]`

- Source: `Agda/GKN_E7_Bridge.agda:73`
- Kind: constructor
- Evidence: constructor of a data type

```agda
  []  : List A
```

### `_∷_`

- Source: `Agda/GKN_E7_Bridge.agda:74`
- Kind: constructor
- Evidence: constructor of a data type

```agda
  _∷_ : A → List A → List A
```

### `map`

- Source: `Agda/GKN_E7_Bridge.agda:76`
- Kind: definition
- Evidence: definition

```agda
map : ∀ {A B : Set} → (A → B) → List A → List B
map f []       = []
map f (x ∷ xs) = f x ∷ map f xs
```

### `NonEmpty`

- Source: `Agda/GKN_E7_Bridge.agda:80`
- Kind: data type
- Evidence: type declaration

```agda
data NonEmpty {A : Set} : List A → Set where
```

### `ne-cons`

- Source: `Agda/GKN_E7_Bridge.agda:81`
- Kind: constructor
- Evidence: constructor of a data type

```agda
  ne-cons : ∀ {x xs} → NonEmpty (x ∷ xs)
```

### `OrderedAnalyticField`

- Source: `Agda/GKN_E7_Bridge.agda:87`
- Kind: record type
- Evidence: type declaration

```agda
record OrderedAnalyticField : Set₁ where
```

### `2R`

- Source: `Agda/GKN_E7_Bridge.agda:138`
- Kind: definition
- Evidence: definition

```agda
  2R : R
  2R = 1R + 1R
```

### `3R`

- Source: `Agda/GKN_E7_Bridge.agda:141`
- Kind: definition
- Evidence: definition

```agda
  3R : R
  3R = 2R + 1R
```

### `4R`

- Source: `Agda/GKN_E7_Bridge.agda:144`
- Kind: definition
- Evidence: definition

```agda
  4R : R
  4R = 2R + 2R
```

### `sq`

- Source: `Agda/GKN_E7_Bridge.agda:147`
- Kind: definition
- Evidence: definition

```agda
  sq : R → R
  sq x = x * x
```

### `cube`

- Source: `Agda/GKN_E7_Bridge.agda:150`
- Kind: definition
- Evidence: definition

```agda
  cube : R → R
  cube x = x * (x * x)
```

### `Oct`

- Source: `Agda/GKN_E7_Bridge.agda:164`
- Kind: record type
- Evidence: type declaration

```agda
  record Oct : Set where
```

### `oct-zero`

- Source: `Agda/GKN_E7_Bridge.agda:170`
- Kind: definition
- Evidence: definition

```agda
  oct-zero : Oct
  oct-zero = mkOct 0R 0R 0R 0R 0R 0R 0R 0R
```

### `oct-add`

- Source: `Agda/GKN_E7_Bridge.agda:173`
- Kind: definition
- Evidence: definition

```agda
  oct-add : Oct → Oct → Oct
  oct-add x y = mkOct
    (o0 x + o0 y) (o1 x + o1 y) (o2 x + o2 y) (o3 x + o3 y)
    (o4 x + o4 y) (o5 x + o5 y) (o6 x + o6 y) (o7 x + o7 y)
```

### `oct-sub`

- Source: `Agda/GKN_E7_Bridge.agda:178`
- Kind: definition
- Evidence: definition

```agda
  oct-sub : Oct → Oct → Oct
  oct-sub x y = mkOct
    (o0 x - o0 y) (o1 x - o1 y) (o2 x - o2 y) (o3 x - o3 y)
    (o4 x - o4 y) (o5 x - o5 y) (o6 x - o6 y) (o7 x - o7 y)
```

### `oct-scale`

- Source: `Agda/GKN_E7_Bridge.agda:183`
- Kind: definition
- Evidence: definition

```agda
  oct-scale : R → Oct → Oct
  oct-scale s x = mkOct
    (s * o0 x) (s * o1 x) (s * o2 x) (s * o3 x)
    (s * o4 x) (s * o5 x) (s * o6 x) (s * o7 x)
```

### `oct-conj`

- Source: `Agda/GKN_E7_Bridge.agda:188`
- Kind: definition
- Evidence: definition

```agda
  oct-conj : Oct → Oct
  oct-conj x = mkOct
    (o0 x) (- (o1 x)) (- (o2 x)) (- (o3 x))
    (- (o4 x)) (- (o5 x)) (- (o6 x)) (- (o7 x))
```

### `oct-re`

- Source: `Agda/GKN_E7_Bridge.agda:193`
- Kind: definition
- Evidence: definition

```agda
  oct-re : Oct → R
  oct-re = o0
```

### `oct-norm2`

- Source: `Agda/GKN_E7_Bridge.agda:196`
- Kind: definition
- Evidence: definition

```agda
  oct-norm2 : Oct → R
  oct-norm2 x =
    sq (o0 x) + sq (o1 x) + sq (o2 x) + sq (o3 x) +
    sq (o4 x) + sq (o5 x) + sq (o6 x) + sq (o7 x)
```

### `oct-mul`

- Source: `Agda/GKN_E7_Bridge.agda:202`
- Kind: definition
- Evidence: definition

```agda
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
```

### `oct-conj-involution`

- Source: `Agda/GKN_E7_Bridge.agda:218`
- Kind: proved proposition
- Evidence: proof term (Agda term of the stated type)

```agda
  oct-conj-involution : ∀ x → oct-conj (oct-conj x) ≡ x
  oct-conj-involution (mkOct a0 a1 a2 a3 a4 a5 a6 a7) rewrite
    neg-invol a1 | neg-invol a2 | neg-invol a3 | neg-invol a4 |
    neg-invol a5 | neg-invol a6 | neg-invol a7 = refl
```

### `oct-re-conj`

- Source: `Agda/GKN_E7_Bridge.agda:223`
- Kind: proved proposition
- Evidence: proof term (Agda term of the stated type)

```agda
  oct-re-conj : ∀ x → oct-re (oct-conj x) ≡ oct-re x
  oct-re-conj (mkOct _ _ _ _ _ _ _ _) = refl
```

### `J3O`

- Source: `Agda/GKN_E7_Bridge.agda:230`
- Kind: record type
- Evidence: type declaration

```agda
  record J3O : Set where
```

### `j3-add`

- Source: `Agda/GKN_E7_Bridge.agda:237`
- Kind: definition
- Evidence: definition

```agda
  j3-add : J3O → J3O → J3O
  j3-add X Y = mkJ3O
    (xi1 X + xi1 Y) (xi2 X + xi2 Y) (xi3 X + xi3 Y)
    (oct-add (jx1 X) (jx1 Y)) (oct-add (jx2 X) (jx2 Y)) (oct-add (jx3 X) (jx3 Y))
```

### `j3-sub`

- Source: `Agda/GKN_E7_Bridge.agda:242`
- Kind: definition
- Evidence: definition

```agda
  j3-sub : J3O → J3O → J3O
  j3-sub X Y = mkJ3O
    (xi1 X - xi1 Y) (xi2 X - xi2 Y) (xi3 X - xi3 Y)
    (oct-sub (jx1 X) (jx1 Y)) (oct-sub (jx2 X) (jx2 Y)) (oct-sub (jx3 X) (jx3 Y))
```

### `j3-scale`

- Source: `Agda/GKN_E7_Bridge.agda:247`
- Kind: definition
- Evidence: definition

```agda
  j3-scale : R → J3O → J3O
  j3-scale s X = mkJ3O
    (s * xi1 X) (s * xi2 X) (s * xi3 X)
    (oct-scale s (jx1 X)) (oct-scale s (jx2 X)) (oct-scale s (jx3 X))
```

### `j3-tr`

- Source: `Agda/GKN_E7_Bridge.agda:252`
- Kind: definition
- Evidence: definition

```agda
  j3-tr : J3O → R
  j3-tr X = xi1 X + xi2 X + xi3 X
```

### `j3-bil`

- Source: `Agda/GKN_E7_Bridge.agda:255`
- Kind: definition
- Evidence: definition

```agda
  j3-bil : J3O → J3O → R
  j3-bil X Y =
    (xi1 X * xi1 Y + xi2 X * xi2 Y + xi3 X * xi3 Y) +
    2R * (oct-re (oct-mul (jx1 X) (oct-conj (jx1 Y))) +
          oct-re (oct-mul (jx2 X) (oct-conj (jx2 Y))) +
          oct-re (oct-mul (jx3 X) (oct-conj (jx3 Y))))
```

### `j3-norm`

- Source: `Agda/GKN_E7_Bridge.agda:262`
- Kind: definition
- Evidence: definition

```agda
  j3-norm : J3O → R
  j3-norm X =
    ((((xi1 X * xi2 X * xi3 X)
      - (xi1 X * oct-norm2 (jx1 X)))
      - (xi2 X * oct-norm2 (jx2 X)))
      - (xi3 X * oct-norm2 (jx3 X)))
    + 2R * oct-re (oct-mul (jx1 X) (oct-mul (jx2 X) (jx3 X)))
```

### `j3-sharp`

- Source: `Agda/GKN_E7_Bridge.agda:270`
- Kind: definition
- Evidence: definition

```agda
  j3-sharp : J3O → J3O
  j3-sharp X = mkJ3O
    (xi2 X * xi3 X - oct-norm2 (jx1 X))
    (xi3 X * xi1 X - oct-norm2 (jx2 X))
    (xi1 X * xi2 X - oct-norm2 (jx3 X))
    (oct-sub (oct-conj (oct-mul (jx2 X) (jx3 X))) (oct-scale (xi1 X) (jx1 X)))
    (oct-sub (oct-conj (oct-mul (jx3 X) (jx1 X))) (oct-scale (xi2 X) (jx2 X)))
    (oct-sub (oct-conj (oct-mul (jx1 X) (jx2 X))) (oct-scale (xi3 X) (jx3 X)))
```

### `j3-cross`

- Source: `Agda/GKN_E7_Bridge.agda:279`
- Kind: definition
- Evidence: definition

```agda
  j3-cross : J3O → J3O → J3O
  j3-cross X Y = j3-sub (j3-sub (j3-sharp (j3-add X Y)) (j3-sharp X)) (j3-sharp Y)
```

### `FTS56`

- Source: `Agda/GKN_E7_Bridge.agda:286`
- Kind: record type
- Evidence: type declaration

```agda
  record FTS56 : Set where
```

### `I4`

- Source: `Agda/GKN_E7_Bridge.agda:295`
- Kind: definition
- Evidence: definition

```agda
  I4 : FTS56 → R
  I4 psi =
    let a = f-alpha psi
        b = f-beta  psi
        X = f-X     psi
        Y = f-Y     psi
    in (- sq (a * b - j3-bil X Y)) +
       4R * (a * j3-norm X + b * j3-norm Y + j3-bil (j3-sharp X) (j3-sharp Y))
```

### `fts-sigma`

- Source: `Agda/GKN_E7_Bridge.agda:305`
- Kind: definition
- Evidence: definition

```agda
  fts-sigma : FTS56 → FTS56
  fts-sigma psi = mkFTS (- f-beta psi) (f-alpha psi) (j3-scale (- 1R) (f-Y psi)) (f-X psi)
```

### `fts-grade`

- Source: `Agda/GKN_E7_Bridge.agda:309`
- Kind: definition
- Evidence: definition

```agda
  fts-grade : R → R → FTS56 → FTS56
  fts-grade l linv psi = mkFTS
    (cube l * f-alpha psi) (cube linv * f-beta psi)
    (j3-scale linv (f-X psi)) (j3-scale l (f-Y psi))
```

### `fts-shift`

- Source: `Agda/GKN_E7_Bridge.agda:315`
- Kind: definition
- Evidence: definition

```agda
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
```

### `E7PolynomialWitness`

- Source: `Agda/GKN_E7_Bridge.agda:328`
- Kind: record type
- Evidence: type declaration

```agda
  record E7PolynomialWitness : Set where
```

### `oct-norm-mult`

- Source: `Agda/GKN_E7_Bridge.agda:330`
- Kind: record field
- Evidence: obligation (record field; no instance in file)

```agda
      oct-norm-mult   : ∀ x y → oct-norm2 (oct-mul x y) ≡ oct-norm2 x * oct-norm2 y
```

### `j3-euler`

- Source: `Agda/GKN_E7_Bridge.agda:331`
- Kind: record field
- Evidence: obligation (record field; no instance in file)

```agda
      j3-euler        : ∀ X → j3-bil (j3-sharp X) X ≡ 3R * j3-norm X
```

### `I4-sigma-inv`

- Source: `Agda/GKN_E7_Bridge.agda:332`
- Kind: record field
- Evidence: obligation (record field; no instance in file)

```agda
      I4-sigma-inv    : ∀ psi → I4 (fts-sigma psi) ≡ I4 psi
```

### `I4-shift-inv`

- Source: `Agda/GKN_E7_Bridge.agda:333`
- Kind: record field
- Evidence: obligation (record field; no instance in file)

```agda
      I4-shift-inv    : ∀ C psi → I4 (fts-shift C psi) ≡ I4 psi
```

### `partition-Z`

- Source: `Agda/GKN_E7_Bridge.agda:339`
- Kind: definition
- Evidence: definition

```agda
  partition-Z : List R → R → R
  partition-Z []         beta = 0R
  partition-Z (E ∷ rest) beta = exp (- (beta * E)) + partition-Z rest beta
```

### `partition-Z-pos`

- Source: `Agda/GKN_E7_Bridge.agda:343`
- Kind: proved proposition
- Evidence: proof term (Agda term of the stated type)

```agda
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
```

### `free-energy-psi`

- Source: `Agda/GKN_E7_Bridge.agda:354`
- Kind: definition
- Evidence: definition

```agda
  free-energy-psi : List R → R → R
  free-energy-psi energies beta = ln (partition-Z energies beta)
```

### `IsLegendreEntropy`

- Source: `Agda/GKN_E7_Bridge.agda:357`
- Kind: record type
- Evidence: type declaration

```agda
  record IsLegendreEntropy (energies : List R) (E S-E : R) : Set where
```

### `fenchel-young-inequality`

- Source: `Agda/GKN_E7_Bridge.agda:362`
- Kind: definition
- Evidence: definition

```agda
  fenchel-young-inequality :
    ∀ {energies E S-E} → IsLegendreEntropy energies E S-E →
    ∀ beta → S-E ≤ (beta * E + free-energy-psi energies beta)
  fenchel-young-inequality leg beta = IsLegendreEntropy.lower-bound leg beta
```

### `logit-Z`

- Source: `Agda/GKN_E7_Bridge.agda:371`
- Kind: definition
- Evidence: definition

```agda
  logit-Z : List R → R → R
  logit-Z logits beta = partition-Z (map (-_) logits) beta
```

### `logit-gate-prob`

- Source: `Agda/GKN_E7_Bridge.agda:374`
- Kind: definition
- Evidence: definition

```agda
  logit-gate-prob : List R → R → R → R
  logit-gate-prob logits beta z-i = exp (beta * z-i) / logit-Z logits beta
```

### `logit-gate-prob-pos`

- Source: `Agda/GKN_E7_Bridge.agda:377`
- Kind: definition
- Evidence: definition

```agda
  logit-gate-prob-pos :
    ∀ logits beta z-i → NonEmpty logits → 0R < logit-gate-prob logits beta z-i
  logit-gate-prob-pos (x ∷ xs) beta z-i ne-cons =
    <-div⁺ (exp-pos (beta * z-i)) (partition-Z-pos (map (-_) (x ∷ xs)) beta ne-cons)
```

### `montgomery-R2`

- Source: `Agda/GKN_E7_Bridge.agda:382`
- Kind: definition
- Evidence: definition

```agda
  montgomery-R2 : R → R
  montgomery-R2 u with isZero? u
  ... | inj₁ _ = 0R
  ... | inj₂ _ = 1R - sq (sin (PI * u) / (PI * u))
```

### `montgomery-R2-at-zero`

- Source: `Agda/GKN_E7_Bridge.agda:387`
- Kind: proved proposition
- Evidence: proof term (Agda term of the stated type)

```agda
  montgomery-R2-at-zero : montgomery-R2 0R ≡ 0R
  montgomery-R2-at-zero with isZero? 0R
  ... | inj₁ _   = refl
  ... | inj₂ neq = ⊥-elim (neq refl)
```

### `montgomery-R2-upper-bound`

- Source: `Agda/GKN_E7_Bridge.agda:392`
- Kind: proved proposition
- Evidence: proof term (Agda term of the stated type)

```agda
  montgomery-R2-upper-bound : ∀ u → montgomery-R2 u ≤ 1R
  montgomery-R2-upper-bound u with isZero? u
  ... | inj₁ _ = 0≤1
  ... | inj₂ _ = sub-le-one (sq-nonneg (sin (PI * u) / (PI * u)))
```

### `BitVec3`

- Source: `Agda/GKN_E7_Bridge.agda:402`
- Kind: definition
- Evidence: definition

```agda
BitVec3 : Set
BitVec3 = Bool × (Bool × Bool)
```

### `encode-bitflip`

- Source: `Agda/GKN_E7_Bridge.agda:405`
- Kind: definition
- Evidence: definition

```agda
encode-bitflip : Bool → BitVec3
encode-bitflip b = (b , (b , b))
```

### `xor3`

- Source: `Agda/GKN_E7_Bridge.agda:408`
- Kind: definition
- Evidence: definition

```agda
xor3 : BitVec3 → BitVec3 → BitVec3
xor3 (v0 , (v1 , v2)) (e0 , (e1 , e2)) = (xor v0 e0 , (xor v1 e1 , xor v2 e2))
```

### `syndrome`

- Source: `Agda/GKN_E7_Bridge.agda:411`
- Kind: definition
- Evidence: definition

```agda
syndrome : BitVec3 → Bool × Bool
syndrome (v0 , (v1 , v2)) = (xor v0 v1 , xor v1 v2)
```

### `recover-bitflip`

- Source: `Agda/GKN_E7_Bridge.agda:414`
- Kind: definition
- Evidence: definition

```agda
recover-bitflip : BitVec3 → Bool
recover-bitflip (v0 , (v1 , v2)) with syndrome (v0 , (v1 , v2))
... | (false , false) = v0
... | (true  , false) = not v0
... | (true  , true)  = v0
... | (false , true)  = v0
```

### `SingleBitError`

- Source: `Agda/GKN_E7_Bridge.agda:421`
- Kind: data type
- Evidence: type declaration

```agda
data SingleBitError : BitVec3 → Set where
```

### `err-none`

- Source: `Agda/GKN_E7_Bridge.agda:422`
- Kind: proved proposition
- Evidence: proof term (Agda term of the stated type)

```agda
  err-none : SingleBitError (false , (false , false))
```

### `err-q0`

- Source: `Agda/GKN_E7_Bridge.agda:423`
- Kind: proved proposition
- Evidence: proof term (Agda term of the stated type)

```agda
  err-q0   : SingleBitError (true  , (false , false))
```

### `err-q1`

- Source: `Agda/GKN_E7_Bridge.agda:424`
- Kind: proved proposition
- Evidence: proof term (Agda term of the stated type)

```agda
  err-q1   : SingleBitError (false , (true  , false))
```

### `err-q2`

- Source: `Agda/GKN_E7_Bridge.agda:425`
- Kind: proved proposition
- Evidence: proof term (Agda term of the stated type)

```agda
  err-q2   : SingleBitError (false , (false , true))
```

### `bitflip-qec-exact-recovery`

- Source: `Agda/GKN_E7_Bridge.agda:427`
- Kind: definition
- Evidence: definition

```agda
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
```

## Dafny — 9 lemmas, 5 methods, 2 predicates, 24 functions (21 plain, 3 {:axiom})

### `OctConj`

- Source: `Dafny/GKN_E7_Bridge.dfy:26`
- Kind: function
- Evidence: function definition

```dafny
  function OctConj(x: Oct): Oct {
    Oct(x.o0, -x.o1, -x.o2, -x.o3, -x.o4, -x.o5, -x.o6, -x.o7)
  }
```

### `OctRe`

- Source: `Dafny/GKN_E7_Bridge.dfy:30`
- Kind: function
- Evidence: function definition

```dafny
  function OctRe(x: Oct): real { x.o0 }
```

### `OctNorm2`

- Source: `Dafny/GKN_E7_Bridge.dfy:32`
- Kind: function
- Evidence: function definition

```dafny
  function OctNorm2(x: Oct): real {
    x.o0*x.o0 + x.o1*x.o1 + x.o2*x.o2 + x.o3*x.o3 +
    x.o4*x.o4 + x.o5*x.o5 + x.o6*x.o6 + x.o7*x.o7
  }
```

### `OctAdd`

- Source: `Dafny/GKN_E7_Bridge.dfy:37`
- Kind: function
- Evidence: function definition

```dafny
  function OctAdd(x: Oct, y: Oct): Oct {
    Oct(x.o0+y.o0, x.o1+y.o1, x.o2+y.o2, x.o3+y.o3,
        x.o4+y.o4, x.o5+y.o5, x.o6+y.o6, x.o7+y.o7)
  }
```

### `OctSub`

- Source: `Dafny/GKN_E7_Bridge.dfy:42`
- Kind: function
- Evidence: function definition

```dafny
  function OctSub(x: Oct, y: Oct): Oct {
    Oct(x.o0-y.o0, x.o1-y.o1, x.o2-y.o2, x.o3-y.o3,
        x.o4-y.o4, x.o5-y.o5, x.o6-y.o6, x.o7-y.o7)
  }
```

### `OctScale`

- Source: `Dafny/GKN_E7_Bridge.dfy:47`
- Kind: function
- Evidence: function definition

```dafny
  function OctScale(s: real, x: Oct): Oct {
    Oct(s*x.o0, s*x.o1, s*x.o2, s*x.o3, s*x.o4, s*x.o5, s*x.o6, s*x.o7)
  }
```

### `OctMul`

- Source: `Dafny/GKN_E7_Bridge.dfy:52`
- Kind: function
- Evidence: function definition

```dafny
  function OctMul(x: Oct, y: Oct): Oct {
    Oct(
      x.o0*y.o0 - x.o1*y.o1 - x.o2*y.o2 - x.o3*y.o3 - x.o4*y.o4 - x.o5*y.o5 - x.o6*y.o6 - x.o7*y.o7,
      x.o0*y.o1 + x.o1*y.o0 + x.o2*y.o3 - x.o3*y.o2 + x.o4*y.o5 - x.o5*y.o4 - x.o6*y.o7 + x.o7*y.o6,
      x.o0*y.o2 - x.o1*y.o3 + x.o2*y.o0 + x.o3*y.o1 + x.o4*y.o6 + x.o5*y.o7 - x.o6*y.o4 - x.o7*y.o5,
      x.o0*y.o3 + x.o1*y.o2 - x.o2*y.o1 + x.o3*y.o0 + x.o4*y.o7 - x.o5*y.o6 + x.o6*y.o5 - x.o7*y.o4,
      x.o0*y.o4 - x.o1*y.o5 - x.o2*y.o6 - x.o3*y.o7 + x.o4*y.o0 + x.o5*y.o1 + x.o6*y.o2 + x.o7*y.o3,
      x.o0*y.o5 + x.o1*y.o4 - x.o2*y.o7 + x.o3*y.o6 - x.o4*y.o1 + x.o5*y.o0 - x.o6*y.o3 + x.o7*y.o2,
      x.o0*y.o6 + x.o1*y.o7 + x.o2*y.o4 - x.o3*y.o5 - x.o4*y.o2 + x.o5*y.o3 + x.o6*y.o0 - x.o7*y.o1,
      x.o0*y.o7 - x.o1*y.o6 + x.o2*y.o5 + x.o3*y.o4 - x.o4*y.o3 - x.o5*y.o2 + x.o6*y.o1 + x.o7*y.o0
    )
  }
```

### `OctNormNonNeg`

- Source: `Dafny/GKN_E7_Bridge.dfy:65`
- Kind: lemma
- Evidence: empty body (discharged by the verifier; no run recorded)

```dafny
  lemma OctNormNonNeg(x: Oct)
    ensures OctNorm2(x) >= 0.0
  {}
```

### `OctConjInvolution`

- Source: `Dafny/GKN_E7_Bridge.dfy:69`
- Kind: lemma
- Evidence: empty body (discharged by the verifier; no run recorded)

```dafny
  lemma OctConjInvolution(x: Oct)
    ensures OctConj(OctConj(x)) == x
  {}
```

### `OctNormMultiplicative`

- Source: `Dafny/GKN_E7_Bridge.dfy:73`
- Kind: lemma
- Evidence: empty body (discharged by the verifier; no run recorded)

```dafny
  lemma OctNormMultiplicative(x: Oct, y: Oct)
    ensures OctNorm2(OctMul(x, y)) == OctNorm2(x) * OctNorm2(y)
  {}
```

### `J3Add`

- Source: `Dafny/GKN_E7_Bridge.dfy:83`
- Kind: function
- Evidence: function definition

```dafny
  function J3Add(X: J3O, Y: J3O): J3O {
    J3O(X.xi1+Y.xi1, X.xi2+Y.xi2, X.xi3+Y.xi3,
        OctAdd(X.jx1, Y.jx1), OctAdd(X.jx2, Y.jx2), OctAdd(X.jx3, Y.jx3))
  }
```

### `J3Sub`

- Source: `Dafny/GKN_E7_Bridge.dfy:88`
- Kind: function
- Evidence: function definition

```dafny
  function J3Sub(X: J3O, Y: J3O): J3O {
    J3O(X.xi1-Y.xi1, X.xi2-Y.xi2, X.xi3-Y.xi3,
        OctSub(X.jx1, Y.jx1), OctSub(X.jx2, Y.jx2), OctSub(X.jx3, Y.jx3))
  }
```

### `J3Scale`

- Source: `Dafny/GKN_E7_Bridge.dfy:93`
- Kind: function
- Evidence: function definition

```dafny
  function J3Scale(s: real, X: J3O): J3O {
    J3O(s*X.xi1, s*X.xi2, s*X.xi3,
        OctScale(s, X.jx1), OctScale(s, X.jx2), OctScale(s, X.jx3))
  }
```

### `J3Bil`

- Source: `Dafny/GKN_E7_Bridge.dfy:98`
- Kind: function
- Evidence: function definition

```dafny
  function J3Bil(X: J3O, Y: J3O): real {
    X.xi1*Y.xi1 + X.xi2*Y.xi2 + X.xi3*Y.xi3 +
    2.0 * (OctRe(OctMul(X.jx1, OctConj(Y.jx1))) +
           OctRe(OctMul(X.jx2, OctConj(Y.jx2))) +
           OctRe(OctMul(X.jx3, OctConj(Y.jx3))))
  }
```

### `J3Norm`

- Source: `Dafny/GKN_E7_Bridge.dfy:105`
- Kind: function
- Evidence: function definition

```dafny
  function J3Norm(X: J3O): real {
    X.xi1*X.xi2*X.xi3 - X.xi1*OctNorm2(X.jx1) - X.xi2*OctNorm2(X.jx2) - X.xi3*OctNorm2(X.jx3)
    + 2.0 * OctRe(OctMul(X.jx1, OctMul(X.jx2, X.jx3)))
  }
```

### `J3Sharp`

- Source: `Dafny/GKN_E7_Bridge.dfy:110`
- Kind: function
- Evidence: function definition

```dafny
  function J3Sharp(X: J3O): J3O {
    J3O(
      X.xi2*X.xi3 - OctNorm2(X.jx1),
      X.xi3*X.xi1 - OctNorm2(X.jx2),
      X.xi1*X.xi2 - OctNorm2(X.jx3),
      OctSub(OctConj(OctMul(X.jx2, X.jx3)), OctScale(X.xi1, X.jx1)),
      OctSub(OctConj(OctMul(X.jx3, X.jx1)), OctScale(X.xi2, X.jx2)),
      OctSub(OctConj(OctMul(X.jx1, X.jx2)), OctScale(X.xi3, X.jx3))
    )
  }
```

### `J3Cross`

- Source: `Dafny/GKN_E7_Bridge.dfy:121`
- Kind: function
- Evidence: function definition

```dafny
  function J3Cross(X: J3O, Y: J3O): J3O {
    J3Sub(J3Sub(J3Sharp(J3Add(X, Y)), J3Sharp(X)), J3Sharp(Y))
  }
```

### `J3BilSymmetric`

- Source: `Dafny/GKN_E7_Bridge.dfy:125`
- Kind: lemma
- Evidence: empty body (discharged by the verifier; no run recorded)

```dafny
  lemma J3BilSymmetric(X: J3O, Y: J3O)
    ensures J3Bil(X, Y) == J3Bil(Y, X)
  {}
```

### `J3EulerIdentity`

- Source: `Dafny/GKN_E7_Bridge.dfy:129`
- Kind: lemma
- Evidence: empty body (discharged by the verifier; no run recorded)

```dafny
  lemma J3EulerIdentity(X: J3O)
    ensures J3Bil(J3Sharp(X), X) == 3.0 * J3Norm(X)
  {}
```

### `I4`

- Source: `Dafny/GKN_E7_Bridge.dfy:138`
- Kind: function
- Evidence: function definition

```dafny
  function I4(psi: FTS56): real {
    var d := psi.alpha * psi.beta - J3Bil(psi.X, psi.Y);
    -(d * d) + 4.0 * (psi.alpha * J3Norm(psi.X) + psi.beta * J3Norm(psi.Y)
                      + J3Bil(J3Sharp(psi.X), J3Sharp(psi.Y)))
  }
```

### `FTSSigma`

- Source: `Dafny/GKN_E7_Bridge.dfy:144`
- Kind: function
- Evidence: function definition

```dafny
  function FTSSigma(psi: FTS56): FTS56 {
    FTS56(-psi.beta, psi.alpha, J3Scale(-1.0, psi.Y), psi.X)
  }
```

### `FTSShift`

- Source: `Dafny/GKN_E7_Bridge.dfy:148`
- Kind: function
- Evidence: function definition

```dafny
  function FTSShift(C: J3O, psi: FTS56): FTS56 {
    FTS56(
      psi.alpha + J3Bil(C, psi.Y) - J3Bil(J3Sharp(C), psi.X) - psi.beta * J3Norm(C),
      psi.beta,
      J3Add(psi.X, J3Scale(psi.beta, C)),
      J3Sub(J3Sub(psi.Y, J3Cross(C, psi.X)), J3Scale(psi.beta, J3Sharp(C)))
    )
  }
```

### `ApplyFTSSigma`

- Source: `Dafny/GKN_E7_Bridge.dfy:157`
- Kind: method
- Evidence: method with body in file

```dafny
  method ApplyFTSSigma(psi: FTS56) returns (out: FTS56)
    ensures I4(out) == I4(psi)
  {
    out := FTSSigma(psi);
    J3BilSymmetric(J3Sharp(psi.Y), J3Sharp(psi.X));
  }
```

### `I4ShiftInvariant`

- Source: `Dafny/GKN_E7_Bridge.dfy:165`
- Kind: lemma {:axiom}
- Evidence: axiomatized ({:axiom})

```dafny
  lemma {:axiom} I4ShiftInvariant(C: J3O, psi: FTS56)
```

### `EncodeBitFlip`

- Source: `Dafny/GKN_E7_Bridge.dfy:173`
- Kind: function
- Evidence: function definition

```dafny
  function EncodeBitFlip(b: bool): BitVec3 { BV3(b, b, b) }
```

### `Xor3`

- Source: `Dafny/GKN_E7_Bridge.dfy:175`
- Kind: function
- Evidence: function definition

```dafny
  function Xor3(v: BitVec3, e: BitVec3): BitVec3 {
    BV3(v.v0 != e.v0, v.v1 != e.v1, v.v2 != e.v2)
  }
```

### `SingleBitError`

- Source: `Dafny/GKN_E7_Bridge.dfy:179`
- Kind: predicate
- Evidence: predicate definition

```dafny
  predicate SingleBitError(e: BitVec3) {
    e == BV3(false, false, false) ||
    e == BV3(true,  false, false) ||
    e == BV3(false, true,  false) ||
    e == BV3(false, false, true)
  }
```

### `RecoverBitFlip`

- Source: `Dafny/GKN_E7_Bridge.dfy:186`
- Kind: method
- Evidence: method with body in file

```dafny
  method RecoverBitFlip(v: BitVec3) returns (b: bool)
    ensures (exists orig: bool, e: BitVec3 ::
              SingleBitError(e) && v == Xor3(EncodeBitFlip(orig), e) ==> b == orig)
  {
    var s1 := (v.v0 != v.v1);
    var s2 := (v.v1 != v.v2);
    if s1 && !s2 {
      b := !v.v0;
    } else {
      b := v.v0;
    }
  }
```

### `BitFlipExactRecovery`

- Source: `Dafny/GKN_E7_Bridge.dfy:199`
- Kind: lemma
- Evidence: empty body (discharged by the verifier; no run recorded)

```dafny
  lemma BitFlipExactRecovery(b: bool, e: BitVec3)
    requires SingleBitError(e)
    ensures var v := Xor3(EncodeBitFlip(b), e);
            var s1 := (v.v0 != v.v1);
            var s2 := (v.v1 != v.v2);
            (if s1 && !s2 then !v.v0 else v.v0) == b
  {}
```

### `Exp`

- Source: `Dafny/GKN_E7_Bridge.dfy:210`
- Kind: function {:axiom}
- Evidence: axiomatized ({:axiom})

```dafny
  function {:axiom} Exp(x: real): real
```

### `Ln`

- Source: `Dafny/GKN_E7_Bridge.dfy:213`
- Kind: function {:axiom}
- Evidence: axiomatized ({:axiom})

```dafny
  function {:axiom} Ln(x: real): real
```

### `PartitionZ`

- Source: `Dafny/GKN_E7_Bridge.dfy:215`
- Kind: function
- Evidence: function definition

```dafny
  function PartitionZ(energies: seq<real>, beta: real): real
    requires |energies| > 0
    ensures PartitionZ(energies, beta) > 0.0
    decreases |energies|
  {
    if |energies| == 1 then Exp(-beta * energies[0])
    else Exp(-beta * energies[0]) + PartitionZ(energies[1..], beta)
  }
```

### `ComputePartitionZ`

- Source: `Dafny/GKN_E7_Bridge.dfy:224`
- Kind: method
- Evidence: method with body in file

```dafny
  method ComputePartitionZ(energies: seq<real>, beta: real) returns (Z: real)
    requires |energies| > 0
    ensures Z > 0.0
  {
    Z := 0.0;
    var i := 0;
    while i < |energies|
      invariant 0 <= i <= |energies|
      invariant i == 0 ==> Z == 0.0
      invariant i > 0 ==> Z > 0.0
    {
      Z := Z + Exp(-beta * energies[i]);
      i := i + 1;
    }
  }
```

### `FreeEnergyPsi`

- Source: `Dafny/GKN_E7_Bridge.dfy:240`
- Kind: function
- Evidence: function definition

```dafny
  function FreeEnergyPsi(energies: seq<real>, beta: real): real
    requires |energies| > 0
  {
    Ln(PartitionZ(energies, beta))
  }
```

### `IsLegendreEntropy`

- Source: `Dafny/GKN_E7_Bridge.dfy:246`
- Kind: predicate
- Evidence: predicate definition

```dafny
  predicate IsLegendreEntropy(energies: seq<real>, E: real, S_E: real)
    requires |energies| > 0
  {
    (forall beta: real :: S_E <= beta * E + FreeEnergyPsi(energies, beta))
  }
```

### `FenchelYoungInequality`

- Source: `Dafny/GKN_E7_Bridge.dfy:252`
- Kind: lemma
- Evidence: empty body (discharged by the verifier; no run recorded)

```dafny
  lemma FenchelYoungInequality(energies: seq<real>, E: real, S_E: real, beta: real)
    requires |energies| > 0
    requires IsLegendreEntropy(energies, E, S_E)
    ensures S_E <= beta * E + FreeEnergyPsi(energies, beta)
  {}
```

### `Sin`

- Source: `Dafny/GKN_E7_Bridge.dfy:261`
- Kind: function {:axiom}
- Evidence: axiomatized ({:axiom})

```dafny
  function {:axiom} Sin(x: real): real
```

### `SincBound`

- Source: `Dafny/GKN_E7_Bridge.dfy:264`
- Kind: lemma {:axiom}
- Evidence: axiomatized ({:axiom})

```dafny
  lemma {:axiom} SincBound(x: real)
```

### `LogitGateDistribution`

- Source: `Dafny/GKN_E7_Bridge.dfy:268`
- Kind: method
- Evidence: method with body in file

```dafny
  method LogitGateDistribution(logits: seq<real>, beta: real) returns (probs: seq<real>)
    requires |logits| > 0
    ensures |probs| == |logits|
    ensures forall k :: 0 <= k < |probs| ==> probs[k] > 0.0
  {
    var Z := 0.0;
    var i := 0;
    while i < |logits|
      invariant 0 <= i <= |logits|
      invariant i == 0 ==> Z == 0.0
      invariant i > 0 ==> Z > 0.0
    {
      Z := Z + Exp(beta * logits[i]);
      i := i + 1;
    }

    probs := [];
    i := 0;
    while i < |logits|
      invariant 0 <= i <= |logits|
      invariant |probs| == i
      invariant forall k :: 0 <= k < i ==> probs[k] > 0.0
    {
      probs := probs + [Exp(beta * logits[i]) / Z];
      i := i + 1;
    }
  }
```

### `MontgomeryR2`

- Source: `Dafny/GKN_E7_Bridge.dfy:296`
- Kind: method
- Evidence: method with body in file

```dafny
  method MontgomeryR2(u: real) returns (r2: real)
    ensures u == 0.0 ==> r2 == 0.0
    ensures 0.0 <= r2 <= 1.0
  {
    if u == 0.0 {
      r2 := 0.0;
    } else {
      SincBound(PI * u);
      var sinc := Sin(PI * u) / (PI * u);
      assert sinc * sinc <= 1.0;
      r2 := 1.0 - sinc * sinc;
    }
  }
```
