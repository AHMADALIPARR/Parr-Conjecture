# Copyright (c) 2026 Ahmad Ali Parr / Bel Esprit D'Accord Irrevocable Trust (EIN 42-697643).
# Released under the GNU Affero General Public License v3.0 or later.
# See the file LICENSE for details.
# Authors: Ahmad Ali Parr
# BOW-Ω-φ-∂-2026

# ==============================================================================
# GKN_E7_Bridge.mod — Lowered from Common Mathematical IR to AMPL
# Supports NLP / MINLP solvers and .nl emission via `write gGKN_E7_Bridge;`
# ==============================================================================

param N_E integer >= 1;
param PI := 3.14159265358979323846;

set QUBITS := 0..2;
set ENERGY_IDX := 1..N_E;

# --- Parameters ---
param E_level {ENERGY_IDX};
param E_target;
param logits {ENERGY_IDX};
param u_grid >= 0;
param b_logical binary;
param e_flip {QUBITS} binary;

# --- J3(R) / FTS56 Parameters (diagonal slice for compact NLP) ---
param alpha_0;
param beta_0;
param X0 {QUBITS};
param Y0 {QUBITS};
param C_shift {QUBITS};

# --- Decision Variables & Numerical Bounds ---
var beta_thermo >= 1e-6, <= 100.0 := 1.0;
var S_entropy;
var p_logit {k in ENERGY_IDX} >= 0, <= 1;
var R2_val >= 0, <= 1;

# --- E_7(7) Quartic Invariant Expressions (diagonal J_3(R) slice) ---
param bil_XY := sum {q in QUBITS} X0[q] * Y0[q];
param norm_X := X0[0] * X0[1] * X0[2];
param norm_Y := Y0[0] * Y0[1] * Y0[2];
param sharpX {q in QUBITS} := X0[(q+1) mod 3] * X0[(q+2) mod 3];
param sharpY {q in QUBITS} := Y0[(q+1) mod 3] * Y0[(q+2) mod 3];
param I4_base := -(alpha_0 * beta_0 - bil_XY)^2 + 4 * (alpha_0 * norm_X + beta_0 * norm_Y + sum {q in QUBITS} sharpX[q] * sharpY[q]);

# Shifted FTS56 state under T_C:
param sharpC {q in QUBITS} := C_shift[(q+1) mod 3] * C_shift[(q+2) mod 3];
param norm_C := C_shift[0] * C_shift[1] * C_shift[2];
param alpha_1 := alpha_0 + (sum {q in QUBITS} C_shift[q]*Y0[q]) - (sum {q in QUBITS} sharpC[q]*X0[q]) - beta_0 * norm_C;
param X1 {q in QUBITS} := X0[q] + beta_0 * C_shift[q];
param crossCX {q in QUBITS} := C_shift[(q+1) mod 3]*X0[(q+2) mod 3] + C_shift[(q+2) mod 3]*X0[(q+1) mod 3];
param Y1 {q in QUBITS} := Y0[q] - crossCX[q] - beta_0 * sharpC[q];
param bil_X1Y1 := sum {q in QUBITS} X1[q] * Y1[q];
param norm_X1 := X1[0] * X1[1] * X1[2];
param norm_Y1 := Y1[0] * Y1[1] * Y1[2];
param sharpX1 {q in QUBITS} := X1[(q+1) mod 3] * X1[(q+2) mod 3];
param sharpY1 {q in QUBITS} := Y1[(q+1) mod 3] * Y1[(q+2) mod 3];
param I4_shifted := -(alpha_1 * beta_0 - bil_X1Y1)^2 + 4 * (alpha_1 * norm_X1 + beta_0 * norm_Y1 + sum {q in QUBITS} sharpX1[q] * sharpY1[q]);

# --- Objective: Legendre-Fenchel Dual Infimum ---
minimize Legendre_Dual_Infimum:
    beta_thermo * E_target + log(sum {k in ENERGY_IDX} exp(-beta_thermo * E_level[k]));

# --- Contracts as Optimization Constraints ---
subject to E7_Shift_I4_Invariance:
    abs(I4_shifted - I4_base) <= 1e-9;

subject to QEC_SingleBitError_Budget:
    sum {q in QUBITS} e_flip[q] <= 1;

subject to Legendre_Fenchel_Young:
    S_entropy <= beta_thermo * E_target + log(sum {k in ENERGY_IDX} exp(-beta_thermo * E_level[k]));

subject to Logit_Gate_Definition {k in ENERGY_IDX}:
    p_logit[k] = exp(beta_thermo * logits[k]) / (sum {j in ENERGY_IDX} exp(beta_thermo * logits[j]));

subject to Logit_Simplex_Normalization:
    sum {k in ENERGY_IDX} p_logit[k] = 1;

subject to Montgomery_R2_Def:
    R2_val = (if u_grid == 0 then 0 else 1 - (sin(PI * u_grid) / (PI * u_grid))^2);

end;
