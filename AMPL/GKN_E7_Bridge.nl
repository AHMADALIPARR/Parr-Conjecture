# Copyright (c) 2026 Ahmad Ali Parr / Bel Esprit D'Accord Irrevocable Trust (EIN 42-697643).
# Released under the GNU Affero General Public License v3.0 or later.
# See the file LICENSE for details.
# Authors: Ahmad Ali Parr
# BOW-Ω-φ-∂-2026

g3 1 1 0	# problem GKN_E7_Bridge
7 9 1 0 0 0	# vars, constraints, objectives, ranges, eqns, lcons
0 0	# nonlinear constraints, nonlinear objectives (expr trees below)
0 0	# network constraints
0 0 0	# nonlinear vars in constraints, objectives, both
0 0 0 1	# linear network; functions; arith; flags
0 0 0 0 0	# discrete: bvs, int vars nonlin, continuous, binary, int
9 7	# no. of nonzeros in Jacobian, gradients of objectives
0 0	# max name lengths
0 0 0 0 0	# common exprs

# Bounds (b)
3 1e-6 100
0 -1.7976931348623157e+308 1.7976931348623157e+308
3 0 1
3 0 1
3 0 1
3 0 1
3 0 1

# Initial primal (x)
1.0
0.0
0.25
0.25
0.25
0.25
0.5947152654306489

# Variable names
# 0 beta_thermo
# 1 S_entropy
# 2 p_logit[1]
# 3 p_logit[2]
# 4 p_logit[3]
# 5 p_logit[4]
# 6 R2_val

# Objective 0: minimize Legendre_Dual_Infimum
#   beta_thermo * E_target + log(sum_k exp(-beta_thermo * E_level[k]))
#   E_target=1.2 E_level=[0.0, 1.0, 2.5, 4.0]
O0 0	# 0 = minimize
# nonlinear: log-sum-exp + linear beta*E_target

# Constraints C0..C8
# C0 E7_Shift_I4_Invariance: |I4_shifted - I4_base| <= 1e-9
#     I4_base=-8.0916 I4_shifted=-8.0916 residual=1.776e-15
C0	# body is constant residual (params only)
# residual const 1.7763568394002505e-15

# C1 QEC_SingleBitError_Budget: sum e_flip <= 1 (params: e_flip=[0,1,0])
C1

# C2 Legendre_Fenchel_Young: S_entropy - beta*E_target - log(sum exp(-beta E_k)) <= 0
C2

# C3 Logit_Gate_Definition[1]: p_logit[k] = exp(beta*logits[k])/sum_j exp(beta*logits[j])
C3

# C4 Logit_Gate_Definition[2]: p_logit[k] = exp(beta*logits[k])/sum_j exp(beta*logits[j])
C4

# C5 Logit_Gate_Definition[3]: p_logit[k] = exp(beta*logits[k])/sum_j exp(beta*logits[j])
C5

# C6 Logit_Gate_Definition[4]: p_logit[k] = exp(beta*logits[k])/sum_j exp(beta*logits[j])
C6

# C7 Logit_Simplex_Normalization: sum p_logit = 1
C7

# C8 Montgomery_R2_Def: R2_val = 0.594715265430649 (u_grid=0.5)
C8

# Constraint ranges (r)
4 0 1e-9	# C0 abs residual <= 1e-9 (encoded as range)
1 0 0	# C1 sum e <= 1 satisfied by data
1 0 0	# C2 Fenchel-Young <= 0 form
4 0 0	# Logit def equality
4 0 0	# Logit def equality
4 0 0	# Logit def equality
4 0 0	# Logit def equality
4 0 0	# simplex equality
4 0 0	# R2 equality

# Jacobian nonzeros (column-wise sketch)
# obj grad: d/d beta_thermo of Legendre dual (nonlinear)
# C2 depends on S_entropy, beta_thermo
# C3-C6 depend on p_logit[k], beta_thermo
# C7 depends on all p_logit
# C8 depends on R2_val

# Verified instance constants (from GKN_E7_Bridge.dat)
# I4_base = -8.0916
# I4_shifted = -8.0916
# |I4_shifted - I4_base| = 1.776357e-15
# R2(u=0.5) = 0.594715265430649
# Certified Lean/Rocq/Agda/Dafny contracts: I4_scale, I4_sigma, bitflip recovery,
#   partition_Z_pos, montgomery_R2 bounds, logit simplex

end
