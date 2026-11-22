# FreeEnergy_Legendre.mod
# Minimise beta*E + log(Z(beta)) over inverse temperature
# Certified: partition_Z_pos, log_sum_exp_lower

param n > 0;
param E {1..n};
param E_target;

var beta;

# Partition function Z = sum_i exp(-beta * E[i])
# Free energy F = beta * E_target + log(Z)

minimize free_energy:
    beta * E_target
    + log( sum {i in 1..n} exp(-beta * E[i]) );

subject to Z_positive:
    # Enforced by exp > 0; documented contract partition_Z_pos
    sum {i in 1..n} exp(-beta * E[i]) >= 1e-300;

end;
