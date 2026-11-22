# I4_ScaleHomogeneous.mod
# Parr Conjecture — GKN quartic scale extremum
# Certified constraint: I4(lambda * s) = lambda^4 * I4(s)

param I4_s default 1;
param s_dim default 56;

var lambda >= 0 <= 5;

maximize abs_I4:
    abs(lambda^4 * I4_s);

subject to homogeneity_doc:
    # Formal contract (Lean): I4_scale_invariant / FTS56.I4_homogeneous
    # At solve-time we optimise the closed form lambda^4 * I4_s
    lambda >= 0;

end;
