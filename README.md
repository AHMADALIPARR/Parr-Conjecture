# Parr Conjecture

Formal Lean 4 development surrounding the **Gates–Parr / Parr Conjectures**, the Günaydin–Koepsell–Nicolai (GKN) quartic invariant \(I_4\) on the 56-dimensional fundamental representation of \(E_7\), exceptional Jordan algebra \(J_3(\mathbb{O})\), bit-flip quantum error correction, quantum partition function Legendre duality, and the Riemann–Metatron logit-gate / Montgomery pair-correlation bridge.

## Structure

- `S_AUTOCODE/` — Core octonion algebra, \(J_3(\mathbb{O})\), State56 / State108, \(I_4\) (Float computational witness)
- `GKN/` — CommRing formalisation of \(I_4\) homogeneity (zero-sorry degree-4 proof)
- `BitFlipCode/` — Three-qubit bit-flip code with master recovery theorem (zero sorry)
- `Quantum/` — QuantumPartitionBridge: free-energy Legendre identity
- `RiemannMetatron/` — Zeta structural facts + LogitGate + GUE conjecture statement

## Build (basic / “lame”)

```bash
lake build
```

Requires Lean 4 + Mathlib (see `lakefile.lean`).

## Attribution

Ahmad Ali Parr · Bel Esprit D'Accord Irrevocable Trust · EIN 42-697643  
BOW-Ω-φ-∂-2026
