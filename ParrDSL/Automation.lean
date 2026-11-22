/-
Copyright (c) 2026 Ahmad Ali Parr / Bel Esprit D'Accord Irrevocable Trust (EIN 42-697643).
Released under the GNU Affero General Public License v3.0 or later.
See the file LICENSE for details.
Authors: Ahmad Ali Parr
BOW-Ω-φ-∂-2026
-/

/-!
# ParrDSL — Domain-specific proof automation

Reusable lemma bundles and simp sets for the Parr Conjecture domain:

* `parr_j3o_simps` — structural simp lemmas for `J3O` / `Octonion`
* `parr_fts_simps` — structural simp lemmas for `FTS56` / `I4` / `symp`
* `parr_homog_lemmas` — homogeneity family
* `parr_bitflip_lemmas` — syndrome / recovery family

These can be used manually (`simp [parr_j3o_simps]`) or via the
`parr_*` tactics in `ParrDSL.Tactics`.
-/

import GKN.I4_CommRing
import BitFlipCode.BitFlipCode
import RiemannMetatron.RiemannMetatron
import Mathlib.Tactic

open GKN_I4_CommRing

namespace ParrDSL

-- ══════════════════════════════════════════════════════════════
-- 1. Simp sets
-- ══════════════════════════════════════════════════════════════

/-- Structural simplification for octonions and J₃(𝕆). -/
lemma parr_j3o_simps_smul_d {R : Type*} [CommRing R] (r : R) (M : J3O R) (i : Fin 3) :
    (r • M).d i = r * M.d i := J3O.smul_d r M i

lemma parr_j3o_simps_smul_o {R : Type*} [CommRing R] (r : R) (M : J3O R) (k : Fin 3) :
    (r • M).o k = r • M.o k := J3O.smul_o r M k

lemma parr_j3o_simps_normSq_smul {R : Type*} [CommRing R] (r : R) (a : Octonion R) :
    Octonion.normSq (r • a) = r ^ 2 * Octonion.normSq a := Octonion.normSq_smul r a

lemma parr_j3o_simps_realPart_smul {R : Type*} [CommRing R] (r : R) (a : Octonion R) :
    Octonion.realPart (r • a) = r * Octonion.realPart a := Octonion.realPart_smul r a

/-- Homogeneity of cubic norm (degree 3). -/
lemma parr_cubicNorm_homog {R : Type*} [CommRing R] (r : R) (M : J3O R) :
    J3O.cubicNorm (r • M) = r ^ 3 * J3O.cubicNorm M := J3O.cubicNorm_smul r M

/-- Homogeneity of adjoint (degree 2). -/
lemma parr_adjoint_homog {R : Type*} [CommRing R] (r : R) (M : J3O R) :
    J3O.adjoint (r • M) = r ^ 2 • J3O.adjoint M := J3O.adjoint_smul r M

/-- I₄ homogeneity (degree 4) — the central GKN identity. -/
lemma parr_I4_homog {R : Type*} [CommRing R] (c : R) (s : FTS56 R) :
    FTS56.I4 (c • s) = c ^ 4 * FTS56.I4 s := FTS56.I4_homogeneous c s

/-- Symplectic form is alternating. -/
lemma parr_symp_alt {R : Type*} [CommRing R] (s : FTS56 R) :
    FTS56.symp s s = 0 := FTS56.symp_self s

/-- Symplectic form is antisymmetric. -/
lemma parr_symp_antisym {R : Type*} [CommRing R] (s t : FTS56 R) :
    FTS56.symp s t = -(FTS56.symp t s) := FTS56.symp_antisym s t

/-- Bit-flip master recovery. -/
lemma parr_bitflip_recover (b : Bool) (i : Fin 3) :
    BitFlipCode.decode
      (BitFlipCode.correct
        (BitFlipCode.syndrome (BitFlipCode.xError i (BitFlipCode.encode b)))
        (BitFlipCode.xError i (BitFlipCode.encode b))) = b :=
  BitFlipCode.recover_single_x b i

/-- Gates normalisation (logit simplex sums to 1). -/
lemma parr_gates_norm (g : RiemannMetatron.LogitGate) :
    ∑ i : Fin g.vocab_size, RiemannMetatron.logitSimplex g i = 1 :=
  RiemannMetatron.logit_simplex_sums_to_one g

/-- Critical strip is open. -/
lemma parr_critical_strip_open : IsOpen RiemannMetatron.criticalStrip :=
  RiemannMetatron.critical_strip_is_open

-- ══════════════════════════════════════════════════════════════
-- 2. Named lemma lists for `simp only [...]`
-- ══════════════════════════════════════════════════════════════

/-- Bundle: homogeneity lemmas. -/
def homogLemmaNames : List Name :=
  [``parr_I4_homog, ``parr_cubicNorm_homog, ``parr_adjoint_homog,
   ``FTS56.I4_homogeneous, ``J3O.cubicNorm_smul, ``J3O.adjoint_smul]

/-- Bundle: symplectic lemmas. -/
def sympLemmaNames : List Name :=
  [``parr_symp_alt, ``parr_symp_antisym, ``FTS56.symp_self, ``FTS56.symp_antisym]

/-- Bundle: bit-flip recovery. -/
def bitflipLemmaNames : List Name :=
  [``parr_bitflip_recover, ``BitFlipCode.recover_single_x,
   ``BitFlipCode.recover_no_error, ``BitFlipCode.syndrome_no_error]

end ParrDSL
