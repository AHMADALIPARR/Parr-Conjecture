import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

open Real Finset BigOperators

namespace QuantumPartitionBridge

/-- Partition function Z_β = ∑_i exp(-β · H(i)). -/
noncomputable def partZ {n : ℕ} (H : Fin n → ℝ) (β : ℝ) : ℝ :=
  ∑ i : Fin n, exp (-β * H i)

/-- Partition function is strictly positive. -/
lemma partZ_pos {n : ℕ} (hn : 0 < n) (H : Fin n → ℝ) (β : ℝ) :
    0 < partZ H β := by
  have i₀ : Fin n := ⟨0, hn⟩
  have h₀ : i₀ ∈ Finset.univ := Finset.mem_univ i₀
  have hle := Finset.single_le_sum (s := Finset.univ) (f := fun i => exp (-β * H i))
    (fun i _ => (exp_pos _).le) h₀
  exact lt_of_lt_of_le (exp_pos _) hle

/-- Gibbs state: ρ_β(i) = exp(-β · H(i)) / Z_β. -/
noncomputable def gibbs {n : ℕ} (H : Fin n → ℝ) (β : ℝ) : Fin n → ℝ :=
  fun i => exp (-β * H i) / partZ H β

/-- Free energy: F_β = -(1/β) · log(Z_β). -/
noncomputable def freeE {n : ℕ} (H : Fin n → ℝ) (β : ℝ) : ℝ :=
  -(1 / β) * Real.log (partZ H β)

/-- Expectation: ⟨H⟩_ρ = ∑_i ρ(i) · H(i). -/
noncomputable def expH {n : ℕ} (H : Fin n → ℝ) (ρ : Fin n → ℝ) : ℝ :=
  ∑ i : Fin n, ρ i * H i

/-- Von Neumann entropy: S_vN(ρ) = -∑_i ρ(i) · log(ρ(i)). -/
noncomputable def SvN {n : ℕ} (ρ : Fin n → ℝ) : ℝ :=
  -∑ i : Fin n, ρ i * Real.log (ρ i)

/-! ## Core identity: S_vN = β·⟨H⟩ + log Z -/

private lemma log_div_exp (a b : ℝ) (ha : 0 < a) (hb : b ≠ 0) :
    Real.log (a / b) = Real.log a - Real.log b :=
  Real.log_div ha.ne' hb

/-- S_vN(ρ_β) = β · ⟨H⟩ + log Z. -/
lemma entropy_eq {n : ℕ} (hn : 0 < n) (H : Fin n → ℝ) (β : ℝ) :
    SvN (gibbs H β) = β * expH H (gibbs H β) + Real.log (partZ H β) := by
  have hZpos : 0 < partZ H β := partZ_pos hn H β
  have hZne : partZ H β ≠ 0 := hZpos.ne'
  simp only [SvN, expH, gibbs, partZ]
  -- Key identity for each summand
  have key : ∀ i : Fin n, ∀ Z : ℝ,
      -(exp (-β * H i) / Z) * Real.log (exp (-β * H i) / Z) =
        (exp (-β * H i) / Z) * (β * H i) +
          (exp (-β * H i) / Z) * Real.log Z := by
    intro i Z
    by_cases hZ : Z = 0
    · simp [hZ]
    · rw [log_div_exp (exp _) _ (exp_pos _) hZ, Real.log_exp]
      ring
  -- Apply key with Z = ∑ j, exp (-β * H j)
  have hZne' : (∑ j : Fin n, exp (-β * H j)) ≠ 0 := hZne
  -- Pull negation out, then use sum_congr
  rw [← Finset.sum_neg_distrib]
  -- Each term: -(e_i/Z)·log(e_i/Z) = (e_i/Z)·βH_i + (e_i/Z)·logZ
  have h2 : ∀ i : Fin n,
      (exp (-β * H i) / ∑ j, exp (-β * H j)) * (β * H i) +
        (exp (-β * H i) / ∑ j, exp (-β * H j)) * Real.log (∑ j, exp (-β * H j)) =
      -((exp (-β * H i) / ∑ j, exp (-β * H j)) *
          Real.log (exp (-β * H i) / ∑ j, exp (-β * H j))) := by
    intro i
    have := key i (∑ j, exp (-β * H j))
    linarith [this]
  rw [Finset.sum_congr rfl (fun i _ => (h2 i).symm)]
  rw [Finset.sum_add_distrib]
  -- First sum: ∑ (e_i/Z)(βH_i) = β ∑ (e_i/Z) H_i
  have h1 : ∑ x : Fin n, (exp (-β * H x) / ∑ j, exp (-β * H j)) * (β * H x) =
      β * ∑ x : Fin n, (exp (-β * H x) / ∑ j, exp (-β * H j)) * H x := by
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _; ring
  -- Second sum: ∑ (e_i/Z) logZ = logZ
  have h2' : ∑ x : Fin n, (exp (-β * H x) / ∑ j, exp (-β * H j)) * Real.log (∑ j, exp (-β * H j)) =
      Real.log (∑ j, exp (-β * H j)) := by
    have hsum : ∑ x : Fin n, (exp (-β * H x) / ∑ j, exp (-β * H j)) = 1 := by
      rw [← Finset.sum_div]
      exact div_self hZne'
    rw [show (∑ x, (exp (-β * H x) / ∑ j, exp (-β * H j)) * Real.log (∑ j, exp (-β * H j))) =
        Real.log (∑ j, exp (-β * H j)) * ∑ x, (exp (-β * H x) / ∑ j, exp (-β * H j)) from by
      rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro x _; ring]
    rw [hsum, mul_one]
  rw [h1, h2']

/-! ## Main theorem -/

/-- **Legendre duality**: F_β = ⟨H⟩_ρ − (1/β) · S_vN(ρ). -/
theorem free_energy_legendre {n : ℕ} (hn : 0 < n) (H : Fin n → ℝ) (β : ℝ) (hβ : 0 < β) :
    freeE H β = expH H (gibbs H β) - (1 / β) * SvN (gibbs H β) := by
  rw [freeE, entropy_eq hn H β]
  have hβne : (β : ℝ) ≠ 0 := ne_of_gt hβ
  field_simp
  ring

end QuantumPartitionBridge
