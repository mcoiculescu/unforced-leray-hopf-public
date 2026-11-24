import UnforcedLeray.Units.B0146.LatticeSums
import UnforcedLeray.Units.B0147.Lattice
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Constructions
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Algebra.Order.Floor.Defs

/-!
# Part I, task `PartI:T08/4/1/1/5/1` (`qcJet_lattice1D_sup_loc`)

Source: `the November 2 reference manuscript`, lines 326-335 and 2217-2234.

Uniform bound for the one-dimensional Gaussian lattice sum over all periods `L ≥ L₀ > 0`.
The library lemma `UnforcedLeray.B0147.lattice1D_sup` covers only `L ≥ 1`. Here `m` is a
natural number with `m L₀ ≥ 1`. The index set `ℤ` is split into the `m` residue classes
`n = k m + j` (`Int.divModEquiv`). Each class is a lattice of period `m L ≥ 1`, so each
class sum is bounded by `2 + θ(β/8)`, and the total is `m (2 + θ(β/8))`.
-/

set_option autoImplicit false

namespace UnforcedLeray.Short.PartI

noncomputable section

/-- A natural multiplier `m ≥ 1` with `1 ≤ m L₀`. -/
lemma exists_nat_mul_ge_one {L₀ : ℝ} (hL₀ : 0 < L₀) :
    ∃ m : ℕ, 0 < m ∧ 1 ≤ (m : ℝ) * L₀ := by
  refine ⟨⌈1 / L₀⌉₊, Nat.ceil_pos.2 (by positivity), ?_⟩
  exact (div_le_iff₀ hL₀).1 (Nat.le_ceil _)

theorem qcJet_lattice1D_sup_loc {β L₀ : ℝ} (hβ : 0 < β) (hL₀ : 0 < L₀) : ∃ M : ℝ, ∀ L : ℝ, L₀ ≤ L → ∀ t : ℝ, ∑' n : ℤ, Real.exp (-(β * (t - n * L) ^ 2)) ≤ M := by
  obtain ⟨m, hm0, hmL₀⟩ := exists_nat_mul_ge_one hL₀
  have : NeZero m := ⟨hm0.ne'⟩
  refine ⟨m * (2 + UnforcedLeray.B0147.theta (β / 8)), fun L hL t => ?_⟩
  have hLpos : 0 < L := lt_of_lt_of_le hL₀ hL
  have hL0 : L ≠ 0 := hLpos.ne'
  have hmL : 1 ≤ (m : ℝ) * L :=
    hmL₀.trans (mul_le_mul_of_nonneg_left hL (Nat.cast_nonneg m))
  have hf : Summable (fun n : ℤ => Real.exp (-(β * (t - n * L) ^ 2))) :=
    UnforcedLeray.B0146.summable_exp_shift hβ hL0 t
  let e : ℤ ≃ Fin m × ℤ := (Int.divModEquiv m).trans (Equiv.prodComm _ _)
  have hsum : Summable (fun q : Fin m × ℤ => Real.exp (-(β * (t - ((e.symm q : ℤ) : ℝ) * L) ^ 2))) :=
    (Equiv.summable_iff e.symm).2 hf
  have key : ∑' n : ℤ, Real.exp (-(β * (t - n * L) ^ 2)) =
      ∑' q : Fin m × ℤ, Real.exp (-(β * (t - ((e.symm q : ℤ) : ℝ) * L) ^ 2)) :=
    (e.symm.tsum_eq (fun n : ℤ => Real.exp (-(β * (t - n * L) ^ 2)))).symm
  have hT : ∀ j : Fin m, ∑' k : ℤ, Real.exp (-(β * (t - ((e.symm (j, k) : ℤ) : ℝ) * L) ^ 2))
      ≤ 2 + UnforcedLeray.B0147.theta (β / 8) := by
    intro j
    have h := UnforcedLeray.B0147.lattice1D_sup hβ hmL (t - ((j : ℕ) : ℝ) * L)
    refine (tsum_congr fun k => ?_).trans_le h
    have he : ((e.symm (j, k) : ℤ) : ℝ) = (k : ℝ) * (m : ℝ) + ((j : ℕ) : ℝ) := by
      show (((k * (m : ℤ) + ((j : ℕ) : ℤ)) : ℤ) : ℝ) = _
      push_cast
      ring
    rw [he]
    congr 1
    ring
  rw [key, Summable.tsum_prod' hsum (fun j => hsum.prod_factor j), tsum_fintype]
  refine (Finset.sum_le_sum fun j _ => hT j).trans (le_of_eq ?_)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

end

end UnforcedLeray.Short.PartI
