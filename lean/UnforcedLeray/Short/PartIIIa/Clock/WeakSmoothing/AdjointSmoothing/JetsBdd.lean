import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_7_2
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_6

/-!
# Weighted jets of BUC trains for the adjoint smoothing (`PartIII-a:T21/2/7/2/5`)

Source of record: `the November 2 reference manuscript` (SP), lines 2866-2873
(weighted jets of the train), 3050-3051 (`TrainWeightedJetPoly`).

`TrainWeightedJetPoly` gives, for each pair of orders `(k, j)`, its own threshold `ν₀` depending on
`j`. Since `TrainJetsBddAll` asks for one `ν₀` for all the orders `j ≤ 6`, we take the minimum of
the finitely many thresholds, and the constant `C` of `TrainJetsBdd` is the finite sum of the
per-order constants (the constant of `TrainJetsBdd tr m S` may depend on the fixed train `tr`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

/-- A finite minimum of positive reals is positive: for a sequence of positive reals `f`, some
`ε > 0` lies below `f j` for all `j < n`. -/
lemma jetsBdd_finite_min (f : ℕ → ℝ) (hf : ∀ j, 0 < f j) (n : ℕ) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ j < n, ε ≤ f j := by
  induction n with
  | zero => exact ⟨1, one_pos, fun j hj => absurd hj (Nat.not_lt_zero _)⟩
  | succ n ih =>
    obtain ⟨ε, hε, h⟩ := ih
    refine ⟨min ε (f n), lt_min hε (hf n), fun j hj => ?_⟩
    rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj' | hj'
    · exact (min_le_left _ _).trans (h j hj')
    · rw [hj']
      exact min_le_right _ _

/-- **Weighted jets of BUC trains** (SP 2866-2873, 3050-3051, `PartIII-a:T21/2/7/2/5`): the target
`TrainJetsBddAll m` follows from the polynomial weighted jet bound `TrainWeightedJetPoly`, taking
the minimum of the thresholds of the orders `j ≤ 6`. -/
theorem trainJetsBddAll (m : ℝ) (hW : UnforcedLeray.Short.IIIa.TrainWeightedJetPoly) :
    UnforcedLeray.Short.IIIa.TrainJetsBddAll m := by
  set k : ℕ := ⌈max 0 ((m + 2) / 2)⌉₊ with hk
  have hW' : ∀ j : ℕ, ∃ (C : ℝ) (N : ℕ) (ν₀ : ℝ), 0 < ν₀ ∧ ∀ ν ∈ Ioc 0 ν₀,
      ∀ tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ)),
        UnforcedLeray.Short.PartI.IsBUCTrain tr → ∀ s : ℝ, 0 ≤ s → ∀ x : ℝ × ℝ,
          (1 + x.2 ^ 2) ^ k * ‖iteratedFDeriv ℝ j (tr.v s) x‖ ≤ C * ν⁻¹ ^ N * (1 + s) ^ N :=
    fun j => hW k j
  choose C N ν₀ hν₀ hbd using hW'
  obtain ⟨ε, hε, hεle⟩ := jetsBdd_finite_min ν₀ hν₀ 7
  refine ⟨ε, hε, fun ν hν tr htr S hS => ?_⟩
  unfold UnforcedLeray.Short.IIIa.TrainJetsBdd
  refine ⟨∑ j ∈ Finset.range 7,
    |C j| * ν⁻¹ ^ (N j) * (1 + S) ^ (N j), fun j hj ρ hρ x => ?_⟩
  have hjmem : j ∈ Finset.range 7 := Finset.mem_range.2 (by omega)
  have hν' : ν ∈ Ioc 0 (ν₀ j) := ⟨hν.1, hν.2.trans (hεle j (Finset.mem_range.1 hjmem))⟩
  have hρ0 : 0 ≤ ρ := hρ.1
  have hρS : ρ ≤ S := hρ.2
  have hnu : 0 ≤ ν⁻¹ ^ (N j) := pow_nonneg (inv_nonneg.2 hν.1.le) (N j)
  have hpowS : (1 + ρ) ^ (N j) ≤ (1 + S) ^ (N j) :=
    pow_le_pow_left₀ (by linarith) (by linarith) (N j)
  have hterm : ∀ i ∈ Finset.range 7,
      0 ≤ |C i| * ν⁻¹ ^ (N i) * (1 + S) ^ (N i) := by
    intro i _
    exact mul_nonneg (mul_nonneg (abs_nonneg _) (pow_nonneg (inv_nonneg.2 hν.1.le) _))
      (pow_nonneg (by linarith) _)
  calc (1 + x.2 ^ 2) ^ k * ‖iteratedFDeriv ℝ j (tr.v ρ) x‖
      ≤ C j * ν⁻¹ ^ (N j) * (1 + ρ) ^ (N j) :=
        hbd j ν hν' tr htr ρ hρ0 x
    _ ≤ |C j| * ν⁻¹ ^ (N j) * (1 + ρ) ^ (N j) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self _) hnu)
          (pow_nonneg (by linarith) _)
    _ ≤ |C j| * ν⁻¹ ^ (N j) * (1 + S) ^ (N j) :=
        mul_le_mul_of_nonneg_left hpowS (mul_nonneg (abs_nonneg _) hnu)
    _ ≤ ∑ i ∈ Finset.range 7, |C i| * ν⁻¹ ^ (N i) * (1 + S) ^ (N i) :=
        Finset.single_le_sum (f := fun i => |C i| * ν⁻¹ ^ (N i) * (1 + S) ^ (N i))
          hterm hjmem

end UnforcedLeray.Short.IIIa
