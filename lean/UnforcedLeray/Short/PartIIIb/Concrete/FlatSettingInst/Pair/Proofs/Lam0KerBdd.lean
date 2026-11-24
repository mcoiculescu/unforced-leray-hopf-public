import UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst.Pair.Defs
import UnforcedLeray.Lib.Gaussian.Periodization
import UnforcedLeray.Short.PartIIIa.Clock.Frame

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal ComplexConjugate

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst.Pair

/-- **The dual kernels are bounded on the cell, uniformly in the age** (source 2896-2899). -/
theorem lam0KerBdd :
    UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst.Pair.Lam0KerBdd := by
  intro κ ν c k hν hc
  obtain ⟨C, hC⟩ := κ.lamP_decay
  have hc0 : (0 : ℝ) < c := by linarith
  have hsumG : Summable (fun n : ℤ => max C 0 * (1 + |(n : ℝ)|) ^ (-(2 : ℝ))) :=
    (UnforcedLeray.Gaussian.summable_one_add_abs_int_rpow (s := 2) (by norm_num)).mul_left _
  refine ⟨3 * ∑' n : ℤ, max C 0 * (1 + |(n : ℝ)|) ^ (-(2 : ℝ)), fun s x hx => ?_⟩
  obtain ⟨hlo, hhi⟩ := Set.mem_Ico.1 (Set.mem_prod.1 hx).1
  have hA : 1 ≤ bandA ν s ∧ bandA ν s ≤ 3 := by
    simp only [bandA, IIIa.clockA, bandAge, flatSigma]
    have h0 : 0 ≤ max 0 (min s (2 / ν)) := le_max_left _ _
    have h1 : max 0 (min s (2 / ν)) ≤ 2 / ν :=
      max_le (by positivity) (min_le_right _ _)
    have h2 : ν * (2 / ν) = 2 := by field_simp
    constructor
    · nlinarith [mul_nonneg hν.le h0]
    · nlinarith [mul_le_mul_of_nonneg_left h1 hν.le]
  obtain ⟨a1, a3⟩ := hA
  have hapos : (0 : ℝ) < bandA ν s := by linarith
  have hr_pos : (0 : ℝ) < Real.sqrt (bandA ν s) := Real.sqrt_pos.2 hapos
  have hr2 : Real.sqrt (bandA ν s) ≤ 2 := by
    nlinarith [Real.sq_sqrt hapos.le, Real.sqrt_nonneg (bandA ν s)]
  have hsq2 : Real.sqrt (bandA ν s) ^ 2 = bandA ν s := Real.sq_sqrt hapos.le
  have hterm : ∀ n : ℤ,
      ‖κ.lamP k (x.1 / Real.sqrt (bandA ν s) + n * (c / Real.sqrt (bandA ν s)),
          x.2 / Real.sqrt (bandA ν s))‖ ≤ max C 0 * (1 + |(n : ℝ)|) ^ (-(2 : ℝ)) := by
    intro n
    have hu : x.1 / Real.sqrt (bandA ν s) + (n : ℝ) * (c / Real.sqrt (bandA ν s)) =
        (x.1 + n * c) / Real.sqrt (bandA ν s) := by ring
    have hnle : |(n : ℝ)| ≤ |x.1 / Real.sqrt (bandA ν s) + (n : ℝ) * (c / Real.sqrt (bandA ν s))| := by
      rw [hu, abs_div, abs_of_pos hr_pos, le_div_iff₀ hr_pos]
      rcases eq_or_ne n 0 with h0 | h0
      · subst h0
        simp
      · have hn1 : (1 : ℝ) ≤ |(n : ℝ)| := by
          rw [← Int.cast_abs]
          exact_mod_cast Int.one_le_abs h0
        have key1 : |(n : ℝ)| * c - c / 2 ≤ |x.1 + n * c| := by
          rcases le_total 0 (n : ℝ) with hn0 | hn0
          · rw [abs_of_nonneg hn0]
            linarith [le_abs_self (x.1 + n * c)]
          · rw [abs_of_nonpos hn0]
            linarith [neg_le_abs (x.1 + n * c)]
        nlinarith [mul_le_mul_of_nonneg_left hr2 (abs_nonneg (n : ℝ)),
          mul_nonneg (sub_nonneg.2 hn1) (show (0 : ℝ) ≤ c - 2 by linarith)]
    have hinv : (1 + |x.1 / Real.sqrt (bandA ν s) + (n : ℝ) * (c / Real.sqrt (bandA ν s))|
          + |x.2 / Real.sqrt (bandA ν s)|)⁻¹ ≤ (1 + |(n : ℝ)|)⁻¹ := by
      apply inv_anti₀ (by positivity)
      linarith [hnle, abs_nonneg (x.2 / Real.sqrt (bandA ν s))]
    calc _ ≤ max C 0 * (1 + |x.1 / Real.sqrt (bandA ν s) + (n : ℝ) * (c / Real.sqrt (bandA ν s))|
            + |x.2 / Real.sqrt (bandA ν s)|)⁻¹ ^ 2 :=
          (hC k _).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (sq_nonneg _))
      _ ≤ max C 0 * ((1 + |(n : ℝ)|)⁻¹) ^ 2 :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hinv 2) (le_max_right _ _)
      _ = max C 0 * (1 + |(n : ℝ)|) ^ (-(2 : ℝ)) := by
          rw [Real.rpow_neg (by positivity), Real.rpow_two, inv_pow]
  have hsumN : Summable (fun n : ℤ =>
      ‖κ.lamP k (x.1 / Real.sqrt (bandA ν s) + n * (c / Real.sqrt (bandA ν s)),
          x.2 / Real.sqrt (bandA ν s))‖) :=
    Summable.of_nonneg_of_le (fun n => norm_nonneg _) hterm hsumG
  have hbd : ‖∑' n : ℤ, κ.lamP k (x.1 / Real.sqrt (bandA ν s) + n * (c / Real.sqrt (bandA ν s)),
          x.2 / Real.sqrt (bandA ν s))‖ ≤
      ∑' n : ℤ, max C 0 * (1 + |(n : ℝ)|) ^ (-(2 : ℝ)) :=
    (norm_tsum_le_tsum_norm hsumN).trans (Summable.tsum_le_tsum hterm hsumN hsumG)
  have hq : lam0Ker κ ν c k s x = (bandA ν s : ℂ) * ∑' n : ℤ,
        κ.lamP k (x.1 / Real.sqrt (bandA ν s) + n * (c / Real.sqrt (bandA ν s)),
          x.2 / Real.sqrt (bandA ν s)) := rfl
  rw [hq, norm_mul, Complex.norm_real, Real.norm_of_nonneg (by linarith : (0 : ℝ) ≤ bandA ν s)]
  calc bandA ν s * ‖∑' n : ℤ, κ.lamP k (x.1 / Real.sqrt (bandA ν s) + n * (c / Real.sqrt (bandA ν s)),
          x.2 / Real.sqrt (bandA ν s))‖
      ≤ 3 * ‖∑' n : ℤ, κ.lamP k (x.1 / Real.sqrt (bandA ν s) + n * (c / Real.sqrt (bandA ν s)),
          x.2 / Real.sqrt (bandA ν s))‖ :=
        mul_le_mul_of_nonneg_right a3 (norm_nonneg _)
    _ ≤ 3 * ∑' n : ℤ, max C 0 * (1 + |(n : ℝ)|) ^ (-(2 : ℝ)) :=
        mul_le_mul_of_nonneg_left hbd (by norm_num)

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst.Pair
