import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.CylinderHelmholtz.PlaneHelmholtz.RieszFamily.Defs
import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.CylinderHelmholtz.PlaneHelmholtz.RieszFamily.RieszTestContDiff
import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.CylinderHelmholtz.PlaneHelmholtz.RieszFamily.RieszTestDecay
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.MeasureTheory.Function.L2Space

/-!
# Leaf `PartII-b:T12/1/1/2/23`: the test-level Riesz pairs are in `L²`

Source of record: `the November 2 reference manuscript`, line 1670 (`P_0`, the
ordinary planar cylinder projection) and lines 1923-1926 (`P_0` in the causal formula); classical
Calderón-Zygmund theory (Grafakos, *Classical Fourier Analysis*, Cor. 5.2.8).

`S_{ik} f` is continuous (`RieszTestContDiff`) and satisfies `|S_{ik} f(x)| ≤ C ‖x‖⁻²` for
`‖x‖ ≥ R` (`RieszTestDecay`).  Such a function is dominated by a multiple of the planar weight
`(1 + ‖x‖)⁻²`, which is square integrable on the plane since `4 > 2 = finrank`.  The 3D analogue
is `memLp_rieszPairTest` in `Lib/CZL2/RieszL2.lean`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set Metric
open scoped ContDiff ENNReal NNReal Topology

namespace UnforcedLeray.Short.IIb.PlaneRiesz

/-- The planar weight `(1 + ‖x‖)⁻²`. -/
def planeDecayWeight (x : Pl) : ℝ := ((1 + ‖x‖) ^ 2)⁻¹

theorem planeDecayWeight_pos (x : Pl) : 0 < planeDecayWeight x := by
  unfold planeDecayWeight; positivity

theorem continuous_planeDecayWeight : Continuous planeDecayWeight := by
  unfold planeDecayWeight
  exact (continuous_const.add continuous_norm).pow 2 |>.inv₀
    fun x => pow_ne_zero 2 (ne_of_gt (add_pos_of_pos_of_nonneg one_pos (norm_nonneg x)))

/-- `(1 + ‖x‖)⁻²` is square integrable on the plane: `∫ (1 + ‖x‖)⁻⁴ < ∞` as `4 > 2`. -/
theorem memLp_planeDecayWeight : MemLp planeDecayWeight 2 volume := by
  have hm : AEStronglyMeasurable planeDecayWeight volume :=
    continuous_planeDecayWeight.aestronglyMeasurable
  refine (memLp_two_iff_integrable_sq hm).2 ?_
  have hi : Integrable (fun x : Pl => (1 + ‖x‖) ^ (-(4 : ℝ))) volume :=
    integrable_one_add_norm (by simp; norm_num)
  refine hi.congr (Eventually.of_forall fun x => ?_)
  have h1 : 0 < 1 + ‖x‖ := by positivity
  simp only [planeDecayWeight]
  rw [Real.rpow_neg h1.le, show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  rw [inv_pow, ← pow_mul]

/-- **Leaf `PartII-b:T12/1/1/2/23`.**  `S_{ik} f ∈ L²` for a planar test `f`. -/
theorem rieszTestMemLp : RieszTestMemLp := by
  intro i k f hf
  have hcont : Continuous (rieszTest i k f) := (rieszTestContDiff i k f hf).continuous
  obtain ⟨C, R, hCR⟩ := rieszTestDecay i k f hf
  -- the constant on the compact ball of radius `R' = max R 1`
  set R' : ℝ := max R 1 with hR'
  have hR'1 : 1 ≤ R' := le_max_right _ _
  have hRR' : R ≤ R' := le_max_left _ _
  obtain ⟨B, hB⟩ := (isCompact_closedBall (0 : Pl) R').exists_bound_of_continuousOn
    hcont.continuousOn
  have hB0 : 0 ≤ max B 0 := le_max_right _ _
  have hC0 : 0 ≤ max C 0 := le_max_right _ _
  have hpt : ∀ x : Pl, ‖rieszTest i k f x‖ ≤
      (max B 0 * (1 + R') ^ 2 + 4 * max C 0) * planeDecayWeight x := by
    intro x
    have hw := planeDecayWeight_pos x
    by_cases hx : ‖x‖ ≤ R'
    · -- near the origin: bounded by the continuity bound
      have hxB : ‖rieszTest i k f x‖ ≤ B :=
        hB x (by simpa [mem_closedBall, dist_zero_right] using hx)
      have h1 : 1 ≤ (1 + R') ^ 2 * planeDecayWeight x := by
        unfold planeDecayWeight
        rw [← div_eq_mul_inv, one_le_div (by positivity)]
        exact pow_le_pow_left₀ (by positivity) (by linarith) 2
      have h2 : max B 0 ≤ max B 0 * ((1 + R') ^ 2 * planeDecayWeight x) := by
        have := mul_le_mul_of_nonneg_left h1 hB0
        linarith
      have h3 : 0 ≤ 4 * max C 0 * planeDecayWeight x := by positivity
      nlinarith [le_max_left B 0]
    · -- far field: the decay bound `C ‖x‖⁻²`
      push Not at hx
      have hx1 : 1 ≤ ‖x‖ := by linarith
      have hx0 : 0 < ‖x‖ := by linarith
      have hd := hCR x (by linarith)
      rw [Real.rpow_neg (norm_nonneg x), Real.rpow_two] at hd
      have h3 : (‖x‖ ^ 2)⁻¹ ≤ 4 * planeDecayWeight x := by
        unfold planeDecayWeight
        have hsq : (1 + ‖x‖) ^ 2 ≤ 4 * ‖x‖ ^ 2 := by nlinarith
        calc (‖x‖ ^ 2)⁻¹ = 4 * (4 * ‖x‖ ^ 2)⁻¹ := by
              rw [mul_inv, ← mul_assoc, mul_inv_cancel₀ (by norm_num : (4 : ℝ) ≠ 0), one_mul]
          _ ≤ 4 * ((1 + ‖x‖) ^ 2)⁻¹ :=
              mul_le_mul_of_nonneg_left (inv_anti₀ (by positivity) hsq) (by norm_num)
      have h4 : C * (‖x‖ ^ 2)⁻¹ ≤ max C 0 * (‖x‖ ^ 2)⁻¹ :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
      have h5 : max C 0 * (‖x‖ ^ 2)⁻¹ ≤ max C 0 * (4 * planeDecayWeight x) :=
        mul_le_mul_of_nonneg_left h3 hC0
      have h6 : 0 ≤ max B 0 * (1 + R') ^ 2 * planeDecayWeight x := by positivity
      rw [Real.norm_eq_abs]
      nlinarith
  refine (memLp_planeDecayWeight.const_mul
    (max B 0 * (1 + R') ^ 2 + 4 * max C 0)).of_le hcont.aestronglyMeasurable
    (Eventually.of_forall fun x => ?_)
  have hM : 0 ≤ max B 0 * (1 + R') ^ 2 + 4 * max C 0 :=
    add_nonneg (mul_nonneg hB0 (by positivity)) (mul_nonneg (by norm_num) hC0)
  rw [Real.norm_of_nonneg (mul_nonneg hM (planeDecayWeight_pos x).le)]
  exact hpt x

end UnforcedLeray.Short.IIb.PlaneRiesz
