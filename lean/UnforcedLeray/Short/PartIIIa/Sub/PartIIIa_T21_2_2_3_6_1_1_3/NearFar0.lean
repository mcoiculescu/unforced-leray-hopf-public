import UnforcedLeray.Short.PartIIIa.Sub.T21_2_1.Kernel.NearFar
import UnforcedLeray.Units.B0592
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_1.Kernel.DivPointwiseParts.RegDeriv

/-!
# `KerNearFar0`: the near/far split of the periodic kernel for every `d > 0`

Source: `the November 2 reference manuscript` lines 2117-2121, 2876-2881.
For fixed `d > 0` (constant depending on `d`): on the centred cell `‖K_d(z)‖ ≤ 1/(2d) + 1/(4‖z‖)`
(`B0592.norm_bsKernel_le_reduced`, transported through `cyl_formula`), and `‖z‖⁻¹` is integrable
on the unit ball (`B0592.integrable_nearKernel`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

/-- `KerNearFar` for every fixed `d > 0`. -/
def KerNearFar0 : Prop :=
  ∀ d : ℝ, 0 < d → ∃ C : ℝ, 0 ≤ C ∧
    (∀ j : Fin 2, Measurable fun z => kerD d z j) ∧
    (∀ (z : ℝ × ℝ) (j : Fin 2), kerD d (z.1 + d, z.2) j = kerD d z j) ∧
    (∀ (z : ℝ × ℝ) (j : Fin 2), kerD d (-z) j = -kerD d z j) ∧
    (∫⁻ z in B0579.cell d ∩ Metric.ball (0 : ℝ × ℝ) 1, ∑ j, ‖kerD d z j‖ₑ) ≤
      ENNReal.ofReal C ∧
    (∀ z ∈ B0579.cell d, z ∉ Metric.ball (0 : ℝ × ℝ) 1 → ∀ j, |kerD d z j| ≤ C)

theorem den_ne_zero_of_cell {d : ℝ} (hd : 0 < d) {z : ℝ × ℝ} (hz : |z.1| ≤ d / 2)
    (hz0 : z ≠ 0) : UnforcedLeray.B0592.den d z ≠ 0 := by
  intro h
  rw [UnforcedLeray.B0592.den_eq] at h
  have h1 : Real.sin (Real.pi * z.1 / d) ^ 2 = 0 := by
    nlinarith [sq_nonneg (Real.sin (Real.pi * z.1 / d)), sq_nonneg (Real.sinh (Real.pi * z.2 / d))]
  have h2 : Real.sinh (Real.pi * z.2 / d) ^ 2 = 0 := by
    nlinarith [sq_nonneg (Real.sin (Real.pi * z.1 / d)), sq_nonneg (Real.sinh (Real.pi * z.2 / d))]
  have h1' : Real.sin (Real.pi * z.1 / d) = 0 := pow_eq_zero_iff (by norm_num) |>.1 h1
  have h2' : Real.sinh (Real.pi * z.2 / d) = 0 := pow_eq_zero_iff (by norm_num) |>.1 h2
  have hη : z.2 = 0 := by
    rw [Real.sinh_eq_zero] at h2'
    have : Real.pi * z.2 = 0 := by field_simp at h2'; linarith
    rcases mul_eq_zero.1 this with h | h
    · exact absurd h Real.pi_ne_zero
    · exact h
  obtain ⟨n, hn⟩ := Real.sin_eq_zero_iff.1 h1'
  have hq : z.1 = n * d := by
    field_simp at hn
    linarith
  have hn0 : n = 0 := by
    have hab : |(n : ℝ)| * d ≤ d / 2 := by
      rw [hq, abs_mul, abs_of_pos hd] at hz
      exact hz
    have : |(n : ℝ)| ≤ 1 / 2 := by
      by_contra hc
      push Not at hc
      nlinarith
    have h3 : |n| < 1 := by
      have : (|n| : ℤ) < 1 := by
        have : ((|n| : ℤ) : ℝ) < 1 := by push_cast; linarith
        exact_mod_cast this
      exact this
    exact Int.abs_lt_one_iff.1 h3
  apply hz0
  ext
  · simp [hq, hn0]
  · simpa using hη

/-- `‖K_d(z)‖ ≤ 1/(2d) + 1/(4‖z‖)` on the centred cell, for the cylinder kernel `kerD`. -/
theorem norm_kerD_le {d : ℝ} (hd : 0 < d) {z : ℝ × ℝ} (hz : |z.1| ≤ d / 2) :
    ‖UnforcedLeray.Cyl.bsKernel d z‖ ≤ 1 / (2 * d) + 1 / (4 * ‖z‖) := by
  by_cases hz0 : z = 0
  · subst hz0
    have : UnforcedLeray.Cyl.bsC d (0, 0) = 0 := by
      simp [UnforcedLeray.Cyl.bsC, UnforcedLeray.Kernels.cylinderBS, Complex.cot_eq_cos_div_sin]
    rw [UnforcedLeray.Cyl.norm_bsKernel]
    show ‖UnforcedLeray.Cyl.bsC d (0, 0)‖ ≤ _
    rw [this]
    simp only [norm_zero, mul_zero, div_zero, add_zero]
    positivity
  · have hden := den_ne_zero_of_cell hd hz hz0
    have h := UnforcedLeray.B0592.norm_bsKernel_le_reduced hd hz
    have hcyl := cyl_formula d hd.ne' z.1 z.2 (by simpa using hden)
    have e : ‖UnforcedLeray.Cyl.bsKernel d z‖ = ‖UnforcedLeray.B0592.bsKernel d z‖ := by
      rw [UnforcedLeray.Cyl.norm_bsKernel]
      have hz' : z = (z.1, z.2) := rfl
      rw [hz', hcyl]
      have hB : ‖UnforcedLeray.B0592.bsKernel d z‖ =
          Real.sqrt ((-Real.sinh (2 * Real.pi * z.2 / d) / (2 * d * UnforcedLeray.B0592.den d z)) ^ 2 +
            (Real.sin (2 * Real.pi * z.1 / d) / (2 * d * UnforcedLeray.B0592.den d z)) ^ 2) := by
        rw [Complex.norm_eq_sqrt_sq_add_sq]; rfl
      rw [hB, Complex.norm_eq_sqrt_sq_add_sq]
      simp only [Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
        Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, mul_zero, mul_one, zero_add,
        add_zero, sub_zero, zero_sub, neg_sq]
    rw [e]
    exact h

theorem kerNearFar0 : KerNearFar0 := by
  intro d hd
  obtain ⟨C0, hC0, hall⟩ := kerNearFar
  set M : ℝ≥0∞ := ENNReal.ofReal (1 / (2 * d)) * volume (Metric.ball (0 : ℝ × ℝ) 1) +
      ENNReal.ofReal (1 / 4) * UnforcedLeray.B0592.nearMass with hM
  have hMtop : M < ⊤ := by
    have := UnforcedLeray.B0592.volume_isAddHaarMeasure
    exact ENNReal.add_lt_top.mpr ⟨ENNReal.mul_lt_top ENNReal.ofReal_lt_top measure_ball_lt_top,
      ENNReal.mul_lt_top ENNReal.ofReal_lt_top UnforcedLeray.B0592.lintegral_nearKernel_lt_top⟩
  refine ⟨2 * M.toReal + 1 / (2 * d) + 1 / 4, by positivity, ?_⟩
  have hcell : UnforcedLeray.B0579.cell d = UnforcedLeray.Cyl.cell d := cell_eq_Cyl' d
  have hmem : ∀ z ∈ UnforcedLeray.B0579.cell d, |z.1| ≤ d / 2 := by
    intro z hz
    simp only [UnforcedLeray.B0579.cell, Set.mem_prod, Set.mem_Ico, Set.mem_univ, and_true] at hz
    rw [abs_le]; constructor <;> linarith [hz.1, hz.2]
  have hcomp : ∀ (z : ℝ × ℝ) (j : Fin 2), ‖UnforcedLeray.Cyl.bsKernel d z j‖ ≤
      ‖UnforcedLeray.Cyl.bsKernel d z‖ := fun z j => PiLp.norm_apply_le _ _
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro j
    exact ((PiLp.continuous_apply 2 _ j).measurable).comp (UnforcedLeray.Cyl.measurable_bsKernel d)
  · intro z j
    show UnforcedLeray.Cyl.bsKernel d (z.1 + d, z.2) j = UnforcedLeray.Cyl.bsKernel d z j
    rw [UnforcedLeray.Cyl.isPeriodic_bsKernel d z]
  · intro z j
    exact bsKernel_neg' d z j
  · have hcm : MeasurableSet (UnforcedLeray.B0579.cell d) := by
      rw [hcell]; exact UnforcedLeray.Cyl.measurableSet_cell d
    have hmeas : MeasurableSet (UnforcedLeray.B0579.cell d ∩ Metric.ball (0 : ℝ × ℝ) 1) :=
      hcm.inter Metric.isOpen_ball.measurableSet
    have hpt : ∀ z ∈ UnforcedLeray.B0579.cell d ∩ Metric.ball (0 : ℝ × ℝ) 1,
        ∑ j, ‖kerD d z j‖ₑ ≤ 2 * (ENNReal.ofReal (1 / (2 * d)) +
          ENNReal.ofReal (1 / 4) * ENNReal.ofReal (UnforcedLeray.B0592.nearKernel z)) := by
      intro z hz
      have hz1 := hmem z hz.1
      have hb := norm_kerD_le hd hz1
      have hn : 1 / (4 * ‖z‖) ≤ 1 / 4 * UnforcedLeray.B0592.nearKernel z := by
        by_cases hz0 : z = 0
        · subst hz0
          simp only [norm_zero, mul_zero, div_zero]
          exact mul_nonneg (by norm_num) (UnforcedLeray.B0592.nearKernel_nonneg 0)
        · have hzn : ‖z‖ < 1 := mem_ball_zero_iff.1 hz.2
          have : UnforcedLeray.B0592.nearKernel z = ‖z‖⁻¹ := by
            unfold UnforcedLeray.B0592.nearKernel
            rw [Set.indicator_of_mem (by simpa using hzn)]
          rw [this]
          have e : 1 / (4 * ‖z‖) = 1 / 4 * ‖z‖⁻¹ := by ring
          rw [e]
      have hsum : ∑ j, ‖kerD d z j‖ₑ ≤ 2 * ‖UnforcedLeray.Cyl.bsKernel d z‖ₑ := by
        have h : ∀ j, ‖UnforcedLeray.Cyl.bsKernel d z j‖ₑ ≤ ‖UnforcedLeray.Cyl.bsKernel d z‖ₑ :=
          fun j => PiLp.enorm_apply_le _ j
        calc ∑ j, ‖kerD d z j‖ₑ ≤ ∑ _j : Fin 2, ‖UnforcedLeray.Cyl.bsKernel d z‖ₑ :=
              Finset.sum_le_sum fun j _ => h j
          _ = 2 * ‖UnforcedLeray.Cyl.bsKernel d z‖ₑ := by simp [two_mul]
      refine hsum.trans (mul_le_mul' le_rfl ?_)
      rw [← ofReal_norm, ← ENNReal.ofReal_mul (by norm_num),
        ← ENNReal.ofReal_add (by positivity)
          (mul_nonneg (by norm_num) (UnforcedLeray.B0592.nearKernel_nonneg z))]
      exact ENNReal.ofReal_le_ofReal (by linarith)
    calc ∫⁻ z in UnforcedLeray.B0579.cell d ∩ Metric.ball (0 : ℝ × ℝ) 1, ∑ j, ‖kerD d z j‖ₑ
        ≤ ∫⁻ z in UnforcedLeray.B0579.cell d ∩ Metric.ball (0 : ℝ × ℝ) 1,
            2 * (ENNReal.ofReal (1 / (2 * d)) +
              ENNReal.ofReal (1 / 4) * ENNReal.ofReal (UnforcedLeray.B0592.nearKernel z)) :=
          setLIntegral_mono' hmeas hpt
      _ ≤ ∫⁻ z in Metric.ball (0 : ℝ × ℝ) 1,
            2 * (ENNReal.ofReal (1 / (2 * d)) +
              ENNReal.ofReal (1 / 4) * ENNReal.ofReal (UnforcedLeray.B0592.nearKernel z)) :=
          lintegral_mono_set inter_subset_right
      _ ≤ 2 * M := by
          have hmn : Measurable fun z : ℝ × ℝ =>
              ENNReal.ofReal (UnforcedLeray.B0592.nearKernel z) :=
            ENNReal.measurable_ofReal.comp UnforcedLeray.B0592.measurable_nearKernel
          rw [lintegral_const_mul' _ _ (by simp), lintegral_add_left measurable_const,
            lintegral_const, Measure.restrict_apply_univ, lintegral_const_mul _ hmn, hM]
          exact mul_le_mul' le_rfl (add_le_add le_rfl (mul_le_mul_right
            (setLIntegral_le_lintegral _ _) _))
      _ ≤ ENNReal.ofReal (2 * M.toReal + 1 / (2 * d) + 1 / 4) := by
          have h2 : 2 * M = ENNReal.ofReal (2 * M.toReal) := by
            rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_toReal hMtop.ne]
            simp
          rw [h2]
          exact ENNReal.ofReal_le_ofReal (by
            have : 0 < 1 / (2 * d) := by positivity
            linarith)
  · intro z hz hball j
    have h1 : 1 ≤ ‖z‖ := not_lt.1 (fun h => hball (mem_ball_zero_iff.2 h))
    have hb := norm_kerD_le hd (hmem z hz)
    have : 1 / (4 * ‖z‖) ≤ 1 / 4 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
    calc |kerD d z j| = ‖UnforcedLeray.Cyl.bsKernel d z j‖ := (Real.norm_eq_abs _).symm
      _ ≤ _ := hcomp z j
      _ ≤ _ := hb
      _ ≤ 2 * M.toReal + 1 / (2 * d) + 1 / 4 := by
          have : 0 ≤ M.toReal := ENNReal.toReal_nonneg
          linarith

end UnforcedLeray.Short.IIIa
