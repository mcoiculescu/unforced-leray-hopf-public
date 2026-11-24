import UnforcedLeray.Short.PartI.Sub.T02_4

/-!
# Part I, task `PartI:T02/4`: weighted integrability on the cell (`SechMomentIntegrable`)

Source of record: `the November 2 reference manuscript`, lines 276-288 (the
`sech` first moment on the cell, used by the parabolic barrier).

The target `sechMomentIntegrable` proves `SechMomentIntegrable` (`Short/PartI/Sub/T02_4.lean`):
for continuous `f` with `|f z| ≤ C (cosh(a η))⁻¹`, the function `(1 + |η|) |f|` is integrable over
`Cyl.cell c = [-c/2, c/2) × ℝ`.

Proof outline.  With `M = 1 + 12/a³` one has `(1 + |η|)(1 + η²) ≤ 3 M cosh(aη)` (`smKey`, from
`cosh(aη) ≥ a³|η|³/12` and `cosh ≥ 1`).  Hence the pointwise domination
`(1 + |η|) |f z| ≤ 3 M |C| (1 + η²)⁻¹` (`smPoint`).  The dominating function does not depend on
`q`.  It is integrable on the cell because the `q`-factor is the constant `1` on the finite-length
interval `[-c/2, c/2)`, and `η ↦ (1 + η²)⁻¹` is integrable on `ℝ` (`integrable_inv_one_add_sq`).
Helpers are prefixed `sm`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory

namespace UnforcedLeray.Short.PartI

open UnforcedLeray
open UnforcedLeray.Cyl (Plane)

/-- `cosh(aη) ≥ a³|η|³/12` for `a > 0`: from `e^s ≥ s³/6` (`s = a|η| ≥ 0`) and
`cosh x ≥ e^{|x|}/2`. -/
theorem smCosh_ge_cube (a η : ℝ) (ha : 0 < a) :
    a ^ 3 * |η| ^ 3 / 12 ≤ Real.cosh (a * η) := by
  have hs : 0 ≤ a * |η| := mul_nonneg ha.le (abs_nonneg η)
  have hexp : (a * |η|) ^ 3 / 6 ≤ Real.exp (a * |η|) := by
    have h := Real.pow_div_factorial_le_exp (a * |η|) hs 3
    have h6 : ((Nat.factorial 3 : ℕ) : ℝ) = 6 := by norm_num [Nat.factorial]
    rw [h6] at h
    exact h
  have hcosh : Real.exp (a * |η|) / 2 ≤ Real.cosh (a * |η|) := by
    rw [Real.cosh_eq]
    have := Real.exp_pos (-(a * |η|))
    linarith
  have hcc : Real.cosh (a * η) = Real.cosh (a * |η|) := by
    rw [← Real.cosh_abs (a * η), abs_mul, abs_of_pos ha]
  have hcalc : a ^ 3 * |η| ^ 3 / 12 = (a * |η|) ^ 3 / 6 / 2 := by ring
  rw [hcc, hcalc]
  linarith

/-- The elementary inequality `(1 + |η|)(1 + η²) ≤ 3 (1 + 12/a³) cosh(aη)`. -/
theorem smKey (a η : ℝ) (ha : 0 < a) :
    (1 + |η|) * (1 + η ^ 2) ≤ 3 * (1 + 12 / a ^ 3) * Real.cosh (a * η) := by
  have hc1 : 1 ≤ Real.cosh (a * η) := Real.one_le_cosh _
  have hcl := smCosh_ge_cube a η ha
  have ht : 0 ≤ |η| := abs_nonneg η
  have hd : 0 ≤ 12 / a ^ 3 := by positivity
  have ha3 : a ^ 3 ≠ 0 := pow_ne_zero 3 ha.ne'
  have hdiv : 12 / a ^ 3 * (a ^ 3 * |η| ^ 3 / 12) = |η| ^ 3 := by
    rw [div_mul_eq_mul_div, div_eq_iff ha3]
    ring
  have h4 := mul_le_mul_of_nonneg_left hcl hd
  rw [hdiv] at h4
  have hM : 1 + |η| ^ 3 ≤ (1 + 12 / a ^ 3) * Real.cosh (a * η) := by
    nlinarith [h4, hc1]
  have hsq : η ^ 2 = |η| ^ 2 := (sq_abs η).symm
  rw [hsq]
  nlinarith [mul_nonneg ht (sq_nonneg (|η| - 1)), sq_nonneg (|η| - 1 / 2), hM]

/-- Pointwise domination: `(1 + |η|) · (|C| (cosh aη)⁻¹) ≤ 3 (1 + 12/a³) |C| (1 + η²)⁻¹`. -/
theorem smPoint (a C η : ℝ) (ha : 0 < a) :
    (1 + |η|) * (|C| * (Real.cosh (a * η))⁻¹) ≤
      3 * (1 + 12 / a ^ 3) * |C| * (1 + η ^ 2)⁻¹ := by
  have hc0 : 0 < Real.cosh (a * η) := Real.cosh_pos _
  have hpos : 0 < 1 + η ^ 2 := by positivity
  have e1 : (1 + |η|) * (|C| * (Real.cosh (a * η))⁻¹)
      = |C| * ((1 + |η|) / Real.cosh (a * η)) := by ring
  have e2 : 3 * (1 + 12 / a ^ 3) * |C| * (1 + η ^ 2)⁻¹
      = |C| * ((3 * (1 + 12 / a ^ 3)) / (1 + η ^ 2)) := by ring
  rw [e1, e2]
  refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg C)
  rw [div_le_div_iff₀ hc0 hpos]
  exact smKey a η ha

/-- **The `sech` first moment is integrable on the cell** (`SechMomentIntegrable`). -/
theorem sechMomentIntegrable : SechMomentIntegrable := by
  intro c a C f hc ha hf hbound
  -- the `η`-dominator `3 M |C| (1 + η²)⁻¹` (independent of `q`) is integrable on `ℝ`
  have hG : Integrable (fun η : ℝ => 3 * (1 + 12 / a ^ 3) * |C| * (1 + η ^ 2)⁻¹) :=
    integrable_inv_one_add_sq.const_mul _
  -- the `q`-factor is the constant `1` on the finite-length interval `[-c/2, c/2)`
  have h1 : Integrable (fun _ : ℝ => (1 : ℝ)) (volume.restrict (Ico (-c / 2) (c / 2))) :=
    integrableOn_const (by rw [Real.volume_Ico]; exact ENNReal.ofReal_ne_top) (by simp)
  have h2 : Integrable (fun η : ℝ => 3 * (1 + 12 / a ^ 3) * |C| * (1 + η ^ 2)⁻¹)
      (volume.restrict univ) := by
    rw [Measure.restrict_univ]
    exact hG
  have hprod := Integrable.mul_prod h1 h2
  rw [Measure.prod_restrict, ← Measure.volume_eq_prod] at hprod
  have hcellG : Integrable (fun z : Plane => 3 * (1 + 12 / a ^ 3) * |C| * (1 + z.2 ^ 2)⁻¹)
      (volume.restrict (Cyl.cell c)) := by
    have hprod' : Integrable (fun z : Plane => 1 * (3 * (1 + 12 / a ^ 3) * |C| * (1 + z.2 ^ 2)⁻¹))
        (volume.restrict (Ico (-c / 2) (c / 2) ×ˢ univ)) := hprod
    simp only [one_mul] at hprod'
    exact hprod'
  -- domination of `(1 + |η|) |f|` on the cell
  have hcont : Continuous (fun z : Plane => (1 + |z.2|) * |f z|) := by
    fun_prop
  refine Integrable.mono' hcellG hcont.aestronglyMeasurable ?_
  refine Filter.Eventually.of_forall (fun z => ?_)
  show ‖(1 + |z.2|) * |f z|‖ ≤ 3 * (1 + 12 / a ^ 3) * |C| * (1 + z.2 ^ 2)⁻¹
  have hz0 : 0 ≤ (1 + |z.2|) * |f z| := by positivity
  rw [Real.norm_of_nonneg hz0]
  have hc0 : 0 ≤ (Real.cosh (a * z.2))⁻¹ := inv_nonneg.mpr (Real.cosh_pos _).le
  have hfz : |f z| ≤ |C| * (Real.cosh (a * z.2))⁻¹ :=
    (hbound z).trans (mul_le_mul_of_nonneg_right (le_abs_self C) hc0)
  calc (1 + |z.2|) * |f z| ≤ (1 + |z.2|) * (|C| * (Real.cosh (a * z.2))⁻¹) :=
        mul_le_mul_of_nonneg_left hfz (by positivity)
    _ ≤ 3 * (1 + 12 / a ^ 3) * |C| * (1 + z.2 ^ 2)⁻¹ := smPoint a C z.2 ha

end UnforcedLeray.Short.PartI

end
