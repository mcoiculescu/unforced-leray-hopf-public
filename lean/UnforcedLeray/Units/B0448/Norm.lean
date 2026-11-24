import UnforcedLeray.Lib.Gaussian.SpaceTime
import UnforcedLeray.Analysis.Heat.KernelNorm

/-!
# B0448, part 1: the causal resolvent kernel and its `L^{q'}` norm (eq:free-stress-22)

Manuscript `paper/main.tex` lines 7663–7676 (blueprint unit B0448, label `eq:free-stress-22`):
the causal inverse kernel `K(t,z) = 1_{t>0} e^{-t} H_t(z)` "belongs to `L^{q'}` precisely when
`q > 5/2`, because `‖K‖_{L^{q'}}^{q'} = C ∫_0^∞ e^{-q't} t^{-3(q'-1)/2} dt`".

The kernel is the drafted `UnforcedLeray.Gaussian.causalKernel 3`

redefined. Here:

* `kernel_of_pos`, `kernel_of_nonpos`: `K(t,z) = e^{-t} H_t(z)` for `t > 0`, with `H_t` the
  compiled heat kernel `UnforcedLeray.Heat.kernel`, and `K = 0` for `t ≤ 0`;
* `lintegral_rpow_kernel`: `∫⁻ |K|^r = C_r ∫⁻_{(0,∞)} e^{-rt} t^{-3(r-1)/2} dt` for every
  `r > 0`, in `ℝ≥0∞` (both sides may be `∞`; no junk value of a Bochner integral is used);
* `eLpNorm_rpow_kernel` (eq:free-stress-22): the same identity for `‖K‖_{L^r}^r`;
* `memLp_kernel_iff`: for Hölder conjugate `q, q'`, `K ∈ L^{q'}` iff `5/2 < q`.
-/

noncomputable section

set_option autoImplicit false

namespace UnforcedLeray.B0448

open MeasureTheory Real Set
open scoped ENNReal

/-- The causal resolvent kernel `K(t,z) = 1_{t>0} e^{-t} H_t(z)` on `ℝ × ℝ³`
(tex 7666–7669, B0448). It is the drafted `Gaussian.causalKernel 3`. -/
abbrev kernel : ℝ × Space → ℝ := Gaussian.causalKernel 3

/-- For `t > 0`, `K(t,z) = e^{-t} H_t(z)` with `H_t = Heat.kernel t`, the heat kernel
`(4πt)^{-3/2} e^{-|z|²/(4t)}` (tex 7668). -/
theorem kernel_of_pos {t : ℝ} (ht : 0 < t) (z : Space) :
    kernel (t, z) = Real.exp (-t) * Heat.kernel t z := by
  simp [kernel, Gaussian.causalKernel, ht, Gaussian.gaussKernel_three_eq]

/-- For `t ≤ 0`, `K(t,z) = 0` (the indicator `1_{t>0}`, tex 7668). -/
theorem kernel_of_nonpos {t : ℝ} (ht : t ≤ 0) (z : Space) : kernel (t, z) = 0 := by
  simp [kernel, Gaussian.causalKernel, not_lt.2 ht]

theorem kernel_nonneg (X : ℝ × Space) : 0 ≤ kernel X := Gaussian.causalKernel_nonneg X

theorem measurable_kernel : Measurable kernel := Gaussian.measurable_causalKernel

/-- The constant `C` of eq:free-stress-22 for the exponent `r`:
`C_r = (4π)^{-3r/2} (4π/r)^{3/2}`. -/
abbrev normConst (r : ℝ) : ℝ := Gaussian.causalConst 3 r

theorem normConst_pos {r : ℝ} (hr : 0 < r) : 0 < normConst r := Gaussian.causalConst_pos hr

/-- **eq:free-stress-22, lintegral form.** For every `r > 0`,
`∫⁻ |K|^r = C_r ∫⁻_{(0,∞)} e^{-rt} t^{-3(r-1)/2} dt` (tex 7674–7676). -/
theorem lintegral_rpow_kernel {r : ℝ} (hr : 0 < r) :
    ∫⁻ X, ‖kernel X‖ₑ ^ r = ENNReal.ofReal (normConst r) *
      ∫⁻ t in Ioi 0, ENNReal.ofReal (Real.exp (-r * t) * t ^ (-(3 * (r - 1) / 2))) := by
  have hmeas : AEMeasurable (fun X : ℝ × Space => ‖kernel X‖ₑ ^ r)
      ((volume : Measure ℝ).prod (volume : Measure Space)) :=
    (measurable_kernel.enorm.pow_const r).aemeasurable
  rw [Measure.volume_eq_prod, lintegral_prod _ hmeas]
  have hslice : ∀ t : ℝ, (∫⁻ y : Space, ‖kernel (t, y)‖ₑ ^ r) =
      (Ioi (0 : ℝ)).indicator (fun t => ENNReal.ofReal (normConst r) *
        ENNReal.ofReal (Real.exp (-r * t) * t ^ (-(3 * (r - 1) / 2)))) t := by
    intro t
    have hn : ∀ y : Space, ‖kernel (t, y)‖ₑ ^ r = ENNReal.ofReal (‖kernel (t, y)‖ ^ r) := by
      intro y
      rw [← ofReal_norm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hr.le]
    simp_rw [hn]
    rw [← ofReal_integral_eq_lintegral_ofReal
      (Gaussian.integrable_causalKernel_rpow_slice (d := 3) hr t)
      (Filter.Eventually.of_forall fun y => Real.rpow_nonneg (norm_nonneg _) _)]
    by_cases ht : 0 < t
    · rw [Set.indicator_of_mem (show t ∈ Ioi (0 : ℝ) from ht),
        Gaussian.integral_causalKernel_rpow_slice hr ht,
        ← ENNReal.ofReal_mul (normConst_pos hr).le]
      congr 1
      push_cast
      rw [show -((3 : ℝ) / 2 * (r - 1)) = -(3 * (r - 1) / 2) by ring]
      ring
    · rw [Set.indicator_of_notMem (show t ∉ Ioi (0 : ℝ) from ht)]
      have : (fun y : Space => ‖kernel (t, y)‖ ^ r) = fun _ => 0 := by
        funext y; rw [kernel_of_nonpos (not_lt.1 ht)]; simp [Real.zero_rpow hr.ne']
      rw [this, integral_zero, ENNReal.ofReal_zero]
  simp_rw [hslice]
  rw [lintegral_indicator measurableSet_Ioi, lintegral_const_mul _ (by fun_prop)]

/-- **eq:free-stress-22.** For every `r > 0`,
`‖K‖_{L^r}^r = C_r ∫_0^∞ e^{-rt} t^{-3(r-1)/2} dt` in `ℝ≥0∞`, with `C_r > 0`
(tex 7674–7676; the manuscript's case is `r = q'`). -/
theorem eLpNorm_rpow_kernel {r : ℝ} (hr : 0 < r) :
    eLpNorm kernel (ENNReal.ofReal r) volume ^ r = ENNReal.ofReal (normConst r) *
      ∫⁻ t in Ioi 0, ENNReal.ofReal (Real.exp (-r * t) * t ^ (-(3 * (r - 1) / 2))) := by
  rw [eLpNorm_eq_eLpNorm' (by simpa using hr) ENNReal.ofReal_ne_top, eLpNorm',
    ENNReal.toReal_ofReal hr.le, ← lintegral_rpow_kernel hr, one_div,
    ENNReal.rpow_inv_rpow hr.ne']

/-- **B0448 (tex 7671–7676).** For Hölder conjugate exponents `q, q'`
(`1/q + 1/q' = 1`, so `1 < q < ∞`), the causal kernel belongs to `L^{q'}(ℝ × ℝ³)` precisely
when `q > 5/2`. -/
theorem memLp_kernel_iff {q q' : ℝ} (hqq' : q.HolderConjugate q') :
    MemLp kernel (ENNReal.ofReal q') volume ↔ 5 / 2 < q := by
  rw [Gaussian.memLp_causalKernel_three_iff hqq'.symm.left_pos, hqq'.conjugate_eq]
  have h1 : 0 < q - 1 := hqq'.sub_one_pos
  rw [div_lt_iff₀ h1]
  constructor <;> intro h <;> linarith

/-- The same criterion for the finiteness of the norm in eq:free-stress-22:
`‖K‖_{L^{q'}} < ∞` iff `q > 5/2`. -/
theorem eLpNorm_kernel_lt_top_iff {q q' : ℝ} (hqq' : q.HolderConjugate q') :
    eLpNorm kernel (ENNReal.ofReal q') volume < ∞ ↔ 5 / 2 < q := by
  rw [← memLp_kernel_iff hqq']
  exact ⟨fun h => ⟨measurable_kernel.aestronglyMeasurable, h⟩, fun h => h.2⟩

/-- The kernel is integrable (`q = ∞`, `q' = 1`): `‖K‖_{L¹} = ∫_0^∞ e^{-t} dt = 1`. -/
theorem integrable_kernel : Integrable kernel volume := by
  have h := (Gaussian.memLp_causalKernel_three_iff (r := 1) one_pos).2 (by norm_num)
  rw [ENNReal.ofReal_one] at h
  exact memLp_one_iff_integrable.1 h

end UnforcedLeray.B0448
