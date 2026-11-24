import UnforcedLeray.Loc.L09CompactDatum.ParamIntegral
import UnforcedLeray.Loc.L09CompactDatum.Vector

/-!
# L9 helper: inverse-distance bounds and the smoothed defect

Helper of `Loc/L09CompactDatum.lean` (step L9, `paper/main.tex` lines 442–461, blueprint
units B0719, B0720).

* `integrable_of_inverse_bound`, `memLp_two_of_inverse_bound`: a field continuous off zero,
  with `|f(x)||x| ≤ C` and vanishing outside a ball, is in `L¹` and in `L²`
  (`|x|^{-2}` is integrable near zero in `ℝ³`, line 451: "`u_{0,h} = O(|x|^{-1})` near `0`").
* `smoothDefect ρ d`: a field `d` vanishing on the punctured ball `0 < |x| < ρ` and smooth off
  zero agrees off zero with a globally smooth field; its value at `0` is irrelevant to every
  heat integral. This is how `d_loc = u_{0,h} - u_dss`, which vanishes near the origin
  (line 446), is handled: the junk value of `d_loc` at `0` never enters.
* `heatProfile_tail`: the heat profile `K(y,τ) = e^{τ/2}[e^{he^τΔ}d](e^{τ/2}y)` of such a
  defect, with derivatives of every order bounded on `|x| ≥ ρ`, is smooth and
  `‖∇ⁿK(τ)‖_∞ ≤ C e^{τ/2}` for `τ ≤ 0` (`loc:eq:heat-correction`, lines 455–458; for
  `τ ≤ 0` the rescaling factors `e^{nτ/2}` are at most `1`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter
open scoped ContDiff Topology

namespace UnforcedLeray.L09

open UnforcedLeray.Blueprint

/-! ## Integrability from `|f(x)| ≤ C|x|^{-1}` -/

theorem aestronglyMeasurable_of_continuousOn_compl_zero {f : SpatialField}
    (hcont : ContinuousOn f {0}ᶜ) : AEStronglyMeasurable f volume := by
  have h := hcont.aestronglyMeasurable (μ := volume) isOpen_compl_singleton.measurableSet
  rwa [restrict_compl_singleton] at h

/-- Bounded by `C|x|^{-α}` off zero, `α < 3`, and zero outside a ball: integrable. -/
theorem integrable_of_rpow_bound {F : Type*} [NormedAddCommGroup F] {f : Space → F}
    (hmeas : AEStronglyMeasurable f volume) {C α R : ℝ} (hα : α < 3)
    (hdec : ∀ x : Space, x ≠ 0 → ‖f x‖ ≤ C * ‖x‖ ^ (-α))
    (hR : ∀ x : Space, R < ‖x‖ → f x = 0) : Integrable f volume := by
  have hdim : Module.finrank ℝ Space = 3 := finrank_euclideanSpace_fin
  have hdec' : ∀ᵐ x ∂(volume : Measure Space), ‖f x‖ ≤ C * ‖x‖ ^ (-α) := by
    filter_upwards [compl_mem_ae_iff.mpr (measure_singleton (0 : Space))] with x hx
    exact hdec x hx
  have hball : IntegrableOn f (Metric.ball (0 : Space) (max R 0 + 1)) volume :=
    integrableOn_ball_of_norm_le_rpow (by rw [hdim]; norm_num)
      (by rw [hdim]; exact_mod_cast hα) (ae_restrict_of_ae hdec') hmeas
  refine (integrableOn_iff_integrable_of_support_subset ?_).mp hball
  intro y hy
  rw [Function.mem_support] at hy
  rw [mem_ball_zero_iff]
  by_contra hcon
  exact hy (hR y (by linarith [le_max_left R 0, not_lt.mp hcon]))

/-- `|f(x)||x| ≤ C` off zero and `f = 0` outside a ball give `f ∈ L¹`. -/
theorem integrable_of_inverse_bound {f : SpatialField} (hcont : ContinuousOn f {0}ᶜ)
    {C R : ℝ} (hC : ∀ x : Space, x ≠ 0 → ‖f x‖ * ‖x‖ ≤ C)
    (hR : ∀ x : Space, R < ‖x‖ → f x = 0) : Integrable f volume := by
  refine integrable_of_rpow_bound (aestronglyMeasurable_of_continuousOn_compl_zero hcont)
    (α := 1) (C := C) (R := R) (by norm_num) (fun x hx => ?_) hR
  have hpos : 0 < ‖x‖ := norm_pos_iff.mpr hx
  rw [Real.rpow_neg_one, ← div_eq_mul_inv, le_div_iff₀ hpos]
  exact hC x hx

/-- `|f(x)||x| ≤ C` off zero and `f = 0` outside a ball give `f ∈ L²` (line 451). -/
theorem memLp_two_of_inverse_bound {f : SpatialField} (hcont : ContinuousOn f {0}ᶜ)
    {C R : ℝ} (hC : ∀ x : Space, x ≠ 0 → ‖f x‖ * ‖x‖ ≤ C)
    (hR : ∀ x : Space, R < ‖x‖ → f x = 0) : MemLp f 2 volume := by
  have hmeas := aestronglyMeasurable_of_continuousOn_compl_zero hcont
  rw [memLp_two_iff_integrable_sq_norm hmeas]
  refine integrable_of_rpow_bound (hmeas.norm.pow 2) (α := 2) (C := C ^ 2) (R := R) (by norm_num)
    (fun x hx => ?_) (fun x hx => by simp [hR x hx])
  have hpos : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have h0 : 0 ≤ ‖f x‖ * ‖x‖ := by positivity
  rw [Real.norm_of_nonneg (by positivity), Real.rpow_neg hpos.le, Real.rpow_two,
    ← div_eq_mul_inv, le_div_iff₀ (by positivity)]
  calc ‖f x‖ ^ 2 * ‖x‖ ^ 2 = (‖f x‖ * ‖x‖) ^ 2 := by ring
    _ ≤ C ^ 2 := pow_le_pow_left₀ h0 (hC x hx) 2

/-! ## The smoothed defect -/

/-- `d` with its value on the open ball `|x| < ρ` replaced by `0`. When `d` already vanishes
on the punctured ball, only the (junk) value at `0` changes. -/
def smoothDefect (ρ : ℝ) (d : SpatialField) (x : Space) : Space :=
  if ‖x‖ < ρ then 0 else d x

variable {ρ : ℝ} {d : SpatialField}

theorem smoothDefect_eq (hd0 : ∀ x : Space, x ≠ 0 → ‖x‖ < ρ → d x = 0) {x : Space}
    (hx : x ≠ 0) : smoothDefect ρ d x = d x := by
  unfold smoothDefect
  split_ifs with h
  · exact (hd0 x hx h).symm
  · rfl

theorem smoothDefect_eventuallyEq (hd0 : ∀ x : Space, x ≠ 0 → ‖x‖ < ρ → d x = 0) {x : Space}
    (hx : x ≠ 0) : smoothDefect ρ d =ᶠ[𝓝 x] d := by
  filter_upwards [isOpen_compl_singleton.mem_nhds hx] with y hy
  exact smoothDefect_eq hd0 hy

theorem smoothDefect_eventually_zero {x : Space} (hx : ‖x‖ < ρ) :
    smoothDefect ρ d =ᶠ[𝓝 x] fun _ => 0 := by
  filter_upwards [(isOpen_lt continuous_norm continuous_const).mem_nhds hx] with y hy
  have hy' : ‖y‖ < ρ := hy
  simp [smoothDefect, hy']

theorem smoothDefect_contDiff (hρ : 0 < ρ) (hd0 : ∀ x : Space, x ≠ 0 → ‖x‖ < ρ → d x = 0)
    (hds : ContDiffOn ℝ ∞ d {0}ᶜ) : ContDiff ℝ ∞ (smoothDefect ρ d) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x = 0
  · have h : ‖x‖ < ρ := by rw [hx, norm_zero]; exact hρ
    exact contDiffAt_const.congr_of_eventuallyEq (smoothDefect_eventually_zero h)
  · exact (hds.contDiffAt (isOpen_compl_singleton.mem_nhds hx)).congr_of_eventuallyEq
      (smoothDefect_eventuallyEq hd0 hx)

theorem smoothDefect_bounds (hρ : 0 < ρ) (hd0 : ∀ x : Space, x ≠ 0 → ‖x‖ < ρ → d x = 0)
    (hdb : ∀ n : ℕ, ∃ M : ℝ, ∀ x : Space, ρ ≤ ‖x‖ → ‖iteratedFDeriv ℝ n d x‖ ≤ M) (n : ℕ) :
    ∃ M : ℝ, ∀ x : Space, ‖iteratedFDeriv ℝ n (smoothDefect ρ d) x‖ ≤ M := by
  obtain ⟨M, hM⟩ := hdb n
  refine ⟨max M 0, fun x => ?_⟩
  by_cases hx : ‖x‖ < ρ
  · rw [((smoothDefect_eventually_zero hx).iteratedFDeriv ℝ n).eq_of_nhds,
      iteratedFDeriv_fun_zero]
    simp
  · rw [not_lt] at hx
    have hx0 : x ≠ 0 := by
      intro h0; rw [h0, norm_zero] at hx; linarith
    rw [((smoothDefect_eventuallyEq hd0 hx0).iteratedFDeriv ℝ n).eq_of_nhds]
    exact (hM x hx).trans (le_max_left _ _)

/-- The heat average does not see the value of `d` at `0`. -/
theorem average_smoothDefect (hd0 : ∀ x : Space, x ≠ 0 → ‖x‖ < ρ → d x = 0) (t : ℝ)
    (x : Space) : Heat.average t d x = Heat.average t (smoothDefect ρ d) x := by
  unfold Heat.average
  refine integral_congr_ae ?_
  filter_upwards [compl_mem_ae_iff.mpr (measure_singleton x)] with z hz
  have hxz : x - z ≠ 0 := sub_ne_zero.mpr (Ne.symm hz)
  rw [smoothDefect_eq hd0 hxz]

theorem heatProfile_smoothDefect (hd0 : ∀ x : Space, x ≠ 0 → ‖x‖ < ρ → d x = 0) (h τ : ℝ) :
    heatProfile h d τ = fun y => Real.exp (τ / 2) •
      Heat.average (h * Real.exp τ) (smoothDefect ρ d) (Real.exp (τ / 2) • y) := by
  funext y
  unfold heatProfile
  rw [average_smoothDefect hd0]

/-- **The heat tail of a defect vanishing near zero** (`loc:eq:heat-correction`,
lines 455–458): smooth, and `‖∇ⁿK(τ)‖_∞ ≤ C_n e^{τ/2}` for `τ ≤ 0`. -/
theorem heatProfile_tail (hρ : 0 < ρ) (hd0 : ∀ x : Space, x ≠ 0 → ‖x‖ < ρ → d x = 0)
    (hds : ContDiffOn ℝ ∞ d {0}ᶜ)
    (hdb : ∀ n : ℕ, ∃ M : ℝ, ∀ x : Space, ρ ≤ ‖x‖ → ‖iteratedFDeriv ℝ n d x‖ ≤ M)
    {h : ℝ} (hh : 0 < h) :
    (∀ τ : ℝ, ContDiff ℝ ∞ (heatProfile h d τ)) ∧
    ∀ n : ℕ, ∃ C : ℝ, ∀ τ : ℝ, τ ≤ 0 → ∀ y : Space,
      ‖iteratedFDeriv ℝ n (heatProfile h d τ) y‖ ≤ C * Real.exp ((1 / 2) * τ) := by
  have hs := smoothDefect_contDiff hρ hd0 hds
  have hb := smoothDefect_bounds hρ hd0 hdb
  have hH := fun τ : ℝ => heatAverage_smooth_bounds hs hb (mul_pos hh (Real.exp_pos τ))
  refine ⟨fun τ => ?_, fun n => ?_⟩
  · rw [heatProfile_smoothDefect hd0]
    exact ((hH τ).1.comp (contDiff_const_smul _)).const_smul _
  · obtain ⟨M, hM⟩ := hb n
    refine ⟨M, fun τ hτ y => ?_⟩
    rw [heatProfile_smoothDefect hd0,
      Kernels.iteratedFDeriv_comp_smul n (Heat.average (h * Real.exp τ) (smoothDefect ρ d))
        (Real.exp (τ / 2)) (Real.exp (τ / 2)) y, norm_smul,
      Real.norm_of_nonneg (by positivity)]
    have ha : Real.exp (τ / 2) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    have hpow : Real.exp (τ / 2) ^ n ≤ 1 := pow_le_one₀ (Real.exp_pos _).le ha
    have hb' := (hH τ).2 n M hM (Real.exp (τ / 2) • y)
    calc Real.exp (τ / 2) * Real.exp (τ / 2) ^ n *
          ‖iteratedFDeriv ℝ n (Heat.average (h * Real.exp τ) (smoothDefect ρ d))
            (Real.exp (τ / 2) • y)‖ ≤ Real.exp (τ / 2) * 1 * M :=
          mul_le_mul (mul_le_mul_of_nonneg_left hpow (Real.exp_pos _).le) hb' (norm_nonneg _)
            (by positivity)
      _ = M * Real.exp ((1 / 2) * τ) := by
          rw [mul_one, mul_comm, show (1 / 2 : ℝ) * τ = τ / 2 by ring]

end UnforcedLeray.L09
