import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D2_1_3_1_2_1_3_1_5

/-!
# Helper: the radial bump `b` and its potential `V` (source lines 1351-1362, 1470-1480)

`b(z) = γ(|z|²)`, `γ = β/M`, `β(t) = smoothTransition(1-t)`, `M = ∫ β(|z|²) dz`;
`B(t) = ∫_t^1 γ`, `V(z) = -½ B(|z|²)`, so that `∇V = z b(z)`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- The profile `β(t) = smoothTransition (1 - t)`. -/
def radBeta (t : ℝ) : ℝ := Real.smoothTransition (1 - t)

theorem contDiff_radBeta : ContDiff ℝ ∞ radBeta := by
  unfold radBeta
  exact Real.smoothTransition.contDiff.comp (by fun_prop)

theorem radBeta_nonneg (t : ℝ) : 0 ≤ radBeta t := Real.smoothTransition.nonneg _

theorem radBeta_zero_of_one_le {t : ℝ} (ht : 1 ≤ t) : radBeta t = 0 :=
  Real.smoothTransition.zero_of_nonpos (by linarith)

theorem radBeta_pos {t : ℝ} (ht : t < 1) : 0 < radBeta t :=
  Real.smoothTransition.pos_of_pos (by linarith)

/-- Normalising constant. -/
def radM : ℝ := ∫ z : Space, radBeta (‖z‖ ^ 2)

theorem radBeta_norm_sq_support : HasCompactSupport (fun z : Space => radBeta (‖z‖ ^ 2)) := by
  refine HasCompactSupport.intro (isCompact_closedBall (0 : Space) 1) fun z hz => ?_
  apply radBeta_zero_of_one_le
  have : 1 < ‖z‖ := by simpa using hz
  nlinarith

theorem radBeta_norm_sq_cont : ContDiff ℝ ∞ (fun z : Space => radBeta (‖z‖ ^ 2)) :=
  contDiff_radBeta.comp (contDiff_norm_sq ℝ)

theorem radM_pos : 0 < radM := by
  have hint : Integrable (fun z : Space => radBeta (‖z‖ ^ 2)) :=
    radBeta_norm_sq_cont.continuous.integrable_of_hasCompactSupport radBeta_norm_sq_support
  unfold radM
  rw [integral_pos_iff_support_of_nonneg (fun z => radBeta_nonneg _) hint]
  refine lt_of_lt_of_le (Metric.measure_ball_pos volume (0 : Space) one_pos) (measure_mono ?_)
  intro z hz
  have : ‖z‖ < 1 := by simpa using hz
  show radBeta (‖z‖ ^ 2) ≠ 0
  exact (radBeta_pos (by nlinarith [norm_nonneg z])).ne'

/-- `γ = β / M`. -/
def radG (t : ℝ) : ℝ := radBeta t / radM

theorem contDiff_radG : ContDiff ℝ ∞ radG := by
  unfold radG; exact contDiff_radBeta.div_const _

theorem radG_nonneg (t : ℝ) : 0 ≤ radG t := div_nonneg (radBeta_nonneg t) radM_pos.le

theorem radG_zero_of_one_le {t : ℝ} (ht : 1 ≤ t) : radG t = 0 := by
  unfold radG; rw [radBeta_zero_of_one_le ht, zero_div]

/-- The bump `b(z) = γ(|z|²)`. -/
def radB (z : Space) : ℝ := radG (‖z‖ ^ 2)

theorem radB_nonneg (z : Space) : 0 ≤ radB z := radG_nonneg _

theorem radB_contDiff : ContDiff ℝ ∞ radB := contDiff_radG.comp (contDiff_norm_sq ℝ)

theorem radB_zero {z : Space} (hz : 1 < ‖z‖) : radB z = 0 :=
  radG_zero_of_one_le (by nlinarith)

theorem radB_support : HasCompactSupport radB :=
  HasCompactSupport.intro (isCompact_closedBall (0 : Space) 1) fun z hz =>
    radB_zero (by simpa using hz)

theorem radB_integral : ∫ z, radB z = 1 := by
  have : radB = fun z : Space => radBeta (‖z‖ ^ 2) / radM := rfl
  rw [this, integral_div]
  exact div_self radM_pos.ne'

/-- `B(t) = ∫_t^1 γ`. -/
def radBB (t : ℝ) : ℝ := (∫ s in (0 : ℝ)..1, radG s) - ∫ s in (0 : ℝ)..t, radG s

theorem radBB_hasDerivAt (t : ℝ) : HasDerivAt radBB (-radG t) t := by
  have := (contDiff_radG.continuous.integral_hasStrictDerivAt (0 : ℝ) t).hasDerivAt
  exact this.const_sub (∫ s in (0 : ℝ)..1, radG s)

theorem contDiff_radBB : ContDiff ℝ ∞ radBB := by
  rw [contDiff_infty_iff_deriv]
  refine ⟨fun t => (radBB_hasDerivAt t).differentiableAt, ?_⟩
  have : deriv radBB = fun t => -radG t := funext fun t => (radBB_hasDerivAt t).deriv
  rw [this]
  exact contDiff_radG.neg

theorem radBB_zero_of_one_le {t : ℝ} (ht : 1 ≤ t) : radBB t = 0 := by
  unfold radBB
  have h1 : IntervalIntegrable radG volume 0 1 := contDiff_radG.continuous.intervalIntegrable _ _
  have h2 : IntervalIntegrable radG volume 1 t := contDiff_radG.continuous.intervalIntegrable _ _
  have h3 : ∫ s in (1 : ℝ)..t, radG s = 0 := by
    rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)) (fun x hx => ?_)]
    · simp
    · rw [uIcc_of_le ht] at hx
      exact radG_zero_of_one_le hx.1
  rw [← intervalIntegral.integral_add_adjacent_intervals h1 h2, h3]
  ring

/-- The potential `V(z) = -½ B(|z|²)`. -/
def radV (z : Space) : ℝ := -(1 / 2) * radBB (‖z‖ ^ 2)

theorem radV_contDiff : ContDiff ℝ ∞ radV :=
  contDiff_const.mul (contDiff_radBB.comp (contDiff_norm_sq ℝ))

theorem radV_support : HasCompactSupport radV := by
  refine HasCompactSupport.intro (isCompact_closedBall (0 : Space) 1) fun z hz => ?_
  have : 1 < ‖z‖ := by simpa using hz
  unfold radV
  rw [radBB_zero_of_one_le (by nlinarith), mul_zero]

theorem radV_fderiv (z w : Space) : fderiv ℝ radV z w = radB z * inner ℝ z w := by
  have h1 : HasFDerivAt (fun z : Space => ‖z‖ ^ 2) (2 • innerSL ℝ z) z :=
    (hasStrictFDerivAt_norm_sq z).hasFDerivAt
  have h2 := (radBB_hasDerivAt (‖z‖ ^ 2)).comp_hasFDerivAt z h1
  have h3 := h2.const_mul (-(1 / 2 : ℝ))
  have : fderiv ℝ radV z = _ := h3.fderiv
  rw [this]
  simp [radB]
  ring

end UnforcedLeray.Short.PartIIIb.Concrete
