import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_4_2_4_2_of
import UnforcedLeray.Lib.Gaussian.LpNorm
import UnforcedLeray.Lib.HeatR3.Bounded

/-!
# `SFCHeatBounds` (decomposition of `PartIII-b:C/flatset/col/7/1/1/2/4/2/4/2`)

Source `the November 2 reference manuscript`
1650-1656, 1684-1689, 3426-3430.  Gaussian average of a bounded continuous datum on the plane:
differentiation under the integral after moving the shift onto the kernel, the `L¹` norm of the
Gaussian gradient scaling as `θ^{-1/2}`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Gaussian UnforcedLeray.B0224
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

/-- The linear map `ℝ² → Euc 2`, inverse of `planeι`. -/
def planeLp : ℝ × ℝ →L[ℝ] Euc 2 :=
  (ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight (EuclideanSpace.single (0 : Fin 2) (1 : ℝ)) +
  (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight (EuclideanSpace.single (1 : Fin 2) (1 : ℝ))

theorem planeι_planeLp (x : ℝ × ℝ) : planeι (planeLp x) = x := by
  simp [planeLp, planeι_apply]

/-- Gradient of the Gaussian kernel. -/
def gradG (θ : ℝ) (z : Euc 2) : Euc 2 →L[ℝ] ℝ :=
  (-(1 / (2 * θ)) * gaussKernel 2 θ z) • innerSL ℝ z

theorem hasFDerivAt_gaussKernel_grad {θ : ℝ} (hθ : 0 < θ) (z : Euc 2) :
    HasFDerivAt (gaussKernel 2 θ) (gradG θ z) z := by
  have h1 : HasFDerivAt (fun z : Euc 2 => ‖z‖ ^ 2) (2 • (innerSL ℝ z)) z :=
    hasStrictFDerivAt_norm_sq z |>.hasFDerivAt
  have h2 := ((h1.fun_neg.const_mul (1 / (4 * θ))).exp).const_mul
    ((4 * Real.pi * θ) ^ (-(2 : ℕ) / 2 : ℝ))
  have hf : gaussKernel 2 θ = fun z : Euc 2 => (4 * Real.pi * θ) ^ (-(2 : ℕ) / 2 : ℝ) *
      Real.exp (1 / (4 * θ) * -‖z‖ ^ 2) := by
    ext z; unfold gaussKernel; congr 2; ring
  rw [hf]
  refine h2.congr_fderiv ?_
  ext v
  simp only [gradG, gaussKernel]
  simp
  field_simp
  ring

theorem fderiv_gaussKernel_eq {θ : ℝ} (hθ : 0 < θ) (z : Euc 2) :
    fderiv ℝ (gaussKernel 2 θ) z = gradG θ z :=
  (hasFDerivAt_gaussKernel_grad hθ z).fderiv


theorem norm_gradG_le : ∃ C : ℝ, 0 < C ∧ ∀ {θ : ℝ}, 0 < θ → ∀ z : Euc 2,
    ‖gradG θ z‖ ≤ C * θ ^ (-(3 / 2 : ℝ)) * Real.exp (-‖z‖ ^ 2 / (8 * θ)) := by
  obtain ⟨C, hC, h⟩ := norm_iteratedFDeriv_gaussKernel_le 2 1
  refine ⟨C, hC, fun {θ} hθ z => ?_⟩
  have := h hθ z
  rw [norm_iteratedFDeriv_one, fderiv_gaussKernel_eq hθ] at this
  convert this using 4
  norm_num

theorem exp_shift_le {θ R : ℝ} (hθ : 0 < θ) (hR : 0 ≤ R) {w y : Euc 2} (hw : ‖w‖ ≤ R) :
    Real.exp (-‖w - y‖ ^ 2 / (8 * θ)) ≤
      Real.exp (R ^ 2 / (8 * θ)) * Real.exp (-(1 / (16 * θ)) * ‖y‖ ^ 2) := by
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have h1 : ‖y‖ ≤ ‖w - y‖ + R := by
    have := norm_sub_le w (w - y)
    rw [sub_sub_cancel] at this
    linarith
  have h2 : ‖y‖ ^ 2 ≤ 2 * ‖w - y‖ ^ 2 + 2 * R ^ 2 := by
    nlinarith [sq_nonneg (‖w - y‖ - R), norm_nonneg y, norm_nonneg (w - y)]
  have h8 : 0 < 8 * θ := by positivity
  rw [show -(1 / (16 * θ)) * ‖y‖ ^ 2 = -(‖y‖ ^ 2 / 2) / (8 * θ) by field_simp; ring,
    ← add_div, div_le_div_iff_of_pos_right h8]
  nlinarith

theorem planeHeat_eq_shift {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {θ : ℝ}
    (hθ : 0 < θ) (u : ℝ × ℝ → E) (x : ℝ × ℝ) :
    planeHeat θ u x = ∫ y : Euc 2, gaussKernel 2 θ (planeLp x - y) • u (planeι y) := by
  rw [planeHeat_of_pos hθ]
  rw [← integral_sub_left_eq_self (fun y : Euc 2 => gaussKernel 2 θ y • u (x - planeι y))
    volume (planeLp x)]
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  simp only [map_sub, planeι_planeLp, sub_sub_cancel]


theorem continuous_gradG (θ : ℝ) : Continuous (gradG θ) := by
  unfold gradG
  exact ((continuous_const.mul (continuous_gaussKernel θ))).smul (innerSL ℝ).continuous

theorem continuous_smulRight_pair {α E : Type*} [TopologicalSpace α] [NormedAddCommGroup E]
    [NormedSpace ℝ E] {c : α → (ℝ × ℝ) →L[ℝ] ℝ} {w : α → E} (hc : Continuous c)
    (hw : Continuous w) : Continuous fun a => (c a).smulRight (w a) :=
  (ContinuousLinearMap.smulRightL ℝ (ℝ × ℝ) E).continuous₂.comp (hc.prodMk hw)

theorem hasFDerivAt_planeHeat {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] {θ : ℝ} (hθ : 0 < θ) {u : ℝ × ℝ → E} (hu : Continuous u) {M : ℝ}
    (hM : ∀ y, ‖u y‖ ≤ M) (x₀ : ℝ × ℝ) :
    HasFDerivAt (planeHeat θ u)
      (∫ y : Euc 2, ((gradG θ (planeLp x₀ - y)).comp planeLp).smulRight (u (planeι y))) x₀ := by
  have hrep : planeHeat θ u =
      fun x => ∫ y : Euc 2, gaussKernel 2 θ (planeLp x - y) • u (planeι y) :=
    funext (planeHeat_eq_shift hθ u)
  rw [hrep]
  obtain ⟨C, hC, hCb⟩ := norm_gradG_le
  set R : ℝ := ‖planeLp‖ * (‖x₀‖ + 1) with hRdef
  have hR : 0 ≤ R := by positivity
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  set w : Euc 2 → E := fun y => u (planeι y) with hw
  have hwc : Continuous w := hu.comp continuous_planeι
  have hLc := planeLp.continuous
  have hFc : ∀ x : ℝ × ℝ, Continuous fun y : Euc 2 => gaussKernel 2 θ (planeLp x - y) • w y :=
    fun x => ((continuous_gaussKernel θ).comp (continuous_const.sub continuous_id)).smul hwc
  have hF'c : ∀ x : ℝ × ℝ, Continuous fun y : Euc 2 =>
      ((gradG θ (planeLp x - y)).comp planeLp).smulRight (w y) := by
    intro x
    refine continuous_smulRight_pair ?_ hwc
    exact ((ContinuousLinearMap.compL ℝ (ℝ × ℝ) (Euc 2) ℝ).flip planeLp).continuous.comp
      ((continuous_gradG θ).comp (continuous_const.sub continuous_id))
  refine hasFDerivAt_integral_of_dominated_of_fderiv_le (μ := (volume : Measure (Euc 2)))
    (F := fun x y => gaussKernel 2 θ (planeLp x - y) • w y)
    (F' := fun x y => ((gradG θ (planeLp x - y)).comp planeLp).smulRight (w y))
    (bound := fun y => ‖planeLp‖ * M * (C * θ ^ (-(3 / 2 : ℝ)) * Real.exp (R ^ 2 / (8 * θ))) *
      Real.exp (-(1 / (16 * θ)) * ‖y‖ ^ 2))
    (s := Metric.ball x₀ 1) (Metric.ball_mem_nhds x₀ one_pos) (Eventually.of_forall fun x => (hFc x).aestronglyMeasurable) ?_
    (hF'c x₀).aestronglyMeasurable ?_ ?_ ?_
  · refine (((integrable_gaussKernel (d := 2) hθ).comp_sub_left (planeLp x₀)).mul_const M).mono'
      (hFc x₀).aestronglyMeasurable (Eventually.of_forall fun y => ?_)
    rw [norm_smul, Real.norm_of_nonneg (gaussKernel_nonneg hθ _)]
    exact mul_le_mul_of_nonneg_left (hM _) (gaussKernel_nonneg hθ _)
  · refine Eventually.of_forall fun y x hx => ?_
    have hxn : ‖planeLp x‖ ≤ R := by
      have h1 : ‖x‖ ≤ ‖x₀‖ + 1 := by
        have := norm_le_norm_add_norm_sub' x x₀
        rw [Metric.mem_ball, dist_eq_norm] at hx
        linarith
      calc ‖planeLp x‖ ≤ ‖planeLp‖ * ‖x‖ := planeLp.le_opNorm x
        _ ≤ R := by rw [hRdef]; gcongr
    rw [ContinuousLinearMap.norm_smulRight_apply]
    have e1 := exp_shift_le hθ hR hxn (y := y)
    have e2 := hCb hθ (planeLp x - y)
    have e3 : ‖(gradG θ (planeLp x - y)).comp planeLp‖ ≤ ‖gradG θ (planeLp x - y)‖ * ‖planeLp‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    have e4 := hM (planeι y)
    have hw' : ‖w y‖ ≤ M := e4
    calc ‖(gradG θ (planeLp x - y)).comp planeLp‖ * ‖w y‖
        ≤ (‖gradG θ (planeLp x - y)‖ * ‖planeLp‖) * M := by gcongr
      _ ≤ ((C * θ ^ (-(3 / 2 : ℝ)) * Real.exp (-‖planeLp x - y‖ ^ 2 / (8 * θ))) * ‖planeLp‖) * M := by
          gcongr
      _ ≤ ((C * θ ^ (-(3 / 2 : ℝ)) * (Real.exp (R ^ 2 / (8 * θ)) *
            Real.exp (-(1 / (16 * θ)) * ‖y‖ ^ 2))) * ‖planeLp‖) * M := by
          gcongr
      _ = _ := by ring
  · exact (((Gaussian.integrable_exp_neg_mul_sq_norm (d := 2) (b := 1 / (16 * θ))
      (by positivity)).const_mul (‖planeLp‖ * M * (C * θ ^ (-(3 / 2 : ℝ)) *
        Real.exp (R ^ 2 / (8 * θ))))).congr (Eventually.of_forall fun y => by simp [neg_mul]))
  · refine Eventually.of_forall fun y x _ => ?_
    have h1 : HasFDerivAt (fun x : ℝ × ℝ => planeLp x - y) planeLp x :=
      planeLp.hasFDerivAt.sub_const y
    have h2 := (hasFDerivAt_gaussKernel_grad hθ (planeLp x - y)).comp x h1
    exact h2.smul_const (w y)


theorem integrable_norm_gradG {θ : ℝ} (hθ : 0 < θ) : Integrable (fun z : Euc 2 => ‖gradG θ z‖) := by
  have h := (memLp_one_iff_integrable.1 (memLp_iteratedFDeriv_gaussKernel (d := 2) 1 hθ 1)).norm
  refine h.congr (Eventually.of_forall fun z => ?_)
  simp only [norm_iteratedFDeriv_one, fderiv_gaussKernel_eq hθ]

theorem integral_norm_gradG {θ : ℝ} (hθ : 0 < θ) :
    ∫ z : Euc 2, ‖gradG θ z‖ = derivLpConst 2 1 1 * θ ^ (-(1 / 2 : ℝ)) := by
  have h := eLpNorm_iteratedFDeriv_gaussKernel_toReal (d := 2) 1 hθ 1
  rw [eLpNorm_one_eq_lintegral_enorm] at h
  have hI := integrable_norm_gradG hθ
  have e1 : ∫ z : Euc 2, ‖gradG θ z‖ =
      (∫⁻ z, ‖iteratedFDeriv ℝ 1 (gaussKernel 2 θ) z‖ₑ).toReal := by
    rw [← integral_norm_eq_lintegral_enorm]
    · simp only [norm_iteratedFDeriv_one, fderiv_gaussKernel_eq hθ, norm_norm]
    · exact (contDiff_gaussKernel (n := 1) θ).continuous_iteratedFDeriv le_rfl
        |>.aestronglyMeasurable
  rw [e1, h]
  congr 1
  norm_num

theorem sfcHeatBounds : SFCHeatBounds := by
  refine ⟨‖planeLp‖ * derivLpConst 2 1 1, fun θ hθ u hu M hM x => ⟨?_, ?_, ?_⟩⟩
  · exact (hasFDerivAt_planeHeat hθ hu hM x).differentiableAt
  · have := Heat.norm_heatConv_le_of_bound planeι hθ hM x
    simpa [planeHeat, hθ] using this
  · rw [(hasFDerivAt_planeHeat hθ hu hM x).fderiv]
    have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
    have hI : Integrable (fun y : Euc 2 => ‖gradG θ (planeLp x - y)‖) :=
      (integrable_norm_gradG hθ).comp_sub_left (planeLp x)
    refine (norm_integral_le_of_norm_le (hI.mul_const (‖planeLp‖ * M))
      (Eventually.of_forall fun y => ?_)).trans (le_of_eq ?_)
    · rw [ContinuousLinearMap.norm_smulRight_apply]
      calc ‖(gradG θ (planeLp x - y)).comp planeLp‖ * ‖u (planeι y)‖
          ≤ (‖gradG θ (planeLp x - y)‖ * ‖planeLp‖) * M := by
            gcongr
            · exact ContinuousLinearMap.opNorm_comp_le _ _
            · exact hM _
        _ = _ := by ring
    · rw [integral_mul_const, integral_sub_left_eq_self (fun z : Euc 2 => ‖gradG θ z‖)
        volume (planeLp x), integral_norm_gradG hθ]
      ring

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
