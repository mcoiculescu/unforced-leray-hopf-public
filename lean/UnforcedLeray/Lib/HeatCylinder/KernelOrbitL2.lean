import UnforcedLeray.Lib.HeatCylinder.KernelTimeContinuity

/-!
# L² continuity of the actual periodic heat-divergence kernel

The time difference is itself an actual convolution, with the operator-norm difference of the
two Gaussian-gradient kernels as an L¹ majorant. -/

set_option autoImplicit false
set_option maxHeartbeats 500000

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace UnforcedLeray.HeatCylinder

open UnforcedLeray.B0284 (cellMeasure IsQPeriodic)
open UnforcedLeray.GaussianVortex (Plane)

private def divKernelTimeDiff (θ θ₀ : ℝ) (w : Plane) :
    (Plane × Plane) →L[ℝ] Plane := divKernelCLM θ w - divKernelCLM θ₀ w

private def divKernelTimeDiffAbs (θ θ₀ : ℝ) (w : Plane) : ℝ≥0∞ :=
  ENNReal.ofReal ‖divKernelTimeDiff θ θ₀ w‖

private theorem continuous_divKernelCLM_space_local (θ : ℝ) :
    Continuous (fun w : Plane => divKernelCLM θ w) := by
  have hg₁ : Continuous (fun w : Plane => (UnforcedLeray.B0296.gradHeatKernel2 θ w).1) := by
    unfold UnforcedLeray.B0296.gradHeatKernel2
    exact (UnforcedLeray.B0296.continuous_dHeatKernel θ).comp continuous_fst |>.mul
      ((UnforcedLeray.B0296.continuous_heatKernel1 θ).comp continuous_snd)
  have hg₂ : Continuous (fun w : Plane => (UnforcedLeray.B0296.gradHeatKernel2 θ w).2) := by
    unfold UnforcedLeray.B0296.gradHeatKernel2
    exact ((UnforcedLeray.B0296.continuous_heatKernel1 θ).comp continuous_fst).mul
      ((UnforcedLeray.B0296.continuous_dHeatKernel θ).comp continuous_snd)
  unfold divKernelCLM
  exact (hg₁.smul continuous_const).add (hg₂.smul continuous_const)

private theorem divKernelTimeDiffAbs_measurable (θ θ₀ : ℝ) :
    Measurable (divKernelTimeDiffAbs θ θ₀) := by
  have hθ := continuous_divKernelCLM_space_local θ
  have hθ₀ := continuous_divKernelCLM_space_local θ₀
  have hnorm := (hθ.sub hθ₀).norm.measurable
  have hEq : divKernelTimeDiffAbs θ θ₀ =
      fun w => ENNReal.ofReal ‖divKernelCLM θ w - divKernelCLM θ₀ w‖ := by
    funext w
    rfl
  rw [hEq]
  exact hnorm.ennreal_ofReal

private theorem divKernelTimeDiffAbs_ne_top (θ θ₀ : ℝ) (w : Plane) :
    divKernelTimeDiffAbs θ θ₀ w ≠ ⊤ := by
  rw [divKernelTimeDiffAbs, divKernelTimeDiff]
  exact ENNReal.ofReal_ne_top

private theorem divKernelTimeDiffAbs_le_gradSum {θ θ₀ : ℝ} (w : Plane) :
    divKernelTimeDiffAbs θ θ₀ w ≤
      UnforcedLeray.B0296.gradKernelAbs θ w + UnforcedLeray.B0296.gradKernelAbs θ₀ w := by
  have hnorm := norm_sub_le (divKernelCLM θ w) (divKernelCLM θ₀ w)
  have hreal : ‖divKernelCLM θ w - divKernelCLM θ₀ w‖ ≤
      (UnforcedLeray.B0296.gradKernelAbs θ w).toReal +
        (UnforcedLeray.B0296.gradKernelAbs θ₀ w).toReal := by
    calc
      _ ≤ ‖divKernelCLM θ w‖ + ‖divKernelCLM θ₀ w‖ := hnorm
      _ ≤ _ := add_le_add (divKernelCLM_norm_le θ w) (divKernelCLM_norm_le θ₀ w)
  have htop₁ := UnforcedLeray.B0296.gradKernelAbs_ne_top θ w
  have htop₀ := UnforcedLeray.B0296.gradKernelAbs_ne_top θ₀ w
  rw [divKernelTimeDiffAbs, divKernelTimeDiff]
  rw [← ENNReal.ofReal_toReal htop₁, ← ENNReal.ofReal_toReal htop₀,
    ← ENNReal.ofReal_add ENNReal.toReal_nonneg ENNReal.toReal_nonneg]
  exact ENNReal.ofReal_le_ofReal hreal

private theorem integrable_divKernelTimeDiff_norm {θ θ₀ : ℝ}
    (hθ : 0 < θ) (hθ₀ : 0 < θ₀) :
    Integrable (fun w : Plane => ‖divKernelCLM θ w - divKernelCLM θ₀ w‖) := by
  have h₁ := integrable_gradKernelAbs_toReal hθ
  have h₀ := integrable_gradKernelAbs_toReal hθ₀
  have hsum := h₁.add h₀
  have hmeas : AEStronglyMeasurable
      (fun w : Plane => ‖divKernelCLM θ w - divKernelCLM θ₀ w‖) :=
    ((continuous_divKernelCLM_space_local θ).sub (continuous_divKernelCLM_space_local θ₀)).norm.measurable.aestronglyMeasurable
  refine hsum.mono' hmeas (Filter.Eventually.of_forall fun w => ?_)
  have hn := norm_sub_le (divKernelCLM θ w) (divKernelCLM θ₀ w)
  calc
    ‖‖divKernelCLM θ w - divKernelCLM θ₀ w‖‖ ≤
        ‖divKernelCLM θ w‖ + ‖divKernelCLM θ₀ w‖ := by
          rw [norm_norm]
          exact hn
    _ ≤ (UnforcedLeray.B0296.gradKernelAbs θ w).toReal +
        (UnforcedLeray.B0296.gradKernelAbs θ₀ w).toReal :=
      add_le_add (divKernelCLM_norm_le θ w) (divKernelCLM_norm_le θ₀ w)

/-- The cylinder `L²` norm of the difference of two actual heat-divergence outputs is bounded
by the `L¹` difference of their actual operator kernels. -/
theorem eLpNorm_heatDiv_timeDiff_le {c θ θ₀ : ℝ} (hc : 0 < c)
    (hθ : 0 < θ) (hθ₀ : 0 < θ₀) {T : Plane → Plane × Plane}
    (hper : IsQPeriodic c T) (hTm : AEStronglyMeasurable T volume)
    (hT : MemLp T 2 (cellMeasure c)) :
    eLpNorm (UnforcedLeray.B0296.heatDiv θ T - UnforcedLeray.B0296.heatDiv θ₀ T)
      2 (cellMeasure c) ≤
      ENNReal.ofReal (∫ w : Plane, ‖divKernelCLM θ w - divKernelCLM θ₀ w‖) *
        eLpNorm T 2 (cellMeasure c) := by
  let A := divKernelTimeDiff θ θ₀
  let k := divKernelTimeDiffAbs θ θ₀
  have hk : Measurable k := divKernelTimeDiffAbs_measurable θ θ₀
  have hk' : ∀ w, k w ≠ ⊤ := divKernelTimeDiffAbs_ne_top θ θ₀
  have hmassReal := integrable_divKernelTimeDiff_norm hθ hθ₀
  have hmass : ∫⁻ w : Plane, k w =
      ENNReal.ofReal (∫ w : Plane, ‖divKernelCLM θ w - divKernelCLM θ₀ w‖) := by
    calc
      ∫⁻ w : Plane, k w = ∫⁻ w : Plane,
          ENNReal.ofReal ‖divKernelCLM θ w - divKernelCLM θ₀ w‖ := by
        exact lintegral_congr fun w => by
          simp [k, divKernelTimeDiffAbs, divKernelTimeDiff]
      _ = ENNReal.ofReal (∫ w : Plane,
          ‖divKernelCLM θ w - divKernelCLM θ₀ w‖) :=
        (ofReal_integral_eq_lintegral_ofReal hmassReal
          (Filter.Eventually.of_forall fun w => by positivity)).symm
  have hmassTop : (∫⁻ w : Plane, k w) ≠ ⊤ := by
    rw [hmass]
    exact ENNReal.ofReal_ne_top
  have hA : ∀ w x, ‖A w x‖ₑ ≤ k w * ‖x‖ₑ := by
    intro w x
    have hn := (A w).le_opNorm x
    calc
      ‖(divKernelTimeDiff θ θ₀ w) x‖ₑ = ENNReal.ofReal ‖(divKernelTimeDiff θ θ₀ w) x‖ :=
        (ofReal_norm _).symm
      _ ≤ ENNReal.ofReal (‖divKernelTimeDiff θ θ₀ w‖ * ‖x‖) :=
        ENNReal.ofReal_le_ofReal hn
      _ = ‖divKernelTimeDiff θ θ₀ w‖ₑ * ‖x‖ₑ := by
        rw [← ofReal_norm, ← ofReal_norm,
          ← ENNReal.ofReal_mul (norm_nonneg _)]
      _ = k w * ‖x‖ₑ := by
        simp [k, divKernelTimeDiffAbs, divKernelTimeDiff, ← ofReal_norm]
  have hconv := UnforcedLeray.B0296.eLpNorm_kconv_le (E := Plane × Plane) hc hk hk'
    (fun w x => A w x) hA hper hTm
    (by norm_num : (1 : ℝ≥0∞) ≤ 2) ENNReal.ofNat_ne_top
  have hfiniteθ : ∫⁻ w : Plane, UnforcedLeray.B0296.gradKernelAbs θ w ≠ ⊤ := by
    rw [UnforcedLeray.B0296.lintegral_gradKernelAbs hθ]
    exact ENNReal.ofReal_ne_top
  have hfiniteθ₀ : ∫⁻ w : Plane, UnforcedLeray.B0296.gradKernelAbs θ₀ w ≠ ⊤ := by
    rw [UnforcedLeray.B0296.lintegral_gradKernelAbs hθ₀]
    exact ENNReal.ofReal_ne_top
  have hbadθ := UnforcedLeray.B0296.ae_kernelAbs_lt_top'
    hc (UnforcedLeray.B0296.measurable_gradKernelAbs θ)
    (UnforcedLeray.B0296.gradKernelAbs_ne_top θ) hfiniteθ hper hTm
    (by norm_num : (1 : ℝ≥0∞) ≤ 2) ENNReal.ofNat_ne_top hT.eLpNorm_ne_top
  have hbadθ₀ := UnforcedLeray.B0296.ae_kernelAbs_lt_top'
    hc (UnforcedLeray.B0296.measurable_gradKernelAbs θ₀)
    (UnforcedLeray.B0296.gradKernelAbs_ne_top θ₀) hfiniteθ₀ hper hTm
    (by norm_num : (1 : ℝ≥0∞) ≤ 2) ENNReal.ofNat_ne_top hT.eLpNorm_ne_top
  have hEq : (UnforcedLeray.B0296.heatDiv θ T - UnforcedLeray.B0296.heatDiv θ₀ T) =ᵐ[
      cellMeasure c] (fun z => ∫ w : Plane, A w (T (z - w))) := by
    filter_upwards [hbadθ, hbadθ₀] with z hz hz₀
    have hiθ := UnforcedLeray.B0296.integrable_kconv_of_lt_top
      (A := UnforcedLeray.B0296.divKernel θ)
      (UnforcedLeray.B0296.enorm_divKernel_le θ) z
      (UnforcedLeray.B0296.aestronglyMeasurable_divIntegrand θ hTm z) hz
    have hiθ₀ := UnforcedLeray.B0296.integrable_kconv_of_lt_top
      (A := UnforcedLeray.B0296.divKernel θ₀)
      (UnforcedLeray.B0296.enorm_divKernel_le θ₀) z
      (UnforcedLeray.B0296.aestronglyMeasurable_divIntegrand θ₀ hTm z) hz₀
    change UnforcedLeray.B0296.heatDiv θ T z -
      UnforcedLeray.B0296.heatDiv θ₀ T z = _
    rw [UnforcedLeray.B0296.heatDiv_apply_of_pos hθ,
      UnforcedLeray.B0296.heatDiv_apply_of_pos hθ₀,
      ← integral_sub hiθ hiθ₀]
    simp [A, divKernelTimeDiff, divKernelCLM_apply]
  rw [eLpNorm_congr_ae hEq]
  exact hconv.trans_eq (by rw [hmass])

end UnforcedLeray.HeatCylinder

#print axioms UnforcedLeray.HeatCylinder.eLpNorm_heatDiv_timeDiff_le
