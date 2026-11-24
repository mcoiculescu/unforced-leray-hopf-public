import UnforcedLeray.Lib.HeatCylinder.KernelTimeMajorant

/-!
# Positive-time continuity of the actual Gaussian-gradient kernel

The local time DCT uses the existing exact gradient mass as an integrable dominating function.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace UnforcedLeray.HeatCylinder

open UnforcedLeray.GaussianVortex (Plane)

/-- The real-valued version of the exact Gaussian-gradient mass is integrable in the plane. -/
theorem integrable_gradKernelAbs_toReal {b : ℝ} (hb : 0 < b) :
    Integrable (fun w : Plane => (UnforcedLeray.B0296.gradKernelAbs b w).toReal) := by
  refine ⟨(UnforcedLeray.B0296.measurable_gradKernelAbs b).ennreal_toReal.aestronglyMeasurable,
    ?_⟩
  change ∫⁻ w : Plane, ‖(UnforcedLeray.B0296.gradKernelAbs b w).toReal‖ₑ < ∞
  have hnorm : (fun w : Plane =>
      ‖(UnforcedLeray.B0296.gradKernelAbs b w).toReal‖ₑ) =
      UnforcedLeray.B0296.gradKernelAbs b := by
    funext w
    rw [Real.enorm_eq_ofReal_abs, abs_of_nonneg ENNReal.toReal_nonneg,
      ENNReal.ofReal_toReal (UnforcedLeray.B0296.gradKernelAbs_ne_top b w)]
  rw [hnorm, UnforcedLeray.B0296.lintegral_gradKernelAbs hb]
  exact ENNReal.ofReal_lt_top

/-- Positive-time continuity of the one-dimensional Gaussian kernel in its heat parameter. -/
private theorem continuousOn_heatKernel_age (x : ℝ) :
    ContinuousOn (fun θ : ℝ => UnforcedLeray.B0191.heatKernel 1 θ x) (Ioi 0) := by
  unfold UnforcedLeray.B0191.heatKernel
  have harg : Continuous (fun θ : ℝ => 4 * Real.pi * 1 * θ) := by fun_prop
  have hsqrt : Continuous (fun θ : ℝ => Real.sqrt (4 * Real.pi * 1 * θ)) :=
    Real.continuous_sqrt.comp harg
  have hsqrtnz : ∀ θ ∈ Ioi (0 : ℝ), Real.sqrt (4 * Real.pi * 1 * θ) ≠ 0 := by
    intro θ hθ
    have hp : 0 < 4 * Real.pi * 1 * θ :=
      mul_pos (mul_pos (mul_pos (by norm_num : (0 : ℝ) < 4) Real.pi_pos)
        (by norm_num)) hθ
    exact (Real.sqrt_pos.2 hp).ne'
  have hpref : ContinuousOn
      (fun θ : ℝ => (Real.sqrt (4 * Real.pi * 1 * θ))⁻¹) (Ioi 0) :=
    hsqrt.continuousOn.inv₀ hsqrtnz
  have hden : ContinuousOn (fun θ : ℝ => 4 * θ) (Ioi 0) := by fun_prop
  have hdennz : ∀ θ ∈ Ioi (0 : ℝ), 4 * θ ≠ 0 := by
    intro θ hθ
    exact (mul_pos (by norm_num : (0 : ℝ) < 4) hθ).ne'
  have hinv : ContinuousOn (fun θ : ℝ => (4 * θ)⁻¹) (Ioi 0) :=
    hden.inv₀ hdennz
  have hexpArg : ContinuousOn (fun θ : ℝ => -(x ^ 2) * (4 * θ)⁻¹) (Ioi 0) :=
    continuousOn_const.mul hinv
  have hexp : ContinuousOn (fun θ : ℝ => Real.exp (-(x ^ 2) * (4 * θ)⁻¹))
      (Ioi 0) := by
    have hExpAll : ContinuousOn Real.exp Set.univ := Real.continuous_exp.continuousOn
    exact hExpAll.comp hexpArg (by intro θ hθ; exact Set.mem_univ _)
  have hp := hpref.mul hexp
  convert hp using 1
  ext θ
  simp only [neg_div, div_eq_mul_inv, mul_one, Pi.mul_apply]

private theorem continuousOn_dHeatKernel_age (x : ℝ) :
    ContinuousOn (fun θ : ℝ => UnforcedLeray.B0296.dHeatKernel θ x) (Ioi 0) := by
  unfold UnforcedLeray.B0296.dHeatKernel
  have hden : ContinuousOn (fun θ : ℝ => 2 * θ) (Ioi 0) := by fun_prop
  have hdennz : ∀ θ ∈ Ioi (0 : ℝ), 2 * θ ≠ 0 := by
    intro θ hθ
    exact (mul_pos (by norm_num : (0 : ℝ) < 2) hθ).ne'
  have hinv : ContinuousOn (fun θ : ℝ => (2 * θ)⁻¹) (Ioi 0) := hden.inv₀ hdennz
  have hfactor : ContinuousOn (fun θ : ℝ => -(x / (2 * θ))) (Ioi 0) := by
    have hconst : ContinuousOn (fun _ : ℝ => -x) (Ioi 0) := continuousOn_const
    have hprod := hconst.mul hinv
    convert hprod using 1
    ext θ
    simp only [div_eq_mul_inv, neg_mul, mul_comm, Pi.mul_apply]
  have hkernel := continuousOn_heatKernel_age x
  have hprod := hfactor.mul hkernel
  convert hprod using 1
  ext θ
  rfl

/-- For fixed displacement, the actual divergence kernel as a continuous linear map is
continuous in positive heat age. -/
theorem continuousOn_divKernelCLM_time (w : Plane) :
    ContinuousOn (fun θ : ℝ => divKernelCLM θ w) (Ioi 0) := by
  have hg₁ : ContinuousOn (fun θ : ℝ =>
      (UnforcedLeray.B0296.gradHeatKernel2 θ w).1) (Ioi 0) := by
    change ContinuousOn (fun θ =>
      UnforcedLeray.B0296.dHeatKernel θ w.1 *
        UnforcedLeray.B0191.heatKernel 1 θ w.2) (Ioi 0)
    exact (continuousOn_dHeatKernel_age w.1).mul (continuousOn_heatKernel_age w.2)
  have hg₂ : ContinuousOn (fun θ : ℝ =>
      (UnforcedLeray.B0296.gradHeatKernel2 θ w).2) (Ioi 0) := by
    change ContinuousOn (fun θ =>
      UnforcedLeray.B0191.heatKernel 1 θ w.1 *
        UnforcedLeray.B0296.dHeatKernel θ w.2) (Ioi 0)
    exact (continuousOn_heatKernel_age w.1).mul (continuousOn_dHeatKernel_age w.2)
  unfold divKernelCLM
  exact (hg₁.smul continuousOn_const).add (hg₂.smul continuousOn_const)

private theorem continuous_divKernelCLM_space (θ : ℝ) :
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

/-- The `L¹` difference of the actual Gaussian-gradient continuous-linear kernels tends to zero
with the heat age. Its dominating function is an explicit multiple of the exact gradient mass at
the fixed positive time `θ₀`. -/
theorem tendsto_integral_norm_divKernelCLM_sub {θ₀ : ℝ} (hθ₀ : 0 < θ₀) :
    Tendsto (fun θ : ℝ => ∫ w : Plane,
      ‖divKernelCLM θ w - divKernelCLM θ₀ w‖) (𝓝 θ₀) (𝓝 0) := by
  let a : ℝ := θ₀ / 2
  let b : ℝ := 2 * θ₀
  let C : ℝ := (b / a) ^ 2
  let F : ℝ → Plane → ℝ := fun θ w => ‖divKernelCLM θ w - divKernelCLM θ₀ w‖
  let g : Plane → ℝ := fun w => (2 * C) *
    (UnforcedLeray.B0296.gradKernelAbs b w).toReal
  have ha : 0 < a := by dsimp [a]; linarith
  have hb : 0 < b := by dsimp [b]; positivity
  have hθ₀ab : θ₀ ∈ Icc a b := by
    simp only [mem_Icc, a, b]
    constructor <;> linarith
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hg : Integrable g := by
    have hbase := integrable_gradKernelAbs_toReal hb
    have hmul := hbase.const_mul (2 * C)
    refine hmul.congr ?_
    filter_upwards [] with w
    simp [g, mul_comm]
  have hmeas : ∀ᶠ θ in 𝓝 θ₀, AEStronglyMeasurable (F θ) volume := by
    filter_upwards [] with θ
    exact (continuous_divKernelCLM_space θ).sub (continuous_divKernelCLM_space θ₀) |>.norm.measurable.aestronglyMeasurable
  have hdom : ∀ᶠ θ in 𝓝 θ₀, ∀ᵐ w ∂(volume : Measure Plane),
      ‖F θ w‖ ≤ g w := by
    have hlo : a < θ₀ := by dsimp [a]; linarith
    have hhi : θ₀ < b := by dsimp [b]; linarith
    filter_upwards [Icc_mem_nhds hlo hhi]
      with θ hθ
    refine Eventually.of_forall fun w => ?_
    have hθpos : 0 < θ := lt_of_lt_of_le ha hθ.1
    have hgrad := gradKernelAbs_le_of_interval ha hθpos hb hθ.1 hθ.2 w
    have hright : ENNReal.ofReal C * UnforcedLeray.B0296.gradKernelAbs b w ≠ ∞ :=
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top
        (UnforcedLeray.B0296.gradKernelAbs_ne_top b w)
    have hreal := ENNReal.toReal_mono hright hgrad
    rw [ENNReal.toReal_mul,
      ENNReal.toReal_ofReal hC] at hreal
    have hkernelθ : ‖divKernelCLM θ w‖ ≤
        C * (UnforcedLeray.B0296.gradKernelAbs b w).toReal :=
      (divKernelCLM_norm_le θ w).trans hreal
    have hkernel₀ : ‖divKernelCLM θ₀ w‖ ≤
        C * (UnforcedLeray.B0296.gradKernelAbs b w).toReal := by
      have h₀ := divKernelCLM_norm_le θ₀ w
      have hmass := gradKernelAbs_le_of_interval ha hθ₀ hb hθ₀ab.1 hθ₀ab.2 w
      have hfinite : ENNReal.ofReal C *
          UnforcedLeray.B0296.gradKernelAbs b w ≠ ∞ :=
        ENNReal.mul_ne_top ENNReal.ofReal_ne_top
          (UnforcedLeray.B0296.gradKernelAbs_ne_top b w)
      have hreal0 := ENNReal.toReal_mono hfinite hmass
      rw [ENNReal.toReal_mul,
        ENNReal.toReal_ofReal hC] at hreal0
      exact h₀.trans hreal0
    have hnorm := norm_sub_le (divKernelCLM θ w) (divKernelCLM θ₀ w)
    have hbound : ‖divKernelCLM θ w - divKernelCLM θ₀ w‖ ≤
        (2 * C) * (UnforcedLeray.B0296.gradKernelAbs b w).toReal := by
      calc
        _ ≤ ‖divKernelCLM θ w‖ + ‖divKernelCLM θ₀ w‖ := hnorm
        _ ≤ C * (UnforcedLeray.B0296.gradKernelAbs b w).toReal +
            C * (UnforcedLeray.B0296.gradKernelAbs b w).toReal := by
          gcongr
        _ = (2 * C) * (UnforcedLeray.B0296.gradKernelAbs b w).toReal := by ring
    simpa [F, g] using hbound
  have hpoint : ∀ᵐ w ∂(volume : Measure Plane),
      Tendsto (fun θ : ℝ => F θ w) (𝓝 θ₀) (𝓝 0) := by
    filter_upwards [] with w
    have hcont := (continuousOn_divKernelCLM_time w).continuousAt
      (Ioi_mem_nhds hθ₀)
    have hconst : Tendsto (fun _ : ℝ => divKernelCLM θ₀ w) (𝓝 θ₀)
        (𝓝 (divKernelCLM θ₀ w)) := tendsto_const_nhds
    have hlim := ((hcont.sub hconst).norm).tendsto
    simpa [F] using hlim
  have h := tendsto_integral_filter_of_dominated_convergence (μ := volume) (l := 𝓝 θ₀)
    (F := F) (f := fun _ => (0 : ℝ)) g hmeas hdom hg hpoint
  simpa [F] using h

end UnforcedLeray.HeatCylinder

#print axioms UnforcedLeray.HeatCylinder.integrable_gradKernelAbs_toReal
