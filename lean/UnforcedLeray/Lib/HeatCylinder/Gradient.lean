import UnforcedLeray.Units.B0296.Conv

/-!
# Cylinder heat smoothing in divergence form

Concrete periodic-cylinder heat estimate needed by the train mild equation. The underlying
operator is the planar Gaussian heat kernel followed by divergence, acting on the normalized
cell space `dq/c dη`; the kernel derivative has exact `L¹` mass `2 / sqrt(π θ)`.

This exports the `p = 2` case for the existing `Plane = ℝ × ℝ` max norm. It is not identified
with the Euclidean `Vec` Hilbert carrier or with a Leray-projected operator. No abstract
semigroup assumption is introduced.
-/

set_option autoImplicit false
set_option maxHeartbeats 500000

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace UnforcedLeray.HeatCylinder

open UnforcedLeray.B0284 (cellMeasure IsQPeriodic)
open UnforcedLeray.GaussianVortex (Plane)

/-- The cylinder heat-divergence operator has the expected `L²` smoothing bound in the existing
`Plane` max norm. Its constant is
independent of the period `c`; with `θ = ν t` the right side is
`(2 / sqrt(π ν t)) ‖T‖₂`. This is the concrete kernel estimate used in the mild train equation. -/
theorem heatDiv_L2_smoothing {c θ : ℝ} (hc : 0 < c) (hθ : 0 < θ)
    {T : Plane → Plane × Plane} (hper : IsQPeriodic c T)
    (hT : AEStronglyMeasurable T volume) :
    eLpNorm (UnforcedLeray.B0296.heatDiv θ T) 2 (cellMeasure c) ≤
      ENNReal.ofReal (4 * (Real.sqrt (4 * Real.pi * 1 * θ))⁻¹) *
        eLpNorm T 2 (cellMeasure c) := by
  exact UnforcedLeray.B0296.eLpNorm_heatDiv_le hc hθ hper hT
    (by norm_num : (1 : ℝ≥0∞) ≤ 2) ENNReal.ofNat_ne_top

/-- Joint measurability of the scalar planar Gaussian kernel in heat time and space. -/
theorem measurable_heatKernel_param :
    Measurable (fun q : ℝ × ℝ => UnforcedLeray.B0191.heatKernel 1 q.1 q.2) := by
  unfold UnforcedLeray.B0191.heatKernel
  fun_prop

/-- Joint measurability of the scalar Gaussian derivative in heat time and space. -/
theorem measurable_dHeatKernel_param :
    Measurable (fun q : ℝ × ℝ => UnforcedLeray.B0296.dHeatKernel q.1 q.2) := by
  unfold UnforcedLeray.B0296.dHeatKernel
  have hratio : Measurable (fun q : ℝ × ℝ => q.2 / (2 * q.1)) := by
    fun_prop
  exact hratio.neg.mul measurable_heatKernel_param

/-- Joint measurability of the explicit Gaussian-gradient kernel action, including its heat-time
parameter. This is the integrand needed to establish measurability of the time-dependent mild
operator from a jointly measurable tensor path. -/
theorem measurable_divKernel_param :
    Measurable (fun q : ℝ × (Plane × (Plane × Plane)) =>
      UnforcedLeray.B0296.divKernel q.1 q.2.1 q.2.2) := by
  unfold UnforcedLeray.B0296.divKernel UnforcedLeray.B0296.gradHeatKernel2
  let p₁ : ℝ × (Plane × (Plane × Plane)) → ℝ × ℝ :=
    fun q => (q.1, q.2.1.1)
  let p₂ : ℝ × (Plane × (Plane × Plane)) → ℝ × ℝ :=
    fun q => (q.1, q.2.1.2)
  have hp₁ : Measurable p₁ := by
    exact measurable_fst.prodMk
      (measurable_fst.comp (measurable_fst.comp measurable_snd))
  have hp₂ : Measurable p₂ := by
    exact measurable_fst.prodMk
      (measurable_snd.comp (measurable_fst.comp measurable_snd))
  have hv₁ : Measurable (fun q : ℝ × (Plane × (Plane × Plane)) => q.2.2.1) :=
    measurable_fst.comp (measurable_snd.comp measurable_snd)
  have hv₂ : Measurable (fun q : ℝ × (Plane × (Plane × Plane)) => q.2.2.2) :=
    measurable_snd.comp (measurable_snd.comp measurable_snd)
  have hd₁ := measurable_dHeatKernel_param.comp hp₁
  have hd₂ := measurable_dHeatKernel_param.comp hp₂
  have hk₁ := measurable_heatKernel_param.comp hp₁
  have hk₂ := measurable_heatKernel_param.comp hp₂
  exact (hd₁.mul hk₂).smul hv₁ |>.add ((hk₁.mul hd₂).smul hv₂)

/-- The full space-time/kernel integrand for `e^{ν(s-r)Δ} div T(r)`. If the input tensor path is
jointly measurable, the explicit Gaussian-gradient integrand is jointly measurable as well. -/
theorem measurable_heatDiv_timeKernel {ν s : ℝ} {T : ℝ × Plane → Plane × Plane}
    (hT : Measurable T) :
    Measurable (fun q : ℝ × Plane × Plane =>
      UnforcedLeray.B0296.divKernel (ν * (s - q.1)) q.2.2
        (T (q.1, q.2.1 - q.2.2))) := by
  have hθ : Measurable (fun q : ℝ × Plane × Plane => ν * (s - q.1)) := by
    exact measurable_const.mul (measurable_const.sub measurable_fst)
  have hw : Measurable (fun q : ℝ × Plane × Plane => q.2.2) :=
    measurable_snd.comp measurable_snd
  have hT' : Measurable (fun q : ℝ × Plane × Plane => T (q.1, q.2.1 - q.2.2)) := by
    exact hT.comp (measurable_fst.prodMk
      ((measurable_fst.comp measurable_snd).sub (measurable_snd.comp measurable_snd)))
  have hm : Measurable (fun q : ℝ × Plane × Plane =>
      (ν * (s - q.1), (q.2.2, T (q.1, q.2.1 - q.2.2)))) :=
    hθ.prodMk (hw.prodMk hT')
  exact measurable_divKernel_param.comp hm

/-- The actual `B0296.heatDiv` output along a jointly measurable tensor path is jointly almost
everywhere strongly measurable in time and space. This keeps the concrete Gaussian integral
formula and allows the spatial measure to be restricted to one cylinder cell. -/
theorem aestronglyMeasurable_heatDiv_timePath {c ν s : ℝ}
    {T : ℝ × Plane → Plane × Plane} (hT : Measurable T) :
    AEStronglyMeasurable
      (fun q : ℝ × Plane =>
        UnforcedLeray.B0296.heatDiv (ν * (s - q.1)) (fun z => T (q.1, z)) q.2)
      ((volume : Measure ℝ).prod (cellMeasure c)) := by
  let kernel (q : (ℝ × Plane) × Plane) : Plane :=
    UnforcedLeray.B0296.divKernel (ν * (s - q.1.1)) q.2
      (T (q.1.1, q.1.2 - q.2))
  have hkernel : Measurable kernel := by
    have hmap : Measurable (fun q : (ℝ × Plane) × Plane => (q.1.1, q.1.2, q.2)) := by
      exact (measurable_fst.comp measurable_fst).prodMk
        ((measurable_snd.comp measurable_fst).prodMk measurable_snd)
    exact measurable_heatDiv_timeKernel hT |>.comp hmap
  have hint : AEStronglyMeasurable (fun q : ℝ × Plane => ∫ w : Plane, kernel (q, w))
      ((volume : Measure ℝ).prod volume) :=
    hkernel.aestronglyMeasurable.integral_prod_right'
  have hintCell : AEStronglyMeasurable (fun q : ℝ × Plane => ∫ w : Plane, kernel (q, w))
      ((volume : Measure ℝ).prod (cellMeasure c)) :=
    hint.mono_ac (Measure.AbsolutelyContinuous.rfl.prod
      (UnforcedLeray.B0284.cellMeasure_ac c))
  have hθ : Measurable (fun q : ℝ × Plane => ν * (s - q.1)) := by
    exact measurable_const.mul (measurable_const.sub measurable_fst)
  have hset : MeasurableSet {q : ℝ × Plane | 0 < ν * (s - q.1)} :=
    measurableSet_lt measurable_const hθ
  have hpw : AEStronglyMeasurable
      (fun q : ℝ × Plane => if 0 < ν * (s - q.1) then ∫ w : Plane, kernel (q, w) else 0)
      ((volume : Measure ℝ).prod (cellMeasure c)) := by
    rcases hintCell with ⟨g, hg, hEq⟩
    refine ⟨fun q => if 0 < ν * (s - q.1) then g q else 0, ?_, ?_⟩
    · exact hg.piecewise hset stronglyMeasurable_const
    · filter_upwards [hEq] with q hq
      by_cases hqθ : 0 < ν * (s - q.1) <;> simp [hqθ, hq]
  refine hpw.congr ?_
  filter_upwards [] with q
  by_cases hq : 0 < ν * (s - q.1)
  · simp [UnforcedLeray.B0296.heatDiv, hq, kernel]
  · simp [UnforcedLeray.B0296.heatDiv, hq]

/-- The spatial heat-divergence operator respects volume-a.e. equality of periodic cylinder
tensors, when both inputs are in cell `L²`. This is the representative-independence step needed
to descend the pointwise kernel formula to cylinder `L²`. -/
theorem heatDiv_congr_ae {c θ : ℝ} (hc : 0 < c) (hθ : 0 < θ)
    {T₁ T₂ : Plane → Plane × Plane}
    (hper₁ : IsQPeriodic c T₁) (hper₂ : IsQPeriodic c T₂)
    (hT₁m : AEStronglyMeasurable T₁ volume) (hT₂m : AEStronglyMeasurable T₂ volume)
    (hT₁ : MemLp T₁ 2 (cellMeasure c)) (hT₂ : MemLp T₂ 2 (cellMeasure c))
    (hTae : T₁ =ᵐ[volume] T₂) :
    UnforcedLeray.B0296.heatDiv θ T₁ =ᵐ[cellMeasure c] UnforcedLeray.B0296.heatDiv θ T₂ := by
  have hdiff : T₁ - T₂ =ᵐ[cellMeasure c] 0 := by
    have hnull : volume {z : Plane | T₁ z ≠ T₂ z} = 0 := by
      change volume {z : Plane | (fun z => T₁ z = T₂ z) z}ᶜ = 0
      exact hTae
    have hcellnull := (UnforcedLeray.B0284.cellMeasure_ac c) hnull
    filter_upwards [ae_iff.mpr hcellnull] with z hz
    simp [hz]
  have hnorm : eLpNorm (T₁ - T₂) 2 (cellMeasure c) = 0 := by
    rw [eLpNorm_congr_ae hdiff]
    simp
  have hbound := UnforcedLeray.B0296.eLpNorm_heatDiv_sub_le hc hθ hper₁ hper₂ hT₁m hT₂m
    (by norm_num : (1 : ℝ≥0∞) ≤ 2) ENNReal.ofNat_ne_top hT₁.eLpNorm_ne_top hT₂.eLpNorm_ne_top
  have hzero : eLpNorm (UnforcedLeray.B0296.heatDiv θ T₁ -
      UnforcedLeray.B0296.heatDiv θ T₂) 2 (cellMeasure c) = 0 := by
    apply le_antisymm
    · simpa [hnorm] using hbound
    · exact bot_le
  have hmem₁ := UnforcedLeray.B0296.memLp_heatDiv hc hθ hper₁ hT₁m
    (by norm_num : (1 : ℝ≥0∞) ≤ 2) ENNReal.ofNat_ne_top hT₁.eLpNorm_ne_top
  have hmem₂ := UnforcedLeray.B0296.memLp_heatDiv hc hθ hper₂ hT₂m
    (by norm_num : (1 : ℝ≥0∞) ≤ 2) ENNReal.ofNat_ne_top hT₂.eLpNorm_ne_top
  have hdiffMem := hmem₁.sub hmem₂
  have hae := (eLpNorm_eq_zero_iff hdiffMem.aestronglyMeasurable two_ne_zero).mp hzero
  filter_upwards [hae] with z hz
  exact sub_eq_zero.mp hz

end UnforcedLeray.HeatCylinder
