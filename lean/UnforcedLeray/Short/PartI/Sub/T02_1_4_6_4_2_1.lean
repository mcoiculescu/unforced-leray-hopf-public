import UnforcedLeray.Short.PartI.Sub.T02_1_4_6_4_2
import UnforcedLeray.Lib.HeatCylinder.HeatKernelAgeMajorant
import UnforcedLeray.Lib.HeatCylinder.HeatKernelAgeDerivative
import Mathlib.Analysis.Calculus.ParametricIntegral

/-!
# Part I, leaf `PartI:T02/1/4/6/4/2/1` (`LeafAgeWeightedCH`)

Scalar age derivative of the planar Gaussian integral against a bounded continuous weight.
This is the scalar analogue of `HeatCylinder.hasDerivAt_heatVecConvolution_age`
(`Lib/HeatCylinder/HeatVecAgeDerivative.lean`), proved directly with
`hasDerivAt_integral_of_dominated_loc_of_deriv_le`, so no vector-valued reduction is needed.
The dominating function is the local majorant of `HeatKernelAgeMajorant`, times `M`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace UnforcedLeray.Short.PartI

open UnforcedLeray.GaussianVortex (Plane)

theorem leafAgeWeightedCH_proof : UnforcedLeray.Short.PartI.LeafAgeWeightedCH := by
  unfold UnforcedLeray.Short.PartI.LeafAgeWeightedCH
  intro θ hθ G hG hGb
  obtain ⟨M, hM⟩ := hGb
  have hM0 : 0 ≤ M := le_trans (norm_nonneg _) (hM 0)
  have hθhalf : θ / 2 < θ := by linarith
  have hθdouble : θ < 2 * θ := by linarith
  have hball : Set.Ioo (θ / 2) (2 * θ) ∈ 𝓝 θ := Ioo_mem_nhds hθhalf hθdouble
  have hwide : Integrable
      (fun w : Plane => (1 + w.1 ^ 2 + w.2 ^ 2) *
        UnforcedLeray.B0284.heatKernel2 (2 * θ) w) :=
    UnforcedLeray.HeatCylinder.integrable_one_add_sq_mul_heatKernel2 (by positivity)
  have hdomInt : Integrable
      (fun w : Plane => 4 * (θ⁻¹ ^ 2 + 2 / θ) * M *
        ((1 + w.1 ^ 2 + w.2 ^ 2) * UnforcedLeray.B0284.heatKernel2 (2 * θ) w)) :=
    hwide.const_mul _
  have hkc : ∀ s : ℝ, Continuous (UnforcedLeray.B0284.heatKernel2 s) := by
    intro s
    unfold UnforcedLeray.B0284.heatKernel2 UnforcedLeray.B0191.heatKernel
    fun_prop
  have hFmeas : ∀ᶠ s : ℝ in 𝓝 θ,
      AEStronglyMeasurable (fun w : Plane => UnforcedLeray.B0284.heatKernel2 s w * G w)
        volume := by
    refine Eventually.of_forall fun s => ?_
    exact ((hkc s).mul hG).aestronglyMeasurable
  have hFint : Integrable (fun w : Plane => UnforcedLeray.B0284.heatKernel2 θ w * G w) := by
    refine Integrable.mono'
      ((UnforcedLeray.B0284.integrable_heatKernel2 hθ).mul_const M)
      ((hkc θ).mul hG).aestronglyMeasurable ?_
    refine Eventually.of_forall fun w => ?_
    rw [norm_mul, Real.norm_of_nonneg (UnforcedLeray.B0284.heatKernel2_nonneg hθ w)]
    exact mul_le_mul_of_nonneg_left (hM w) (UnforcedLeray.B0284.heatKernel2_nonneg hθ w)
  have hFprimeMeas : AEStronglyMeasurable
      (fun w : Plane => UnforcedLeray.HeatCylinder.heatKernel2AgeDerivative θ w * G w) volume := by
    have hk : Measurable (UnforcedLeray.HeatCylinder.heatKernel2AgeDerivative θ) := by
      unfold UnforcedLeray.HeatCylinder.heatKernel2AgeDerivative
        UnforcedLeray.B0284.heatKernel2 UnforcedLeray.B0191.heatKernel
      fun_prop
    exact (hk.mul hG.measurable).aestronglyMeasurable
  have hFprimeBound : ∀ᵐ w ∂(volume : Measure Plane), ∀ s ∈ Set.Ioo (θ / 2) (2 * θ),
      ‖UnforcedLeray.HeatCylinder.heatKernel2AgeDerivative s w * G w‖ ≤
        4 * (θ⁻¹ ^ 2 + 2 / θ) * M *
          ((1 + w.1 ^ 2 + w.2 ^ 2) * UnforcedLeray.B0284.heatKernel2 (2 * θ) w) := by
    refine Eventually.of_forall fun w => ?_
    intro s hs
    have hlocal := UnforcedLeray.HeatCylinder.abs_heatKernel2AgeDerivative_le_local
      (θ₀ := θ) hθ hs.1 hs.2 w
    have hGM : |G w| ≤ M := by
      rw [← Real.norm_eq_abs]
      exact hM w
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
    calc |UnforcedLeray.HeatCylinder.heatKernel2AgeDerivative s w| * |G w|
        ≤ |UnforcedLeray.HeatCylinder.heatKernel2AgeDerivative s w| * M :=
          mul_le_mul_of_nonneg_left hGM (abs_nonneg _)
      _ ≤ (4 * (θ⁻¹ ^ 2 + 2 / θ) *
          ((1 + w.1 ^ 2 + w.2 ^ 2) * UnforcedLeray.B0284.heatKernel2 (2 * θ) w)) * M :=
          mul_le_mul_of_nonneg_right hlocal hM0
      _ = 4 * (θ⁻¹ ^ 2 + 2 / θ) * M *
          ((1 + w.1 ^ 2 + w.2 ^ 2) * UnforcedLeray.B0284.heatKernel2 (2 * θ) w) := by ring
  have hdiff : ∀ᵐ w ∂(volume : Measure Plane), ∀ s ∈ Set.Ioo (θ / 2) (2 * θ),
      HasDerivAt (fun s' : ℝ => UnforcedLeray.B0284.heatKernel2 s' w * G w)
        (UnforcedLeray.HeatCylinder.heatKernel2AgeDerivative s w * G w) s := by
    refine Eventually.of_forall fun w => ?_
    intro s hs
    have hpos : 0 < s := lt_trans (by positivity) hs.1
    exact (UnforcedLeray.HeatCylinder.hasDerivAt_heatKernel2_age hpos w).mul_const (G w)
  have hparam := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := (volume : Measure Plane))
    (F := fun (s : ℝ) (w : Plane) => UnforcedLeray.B0284.heatKernel2 s w * G w)
    (F' := fun (s : ℝ) (w : Plane) => UnforcedLeray.HeatCylinder.heatKernel2AgeDerivative s w * G w)
    (bound := fun w : Plane => 4 * (θ⁻¹ ^ 2 + 2 / θ) * M *
          ((1 + w.1 ^ 2 + w.2 ^ 2) * UnforcedLeray.B0284.heatKernel2 (2 * θ) w))
    hball hFmeas hFint hFprimeMeas hFprimeBound hdomInt hdiff
  exact hparam.2

end UnforcedLeray.Short.PartI
