import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D2_3_1_3_1_1_1
import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_1_1_2.L2
import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_1_1_2.L3
import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_1_1_2.L4
import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_1_1_2.L5
import UnforcedLeray.Short.PartIIIa.T15_SepKernelBounds
import Mathlib.Analysis.Calculus.ParametricIntegral

/-!
# `SepWFderivIntegral` (`PartIII-b:IIIb-D2/3/1/3/1/1/1/4`)

Source `the November 2 reference manuscript`
4155-4186, 3604-3646.  Differentiation under the integral sign at a gap point with the gap
majorant `sepMajorant μ T τ 1`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411

theorem sepWFderivIntegral : SepWFderivIntegral := by
  intro ν μ rOut P T hν hμ hr hP hS hM τ i y₀ hy₀
  obtain ⟨ε, hε, C, hC0, hb⟩ :=
    sepGapPointwise IIIa.sepKernelBounds ν μ rOut P T hν hμ hr.le hP hS τ i y₀ hy₀
  have hint : ∀ n : ℕ, n ≤ 2 → Integrable (fun p => C * sepMajorant μ T τ n p) sepRho :=
    fun n hn => (sepGapMajorantIntegrable μ P rOut T hμ hP hS hM τ n hn).const_mul C
  have hbound : ∀ n : ℕ, n ≤ 2 → ∀ᵐ p ∂sepRho, ∀ y ∈ Metric.ball y₀ ε,
      ‖iteratedFDeriv ℝ n (sepPhi ν μ T τ i p) y‖ ≤ C * sepMajorant μ T τ n p := by
    intro n hn
    filter_upwards [ae_mem_Ioo_sepRho] with p hp y hy
    exact hb y hy p.1 hp p.2 n hn
  have hm : ∀ y : Space, AEStronglyMeasurable (fun p => sepPhi ν μ T τ i p y) sepRho := by
    intro y
    have := (continuousMultilinearCurryFin0 ℝ Space ℂ).continuous.comp_aestronglyMeasurable
      (sepPhiMeasurable ν μ P rOut T hν hS τ i 0 (by norm_num) y)
    refine this.congr (Filter.Eventually.of_forall fun p => ?_)
    simp [iteratedFDeriv_zero_eq_comp]
  have hint0 : ∀ y ∈ Metric.ball y₀ ε, Integrable (fun p => sepPhi ν μ T τ i p y) sepRho := by
    intro y hy
    refine Integrable.mono' (hint 0 (by norm_num)) (hm y) ?_
    filter_upwards [hbound 0 (by norm_num)] with p hp
    have := hp y hy
    simpa [norm_iteratedFDeriv_zero] using this
  have hF'm : AEStronglyMeasurable (fun p => fderiv ℝ (sepPhi ν μ T τ i p) y₀) sepRho := by
    have := (continuousMultilinearCurryFin1 ℝ Space ℂ).continuous.comp_aestronglyMeasurable
      (sepPhiMeasurable ν μ P rOut T hν hS τ i 1 (by norm_num) y₀)
    refine this.congr (Filter.Eventually.of_forall fun p => ?_)
    ext v
    simp
  have hbd : ∀ᵐ p ∂sepRho, ∀ y ∈ Metric.ball y₀ ε,
      ‖fderiv ℝ (sepPhi ν μ T τ i p) y‖ ≤ C * sepMajorant μ T τ 1 p := by
    filter_upwards [hbound 1 (by norm_num)] with p hp y hy
    have := hp y hy
    simpa [norm_iteratedFDeriv_one] using this
  have hdiff : ∀ᵐ p ∂sepRho, ∀ y ∈ Metric.ball y₀ ε,
      HasFDerivAt (fun y' => sepPhi ν μ T τ i p y') (fderiv ℝ (sepPhi ν μ T τ i p) y) y := by
    filter_upwards [ae_mem_Ioo_sepRho] with p hp y _
    have hc := sepPhi_contDiff heatLerayKSmooth ν μ T τ i p.1 p.2 hν hp
    exact ((hc.differentiable (by norm_num)) y).hasFDerivAt
  have hd := hasFDerivAt_integral_of_dominated_of_fderiv_le
    (F := fun y p => sepPhi ν μ T τ i p y) (F' := fun y p => fderiv ℝ (sepPhi ν μ T τ i p) y)
    (bound := fun p => C * sepMajorant μ T τ 1 p) (Metric.ball_mem_nhds y₀ hε)
    (Filter.Eventually.of_forall hm) (hint0 y₀ (Metric.mem_ball_self hε)) hF'm hbd
    (hint 1 (by norm_num)) hdiff
  refine ⟨hint0 y₀ (Metric.mem_ball_self hε), ?_⟩
  have heq : (fun y' => IIIa.sepW ν μ T y' τ i) =ᶠ[nhds y₀]
      fun y' => ∫ p, sepPhi ν μ T τ i p y' ∂sepRho := by
    filter_upwards [Metric.ball_mem_nhds y₀ hε] with y hy
    exact sepW_eq_integral ν μ T τ i y (hint0 y hy)
  exact ((hd.congr_of_eventuallyEq heq)).fderiv

end UnforcedLeray.Short.PartIIIb.Concrete
