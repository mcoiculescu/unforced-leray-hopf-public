import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_1_1_2
import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_1_1_2.L2
import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_1_1_2.L3
import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_1_1_2.L4
import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_1_1_2.L5
import UnforcedLeray.Short.PartIIIa.T15_SepKernelBounds

/-!
# Differentiation of `sepW` under the integral (`PartIII-b:IIIb-D2/3/1/2/2`)

Source `the November 2 reference manuscript` 3604-3621.
For `rOut < ϱ y`: `y' ↦ sepW ν μ T y' τ i` has Fréchet derivative `∫ D_y sepPhi dρ` at `y`
(`hasFDerivAt_integral_of_dominated_of_fderiv_le`, dominated by `C · sepMajorant μ T τ 1`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411

theorem sepW_hasFDerivAt (ν : ℝ) (μ : ℂ) (rOut P : ℝ)
    (T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ) (hν : 0 < ν) (hμ : -(1 / 4) < μ.re)
    (hr : 0 ≤ rOut) (hP : 0 < P) (hS : IIIa.IsSepSource P rOut T) (hM : SepMoment P T)
    (τ : ℝ) (i : Fin 3) (y : Space) (hy : rOut < ϱ y) :
    HasFDerivAt (fun y' => IIIa.sepW ν μ T y' τ i)
      (∫ p, fderiv ℝ (sepPhi ν μ T τ i p) y ∂sepRho) y ∧
    Integrable (fun p => fderiv ℝ (sepPhi ν μ T τ i p) y) sepRho := by
  obtain ⟨ε, hε, C, hC0, hb⟩ :=
    sepGapPointwise IIIa.sepKernelBounds ν μ rOut P T hν hμ hr hP hS τ i y hy
  have hU : IsOpen (Metric.ball y ε) := Metric.isOpen_ball
  have hint : ∀ n : ℕ, n ≤ 2 → Integrable (fun p => C * sepMajorant μ T τ n p) sepRho :=
    fun n hn => (sepGapMajorantIntegrable μ P rOut T hμ hP hS hM τ n hn).const_mul C
  have hbound : ∀ n : ℕ, n ≤ 2 → ∀ᵐ p ∂sepRho, ∀ y' ∈ Metric.ball y ε,
      ‖iteratedFDeriv ℝ n (sepPhi ν μ T τ i p) y'‖ ≤ C * sepMajorant μ T τ n p := by
    intro n hn
    filter_upwards [ae_mem_Ioo_sepRho] with p hp y' hy'
    exact hb y' hy' p.1 hp p.2 n hn
  have hmeas : ∀ n : ℕ, n ≤ 2 → ∀ y' : Space,
      AEStronglyMeasurable (fun p => iteratedFDeriv ℝ n (sepPhi ν μ T τ i p) y') sepRho :=
    fun n hn y' => sepPhiMeasurable ν μ P rOut T hν hS τ i n hn y'
  have hm0 : ∀ y' : Space, AEStronglyMeasurable (fun p => sepPhi ν μ T τ i p y') sepRho := by
    intro y'
    have h := (continuousMultilinearCurryFin0 ℝ Space ℂ).continuous.comp_aestronglyMeasurable
      (hmeas 0 (by norm_num) y')
    refine h.congr (Filter.Eventually.of_forall fun p => ?_)
    simp [iteratedFDeriv_zero_eq_comp]
  have hcurry1 : ∀ (G : Space → ℂ) (z : Space),
      continuousMultilinearCurryFin1 ℝ Space ℂ (iteratedFDeriv ℝ 1 G z) = fderiv ℝ G z := by
    intro G z
    ext v
    simp [continuousMultilinearCurryFin1_apply, iteratedFDeriv_one_apply]
  have hm1 : ∀ y' : Space,
      AEStronglyMeasurable (fun p => fderiv ℝ (sepPhi ν μ T τ i p) y') sepRho := by
    intro y'
    have h := (continuousMultilinearCurryFin1 ℝ Space ℂ).continuous.comp_aestronglyMeasurable
      (hmeas 1 (by norm_num) y')
    refine h.congr (Filter.Eventually.of_forall fun p => ?_)
    exact hcurry1 _ y'
  have hB0 : ∀ᵐ p ∂sepRho, ∀ y' ∈ Metric.ball y ε,
      ‖sepPhi ν μ T τ i p y'‖ ≤ C * sepMajorant μ T τ 0 p := by
    filter_upwards [hbound 0 (by norm_num)] with p hp y' hy'
    simpa [norm_iteratedFDeriv_zero] using hp y' hy'
  have hB1 : ∀ᵐ p ∂sepRho, ∀ y' ∈ Metric.ball y ε,
      ‖fderiv ℝ (sepPhi ν μ T τ i p) y'‖ ≤ C * sepMajorant μ T τ 1 p := by
    filter_upwards [hbound 1 (by norm_num)] with p hp y' hy'
    simpa [norm_iteratedFDeriv_one] using hp y' hy'
  have hint0 : ∀ y' ∈ Metric.ball y ε, Integrable (fun p => sepPhi ν μ T τ i p y') sepRho :=
    fun y' hy' => (hint 0 (by norm_num)).mono' (hm0 y') (hB0.mono fun p hp => hp y' hy')
  have hint1 : Integrable (fun p => fderiv ℝ (sepPhi ν μ T τ i p) y) sepRho :=
    (hint 1 (by norm_num)).mono' (hm1 y)
      (hB1.mono fun p hp => hp y (Metric.mem_ball_self hε))
  have hdiff1 : ∀ᵐ p ∂sepRho, ∀ x ∈ Metric.ball y ε,
      HasFDerivAt (fun y' => sepPhi ν μ T τ i p y') (fderiv ℝ (sepPhi ν μ T τ i p) x) x := by
    filter_upwards [ae_mem_Ioo_sepRho] with p hp x _
    exact ((sepPhi_contDiff heatLerayKSmooth ν μ T τ i p.1 p.2 hν hp).differentiable
      (by norm_num) x).hasFDerivAt
  have hD1 : HasFDerivAt (fun y' => ∫ p, sepPhi ν μ T τ i p y' ∂sepRho)
      (∫ p, fderiv ℝ (sepPhi ν μ T τ i p) y ∂sepRho) y :=
    hasFDerivAt_integral_of_dominated_of_fderiv_le (F := fun y' p => sepPhi ν μ T τ i p y')
      (F' := fun y' p => fderiv ℝ (sepPhi ν μ T τ i p) y') (bound := fun p => C * sepMajorant μ T τ 1 p)
      (hU.mem_nhds (Metric.mem_ball_self hε))
      (Filter.eventually_of_mem (hU.mem_nhds (Metric.mem_ball_self hε)) fun y' hy' => hm0 y')
      (hint0 y (Metric.mem_ball_self hε)) (hm1 y) hB1 (hint 1 (by norm_num)) hdiff1
  refine ⟨?_, hint1⟩
  refine hD1.congr_of_eventuallyEq ?_
  filter_upwards [hU.mem_nhds (Metric.mem_ball_self hε)] with y' hy'
  exact sepW_eq_integral ν μ T τ i y' (hint0 y' hy')

end UnforcedLeray.Short.PartIIIb.Concrete
