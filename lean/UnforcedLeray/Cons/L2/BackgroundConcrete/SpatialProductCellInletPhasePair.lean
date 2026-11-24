import UnforcedLeray.Cons.L2.BackgroundConcrete.SpatialProductCellSolenoidalTest
import UnforcedLeray.Cons.L2.BackgroundConcrete.SpatialProductCellHolder
import UnforcedLeray.Cons.L2.BackgroundConcrete.SpatialProductCellVectorSupport

set_option autoImplicit false
set_option maxHeartbeats 3000000

noncomputable section

open MeasureTheory Set
open scoped ENNReal ContDiff

namespace UnforcedLeray.Cons.C03.Concrete

open UnforcedLeray.Blueprint
open UnforcedLeray.PhaseSpace
open UnforcedLeray.B0412
open UnforcedLeray.Axi

private theorem realC_eq_cplxV_inletPair : realC = UnforcedLeray.Axi.cplxV := by
  funext x
  ext i
  simp [realC_apply, UnforcedLeray.Axi.cplxV_apply]

private theorem norm_realC_inletPair (x : Space) : ‖realC x‖ = ‖x‖ := by
  rw [realC_eq_cplxV_inletPair, UnforcedLeray.Axi.norm_cplxV]

/-- The phasewise distributional solenoidality of a bounded real background annihilates the
gradient of every smooth periodic compact-spatial scalar test on the actual period cell. This
does not place the background itself in a global spatial `L^q` space. -/
theorem integral_phaseTest_gradient_pair_boundedSolenoidal_zero {P : ℝ}
    [Fact (0 < P)] {Φ : ℝ × Space → ℂ} (hΦ : IsPhaseTest P Φ)
    {V : ℝ → SpatialField} (hV : IsBoundedBackground V)
    (hsol : ∀ τ, IsSolenoidal (V τ)) :
    ∫ z : SpaceTime, dotL (PhaseSpace.gradT Φ z) (realC (V z.1 z.2))
      ∂(volume.restrict (phaseCell P)) = 0 := by
  let μ : Measure SpaceTime := volume.restrict (phaseCell P)
  let F : SpaceTime → CVec3 := fun z => PhaseSpace.gradT Φ z
  let E : SpaceTime → CVec3 := fun z => realC (V z.1 z.2)
  obtain ⟨R0, hspace0⟩ := (hΦ.dy 0).bounded_support
  obtain ⟨R1, hspace1⟩ := (hΦ.dy 1).bounded_support
  obtain ⟨R2, hspace2⟩ := (hΦ.dy 2).bounded_support
  let R : ℝ := max R0 (max R1 R2)
  have hR0 : R0 ≤ R := le_max_left _ _
  have hR1 : R1 ≤ R := le_trans (le_max_left _ _) (le_max_right _ _)
  have hR2 : R2 ≤ R := le_trans (le_max_right _ _) (le_max_right _ _)
  let K : Set SpaceTime := Icc (0 : ℝ) P ×ˢ Metric.closedBall (0 : Space) R
  have hK : IsCompact K := isCompact_Icc.prod (isCompact_closedBall _ _)
  have hFc : Continuous F := by
    have hterm (j : Fin 3) : Continuous (fun z : SpaceTime =>
        PhaseSpace.dy j Φ z • EuclideanSpace.single j (1 : ℂ)) :=
      ((hΦ.dy j).smooth.continuous).smul continuous_const
    have hsum := continuous_finsetSum Finset.univ fun j _ => hterm j
    simpa [F, PhaseSpace.gradT] using hsum
  obtain ⟨MF, _hMF0, hMF⟩ := exists_norm_bound_on_compact F hFc (by simpa [K] using hK)
  have hFzero : ∀ τ ∈ Ioc (0 : ℝ) P, ∀ y : Space, R < ‖y‖ → F (τ, y) = 0 := by
    intro τ hτ y hy
    have hz0 := hspace0 τ y (lt_of_le_of_lt hR0 hy)
    have hz1 := hspace1 τ y (lt_of_le_of_lt hR1 hy)
    have hz2 := hspace2 τ y (lt_of_le_of_lt hR2 hy)
    have hz (j : Fin 3) : PhaseSpace.dy j Φ (τ, y) = 0 := by
      fin_cases j <;> assumption
    simp [F, PhaseSpace.gradT, hz]
  have hFmem : MemLp F 1 μ := by
    have hbound : ∃ C : ℝ, ∀ z ∈ Icc (0 : ℝ) P ×ˢ Metric.closedBall (0 : Space) R,
        ‖F z‖ ≤ C := ⟨MF, fun z hz => hMF z (by simpa [K] using hz)⟩
    exact memLp_vector_on_phaseCell_of_spatialSupport (P := P) (R := R)
      (p := 1) (by norm_num) hFc.aestronglyMeasurable hbound hFzero
  have hEm : AEStronglyMeasurable E μ := by
    have hreal : AEStronglyMeasurable
        (fun z : SpaceTime => realC (V z.1 z.2)) volume :=
      (UnforcedLeray.Axi.cplxV.continuous).comp_aestronglyMeasurable hV.measurable
        |>.congr (ae_of_all _ fun z => by rw [realC_eq_cplxV_inletPair])
    exact hreal.mono_measure Measure.restrict_le_self
  obtain ⟨CV, hCV⟩ := hV.bounded
  have hEbound : ∀ᵐ z ∂μ, ‖E z‖ ≤ CV := by
    filter_upwards [ae_restrict_mem (measurableSet_Ioc.prod MeasurableSet.univ)] with z hz
    change ‖realC (V z.1 z.2)‖ ≤ CV
    rw [norm_realC_inletPair]
    exact (hCV z.1 z.2).1
  have hEmem : MemLp E ⊤ μ := memLp_top_of_bound hEm CV hEbound
  have hInt : Integrable (fun z : SpaceTime => dotL (F z) (E z)) μ := by
    exact integrable_dotL_of_memLp_holder hFmem hEmem
  let μt : Measure ℝ := volume.restrict (Ioc (0 : ℝ) P)
  have hprod : μ = μt.prod (volume : Measure Space) := by
    simpa [μ, μt, phaseCell, Measure.volume_eq_prod] using
      (Measure.restrict_prod_eq_prod_univ (μ := (volume : Measure ℝ))
        (ν := (volume : Measure Space)) (Ioc (0 : ℝ) P)).symm
  have hInt' : Integrable (fun z : ℝ × Space => dotL (F z) (E z))
      (μt.prod (volume : Measure Space)) := by
    rw [← hprod]
    exact hInt
  have hslice (τ : ℝ) : ∫ y : Space, dotL (F (τ, y)) (E (τ, y)) = 0 := by
    let ψ : Space → ℂ := fun y => Φ (τ, y)
    have hψs : ContDiff ℝ ∞ ψ := hΦ.smooth.comp (contDiff_const.prodMk contDiff_id)
    have hψc : HasCompactSupport ψ := hΦ.hasCompactSupport_slice τ
    have hderiv (j : Fin 3) (y : Space) : PhaseSpace.dy j Φ (τ, y) =
        fderiv ℝ ψ y (coordinateVector j) := by
      have hΦd : HasFDerivAt Φ (fderiv ℝ Φ (τ, y)) (τ, y) :=
        (hΦ.smooth.differentiable (by simp) (τ, y)).hasFDerivAt
      have hψd : HasFDerivAt ψ
          ((fderiv ℝ Φ (τ, y)).comp (ContinuousLinearMap.inr ℝ ℝ Space)) y :=
        hΦd.comp y (hasFDerivAt_prodMk_right τ y)
      have he := congrArg (fun L : Space →L[ℝ] ℂ => L (coordinateVector j)) hψd.fderiv
      simpa [PhaseSpace.dy, ContinuousLinearMap.comp_apply] using he.symm
    have hzero := integral_complexTest_gradient_pair_solenoidal (hsol τ) hψs hψc
    have heq : (fun y : Space => dotL (F (τ, y)) (E (τ, y))) = fun y =>
        ∑ j : Fin 3, (V τ y j : ℂ) * fderiv ℝ ψ y (coordinateVector j) := by
      funext y
      simp [F, E, PhaseSpace.gradT, dotL_apply, realC_apply, hderiv, mul_comm]
    rw [heq]
    exact hzero.2
  calc
    ∫ z : SpaceTime, dotL (F z) (E z) ∂μ =
        ∫ z : SpaceTime, dotL (F z) (E z) ∂(μt.prod (volume : Measure Space)) := by
          rw [hprod]
    _ = ∫ τ in Ioc (0 : ℝ) P, ∫ y : Space, dotL (F (τ, y)) (E (τ, y)) := by
          rw [integral_prod _ hInt']
    _ = 0 := by
          have heq : (fun τ : ℝ => ∫ y : Space,
              dotL (F (τ, y)) (E (τ, y))) = fun _ => (0 : ℂ) := funext hslice
          rw [heq]
          simp

#print axioms integral_phaseTest_gradient_pair_boundedSolenoidal_zero

end UnforcedLeray.Cons.C03.Concrete
