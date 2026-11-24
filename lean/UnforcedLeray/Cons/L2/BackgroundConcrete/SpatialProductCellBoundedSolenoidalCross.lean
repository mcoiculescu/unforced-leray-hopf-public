import UnforcedLeray.Cons.L2.BackgroundConcrete.SpatialProductCellInletOuterPairing
import UnforcedLeray.Cons.L2.BackgroundConcrete.SpatialProductCellGradUT
import UnforcedLeray.Cons.L2.BackgroundConcrete.SpatialProductCellPairF

set_option autoImplicit false
set_option maxHeartbeats 3000000

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace UnforcedLeray.Cons.C03.Concrete

open UnforcedLeray.Blueprint
open UnforcedLeray.PhaseSpace
open UnforcedLeray.B0412

private theorem realC_eq_cplxV_boundedCross : realC = UnforcedLeray.Axi.cplxV := by
  funext x
  ext i
  simp [realC_apply, UnforcedLeray.Axi.cplxV_apply]

private theorem norm_realC_boundedCross (x : Space) : ‖realC x‖ = ‖x‖ := by
  rw [realC_eq_cplxV_boundedCross, UnforcedLeray.Axi.norm_cplxV]

/-- The transpose-gradient term for one bounded background cancels the advection term in a
bounded pointwise-solenoidal field. The proof uses the actual slice product rule and the preceding
cell `L¹`/`L∞` solenoidal pairing; it does not require either background to belong to global `Yq`.
-/
theorem pairF_gradUT_advT_boundedSolenoidal_sum_eq_zero {P : ℝ} [Fact (0 < P)]
    {Φ : ℝ × Space → CVec3} (hΦ : IsPhaseTest P Φ)
    {V E : ℝ → SpatialField} (hV : IsBoundedBackground V)
    (hE : IsBoundedBackground E) (hEsol : ∀ τ, IsSolenoidal (E τ)) :
    pairF P (gradUT V Φ) (fun z => realC (E z.1 z.2)) +
      pairF P (advT (fun z => realC (E z.1 z.2)) Φ)
        (fun z => realC (V z.1 z.2)) = 0 := by
  let μ : Measure SpaceTime := volume.restrict (phaseCell P)
  let Vc : SpaceTime → CVec3 := fun z => realC (V z.1 z.2)
  let Ec : SpaceTime → CVec3 := fun z => realC (E z.1 z.2)
  let S : SpaceTime → ℂ := fun z =>
    dotL (scalarSliceGrad (scalarTestBackground Φ V) z) (Ec z)
  let A : SpaceTime → ℂ := fun z => dotL (gradUT V Φ z) (Ec z)
  let B : SpaceTime → ℂ := fun z => dotL (advT Ec Φ z) (Vc z)
  have hAfield : MemLp (gradUT V Φ) 1 μ := memLp_gradUT_cell hΦ hV (by simp)
  have hEmeas : AEStronglyMeasurable Ec μ := by
    have hc := UnforcedLeray.Axi.cplxV.continuous.comp_aestronglyMeasurable hE.measurable
    have heq : (fun z : SpaceTime => UnforcedLeray.Axi.cplxV (E z.1 z.2)) = Ec := by
      funext z
      change UnforcedLeray.Axi.cplxV (E z.1 z.2) = realC (E z.1 z.2)
      exact congrFun realC_eq_cplxV_boundedCross.symm (E z.1 z.2)
    exact (hc.congr (ae_of_all _ fun z => congrFun heq z)).mono_measure
      Measure.restrict_le_self
  obtain ⟨CE, hCE⟩ := hE.bounded
  have hEbound : ∀ᵐ z ∂μ, ‖Ec z‖ ≤ CE := by
    filter_upwards [ae_restrict_mem (measurableSet_Ioc.prod MeasurableSet.univ)] with z hz
    change ‖realC (E z.1 z.2)‖ ≤ CE
    rw [norm_realC_boundedCross]
    exact (hCE z.1 z.2).1
  have hEmem : MemLp Ec ⊤ μ := memLp_top_of_bound hEmeas CE hEbound
  have hSfield : MemLp (scalarSliceGrad (scalarTestBackground Φ V)) 1 μ :=
    memLp_scalarSliceGrad_cell hΦ hV (by simp)
  have hS : Integrable S μ := integrable_dotL_of_memLp_holder hSfield hEmem
  have hA : Integrable A μ := by
    exact integrable_dotL_of_memLp_holder hAfield hEmem
  have hpoint (z : SpaceTime) : S z = A z + B z := by
    simpa [S, A, B] using scalarSliceGrad_dotL_productRule hΦ hV Ec z
  have hBAE : B =ᵐ[μ] (fun z => S z - A z) := by
    filter_upwards with z
    rw [hpoint z]
    ring
  have hB : Integrable B μ := Integrable.congr (hS.sub hA) hBAE.symm
  have hSzero : ∫ z, S z ∂μ = 0 := by
    simpa [S, Ec, μ] using
      integral_scalarSliceGrad_pair_boundedSolenoidal_zero hΦ hV hE hEsol
  have hsum : (∫ z, A z ∂μ) + (∫ z, B z ∂μ) = ∫ z, S z ∂μ := by
    rw [← integral_add hA hB]
    apply integral_congr_ae
    exact ae_of_all _ fun z => (hpoint z).symm
  have hsumzero : (∫ z, A z ∂μ) + (∫ z, B z ∂μ) = 0 := by
    rw [hsum, hSzero]
  rw [pairF_eq_restrictedProductIntegral hA,
      pairF_eq_restrictedProductIntegral hB]
  rw [← smul_add, hsumzero]
  simp

#print axioms pairF_gradUT_advT_boundedSolenoidal_sum_eq_zero

end UnforcedLeray.Cons.C03.Concrete
