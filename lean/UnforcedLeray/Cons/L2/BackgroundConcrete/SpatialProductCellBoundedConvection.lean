import UnforcedLeray.Cons.L2.BackgroundConcrete.SpatialProductCellBoundedSolenoidalCross
import UnforcedLeray.Cons.L2.BackgroundConcrete.SpatialProductCellAdvT

set_option autoImplicit false
set_option maxHeartbeats 3000000

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace UnforcedLeray.Cons.C03.Concrete

open UnforcedLeray.Blueprint
open UnforcedLeray.PhaseSpace
open UnforcedLeray.B0412

private theorem realC_eq_cplxV_boundedConvection : realC = UnforcedLeray.Axi.cplxV := by
  funext x
  ext i
  simp [realC_apply, UnforcedLeray.Axi.cplxV_apply]

private theorem norm_realC_boundedConvection (x : Space) : ‖realC x‖ = ‖x‖ := by
  rw [realC_eq_cplxV_boundedConvection, UnforcedLeray.Axi.norm_cplxV]

/-- The actual compact-test convection identity for two bounded backgrounds when the second is
pointwise solenoidal. This is the inlet analogue of the graph-representative identity and uses no
global `Yq` membership for the bounded field. -/
theorem pairF_convT_boundedSolenoidal_convection_identity {P : ℝ} [Fact (0 < P)]
    {Φ : ℝ × Space → CVec3} (hΦ : IsPhaseTest P Φ)
    {V E : ℝ → SpatialField} (hV : IsBoundedBackground V)
    (hE : IsBoundedBackground E) (hEsol : ∀ τ, IsSolenoidal (E τ)) :
    pairF P (convT V Φ) (fun z => realC (E z.1 z.2)) +
      pairF P (advT (fun z => realC (E z.1 z.2)) Φ)
        (fun z => realC (V z.1 z.2)) +
      pairF P (advT (fun z => realC (V z.1 z.2)) Φ)
        (fun z => realC (E z.1 z.2)) = 0 := by
  let μ : Measure SpaceTime := volume.restrict (phaseCell P)
  let Vc : SpaceTime → CVec3 := fun z => realC (V z.1 z.2)
  let Ec : SpaceTime → CVec3 := fun z => realC (E z.1 z.2)
  let T : SpaceTime → CVec3 := fun z => advT Vc Φ z
  haveI : Fact (1 ≤ (1 : ℝ≥0∞)) := ⟨le_rfl⟩
  have hGrad : MemLp (gradUT V Φ) 1 μ := memLp_gradUT_cell hΦ hV (by simp)
  have hT : MemLp T 1 μ := by
    exact memLp_advT_background_cell hΦ hV (by simp)
  have hConv : MemLp (convT V Φ) 1 μ := by
    change MemLp (fun z => gradUT V Φ z - T z) 1 μ
    exact hGrad.sub hT
  have hEcMeas : AEStronglyMeasurable Ec μ := by
    have hc := UnforcedLeray.Axi.cplxV.continuous.comp_aestronglyMeasurable hE.measurable
    have heq : (fun z : SpaceTime => UnforcedLeray.Axi.cplxV (E z.1 z.2)) = Ec := by
      funext z
      change UnforcedLeray.Axi.cplxV (E z.1 z.2) = realC (E z.1 z.2)
      exact congrFun realC_eq_cplxV_boundedConvection.symm (E z.1 z.2)
    exact (hc.congr (ae_of_all _ fun z => congrFun heq z)).mono_measure
      Measure.restrict_le_self
  have hVcMeas : AEStronglyMeasurable Vc μ := by
    have hc := UnforcedLeray.Axi.cplxV.continuous.comp_aestronglyMeasurable hV.measurable
    have heq : (fun z : SpaceTime => UnforcedLeray.Axi.cplxV (V z.1 z.2)) = Vc := by
      funext z
      change UnforcedLeray.Axi.cplxV (V z.1 z.2) = realC (V z.1 z.2)
      exact congrFun realC_eq_cplxV_boundedConvection.symm (V z.1 z.2)
    exact (hc.congr (ae_of_all _ fun z => congrFun heq z)).mono_measure
      Measure.restrict_le_self
  obtain ⟨CE, hCE⟩ := hE.bounded
  have hEbound : ∀ᵐ z ∂μ, ‖Ec z‖ ≤ CE := by
    filter_upwards [ae_restrict_mem (measurableSet_Ioc.prod MeasurableSet.univ)] with z hz
    change ‖realC (E z.1 z.2)‖ ≤ CE
    rw [norm_realC_boundedConvection]
    exact (hCE z.1 z.2).1
  have hEmem : MemLp Ec ⊤ μ := memLp_top_of_bound hEcMeas CE hEbound
  obtain ⟨CV, hCV⟩ := hV.bounded
  have hVbound : ∀ᵐ z ∂μ, ‖Vc z‖ ≤ CV := by
    filter_upwards [ae_restrict_mem (measurableSet_Ioc.prod MeasurableSet.univ)] with z hz
    change ‖realC (V z.1 z.2)‖ ≤ CV
    rw [norm_realC_boundedConvection]
    exact (hCV z.1 z.2).1
  have hVmem : MemLp Vc ⊤ μ := memLp_top_of_bound hVcMeas CV hVbound
  have hConvInt : Integrable (fun z : SpaceTime => dotL (convT V Φ z) (Ec z)) μ :=
    integrable_dotL_of_memLp_holder hConv hEmem
  have hGradInt : Integrable (fun z : SpaceTime => dotL (gradUT V Φ z) (Ec z)) μ :=
    integrable_dotL_of_memLp_holder hGrad hEmem
  have hTInt : Integrable (fun z : SpaceTime => dotL (T z) (Ec z)) μ :=
    integrable_dotL_of_memLp_holder hT hEmem
  have hEAdv : MemLp (advT Ec Φ) 1 μ := memLp_advT_background_cell hΦ hE (by simp)
  have hEAdvInt : Integrable (fun z : SpaceTime => dotL (advT Ec Φ z) (Vc z)) μ :=
    integrable_dotL_of_memLp_holder hEAdv hVmem
  have hconvPoint (z : SpaceTime) : dotL (convT V Φ z) (Ec z) =
      dotL (gradUT V Φ z) (Ec z) - dotL (T z) (Ec z) := by
    simp [convT, T, Vc, dotL_apply]
  have hpairConv : pairF P (convT V Φ) Ec =
      pairF P (gradUT V Φ) Ec - pairF P T Ec := by
    rw [pairF_eq_restrictedProductIntegral hConvInt,
      pairF_eq_restrictedProductIntegral hGradInt,
      pairF_eq_restrictedProductIntegral hTInt]
    rw [← smul_sub]
    congr 1
    calc
      ∫ z, dotL (convT V Φ z) (Ec z) ∂μ =
          ∫ z, (dotL (gradUT V Φ z) (Ec z) - dotL (T z) (Ec z)) ∂μ := by
            apply integral_congr_ae
            exact ae_of_all _ hconvPoint
      _ = (∫ z, dotL (gradUT V Φ z) (Ec z) ∂μ) -
          (∫ z, dotL (T z) (Ec z) ∂μ) := integral_sub hGradInt hTInt
  have hcross := pairF_gradUT_advT_boundedSolenoidal_sum_eq_zero hΦ hV hE hEsol
  calc
    pairF P (convT V Φ) Ec + pairF P (advT Ec Φ) Vc + pairF P T Ec =
        pairF P (gradUT V Φ) Ec + pairF P (advT Ec Φ) Vc := by
          rw [hpairConv]
          ring
    _ = 0 := hcross

#print axioms pairF_convT_boundedSolenoidal_convection_identity

end UnforcedLeray.Cons.C03.Concrete
