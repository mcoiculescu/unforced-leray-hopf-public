import UnforcedLeray.Short.PartI.Sub.PartI_T02_1_4_6_4_1_1_6_Bridges

/-!
# Bridge 3a: centered-to-normalized transport of a periodic class

Source: `the November 2 reference manuscript`,
lines 261-288. The coercion of `centeredVecToNormalizedCLM hc G` is a.e. on the normalized cell the
periodic lift `centeredVecL2PeriodicRep hc G` of the centered representative, and that lift is a.e.
equal on the centered cell to any periodic `F` agreeing with `G` there; then
`ae_eq_of_ae_centered_periodic` transfers the equality to the normalized cell.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff InnerProductSpace

namespace UnforcedLeray.Short.PartI

open UnforcedLeray
open UnforcedLeray.Train (Vec toVec)
open UnforcedLeray.Cyl (Plane)
open UnforcedLeray.HeatCylinder

theorem centeredVecTransportPeriodicAE : CenteredVecTransportPeriodicAE := by
  intro c hc G F hF hGF
  have hcoe : ⇑(centeredVecToNormalizedCLM hc G) =
      ⇑(centeredVecToNormalizedFun hc G) := rfl
  have hrep : (centeredVecToNormalizedCLM hc G : Plane → Vec) =ᵐ[
      UnforcedLeray.B0284.cellMeasure c] centeredVecL2PeriodicRep hc G := by
    rw [hcoe]
    exact (memLp_centeredVecL2PeriodicRep_normalized hc G).coeFn_toLp
  have hfF : centeredVecL2PeriodicRep hc G =ᵐ[UnforcedLeray.Cyl.cellμ c] F :=
    (centeredVecL2PeriodicRep_ae_cell hc G).trans hGF
  exact hrep.trans (ae_eq_of_ae_centered_periodic hc
    (periodic_centeredVecL2PeriodicRep hc G) hF hfF)

end UnforcedLeray.Short.PartI
