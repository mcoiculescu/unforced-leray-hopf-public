import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_6
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_6.L2
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_3_1.T3b
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_3_1.T3c
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_3_1.T9
import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_2.Dense.Reg

/-!
# `WardXDiffOffAxis` (`PartIII-b:C/ward/6/3`)

Source of record: `the November 2 reference manuscript` 4161-4186.
The `C²` regularity of `X` off the axis: the outward primitive of `X₀` is `C²` on the young
region (`outPrimC2Boot_proved`, from `outPrimDerivR`, `outPrimDerivZ`), which gives `wardXr` `C²`
(`t9_wardXr_contDiff`), and `wardX = wardXr` off the axis (`wardXr_eventuallyEq`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411

theorem wardXDiffOffAxis_proved : WardXDiffOffAxis := by
  intro ν μ R c χy hχy hν hR hc hμ g hg τ y hy
  obtain ⟨hZ, hdiv, hax, hdec⟩ := wardX0FactsOldL2_proved ν μ R c hν hR hc hμ g hg
  have hO : ContDiffOn ℝ 2 (fun y : Space => outPrim (wardX0 ν μ R c g) τ (ϱ y) (y 2))
      (youngOpen ν R) :=
    outPrimC2Boot_proved ν R (wardX0 ν μ R c g) τ hν hR (hZ τ)
      (fun r z hr => ⟨outPrimDerivR ν R _ τ (hZ τ) (hdec τ) r z hr,
        outPrimDerivZ ν R _ τ (hZ τ) (hdiv τ) hax (hdec τ) r z hr⟩)
  have hC : ContDiff ℝ 2 (wardXr ν μ R c χy g τ) :=
    t9_wardXr_contDiff g hχy hν hR τ (hZ τ) hO
  exact hC.contDiffAt.congr_of_eventuallyEq (wardXr_eventuallyEq ν μ R c χy g τ hy).symm

end UnforcedLeray.Short.PartIIIb.Concrete
