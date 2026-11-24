import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.Sub.MollCommDefs
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.Sub.MollCommLemmas.MollIntegralSplit
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.AdjMollLocInt

/-!
# `CommSub`: linearity of the commutator in its field

Source `the November 2 reference manuscript` (adjoint graph at `r = 2` and the
mollified commutator; the cited line numbers of the task spec do not match the current file, the
mathematics is that of the docstrings in `MollCommDefs`). `commK ρ (Φ - Ψ) = commK ρ Φ - commK ρ Ψ`
because both integrands `½ kap ρ z • Φ(x - z)` and `½ kap ρ z • Ψ(x - z)` are integrable: the
kernel is continuous with compact support (`mis_halfKap_props`), `Φ` is locally integrable
(`locInt_of_isInYr`) and the phase test `Ψ` is continuous, hence locally integrable.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411
open UnforcedLeray.Cons.C03.Concrete (pairF phaseInt IsSolTest)

theorem commSub : CommSub := by
  intro P hP Φ Ψ hΦ hΨ ρ x
  have hloc : LocallyIntegrable Φ volume := locInt_of_isInYr hP hΦ
  have hΨloc : LocallyIntegrable Ψ volume := hΨ.smooth.continuous.locallyIntegrable
  have hC := mis_halfKap_props ρ
  have hI1 := mis_integrable_kernel hloc hC.1 hC.2 x
  have hI2 := mis_integrable_kernel hΨloc hC.1 hC.2 x
  have hsub : commK ρ (fun w => Φ w - Ψ w) x = commK ρ Φ x - commK ρ Ψ x := by
    simp only [commK, smul_sub]
    exact integral_sub hI1 hI2
  rw [hsub]
  abel

end UnforcedLeray.Short.PartIIIb.Concrete
