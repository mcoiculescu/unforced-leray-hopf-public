import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D2_1_3_1_2_1_3_1_5
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D2_1_3_1_2_2_2
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.PairCont

/-!
# Leaf `PairFSub`: linearity of the phase pairing in its first slot, for `h ∈ Y_2`

Source: `the November 2 reference manuscript` lines 1351-1362, 1470-1480.
Proves `pairFSub : PairFSub`. For `0 < P` both pairings are integrals over `muP P` of
`dotL (A z) (h z)` with `A` a phase test (in `Y_2`), and integrability comes from
`dot_integrable`. For `P ≤ 0` the period set `Ioc 0 P` is empty and both sides vanish.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411
open UnforcedLeray.Cons.C03.Concrete (pairF phaseInt IsSolTest)

theorem pairFSub : PairFSub := by
  intro P h hh A B hA hB
  rcases le_or_gt P 0 with hP | hP
  · simp [pairF, phaseInt, Set.Ioc_eq_empty (not_lt.2 hP)]
  · have hAB : IsPhaseTest P (fun x => A x - B x) := hA.sub hB
    have hIA := isInYr_of_phaseTest hP hA
    have hIB := isInYr_of_phaseTest hP hB
    have hIAB := isInYr_of_phaseTest hP hAB
    rw [pair_eq_integral P (fun x => A x - B x) h (dot_integrable hP hIAB hh),
      pair_eq_integral P A h (dot_integrable hP hIA hh),
      pair_eq_integral P B h (dot_integrable hP hIB hh),
      ← smul_sub, ← integral_sub (dot_integrable hP hIA hh) (dot_integrable hP hIB hh)]
    congr 1
    refine integral_congr_ae (Eventually.of_forall fun z => ?_)
    simp [map_sub]

end UnforcedLeray.Short.PartIIIb.Concrete
