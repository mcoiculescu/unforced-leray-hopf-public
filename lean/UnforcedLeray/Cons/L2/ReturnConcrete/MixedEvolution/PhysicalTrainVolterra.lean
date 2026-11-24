import UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution.PhysicalHeatStripSupplier
import UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution.Volterra

/-
# Actual-train Volterra evolution with the constructed physical heat family

The only unsupplied datum is ActualTrainFluxPath: it must give the actual B0238 velocity/curl
coefficient paths, all-age centered-cell bounds, and strong continuity. The heat family itself is
now the constructed physical weighted B0284/B0296 family.
-/

set_option autoImplicit false
set_option maxHeartbeats 500000

noncomputable section

namespace UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution

open UnforcedLeray.B0579 hiding Plane

/-- Volterra data for an actual train coefficient path and the already constructed physical heat
supplier; there is no abstract heat-family argument. -/
def actualPhysicalTrainVolterraData {c m ν : ℝ} [Fact (0 < c)]
    (hc1 : 1 ≤ c) (hm : 1 ≤ m) {tr : UnforcedLeray.B0140.TrainSol ν c}
    (P : ActualTrainFluxPath (c := c) (m := m) hm (ν := ν) tr) :
    UnforcedLeray.Infra.VolterraEvolution.VolterraData ℝ
      (ActualVorticity (c := c) (m := m) hm)
      (ActualFlux (c := c) (m := m)) :=
  actualTrainVolterraData hm P (actualPhysicalWeightedHeatStripSupplier hc1 hm)

/-- For every supplied actual train coefficient path, the constructed Volterra family satisfies
the literal physical weighted heat/response mild equation on each unit strip. The remaining
construction obligation is the all-age ActualTrainFluxPath from the chosen TrainSol. -/
theorem actualPhysicalTrainEvolution_mild {c m ν s t : ℝ} [Fact (0 < c)]
    (hc1 : 1 ≤ c) (hm : 1 ≤ m) {tr : UnforcedLeray.B0140.TrainSol ν c}
    (P : ActualTrainFluxPath (c := c) (m := m) hm (ν := ν) tr)
    (hst : s ≤ t) (ht : t ≤ s + 1)
    (w : ActualVorticity (c := c) (m := m) hm) :
    let D := actualPhysicalTrainVolterraData hc1 hm P
    D.evolution t s w =
      actualWeightedHeatS0Totalized hc1 hm (t - s) w +
        ∫ r in s..t,
          actualWeightedHeatResponse (c := c) (m := m) (hm := hm) (t - r)
            (actualTrainFluxB hm P r (D.evolution r s w)) := by
  exact actualTrainEvolution_mild hm P
    (actualPhysicalWeightedHeatStripSupplier hc1 hm) hst ht w

end UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution

#print axioms UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution.actualPhysicalTrainVolterraData
#print axioms UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution.actualPhysicalTrainEvolution_mild
