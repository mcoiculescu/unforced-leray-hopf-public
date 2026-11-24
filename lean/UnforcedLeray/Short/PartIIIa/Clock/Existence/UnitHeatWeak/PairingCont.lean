import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_3_2_1

/-!
# Part III-a, `PartIII-a:T21/3/2/1/3`: continuity of the tested orbit of `S₀` (L3)

Source of record: `the November 2 reference manuscript`, lines 2819-2836.
The cell pairing with a cylinder test is the inner product with the test vector `testVec`
(`B0579.inner_testVec`), a continuous linear functional on the physical state space. The orbit
`θ ↦ S₀ θ w` is continuous on `[0,1]` (the `continuousOn_S₀` field of the supplier).
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

open Set MeasureTheory Filter Topology

namespace UnforcedLeray.Short.IIIa.Exist

open UnforcedLeray.Short.IIIa
open UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution

theorem unitHeatPairingCont : UnforcedLeray.Short.IIIa.Exist.UnitHeatPairingCont := by
  intro c m _ hc1 hm
  haveI := actualVorticityCompleteSpace (c := c) (m := m) hm
  intro w ψ hψ
  have hS : ContinuousOn
      (fun θ : ℝ => (actualPhysicalWeightedHeatStripSupplier (c := c) (m := m) hc1 hm).S₀ θ w)
      (Icc (0 : ℝ) 1) :=
    (actualPhysicalWeightedHeatStripSupplier (c := c) (m := m) hc1 hm).continuousOn_S₀ w
  have hX : ContinuousOn
      (fun θ : ℝ => ((actualPhysicalWeightedHeatStripSupplier (c := c) (m := m) hc1 hm).S₀ θ w :
        UnforcedLeray.B0579.X c m)) (Icc (0 : ℝ) 1) :=
    continuous_subtype_val.comp_continuousOn hS
  have hI : ContinuousOn
      (fun θ : ℝ => inner ℝ (UnforcedLeray.B0579.testVec c m hψ)
        ((actualPhysicalWeightedHeatStripSupplier (c := c) (m := m) hc1 hm).S₀ θ w :
          UnforcedLeray.B0579.X c m)) (Icc (0 : ℝ) 1) :=
    (innerSL ℝ (UnforcedLeray.B0579.testVec c m hψ)).continuous.comp_continuousOn hX
  refine ContinuousOn.congr hI ?_
  intro θ _
  exact (UnforcedLeray.B0579.inner_testVec c m hψ _).symm

end UnforcedLeray.Short.IIIa.Exist
