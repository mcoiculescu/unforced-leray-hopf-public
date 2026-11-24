import UnforcedLeray.Short.PartI.Sub.PartI_T02_1_4_4_1_2

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace UnforcedLeray.Short.PartI

open UnforcedLeray
open UnforcedLeray.Train (Vec toVec)
open UnforcedLeray.Cyl (Plane)
open UnforcedLeray.TrainB

/-- Mixed weak derivatives commute (N3). -/
theorem cylWeakDerivCommute : CylWeakDerivCommute := by
  intro c k i j x
  unfold hVal
  rw [Sob.W.value_partialDeriv, Sob.W.deriv_partialDeriv, Sob.W.value_partialDeriv,
    Sob.W.deriv_partialDeriv]
  have hw1 := Sob.W.hasWeakDeriv x (Sob.Idx.cons j (Sob.Idx.cons i Sob.Idx.zero))
  have hw2 := Sob.W.hasWeakDeriv x (Sob.Idx.cons i (Sob.Idx.cons j Sob.Idx.zero))
  rw [Sob.TestDomain.word_cons, Sob.TestDomain.word_cons, Sob.TestDomain.word_zero] at hw1 hw2
  have hp : ((Sob.cylinder c).dir j :: (Sob.cylinder c).dir i :: []).Perm
      ((Sob.cylinder c).dir i :: (Sob.cylinder c).dir j :: []) :=
    List.Perm.swap _ _ _
  have hw1' := hw1.perm hp
  have hae := hw1'.ae_unique hw2 (Sob.locallyIntegrable_of_memLp (Lp.memLp _))
    (Sob.locallyIntegrable_of_memLp (Lp.memLp _))
  rw [← Cyl.cylinder_μ_eq c]
  exact hae

end UnforcedLeray.Short.PartI
