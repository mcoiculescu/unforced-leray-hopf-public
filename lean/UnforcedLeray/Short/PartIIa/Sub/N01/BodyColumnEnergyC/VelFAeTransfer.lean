import UnforcedLeray.Short.PartIIa.Sub.PartIIa_N01_9_1_3
import UnforcedLeray.Short.PartIIIb.NearInst.Delta.Proofs.CompactWindow.Comparison.FlatStress.CellPtChangeAll

/-!
# `PartII-a:N01/9/1/3/2`: `velFAeTransfer`

Source `the November 2 reference manuscript` lines 1684-1689 (chart recentring).
`velF c f x i = f (cellPtInv c x) i`.  The change of variables `CellPtInvH c`
(`Measure.map (cellPtInv c) (ageμ c (-3/2)) = ofReal c⁻¹ • measureH c`) carries the `measureH`-almost
everywhere statement about `f` back to an `ageμ c (-3/2)`-almost everywhere statement in the chart.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory UnforcedLeray.Axi Set Filter Topology
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIa.N01

theorem velFAeTransfer : VelFAeTransfer := by
  intro c hc f f' hff
  have hmeas : Measurable (UnforcedLeray.Short.PartIIIb.NearInst.Masked.cellPtInv c) :=
    UnforcedLeray.Short.PartIIIb.NearInst.Masked.measurable_cellPtInv c
  have hmap : Measure.map (UnforcedLeray.Short.PartIIIb.NearInst.Masked.cellPtInv c)
      (ageμ c (-3 / 2)) = ENNReal.ofReal c⁻¹ • UnforcedLeray.B0220.measureH c :=
    UnforcedLeray.Short.PartIIIb.NearInst.Masked.cpcInvH_eq c hc
  have hae : ∀ᵐ y ∂(Measure.map (UnforcedLeray.Short.PartIIIb.NearInst.Masked.cellPtInv c)
      (ageμ c (-3 / 2))), ∀ i, f y i = f' y i := by
    rw [hmap]
    exact Measure.ae_smul_measure (hff.mono fun y hy i => by rw [hy]) (ENNReal.ofReal c⁻¹)
  have hae' := ae_of_ae_map hmeas.aemeasurable hae
  filter_upwards [hae'] with x hx
  funext i
  exact hx i

end UnforcedLeray.Short.PartIIa.N01
