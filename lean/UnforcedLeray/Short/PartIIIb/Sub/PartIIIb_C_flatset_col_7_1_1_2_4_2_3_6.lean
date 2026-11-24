import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_4_2_proj2
import UnforcedLeray.Short.PartIIIa.Tasks.AdjSmooth.End.Leaf.WeakCellAeUnique

/-!
# Weak cell derivatives are unique a.e. (organize task
`PartIII-b:C/flatset/col/7/1/1/2/4/2/3/6`)

Source `the November 2 reference manuscript`
1650-1656: the weak derivatives of the flat equation are taken against smooth `c`-periodic tests with
compact `η`-support.

The statement is the `Cyl.cellμ` form of `IIIa.WeakCellAeUnique`, proved in
`Short/PartIII-a/Tasks/AdjSmooth/End/Leaf/WeakCellAeUnique.lean` (`IIIa.weakCellAeUnique`, the
fundamental lemma on the open strip plus local periodization `wkPeriodize`). The only difference is the
cell: `Cyl.cell c = Ico (-c / 2) (c / 2) ×ˢ univ` and `B0579.cell c = Ico (-(c / 2)) (c / 2) ×ˢ univ`,
equal by `neg_div`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

/-- **Weak cell derivatives are unique a.e.** -/
theorem weakCellDerivUnique : WeakCellDerivUnique := by
  intro c _hc j u g₁ g₂ h1 h2
  have hcell : UnforcedLeray.Cyl.cellμ c = volume.restrict (UnforcedLeray.B0579.cell c) := by
    unfold UnforcedLeray.Cyl.cellμ UnforcedLeray.Cyl.cell UnforcedLeray.B0579.cell
    rw [neg_div]
  rw [hcell]
  exact UnforcedLeray.Short.IIIa.weakCellAeUnique c j u g₁ g₂ h1 h2

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
