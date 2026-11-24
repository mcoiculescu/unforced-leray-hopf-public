import UnforcedLeray.Short.Interface.Statements
import UnforcedLeray.Short.Interface.Sub.I03
import UnforcedLeray.Short.Interface.Leaf1_Value
import UnforcedLeray.Short.Interface.Leaf1_Deriv

/-!
# Interface leaf 1 (`L3BackgroundOfPath`): unconditional theorem

Source of record: `the November 2 reference manuscript`, lines 6064-6070
("Gaussian convolution and the bounds on `a` give ... Hence `U ∈ C_per C₀`, `∇U ∈ C_per L³`").

Task `Interface:I03`. The conditional assembly `l3BackgroundOfPath_of` (`Sub/I03.lean`) takes the
two sub-lemmas `C0PathProps` and `L3PathRepProp` as hypotheses. Here both are discharged by the
proved leaves `c0Path_props` (`Leaf1_Value.lean`, task `Interface:I01`) and `l3Path_rep`
(`Leaf1_Deriv.lean`, task `Interface:I02`). No new mathematics is added.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter
open scoped ENNReal ContDiff Topology

namespace UnforcedLeray.Short.Interface

open UnforcedLeray UnforcedLeray.Blueprint UnforcedLeray.Cons.C08

/-- **Leaf 1** (lines 6064-6070: "Gaussian convolution and the bounds on `a` give ... Hence
`U ∈ C_per C₀`, `∇U ∈ C_per L³`"). Unconditional form of `l3BackgroundOfPath_of`, with the
sub-lemmas `c0Path_props` and `l3Path_rep` supplied. -/
theorem l3BackgroundOfPath : L3BackgroundOfPath :=
  l3BackgroundOfPath_of c0Path_props l3Path_rep

end UnforcedLeray.Short.Interface
