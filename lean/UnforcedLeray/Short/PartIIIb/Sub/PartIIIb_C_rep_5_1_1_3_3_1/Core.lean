import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_5_1_1_3_3_1_1
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_5_1_1_3_3_1_1.FarPointDom
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_5_1_1_3_3_1_1.AgeMassLeThin
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_5_1_2_4_1_3.Core

/-!
# `PartIII-b:C/rep/5/1/1/3/3/1`: `tailBoxThinSeq'` from the proved leaves

Source `the November 2 reference manuscript`
5585-5593 (bins), 3604-3621 (kernel gradient), 5569-5575 (Cauchy-Schwarz on the cell).

Leaves: `farPointDom_exists` (witness constant), `ageMassLeThin`, `wardYMajBinCore`, all proved in
their own modules; the statement is `tailBoxThinSeq'_of` applied to them.
-/

set_option autoImplicit false

noncomputable section

open UnforcedLeray.Blueprint.Planar (PlanarData)

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem tailBoxThinSeq' (Pl : PlanarData) (σ₀ mZ dm dp : ℝ) : TailBoxThinSeq Pl σ₀ mZ dm dp :=
  tailBoxThinSeq'_of Pl σ₀ mZ dm dp farPointDom_exists ageMassLeThin wardYMajBinCore

end UnforcedLeray.Short.PartIIIb.Concrete

end
