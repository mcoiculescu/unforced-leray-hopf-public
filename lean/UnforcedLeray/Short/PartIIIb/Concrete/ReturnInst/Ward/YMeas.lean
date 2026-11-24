import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.Ward.Defs
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_6
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.Ward.XDiff

/-!
# `WardYMeas`: measurability of the coefficient of `Y`
(source 4171-4174, 3611-3626)

Source of record: `the November 2 reference manuscript` (73 pages).

`WardYMeas` follows from `wardYMeas_of`, whose two hypotheses are the off-axis `C²` regularity
and the off-axis `τ`-differentiability of `X`. Both are read off `wardXDiff_proved`
(`WardXDiff`, the `ContDiffOn 3` on `axisᶜ` and the `τ`-differentiability clauses).
-/

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411

/-- **`WardYMeas`** (source 4171-4174, 3611-3626). -/
theorem wardYMeas_proved : WardYMeas :=
  wardYMeas_of
    (fun ν μ R c χy hχy hν hR hc hμ g hg τ y hy =>
      ((wardXDiff_proved ν μ R c χy hχy hν hR hc hμ g hg τ).1.contDiffAt
        (isOpen_compl_axis.mem_nhds hy)).of_le (by norm_num))
    (fun ν μ R c χy hχy hν hR hc hμ g hg τ y hy =>
      (wardXDiff_proved ν μ R c χy hχy hν hR hc hμ g hg τ).2.1 y hy)

end UnforcedLeray.Short.PartIIIb.Concrete
