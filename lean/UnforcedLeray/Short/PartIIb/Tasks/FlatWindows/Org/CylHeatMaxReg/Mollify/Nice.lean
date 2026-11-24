import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T13_1_4_3_1
import UnforcedLeray.Short.PartIIb.Tasks.FlatWindows.Org.CylHeatMaxReg.Mollify.LocInt
import UnforcedLeray.Short.PartIIb.Tasks.FlatWindows.Org.CylHeatMaxReg.Mollify.Young

/-!
# Part II-b, task `PartII-b:T13/1/4/3/1` (`chmMollNice`): decomposition

Source: `the November 2 reference manuscript` (SP) lines 1933-1935.

Proof. Assemble `ChmMollNice` from the two leaves: local integrability of a `q`-periodic
`L^r(cylMeas c)` function (`chmLocInt`, task `/2`) and the Young inequality in `L^r(cylMeas c)`
(`chmYoungCyl`, task `/3`), via `chmMollNice_of`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.IIb

/-- **Task `PartII-b:T13/1/4/3/1`.** The mollified functions are smooth, periodic and have all
derivatives in `L^r(cylMeas c)` (SP 1933-1935). -/
theorem chmMollNice : UnforcedLeray.Short.IIb.ChmMollNice :=
  chmMollNice_of chmLocInt chmYoungCyl

end UnforcedLeray.Short.IIb

end
