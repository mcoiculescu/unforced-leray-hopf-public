import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T13_1_4_3_3
import UnforcedLeray.Short.PartIIb.Tasks.FlatWindows.Org.CylHeatMaxReg.Mollify.Conv.Mink
import UnforcedLeray.Short.PartIIb.Tasks.FlatWindows.Org.CylHeatMaxReg.Mollify.Conv.WinMemLp
import UnforcedLeray.Short.PartIIb.Tasks.FlatWindows.Org.CylHeatMaxReg.Mollify.Conv.WinReduce

/-!
# Part II-b, task `PartII-b:T13/1/4/3/3/4` (`chmMollConv`): assembly

Source: `the November 2 reference manuscript` lines 1933-1935.

The three hypotheses of `chmMollConv_of` are supplied by the lemma files
`Conv/Mink.lean` (`chmMink`), `Conv/WinMemLp.lean` (`chmWinMemLp`) and
`Conv/WinReduce.lean` (`chmWinReduce`).
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.IIb

theorem chmMollConv : UnforcedLeray.Short.IIb.ChmMollConv :=
  chmMollConv_of chmMink chmWinMemLp chmWinReduce

end UnforcedLeray.Short.IIb

#print axioms UnforcedLeray.Short.IIb.chmMollConv
