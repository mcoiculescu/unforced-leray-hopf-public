import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.Ward.Bg.YoungW2.Corr.Sub
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.Ward.Bg.YoungW2.Corr.GradGraph
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.Ward.Bg.YoungW2.Corr.HessGraph
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.Ward.Bg.YoungW2.Corr.ContRepWeakSlice
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.Ward.Bg.YoungW2.Corr.WeakDerivClassical

/-!
# `BgCorrYoungJets` from its four leaves (source 1515-1531, 2525-2562, 2607-2609)

Assembly only: `bgCorrYoungJets_of` (`Corr/Sub.lean`) applied to the four proved leaves
`bgCorrGradGraph`, `bgCorrHessGraph`, `bgContRepWeakSlice`, `weakDerivClassicalOn`.
Source of record: `the November 2 reference manuscript` (73 pages). -/

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem bgCorrYoungJets : BgCorrYoungJets :=
  bgCorrYoungJets_of bgCorrGradGraph bgCorrHessGraph bgContRepWeakSlice weakDerivClassicalOn

end UnforcedLeray.Short.PartIIIb.Concrete
