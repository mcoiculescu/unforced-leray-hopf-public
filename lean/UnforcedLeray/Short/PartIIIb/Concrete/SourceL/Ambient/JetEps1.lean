import UnforcedLeray.Short.PartIIIb.Concrete.SourceL.Sub.PartIIIb_C_srcL_9
import UnforcedLeray.Short.PartIIIb.Concrete.SourceL.Ambient.NewtonV
import UnforcedLeray.Short.PartIIIb.Concrete.SourceL.Ambient.StreamCut

/-!
# Part III-b, task `PartIII-b:C/srcL/9/6` (`jetEps1`): assembly

`jetEps1 K χo χy : JetEps1 K χo χy`, from the zero-width Newton field bound
`newtonVRegionBound` (Ambient/NewtonV.lean) and the stream cutoff jet bound `streamCutJet`
(Ambient/StreamCut.lean), via `jetEps1_of`.  Source: `the November 2 reference manuscript`
lines 4776-4782, 4917-4937.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem jetEps1 (K : Set ℝ) (χo χy : ℝ → ℝ) : JetEps1 K χo χy :=
  jetEps1_of (newtonVRegionBound χo) (streamCutJet χy)

end UnforcedLeray.Short.PartIIIb.Concrete
