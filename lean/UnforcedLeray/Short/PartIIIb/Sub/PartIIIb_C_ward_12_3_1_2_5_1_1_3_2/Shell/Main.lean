import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_5_1_1_3_2.Shell.Reduce
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_5_1_1_3_2.Shell.InvBound
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_5_1_1_3_2.Shell.Absorb
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_5_1_1_3_2.Shell.Dtau

/-!
# `nvShellJets : NvShellJets`

Source `the November 2 reference manuscript`
lines 2545-2549, 1206-1222.  Assembled from the shell calculus leaves: `shellFrameJets`,
`shellAgeJets`, `shellPhaseJets`, `shellTransJets` (compactness of the slice
`{ρ₀ ≤ ϱ ≤ R₀, y₃ = 0}` and axial translation), `shellAbsorb` (`(1+|t|)^m e^{-a|t|}` absorbed),
`shellDτ` (`∂_τ = (R/2)∂_ξ`), via `Shell.nvShellJets_of` (Leibniz and Faà di Bruno).
-/

set_option autoImplicit false

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- **`NvShellJets`** (source 2545-2549, 1206-1222). -/
theorem nvShellJets : NvShellJets :=
  Shell.nvShellJets_of Shell.shellFrameJets Shell.shellAgeJets Shell.shellPhaseJets
    Shell.shellTransJets Shell.shellAbsorb Shell.shellDτ

end UnforcedLeray.Short.PartIIIb.Concrete
