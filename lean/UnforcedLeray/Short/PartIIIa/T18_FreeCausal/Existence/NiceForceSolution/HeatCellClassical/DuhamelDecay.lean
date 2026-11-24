import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T18_2_4_1_4
import UnforcedLeray.Short.PartIIIa.T18_FreeCausal.Existence.NiceForceSolution.HeatCellClassical.DuhamelDecay.Value
import UnforcedLeray.Short.PartIIIa.T18_FreeCausal.Existence.NiceForceSolution.HeatCellClassical.DuhamelDecay.DirNice
import UnforcedLeray.Short.PartIIIa.T18_FreeCausal.Existence.NiceForceSolution.HeatCellClassical.DuhamelDecay.FderivComm

/-!
# Part III-a, task `PartIII-a:T18/2/4/1/4`: Gaussian decay of the Duhamel solution

Target: `duhamelDecay : DuhamelDecay` (`Sub/PartIIIa_T18_2_4_1_4.lean`, wiring of the leaves).
Leaves: `duhDecValue` (Value.lean), `duhDecDirNice` (DirNice.lean), `duhDecFderivComm` (FderivComm.lean).
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.IIIa

theorem duhamelDecay : UnforcedLeray.Short.IIIa.DuhamelDecay :=
  UnforcedLeray.Short.IIIa.duhamelDecay_of
    UnforcedLeray.Short.IIIa.duhDecValue
    UnforcedLeray.Short.IIIa.duhDecDirNice
    UnforcedLeray.Short.IIIa.duhDecFderivComm

end UnforcedLeray.Short.IIIa
