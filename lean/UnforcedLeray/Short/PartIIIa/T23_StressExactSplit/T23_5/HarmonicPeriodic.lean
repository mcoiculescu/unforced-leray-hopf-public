import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T23_5_1_1
import UnforcedLeray.Short.PartIIIa.T23_StressExactSplit.T23_5.HarmonicPeriodic.SummDiff
import UnforcedLeray.Short.PartIIIa.T23_StressExactSplit.T23_5.HarmonicPeriodic.LatticeDecay
import UnforcedLeray.Short.PartIIIa.T23_StressExactSplit.T23_5.HarmonicPeriodic.LatticeIdent

/-!
# Part III-a, `PartIII-a:T23/5/1/1`: `HarmonicPeriodicDecay` from its three leaves
(source 2354-2356 of `the November 2 reference manuscript`).

Assembles `harmonicPeriodicDecay_of` from `harmSummDiff` (summability and differentiability),
`latticeSumDecay` (exponential decay of the lattice sums) and `harmLatticeIdent`
(identification of the periodized quadrupole with the lattice sum).
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.IIIa

theorem harmonicPeriodicDecay : UnforcedLeray.Short.IIIa.HarmonicPeriodicDecay :=
  harmonicPeriodicDecay_of harmSummDiff latticeSumDecay harmLatticeIdent

end UnforcedLeray.Short.IIIa
