import UnforcedLeray.Short.PartIIIa.Sub.ParamsWideBridges
import UnforcedLeray.Short.PartIIIa.T23_StressExactSplit.T23_5.PeriodicStreamTail
import UnforcedLeray.Short.PartIIIa.T23_StressExactSplit.T23_5.InletChartFromStream

/-!
# Part III-a, task `PartIII-a:T23/5`: the inlet transverse tail

Source of record: `the November 2 reference manuscript`, lines 2739-2756
(`stress-short:transverse`) and 2347-2366 (the inlet stream and its chart coefficient).

The statement `InletTransverseTail` (`StressInputs.lean`, with the slow binders `Sig`, `lam`, `q`
placed before the constants and `p.ageCut = Sig`, `p.mode = q` on the levels) is proved from the
two leaves `periodicStreamTail` (task `PartIII-a:T23/5/1`) and `inletChartFromStream`
(task `PartIII-a:T23/5/2`) through `inletTransverseTail_of_leaves` (`Sub/ParamsWideBridges.lean`).
-/

set_option autoImplicit false

namespace UnforcedLeray.Short.IIIa

/-- **The inlet transverse tail** (SP 2739-2756, 2347-2366): `InletTransverseTail` from the
periodized stream tail and the inlet chart bound. -/
theorem inletTransverseTail : UnforcedLeray.Short.IIIa.InletTransverseTail :=
  inletTransverseTail_of_leaves periodicStreamTail inletChartFromStream

end UnforcedLeray.Short.IIIa
