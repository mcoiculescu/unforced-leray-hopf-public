import UnforcedLeray.Short.PartIIIa.Sub.T23_3_org
import UnforcedLeray.Short.PartIIIa.Sub.T23_5_Leaves

/-!
# Part III-a: the restated inlet statements from their reductions
(`ORG:stmt/PartIII-a/ParamsWideQuantifiers`)

Source of record: `the November 2 reference manuscript`, lines 2711-2727
(`stress-short:coefficients`, "The finite inlet is absorbed by `P_ν`"), 2739-2745
(`stress-short:transverse`, "the finite inlet's stream tail"), with the inlet construction
2347-2362 and the frozen growing pair 2048-2049.

`StressInputs.InletCoeffBounds` and `StressInputs.InletTransverseTail` now fix the slow age `Σ > 0`
and the growing eigenpair `(λ, q)` before the constants, at the levels with `p.ageCut = Σ`,
`p.mode = q`. This file checks that the restated statements are exactly the corrected statements
already reduced by the organizers:

* `inletCoeffBounds_of_frozen`: `InletCoeffBounds` is `InletCoeffBoundsSlow`
  (`Sub/T23_3_org.lean`), proved there from `IIb.FrozenStreamBounds` (task `PartII-b:G4/2`);
* `inletTransverseTail_of_leaves`: `InletTransverseTail` is `InletTransverseTailQ`
  (`Sub/T23_5_Leaves.lean`) with the slow binders moved after `0 < D`, proved there from
  `PeriodicStreamTail` (task `PartIII-a:T23/5/1`) and `InletChartFromStream` (`PartIII-a:T23/5/2`).
-/

set_option autoImplicit false

namespace UnforcedLeray.Short.IIIa

/-- **The finite inlet is absorbed by `P_ν`** (SP 2711-2727, 2347-2362), from the frozen stream
bounds (SP 2347-2358): the restated `InletCoeffBounds` is `InletCoeffBoundsSlow`. -/
theorem inletCoeffBounds_of_frozen (hF : UnforcedLeray.Short.IIb.FrozenStreamBounds) :
    InletCoeffBounds :=
  inletCoeffBounds_of hF

/-- **The inlet transverse tail** (SP 2739-2745, 2347-2366), from the two leaves: the restated
`InletTransverseTail` is `InletTransverseTailQ` with the slow binders reordered. -/
theorem inletTransverseTail_of_leaves (ha : PeriodicStreamTail) (hb : InletChartFromStream) :
    InletTransverseTail :=
  fun dm dp hdm mZ hmZ bexp D hbexp hD Sig lam q hSig hq =>
    inletTransverseTail_of ha hb Sig lam q hSig hq dm dp hdm mZ hmZ bexp D hbexp hD

end UnforcedLeray.Short.IIIa
