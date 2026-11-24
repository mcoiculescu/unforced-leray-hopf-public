import UnforcedLeray.Short.PartIIb.Tasks.LocalInteractionComparison.RemainderBound.Assembly
import UnforcedLeray.Short.PartIIb.Tasks.LocalInteractionComparison.RemainderBound.BoxJet
import UnforcedLeray.Short.PartIIb.Tasks.WindowComparison.TransverseTail.KOutChart

/-!
# `PartII-b:T20/2` (`LocalInteractionRemainderBound`): reduction to the identification `KOutChartAe`

Source of record: `the November 2 reference manuscript` (SP), lines 2007-2023
(`K_ε - K_0 = sB_0(T_ε - T_0) + s(B_ε - B_0)T_ε`; "Exact chart substitution writes the second as
`ε` times polynomially bounded coefficients multiplying `b, ∂_qb, ∂_ηb, Sb`; these are bounded by
`bg:profile-graph`").

* `RemainderBound/Pointwise.lean`: exact chart substitution, `kOutChart - flatK = εs·remW`
  (`RemBd.diff_apply`, using the flat divergence of the train) and
  `‖remW‖ ≤ 22J(1+|η|)(‖b‖ + ‖Sb‖ + ‖∂_ηb‖)` (`RemBd.diff_norm_le`).
* `RemainderBound/BoxJet.lean`: `rawBoxJet_proof : RawBoxJet` (unconditional; Part I weighted jet
  bounds and transverse tails, `RaisedChartBridge`, `PsiEtaSegment`).
* `RemainderBound/Assembly.lean`: `localInteractionRemainderBound_of_leaves (hId : KOutChartAe)
  (hJ : RawBoxJet)`, with `phys_graph_at_zero`, `hasWeakVec_dqOf`, uniqueness of weak derivatives.

The only open input is the identification leaf `KOutChartAe` (`Tasks/WindowComparison/TransverseTail/
Leaves.lean`, shared with `PartII-b:G3/2`): the weak output `g` of `IsKOut p b g` is a.e. the chart
formula `kOutChart p b Qb Eb` on the strip `s > 0, |q| < c/2`.  Once it is proved,
`localInteractionRemainderBound_of = localInteractionRemainderBound_of_chartAe kOutChartAe_proof`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.IIb

/-- **`LocalInteractionRemainderBound` from the identification leaf `KOutChartAe`** (SP 2007-2023);
the coefficient leaf `RawBoxJet` is proved (`rawBoxJet_proof`). -/
theorem localInteractionRemainderBound_of_chartAe (hId : KOutChartAe) :
    LocalInteractionRemainderBound :=
  localInteractionRemainderBound_of_leaves hId rawBoxJet_proof

theorem localInteractionRemainderBound_of :
    UnforcedLeray.Short.IIb.LocalInteractionRemainderBound :=
  localInteractionRemainderBound_of_chartAe kOutChartAe_proof

end UnforcedLeray.Short.IIb

end

#print axioms UnforcedLeray.Short.IIb.localInteractionRemainderBound_of_chartAe
#print axioms UnforcedLeray.Short.IIb.rawBoxJet_proof
