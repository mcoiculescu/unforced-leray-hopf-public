import UnforcedLeray.Short.PartI.Sub.T02_1

/-!
# Part I, task `PartI:T02/1/1`: the compact mild `H³` solution for `trainDatum c`

Source of record: `the November 2 reference manuscript`, lines 261-285.

Pure library assembly, no new analysis.  The library theorem
`TrainB.exists_uniform_short_projected_NS_mild_train_on_P0_ball_allComponentsDivFree` is applied
with `M = ‖projectedInitialDatumH3 hc‖` at the point `x = projectedInitialDatumH3 hc`.  Its
hypothesis `P0H3CLM hc x = x` is `P0H3CLM_idem` at `datumVecH3 hc`, since
`projectedInitialDatumH3 hc = P0H3CLM hc (datumVecH3 hc)` by definition.  The seed-plus-Duhamel
equation and the trace at time `0` are exactly the first and third conjuncts of `IsMildTrain`,
and the library's `P0H3CLM`-fixed conjunct is the second.
-/

set_option autoImplicit false

namespace UnforcedLeray.Short.PartI

open UnforcedLeray.TrainB

/-- **Step 1** (source lines 261-285): for `ν > 0` and `c ≥ 1` the compact mild `H³` solution
exists on some `[0,T]`, with the projected datum as initial trace. -/
theorem mildTrainExists : MildTrainExists := by
  intro ν c hν hc hc1
  have hM : (0 : ℝ) ≤ ‖projectedInitialDatumH3 hc‖ := norm_nonneg _
  obtain ⟨T, hT, hsource⟩ :=
    exists_uniform_short_projected_NS_mild_train_on_P0_ball_allComponentsDivFree hc hc1 hν hM
  have hP0 : P0H3CLM hc (projectedInitialDatumH3 hc) = projectedInitialDatumH3 hc :=
    P0H3CLM_idem hc (datumVecH3 hc)
  obtain ⟨u, _, hfix, _, hP0u, htrace, _, _, _⟩ :=
    hsource (projectedInitialDatumH3 hc) le_rfl hP0
  refine ⟨T, hT, u, ?_⟩
  unfold IsMildTrain
  exact ⟨hfix, hP0u, htrace⟩

#print axioms UnforcedLeray.Short.PartI.mildTrainExists

end UnforcedLeray.Short.PartI
