import UnforcedLeray.Short.PartIIIb.NearInst.FlatTrain.Defs

/-!
# Measurability of the flat train coefficient (source 261-288, 3566-3567)

The train is smooth on `[0, ∞) × ℝ²` (`B0140.IsTrain.smooth_v`, source 261-288), and the flat
coefficient `trainMer tr` equals `tr.v s z` for `s ≥ 0` and `0` for `s < 0`
(`PartIII-a/FlatCausal.lean`, `IIIa.trainVel`). A function that is continuous on the closed
half-space `{0 ≤ s}` and constant on its complement is measurable.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set

namespace UnforcedLeray.Short.PartIIIb.NearInst

open UnforcedLeray.Short.PartIIIb.Concrete

/-- **Measurability of the flat coefficient** (source 3566-3567, 261-288). -/
theorem trainMerMeasurable : TrainMerMeasurable := by
  classical
  intro ν c tr
  have hS : MeasurableSet {p : Chart | 0 ≤ p.1} :=
    measurableSet_le measurable_const measurable_fst
  have hv : ContinuousOn (fun p : Chart => tr.v p.1 p.2) {p : Chart | 0 ≤ p.1} :=
    tr.isTrain.smooth_v.continuousOn.comp (continuous_fst.prodMk continuous_snd).continuousOn
      (fun p hp => ⟨hp, mem_univ _⟩)
  have hcont : ContinuousOn
      (fun p : Chart => WithLp.toLp 2 (fun i => tr.v p.1 p.2 i) : Chart → WithLp 2 (Fin 2 → ℝ))
      {p : Chart | 0 ≤ p.1} := by
    have hv' : ContinuousOn (fun p : Chart => (tr.v p.1 p.2 : WithLp 2 (Fin 2 → ℝ)))
        {p : Chart | 0 ≤ p.1} := hv
    refine hv'.congr fun p _ => ?_
    simp
  have hcont' : ContinuousOn (fun _ : Chart => (0 : WithLp 2 (Fin 2 → ℝ)))
      {p : Chart | 0 ≤ p.1}ᶜ :=
    continuousOn_const
  have hpw : trainMer tr = Set.piecewise {p : Chart | 0 ≤ p.1}
      (fun p : Chart => WithLp.toLp 2 (fun i => tr.v p.1 p.2 i))
      (fun _ : Chart => (0 : WithLp 2 (Fin 2 → ℝ))) := by
    funext p
    by_cases h : 0 ≤ p.1
    · simp [trainMer, UnforcedLeray.Short.IIIa.trainVel, Set.piecewise, h]
    · simp [trainMer, UnforcedLeray.Short.IIIa.trainVel, Set.piecewise, h]
      ext i
      simp
  rw [hpw]
  exact ContinuousOn.measurable_piecewise hcont hcont' hS

end UnforcedLeray.Short.PartIIIb.NearInst
