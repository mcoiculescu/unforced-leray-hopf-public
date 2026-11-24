import UnforcedLeray.Infra.JointMeasurableRep

/-!
# Jointly measurable representatives of continuous `L^p`-valued paths (INF14 target T5)


target T5 and bypass B7; critic §5a of the Theorem A blueprint (realization measurability:
`IsTheoremASolution` needs jointly measurable `u, G, H` that are correct at **every** time, built
from continuous curves `u ∈ C([0,T]; L²)`, `G, H ∈ C((0,T]; L²)`).

The construction is the audited draft `UnforcedLeray.Infra.JointMeasurableRep`

NonUniqueEuler `JointRep` argument (`NonUniqueEuler/P/Infra/JointRep/Representative.lean`) from
`Lp ℝ 2` to an arbitrary `Lp E p μ`; it is reused here, not rebuilt (task instruction). This file
only restates it in the shape of the scoping signature.

## Main results

* `exists_isJointRep_of_continuousOn`: strongly measurable `U : ℝ × α → E`-representative;
* `exists_measurable_isJointRep_of_continuousOn`: the scoping signature, with
  `Measurable (Function.uncurry U)` (for a Borel target);
* `jointRep_ae_eq_prod`: uniqueness of joint representatives a.e. on the product.

The slice lemma `stronglyMeasurable_toPath_Lq` of the scoping note (product → Bochner slices in
`L^q`) is in `BochnerTime.Slices`.
-/

set_option autoImplicit false

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace UnforcedLeray.BochnerTime

variable {α E : Type*} [MeasurableSpace α] {μ : Measure α} [NormedAddCommGroup E] [CompleteSpace E]
  {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- **Joint representative** (T5). A path `u : ℝ → Lp E p μ` continuous on a measurable set
`s` has a jointly strongly measurable `U` with `U t = u t` a.e. for **every** `t ∈ s`. -/
theorem exists_isJointRep_of_continuousOn {u : ℝ → Lp E p μ} {s : Set ℝ} (hs : MeasurableSet s)
    (hu : ContinuousOn u s) :
    ∃ U : ℝ → α → E, StronglyMeasurable (Function.uncurry U) ∧ ∀ t ∈ s, U t =ᵐ[μ] u t := by
  obtain ⟨F, hF, hFu⟩ :=
    UnforcedLeray.Infra.JointMeasurableRep.exists_stronglyMeasurable_rep_of_continuousOn
      (μ := μ) hs hu
  exact ⟨fun t x => F (t, x), hF, hFu⟩

/-- **Joint representative, measurable form** (T5, the scoping signature): for a Borel target,
`Function.uncurry U` is measurable. -/
theorem exists_measurable_isJointRep_of_continuousOn [MeasurableSpace E] [BorelSpace E]
    {u : ℝ → Lp E p μ} {s : Set ℝ} (hs : MeasurableSet s) (hu : ContinuousOn u s) :
    ∃ U : ℝ → α → E, Measurable (Function.uncurry U) ∧ ∀ t ∈ s, U t =ᵐ[μ] u t := by
  obtain ⟨U, hU, hUu⟩ := exists_isJointRep_of_continuousOn hs hu
  exact ⟨U, hU.measurable, hUu⟩

/-- **Uniqueness** (T5). Two jointly strongly measurable representatives of the same path on a
measurable set `s` of times agree a.e. for `(ν.restrict s).prod μ`. -/
theorem jointRep_ae_eq_prod [SFinite μ] {ν : Measure ℝ} {u : ℝ → Lp E p μ} {s : Set ℝ}
    (hs : MeasurableSet s) {U V : ℝ → α → E} (hU : StronglyMeasurable (Function.uncurry U))
    (hV : StronglyMeasurable (Function.uncurry V)) (hUu : ∀ t ∈ s, U t =ᵐ[μ] u t)
    (hVu : ∀ t ∈ s, V t =ᵐ[μ] u t) :
    Function.uncurry U =ᵐ[(ν.restrict s).prod μ] Function.uncurry V :=
  UnforcedLeray.Infra.JointMeasurableRep.ae_eq_prod_of_isRep hs hU hV hUu hVu

end UnforcedLeray.BochnerTime
