import UnforcedLeray.Short.PartI.Sub.PartI_T02_1_2_3_1_2.SmoothSeq_Sub
import UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution.TrainH3ContinuousRepresentative

/-!
# Part I, task `PartI:T02/1/2/3/1/2/2/2`: a.e. bounded values of `H³` classes

Source of record: `the November 2 reference manuscript`, lines 261-288.

Proves the leaf `BdpValueBound` from `Short/PartI/Sub/PartI_T02_1_2_3_1_2/SmoothSeq_Sub.lean`.
The bounded continuous representative `F` of `TrainB.exists_scalarH3_bcf_representative`
satisfies `‖F‖ ≤ 12 ‖z‖` and `F = W.value z` a.e. on `cellμ c`; the value of `z` is therefore
bounded by `12 ‖z‖` a.e. on `(Sob.cylinder c).μ`, which equals `cellμ c`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace UnforcedLeray.Short.PartI

open UnforcedLeray
open UnforcedLeray.Cyl (Plane)
open UnforcedLeray.TrainB

theorem bdp_valueBound : UnforcedLeray.Short.PartI.BdpValueBound := by
  intro c hc z
  obtain ⟨F, hFae, -, hFnorm⟩ := exists_scalarH3_bcf_representative hc z
  have hpt : ∀ w, |(F : Plane → ℝ) w| ≤ 12 * ‖z‖ := fun w => by
    have h := (BoundedContinuousFunction.norm_coe_le_norm F w).trans hFnorm
    rwa [Real.norm_eq_abs] at h
  have key : ∀ᵐ w ∂Cyl.cellμ c, |(Cyl.H.val z : Plane → ℝ) w| ≤ 12 * ‖z‖ := by
    filter_upwards [hFae] with w hw
    have h1 := hpt w
    rw [hw] at h1
    exact h1
  have gen : ∀ μ' : Measure Plane, μ' = Cyl.cellμ c →
      ∀ᵐ w ∂μ', |(Cyl.H.val z : Plane → ℝ) w| ≤ 12 * ‖z‖ := by
    intro μ' h
    subst h
    exact key
  exact ⟨12 * ‖z‖, gen _ (Cyl.cylinder_μ_eq c)⟩

end UnforcedLeray.Short.PartI
