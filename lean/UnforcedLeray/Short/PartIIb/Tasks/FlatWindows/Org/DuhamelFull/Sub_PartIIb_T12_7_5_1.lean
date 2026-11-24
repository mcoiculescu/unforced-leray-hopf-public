import UnforcedLeray.Short.PartIIb.Tasks.FlatWindows.Org.DuhamelFull.Defs
import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T12_7_5_1
import UnforcedLeray.Short.PartIIb.Tasks.FlatWindows.Org.DuhamelFull.Sub_T12_7_5

/-!
# Part II-b, task `PartII-b:T12/7/5/1` (`dfe_DeqPdPointwise`): decomposition

Source: `the November 2 reference manuscript`,
lines 1923-1927.

`s ↦ deqSmooth ν Ψ i t s z` is differentiated under the `w`-integral (`dfe_DeqpdJointDeriv`), and the
resulting integral is identified with `deqSmoothD` (`dfe_DeqpdSmoothDEq`, using the planar heat
equation `deqHeatDeriv` and the chain-rule identity `dfe_DeqpdCptLap`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

/-- Differentiation under the `w`-integral (SP 1923-1927): for `s > t`,
`d/ds ∫ K_{ν(s-t)}(w) Ψ_i(s, z-w) dw = ∫ [ν (∂_θ K)(ν(s-t), w) Ψ_i(s, z-w) + K ∂_sΨ_i(s, z-w)] dw`.
Proof: `hasDerivAt_integral_of_dominated_loc_of_deriv_le` on a ball of radius `(s-t)/2`, with
`flatHeat_kernel_eq`, `hasDerivAt_heatKernel2_age`, majorant
`abs_heatKernel2AgeDerivative_le_local` (`Lib/HeatCylinder/HeatKernelAgeMajorant.lean`), and the
kernel comparison `heatKernel2 θ w ≤ 4 heatKernel2 (2θ₀) w` for `θ₀/2 < θ < 2θ₀`. -/
def dfe_DeqpdJointDeriv : Prop :=
  ∀ (ν t : ℝ), 0 < ν → ∀ Ψ : Coord → Fin 2 → ℝ, IsPlanarTestDfe Ψ → ∀ i : Fin 2,
    ∀ s : ℝ, t < s → ∀ z : ℝ × ℝ,
      HasDerivAt (fun s' : ℝ => deqSmooth ν Ψ i t s' z)
        (∫ w : ℝ × ℝ,
          (ν * (UnforcedLeray.HeatCylinder.heatKernel2AgeDerivative (ν * (s - t)) w *
              Ψ (s, z - w) i) +
            flatHeatKernel (ν * (s - t)) w * cpd 0 (fun y => Ψ y i) (s, z - w))) s

/-- Chain rule (SP 1923-1927): `planarLap` of the slice `y ↦ Ψ_i(s, y)` is
`(cpd 1 ∘ cpd 1 + cpd 2 ∘ cpd 2) Ψ_i (s, y)`; `fderiv` of `y ↦ Ψ(s, y)` in direction `v` is
`fderiv Ψ (s, y) (0, v)` (compare `partialDerivSlice` in
`Short/PartII-a/Tasks/N02LerayComparison/StreamMember/PartialDerivSlice.lean`). -/
def dfe_DeqpdCptLap : Prop :=
  ∀ (Ψ : Coord → Fin 2 → ℝ), IsPlanarTestDfe Ψ → ∀ (i : Fin 2) (s : ℝ) (y : ℝ × ℝ),
    planarLap (fun y' : ℝ × ℝ => Ψ (s, y') i) y =
      cpd 1 (fun x => cpd 1 (fun z => Ψ z i) x) (s, y) +
        cpd 2 (fun x => cpd 2 (fun z => Ψ z i) x) (s, y)

/-- Identification (SP 1923-1927): for `s > t`, the integral from `dfe_DeqpdJointDeriv` equals
`deqSmoothD ν Ψ i t s z`. Proof: split the integral (integrable: Gaussian times bounded continuous,
`deqhd_int_K`, `integrable_heatKernel2AgeDerivative`), apply `deqhd_hval` (file
`Tasks/FlatCausal/dfe_DuhamelEquation/HeatDeriv.lean`) to `ψ = Ψ_i(s, ·)` (smooth, compact support from
`IsPlanarTestDfe`), `flatHeat_kernel_eq`, and `dfe_DeqpdCptLap`. -/
def dfe_DeqpdSmoothDEq : Prop :=
  ∀ (ν t : ℝ), 0 < ν → ∀ Ψ : Coord → Fin 2 → ℝ, IsPlanarTestDfe Ψ → ∀ i : Fin 2,
    ∀ s : ℝ, t < s → ∀ z : ℝ × ℝ,
      (∫ w : ℝ × ℝ,
          (ν * (UnforcedLeray.HeatCylinder.heatKernel2AgeDerivative (ν * (s - t)) w *
              Ψ (s, z - w) i) +
            flatHeatKernel (ν * (s - t)) w * cpd 0 (fun y => Ψ y i) (s, z - w))) =
        deqSmoothD ν Ψ i t s z

theorem dfe_deqPdPointwise_of (h1 : dfe_DeqpdJointDeriv) (h2 : dfe_DeqpdSmoothDEq) : dfe_DeqPdPointwise := by
  intro ν t hν ht Ψ hΨ i s hs z
  have h := h1 ν t hν Ψ hΨ i s hs z
  rwa [h2 ν t hν Ψ hΨ i s hs z] at h

end UnforcedLeray.Short.IIb
