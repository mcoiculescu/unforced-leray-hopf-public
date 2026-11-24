import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T18_2_4_1_3

/-!
# Part III-a, task `PartIII-a:T18/2/4/1/3/5` (leaf E): abstract FTC on `(0, ∞)`

Target: `duhEqFTC : DuhEqFTC` (`Sub/PartIIIa_T18_2_4_1_3.lean`). Source of record:
`the November 2 reference manuscript`, Duhamel formula for the heat equation.

Proof. Let `ψ = Function.update φ 0 v`. Then `ψ = φ` on `(0, ∞)`, `ψ 0 = v`, `ψ` is
continuous within `Ici 0` at `0` (the limit of `φ` at `0⁺` is `v`), `ψ` has derivative `φ'`
on `(0, ∞)`, and `ψ r = 0` for `r > max T 0`, so `ψ → 0` at `+∞`. Mathlib's
`integral_Ioi_of_hasDerivAt_of_tendsto` gives `∫_{(0,∞)} φ' = 0 - ψ 0 = -v`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology

namespace UnforcedLeray.Short.IIIa

theorem duhEqFTC : UnforcedLeray.Short.IIIa.DuhEqFTC := by
  unfold DuhEqFTC
  intro φ φ' T v hderiv hint hzero hlim
  obtain ⟨ψ, hψdef⟩ : ∃ ψ : ℝ → ℂ, ψ = Function.update φ 0 v := ⟨_, rfl⟩
  have hψpos : ∀ y : ℝ, 0 < y → ψ y = φ y := by
    intro y hy
    rw [hψdef, Function.update_of_ne hy.ne']
  have hψ0 : ψ 0 = v := by
    rw [hψdef]
    simp
  have hcontIoi : ContinuousWithinAt ψ (Ioi 0) 0 := by
    unfold ContinuousWithinAt
    rw [hψ0]
    refine Tendsto.congr' ?_ hlim
    filter_upwards [self_mem_nhdsWithin] with y hy
    exact (hψpos y (Set.mem_Ioi.mp hy)).symm
  have hcont : ContinuousWithinAt ψ (Ici 0) 0 :=
    continuousWithinAt_Ioi_iff_Ici.mp hcontIoi
  have hderivψ : ∀ x ∈ Ioi (0 : ℝ), HasDerivAt ψ (φ' x) x := by
    intro x hx
    refine (hderiv x (Set.mem_Ioi.mp hx)).congr_of_eventuallyEq ?_
    filter_upwards [Ioi_mem_nhds (Set.mem_Ioi.mp hx)] with y hy
    exact hψpos y (Set.mem_Ioi.mp hy)
  have hlimψ : Tendsto ψ atTop (𝓝 0) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_gt_atTop (max T 0)] with r hr
    have hr0 : 0 < r := lt_of_le_of_lt (le_max_right _ _) hr
    have hrT : T < r := lt_of_le_of_lt (le_max_left _ _) hr
    rw [hψpos r hr0]
    exact (hzero r hrT).symm
  have key := integral_Ioi_of_hasDerivAt_of_tendsto hcont hderivψ hint hlimψ
  rw [hψ0, zero_sub] at key
  exact key

end UnforcedLeray.Short.IIIa
