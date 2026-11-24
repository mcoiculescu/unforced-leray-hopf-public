import UnforcedLeray.Short.PartIIb.Tasks.CylEnergy.ClassicalExists.CRDeriv.Diff.Common

/-!


Proves `DCont` (`Sub/T22_1_10_1.lean`). For `τ ∈ [s,T]` and `i`, the map
`x ↦ ∫_s^τ (∂_i K_{ν(τ-r)}) * g(r)(x) dr` is continuous. Dominated continuity over the interval
(`intervalIntegral.continuous_of_dominated_interval`): the integrand is continuous in `x` for
`r < τ` by `heatGradFormula`, its slices are measurable by `dParamCont`, and it is dominated by
`2 e^{ν(T-s)} M0 (1 + ν^{-1/2}(τ-r)^{-1/2})` from `heatWBounds`.
Source `the November 2 reference manuscript`, lines 2074-2093 and 2103-2105.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open UnforcedLeray.Cons.C03.Concrete

namespace UnforcedLeray.Short.IIb.CylPDE

open DiffC in
/-- **`PartII-b:T22/1/10/1/3`** Continuity of the Duhamel derivative in the plane variable (`DCont`). -/
theorem dCont : UnforcedLeray.Short.IIb.CylPDE.DCont := by
  intro ν s T hν hsT g b hH τ hτ i
  have hH' := hH
  obtain ⟨hgc, hbc, hb0, hgb⟩ := hH'
  obtain ⟨hDc, hDd⟩ := dParamCont ν s T hν hsT g b hH τ hτ
  obtain ⟨M0, hM0⟩ := (isCompact_Icc (a := s) (b := T)).exists_bound_of_continuousOn hbc
  have hbM : ∀ t ∈ Icc s T, b t ≤ M0 := fun t ht =>
    (le_abs_self (b t)).trans (by simpa [Real.norm_eq_abs] using hM0 t ht)
  have hτs : s ≤ τ := hτ.1
  have hτT : τ ≤ T := hτ.2
  have hne := ae_ne_point τ
  refine intervalIntegral.continuous_of_dominated_interval (μ := volume)
    (F := fun x t => heatSGd i (ν * (τ - t)) (g t) x)
    (bound := fun t => 2 * Real.exp (ν * (T - s)) * M0 +
      2 * Real.exp (ν * (T - s)) * M0 * ν ^ (-(1 / 2 : ℝ)) * (τ - t) ^ (-(1 / 2 : ℝ)))
    ?_ ?_ ?_ ?_
  · intro x
    rw [uIoc_of_le hτs]
    exact aesm_slice (fun t y => heatSGd i (ν * (τ - t)) (g t) y) (hDd i) x
  · intro x
    filter_upwards [hne] with t ht hmem
    rw [uIoc_of_le hτs] at hmem
    have htτ : t < τ := lt_of_le_of_ne hmem.2 ht
    rw [Real.norm_eq_abs]
    exact heatSGd_bound_int hν hτT hmem.1.le htτ (hbM t ⟨hmem.1.le, htτ.le.trans hτT⟩)
      (hb0 t ⟨hmem.1.le, htτ.le.trans hτT⟩) (hgb t ⟨hmem.1.le, htτ.le.trans hτT⟩) i x
  · have := affine_kernel_intInt (2 * Real.exp (ν * (T - s)) * M0)
      (2 * Real.exp (ν * (T - s)) * M0 * ν ^ (-(1 / 2 : ℝ))) τ s
    exact this
  · filter_upwards [hne] with t ht
    intro hmem
    rw [uIoc_of_le hτs] at hmem
    have htτ : t < τ := lt_of_le_of_ne hmem.2 ht
    have hts : t ∈ Icc s T := ⟨hmem.1.le, htτ.le.trans hτT⟩
    have ha : 0 < ν * (τ - t) := mul_pos hν (by linarith)
    exact (heatGradFormula (b t) (g t) (cont_slice hgc hts) (hgb t hts)
      (ν * (τ - t)) ha).2.2 i

end UnforcedLeray.Short.IIb.CylPDE
