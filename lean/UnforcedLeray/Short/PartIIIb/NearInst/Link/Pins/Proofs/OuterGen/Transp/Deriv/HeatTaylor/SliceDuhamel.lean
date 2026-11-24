import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_near_pins_3_4_2_3_2_4_13

/-!
# Double heat Duhamel on `ℝ³` (task `PartIII-b:C/near/pins/3/4/2/3/2/4/13/5`)

Proves `ODHT_SliceDuhamel`: `e^{θΔ}u - u - θΔu = ∫_0^θ ∫_0^t e^{sΔ}Δ²u ds dt` at every point.
Route: `Heat.average_sub_eq_integral` for `u` gives `e^{θΔ}u - u = ∫_0^θ e^{tΔ}Δu dt`; for
`t > 0` the same lemma applied to `Δu` gives `e^{tΔ}Δu - Δu = ∫_0^t e^{sΔ}Δ²u ds`; the constant
`Δu` is subtracted under the integral (interval integrability from continuity of
`t ↦ e^{tΔ}Δu(x)` on `(0, ∞)` and the uniform bound `‖Δu‖ ≤ 3M`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.PartIIIb.NearInst

theorem odhtSliceDuhamel : ODHT_SliceDuhamel := by
  intro u M hu hb hbv θ hθ x
  have hle2 : (2 : WithTop ℕ∞) ≤ ∞ := by simp
  have hle4 : ((2 + 2 : ℕ) : WithTop ℕ∞) ≤ ∞ := by simp
  have hu2 : ContDiff ℝ 2 u := hu.of_le hle2
  have hu4 : ContDiff ℝ ((2 + 2 : ℕ) : WithTop ℕ∞) u := hu.of_le hle4
  have hv2 : ContDiff ℝ 2 (UnforcedLeray.Heat.vlap u) :=
    UnforcedLeray.Heat.contDiff_vlap (n := 2) hu4
  -- first heat FTC for `u`
  have hF1 : UnforcedLeray.Heat.average θ u x - u x
      = ∫ t in (0 : ℝ)..θ, UnforcedLeray.Heat.average t (UnforcedLeray.Heat.vlap u) x :=
    UnforcedLeray.Heat.average_sub_eq_integral hu2 hb hθ x
  -- heat FTC for `Δu` at each positive time
  have hstep : ∀ t : ℝ, 0 < t →
      UnforcedLeray.Heat.average t (UnforcedLeray.Heat.vlap u) x
        - UnforcedLeray.Heat.vlap u x
      = ∫ s in (0 : ℝ)..t,
          UnforcedLeray.Heat.average s (UnforcedLeray.Heat.vlap (UnforcedLeray.Heat.vlap u)) x :=
    fun t ht => UnforcedLeray.Heat.average_sub_eq_integral hv2 hbv ht x
  -- interval integrability of `t ↦ e^{tΔ}Δu(x)` on `[0, θ]`
  have hvc : Continuous (UnforcedLeray.Heat.vlap u) := UnforcedLeray.Heat.continuous_vlap hu2
  have hvb : ∀ y, ‖UnforcedLeray.Heat.vlap u y‖ ≤ 3 * M :=
    UnforcedLeray.Heat.norm_vlap_le (hb 2 le_rfl)
  have hfc : ContinuousOn (fun s : ℝ => UnforcedLeray.Heat.average s
      (UnforcedLeray.Heat.vlap u) x) (Ioi 0) :=
    UnforcedLeray.Heat.continuousOn_average_time_of_bound hvc.aestronglyMeasurable hvb x
  have hint : IntervalIntegrable (fun s : ℝ => UnforcedLeray.Heat.average s
      (UnforcedLeray.Heat.vlap u) x) volume 0 θ := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hθ.le]
    refine ⟨(hfc.mono fun t ht => ht.1).aestronglyMeasurable measurableSet_Ioc, ?_⟩
    refine HasFiniteIntegral.restrict_of_bounded (C := 3 * M) measure_Ioc_lt_top ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact UnforcedLeray.Heat.norm_average_le_of_bound ht.1 hvb x
  -- the inner integrand agrees with the double integral for `t ∈ (0, θ]`
  have hinner : ∫ t in (0 : ℝ)..θ,
      (UnforcedLeray.Heat.average t (UnforcedLeray.Heat.vlap u) x
        - UnforcedLeray.Heat.vlap u x)
      = ∫ t in (0 : ℝ)..θ, ∫ s in (0 : ℝ)..t,
          UnforcedLeray.Heat.average s (UnforcedLeray.Heat.vlap (UnforcedLeray.Heat.vlap u)) x := by
    refine intervalIntegral.integral_congr_ae (Filter.Eventually.of_forall fun t ht => ?_)
    rw [Set.uIoc_of_le hθ.le] at ht
    exact hstep t ht.1
  -- split off the constant `Δu(x)`
  have hsplit : ∫ t in (0 : ℝ)..θ,
      (UnforcedLeray.Heat.average t (UnforcedLeray.Heat.vlap u) x
        - UnforcedLeray.Heat.vlap u x)
      = (∫ t in (0 : ℝ)..θ, UnforcedLeray.Heat.average t (UnforcedLeray.Heat.vlap u) x)
        - θ • UnforcedLeray.Heat.vlap u x := by
    rw [intervalIntegral.integral_sub hint intervalIntegrable_const,
      intervalIntegral.integral_const, sub_zero]
  rw [hF1, ← hsplit]
  exact hinner

end UnforcedLeray.Short.PartIIIb.NearInst
