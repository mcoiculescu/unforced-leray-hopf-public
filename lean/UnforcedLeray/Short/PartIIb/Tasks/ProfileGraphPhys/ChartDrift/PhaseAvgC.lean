import UnforcedLeray.Short.PartIIb.Tasks.ProfileGraphPhys.ChartDrift.Lift
import UnforcedLeray.Short.PartIIb.Tasks.GradLapNvC.DivVanish.WindowIntegral.RingBridgeC
import UnforcedLeray.Lib.AxisymmetricB.Lift

/-!
# `PartII-b:T10/6/3/1/2b`: the complex phase average over the ring chart

`P⁻¹ ∫_{(0,P]} ∫ G(chart) = π R² ∫ G dageμ c (-5/2)` for measurable, `q`-periodic `G` integrable
for `ageμ c (-5/2)`, `P = 2c/R`.

* `ringBridgeC` (the complex ring-chart bridge, with `ε = R⁻¹`, so `ε⁻¹ = R` and `2εc = 2c/R`)
  gives the phase average as `(πR²/c) ∫_{Ioi × qCell} s^{-5/2} G`, under the lintegral finiteness
  `∫⁻ s^{-5/2} ‖G‖ₑ < ∞` obtained from `Integrable G (ageμ c (-5/2))` via `lintegral_ageμ`.
* The age measure is the density `c⁻¹ s^{-5/2}` against `volume.restrict (Ioi × qCell)`
  (`ph_ageμ_density`, the set-by-set identity from `lintegral_ageμ`), so its Bochner integral is
  `c⁻¹ ∫_{Ioi × qCell} s^{-5/2} G`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal

namespace UnforcedLeray.Short.IIb

/-- The age measure is the density `c⁻¹ s^a` on `Ioi 0 × qCell c` (Lebesgue measure). -/
theorem ph_ageμ_density {c : ℝ} (hc : 0 < c) (a : ℝ) :
    Axi.ageμ c a = (volume.restrict (Ioi (0 : ℝ) ×ˢ Axi.qCell c)).withDensity
      (fun p => ENNReal.ofReal (c⁻¹ * p.1 ^ a)) := by
  refine Measure.ext fun S hS => ?_
  have h := Axi.lintegral_ageμ hc a (f := S.indicator 1) (measurable_one.indicator hS)
  rw [lintegral_indicator_one hS] at h
  rw [h, withDensity_apply _ hS, ← lintegral_indicator hS]
  refine lintegral_congr fun p => ?_
  by_cases hp : p ∈ S <;> simp [hp, Set.indicator]

theorem phaseAvgC_proof : UnforcedLeray.Short.IIb.ChartLift.PhaseAvgC := by
  intro R c G hR hc hG hper hint
  have hS : MeasurableSet (Ioi (0 : ℝ) ×ˢ Axi.qCell c) :=
    measurableSet_Ioi.prod (measurableSet_Ico.prod MeasurableSet.univ)
  have hε : (0 : ℝ) < R⁻¹ := inv_pos.2 hR
  -- finiteness of the weighted lintegral of `‖G‖`
  have hGn : Measurable fun p : ℝ × (ℝ × ℝ) => ‖G p‖ₑ := hG.enorm
  have hfin : ∫⁻ p in Ioi (0 : ℝ) ×ˢ Axi.qCell c,
      ENNReal.ofReal (c⁻¹ * p.1 ^ (-(5 / 2 : ℝ))) * ‖G p‖ₑ < ⊤ := by
    have h1 : ∫⁻ p, ‖G p‖ₑ ∂(Axi.ageμ c (-(5 / 2 : ℝ))) < ⊤ := hint.2
    rw [Axi.lintegral_ageμ hc _ hGn] at h1
    exact h1
  -- the phase average of `G` (complex ring-chart bridge, `ε = R⁻¹`)
  have key := ringBridgeC c R⁻¹ G hc hε hG hper hfin
  rw [inv_inv] at key
  -- the age measure is the weighted cell measure
  have hw : Measurable fun p : ℝ × (ℝ × ℝ) => ENNReal.ofReal (c⁻¹ * p.1 ^ (-(5 / 2 : ℝ))) :=
    ENNReal.measurable_ofReal.comp ((measurable_fst.pow_const _).const_mul _)
  have hRHS : ∫ x, G x ∂(Axi.ageμ c (-(5 / 2 : ℝ))) =
      ((c⁻¹ : ℝ) : ℂ) * ∫ p in Ioi (0 : ℝ) ×ˢ Axi.qCell c,
        ((p.1 ^ (-(5 / 2 : ℝ)) : ℝ) : ℂ) * G p := by
    rw [ph_ageμ_density hc, integral_withDensity_eq_integral_toReal_smul hw
      (ae_of_all _ fun _ => ENNReal.ofReal_lt_top), ← integral_const_mul]
    refine integral_congr_ae ?_
    filter_upwards [ae_restrict_mem hS] with x hx
    have h1 : 0 < x.1 := (Set.mem_prod.1 hx).1
    have hnn : 0 ≤ c⁻¹ * x.1 ^ (-(5 / 2 : ℝ)) :=
      mul_nonneg (inv_nonneg.2 hc.le) (Real.rpow_nonneg h1.le _)
    rw [ENNReal.toReal_ofReal hnn, Complex.real_smul]
    push_cast
    ring
  -- assemble
  have hP : 2 * c / R = 2 * R⁻¹ * c := by ring
  unfold UnforcedLeray.Cons.C03.Concrete.phaseInt
  dsimp only
  rw [hP, key, hRHS]
  push_cast
  ring

end UnforcedLeray.Short.IIb
