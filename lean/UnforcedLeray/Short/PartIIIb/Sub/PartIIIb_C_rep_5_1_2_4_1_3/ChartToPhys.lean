import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_5_1_2_4_1_3.Kernel
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_5_1_2_4_1_3.ChartOfHalfPlane
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_5_1_2_4_1_3.RotZHalfPlane
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_5_1_2_4_1_3.AgeMuInvShift
import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_1_1_1.L5

/-!
# `PartIII-b:C/rep/5/1/2/4/1/3/3/9`: chart output to physical output

Source `the November 2 reference manuscript` 2679-2684 (physical Jacobian
`πR² s^{-5/2} ds dη`, normalized phase `dq/c`).

Proof: the chart integrand `F p = 1_{age ∈ E} Φ(chartTau p, chartY p)` is rotation invariant and
`P`-periodic in the phase, so its chart value at `chartOf R c z τ` is `1_{age R z ∈ E} Φ τ z`
(`chartOfHalfPlane`, `rotZHalfPlane`, periodicity).  Then `ageμInvShift` turns the `s^{-3/2}`
weight with `s⁻¹` into `s^{-5/2}`, and `chartPhaseLIntegral` gives the physical integral over one
period.  The constants satisfy `(2πcR)⁻¹ · (2c/R) · πR² = 1`, so the inequality is an equality.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete.WYCore

theorem chartToPhys_measTau (R : ℝ) : Measurable (NearInst.chartTau R) := by
  unfold NearInst.chartTau
  fun_prop

theorem chartToPhys_measY (R : ℝ) : Measurable (NearInst.chartY R) := by
  unfold NearInst.chartY
  have : Measurable fun p : Chart => (![R / Real.sqrt p.1, 0, p.2.2 / Real.sqrt p.1] : Fin 3 → ℝ) := by
    refine measurable_pi_lambda _ fun i => ?_
    fin_cases i <;> simp <;> fun_prop
  exact (PiLp.continuous_toLp 2 (fun _ : Fin 3 => ℝ)).measurable.comp this

theorem chartToPhys_measAge (R : ℝ) : Measurable (fun y : Space => age R y) := by
  unfold age
  exact measurable_const.div (measurable_ϱ.pow_const 2)

theorem chartToPhys_setMeas (R : ℝ) {E : Set ℝ} (hE : MeasurableSet E) :
    MeasurableSet {y : Space | age R y ∈ E} :=
  hE.preimage (chartToPhys_measAge R)

/-- Pointwise value of the chart indicator at a chart point `chartOf R c z τ`. -/
theorem chartToPhys_pt (R c : ℝ) (hR : 0 < R) (hc : 0 < c) (Φ : ℝ → Space → ℝ≥0∞)
    (hrot : ∀ (α τ : ℝ) (y : Space), Φ τ (Axi.rotZ α y) = Φ τ y)
    (hper : ∀ y : Space, Function.Periodic (fun τ => Φ τ y) (2 * c / R))
    (E : Set ℝ) (hEpos : E ⊆ Ioi 0) (z : Space) (τ : ℝ) :
    {p : Chart | p.1 ∈ E}.indicator
        (fun p => Φ (NearInst.chartTau R p) (NearInst.chartY R p)) (NearInst.chartOf R c z τ)
      = {y : Space | age R y ∈ E}.indicator (Φ τ) z := by
  by_cases hz : age R z ∈ E
  · have hρ0 : 0 ≤ ϱ z := Real.sqrt_nonneg _
    have hρpos : 0 < ϱ z := by
      rcases hρ0.lt_or_eq with h | h
      · exact h
      · exfalso
        have hage : age R z = 0 := by
          unfold age
          rw [← h]
          simp
        have hmem := hEpos hz
        rw [hage] at hmem
        simp at hmem
    have hm1 : NearInst.chartOf R c z τ ∈ {p : Chart | p.1 ∈ E} := hz
    have hm2 : z ∈ {y : Space | age R y ∈ E} := hz
    simp only [Set.indicator_of_mem hm1, Set.indicator_of_mem hm2]
    obtain ⟨α, hα⟩ := rotZHalfPlane z
    obtain ⟨hY, k, hk⟩ := chartOfHalfPlane R c z τ hR hc hρpos
    rw [hY, hk, ← hα, hrot]
    exact (hper z).sub_int_mul_eq k
  · have hm1 : NearInst.chartOf R c z τ ∉ {p : Chart | p.1 ∈ E} := hz
    have hm2 : z ∉ {y : Space | age R y ∈ E} := hz
    simp only [Set.indicator_of_notMem hm1, Set.indicator_of_notMem hm2]

/-- Change of variables from the chart to the physical integral over one period. -/
theorem chartToPhys_lintegral_prod (P R : ℝ) (E : Set ℝ) (hE : MeasurableSet E)
    (Φ : ℝ → Space → ℝ≥0∞) (hΦ : Measurable (fun x : ℝ × Space => Φ x.1 x.2)) :
    ∫⁻ x in Ioc 0 P ×ˢ {y : Space | age R y ∈ E}, Φ x.1 x.2 =
      ∫⁻ τ in Ioc 0 P, ∫⁻ z, {y : Space | age R y ∈ E}.indicator (Φ τ) z := by
  rw [Measure.volume_eq_prod, ← Measure.prod_restrict, lintegral_prod _ hΦ.aemeasurable]
  refine lintegral_congr fun τ => ?_
  rw [lintegral_indicator (chartToPhys_setMeas R hE)]

theorem chartToPhys : ChartToPhys := by
  intro R c hR hc Φ hΦ hrot hper E hE hEpos
  have hR0 : R ≠ 0 := hR.ne'
  have hc0 : c ≠ 0 := hc.ne'
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  obtain ⟨F, hFdef⟩ : ∃ F : Chart → ℝ≥0∞,
      F = {p : Chart | p.1 ∈ E}.indicator
        (fun p => Φ (NearInst.chartTau R p) (NearInst.chartY R p)) := ⟨_, rfl⟩
  have hSm : MeasurableSet {p : Chart | p.1 ∈ E} := measurable_fst hE
  have hFm : Measurable F := by
    rw [hFdef]
    exact Measurable.indicator
      (hΦ.comp ((chartToPhys_measTau R).prodMk (chartToPhys_measY R))) hSm
  have hpt : ∀ τ z, F (NearInst.chartOf R c z τ) =
      {y : Space | age R y ∈ E}.indicator (Φ τ) z := by
    intro τ z
    rw [hFdef]
    exact chartToPhys_pt R c hR hc Φ hrot hper E hEpos z τ
  have hLHS : ∫⁻ p in {p : Chart | p.1 ∈ E}, ENNReal.ofReal (p.1⁻¹) *
        Φ (NearInst.chartTau R p) (NearInst.chartY R p) ∂(ageμ c (-3 / 2)) =
      ∫⁻ p, F p ∂(ageμ c (-5 / 2)) := by
    rw [← ageμInvShift c hc F hFm,
      ← lintegral_indicator hSm (fun p => ENNReal.ofReal (p.1⁻¹) *
        Φ (NearInst.chartTau R p) (NearInst.chartY R p))]
    refine lintegral_congr fun p => ?_
    rw [hFdef]
    by_cases hp : p.1 ∈ E
    · have hm : p ∈ {p : Chart | p.1 ∈ E} := hp
      simp only [Set.indicator_of_mem hm]
    · have hm : p ∉ {p : Chart | p.1 ∈ E} := hp
      simp only [Set.indicator_of_notMem hm, mul_zero]
  have hCPL := chartPhaseLIntegral R c hR hc F hFm
  have hR2 : ∫⁻ τ in Ioc 0 (2 * c / R), ∫⁻ z, {y : Space | age R y ∈ E}.indicator (Φ τ) z =
      ENNReal.ofReal (2 * c / R) * ENNReal.ofReal (Real.pi * R ^ 2) *
        ∫⁻ p, F p ∂(ageμ c (-5 / 2)) := by
    rw [← hCPL]
    exact lintegral_congr fun τ => lintegral_congr fun z => (hpt τ z).symm
  rw [hLHS, chartToPhys_lintegral_prod (2 * c / R) R E hE Φ hΦ, hR2]
  have hp1 : 0 ≤ 2 * c / R := by positivity
  have hp2 : 0 ≤ (2 * Real.pi * c * R)⁻¹ := by positivity
  have hfield : (2 * Real.pi * c * R)⁻¹ * (2 * c / R * (Real.pi * R ^ 2)) = 1 := by
    field_simp
  have hprod : ENNReal.ofReal ((2 * Real.pi * c * R)⁻¹) *
      (ENNReal.ofReal (2 * c / R) * ENNReal.ofReal (Real.pi * R ^ 2)) = 1 := by
    rw [← ENNReal.ofReal_mul hp1, ← ENNReal.ofReal_mul hp2, hfield, ENNReal.ofReal_one]
  refine le_of_eq ?_
  calc ∫⁻ p, F p ∂(ageμ c (-5 / 2))
      = (ENNReal.ofReal ((2 * Real.pi * c * R)⁻¹) *
          (ENNReal.ofReal (2 * c / R) * ENNReal.ofReal (Real.pi * R ^ 2))) *
            ∫⁻ p, F p ∂(ageμ c (-5 / 2)) := by
        rw [hprod, one_mul]
    _ = ENNReal.ofReal ((2 * Real.pi * c * R)⁻¹) *
          (ENNReal.ofReal (2 * c / R) * ENNReal.ofReal (Real.pi * R ^ 2) *
            ∫⁻ p, F p ∂(ageμ c (-5 / 2))) := by
        ring

end UnforcedLeray.Short.PartIIIb.Concrete.WYCore

end
