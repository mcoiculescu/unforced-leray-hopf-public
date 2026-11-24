import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_1_1_1
import UnforcedLeray.Short.PartIIIb.NearInst.Link.Pins.Proofs.StressPairAE

/-!
# `ChartPhaseLIntegral` (source 2666-2668, 3256-3268)

Change of variables from the similarity points `(τ, z)` to the chart over one period `P = 2c/R`:
`chartOf R c z τ = (age, (cellRep c (phase), trans))` (`NearInst.chartOf_eq_ring`), then the
ring-chart phase average `Axi.phaseAvg_ringChart`; on the cell `cellRep` is the identity.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411

/-- **Change of variables to the chart over one period** (source 2666-2668, 2684-2687;
`phaseAvg_ringChart`, `NearInst.chartOf_eq_ring`): for `R, c > 0`, `P = 2c/R` and measurable
`F ≥ 0` on the chart, `∫_0^P ∫ F(chartOf R c z τ) dz dτ = P · πR² · ∫ F d(s^{-5/2}dς)`. -/
theorem chartPhaseLIntegral : ChartPhaseLIntegral := by
  intro R c hR hc F hF
  have hP0 : 0 < 2 * c / R := div_pos (mul_pos two_pos hc) hR
  set P := 2 * c / R with hPdef
  let G : ℝ × (ℝ × ℝ) → ℝ≥0∞ := fun p => F (p.1, (cellRep c p.2.1, p.2.2))
  have hGm : Measurable G :=
    hF.comp (measurable_fst.prodMk (((measurable_cellRep c).comp
      (measurable_fst.comp measurable_snd)).prodMk (measurable_snd.comp measurable_snd)))
  have hper : ∀ s q η, G (s, (q + c, η)) = G (s, (q, η)) := by
    intro s q η
    simp only [G, cellRep_add hc.ne']
  have hav := phaseAvg_ringChart hR hc (rfl : P = 2 * c / R) G hGm hper
  have hLHS : ∀ τ : ℝ, ∫⁻ z, F (NearInst.chartOf R c z τ)
      = ∫⁻ z, G (age R z, (phase R τ z, trans R z)) := by
    intro τ
    refine lintegral_congr fun z => ?_
    rw [NearInst.chartOf_eq_ring R c hR hc z τ]
  have hcell : ∫⁻ p in Ioi (0 : ℝ) ×ˢ qCell c,
      ENNReal.ofReal (c⁻¹ * p.1 ^ (-(5 / 2 : ℝ))) * G p
      = ∫⁻ p in Ioi (0 : ℝ) ×ˢ qCell c,
      ENNReal.ofReal (c⁻¹ * p.1 ^ (-(5 / 2 : ℝ))) * F p := by
    refine setLIntegral_congr_fun (measurableSet_Ioi.prod (measurableSet_Ico.prod MeasurableSet.univ))
      fun p hp => ?_
    have hmem : p.2.1 ∈ Ico (-c / 2) (c / 2) := hp.2.1
    simp only [G, cellRep_of_mem hc hmem]
  have e : (-5 / 2 : ℝ) = -(5 / 2) := by norm_num
  have hFint : ∫⁻ p in Ioi (0 : ℝ) ×ˢ qCell c,
      ENNReal.ofReal (c⁻¹ * p.1 ^ (-(5 / 2 : ℝ))) * F p = ∫⁻ p, F p ∂(ageμ c (-5 / 2)) := by
    rw [e, lintegral_ageμ hc _ hF]
  have hPne : ENNReal.ofReal P ≠ 0 := (ENNReal.ofReal_pos.2 hP0).ne'
  have hPtop : ENNReal.ofReal P ≠ ⊤ := ENNReal.ofReal_ne_top
  rw [hcell, hFint] at hav
  calc ∫⁻ τ in Ioc 0 P, ∫⁻ z, F (NearInst.chartOf R c z τ)
      = ∫⁻ τ in Ioc 0 P, ∫⁻ z, G (age R z, (phase R τ z, trans R z)) :=
        lintegral_congr fun τ => hLHS τ
    _ = ENNReal.ofReal P * ((ENNReal.ofReal P)⁻¹ *
          ∫⁻ τ in Ioc 0 P, ∫⁻ z, G (age R z, (phase R τ z, trans R z))) := by
        rw [← mul_assoc, ENNReal.mul_inv_cancel hPne hPtop, one_mul]
    _ = ENNReal.ofReal P * (ENNReal.ofReal (Real.pi * R ^ 2) * ∫⁻ p, F p ∂(ageμ c (-5 / 2))) := by
        rw [hav]
    _ = ENNReal.ofReal P * ENNReal.ofReal (Real.pi * R ^ 2) * ∫⁻ p, F p ∂(ageμ c (-5 / 2)) := by
        rw [mul_assoc]

end UnforcedLeray.Short.PartIIIb.Concrete
