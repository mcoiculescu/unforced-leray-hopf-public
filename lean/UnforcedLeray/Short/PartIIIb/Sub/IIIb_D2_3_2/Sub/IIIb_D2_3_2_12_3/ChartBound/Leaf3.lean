import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D2_3_2_12_3_1
import UnforcedLeray.Short.PartIIIb.NearInst.Link.Pins.Proofs.StressPairAE

/-!
# `PartIII-b:IIIb-D2/3/2/12/3/1/3` (leaf 3: `RingChartRegionLintegral`)

Source of record: `the November 2 reference manuscript`,
lines 2683, 3256-3268.  The chart point `chartOf R c y τ` equals the ring chart point
`(age R y, (cellRep c (phase R τ y), trans R y))` (`NearInst.chartOf_eq_ring`); `G` is `c`-periodic in
the second coordinate, so `G (chartOf ..) = G (age, (phase, trans))` pointwise.  Then the phase cell
integral is the iterated integral of `Axi.phaseAvg_ringChart`, which is applied and multiplied by
`ofReal P`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411
open UnforcedLeray.Cons.C03.Concrete (pairF phaseInt IsSolTest phaseCell)

/-- **Leaf 3** (source 2683, 3256-3268): change of variables `Axi.phaseAvg_ringChart` for the chart
integral over the phase cell. -/
theorem ringChartRegionLintegral_proved : UnforcedLeray.Short.PartIIIb.Concrete.RingChartRegionLintegral := by
  intro R c P hR hc hP G hG hper
  have hP0 : 0 < P := by
    rw [hP]
    exact div_pos (mul_pos two_pos hc) hR
  -- periodicity of `G` in the cell representative
  have hcr : ∀ s q η : ℝ, G (s, (UnforcedLeray.Axi.cellRep c q, η)) = G (s, (q, η)) := by
    intro s q η
    have hp : Function.Periodic (fun r : ℝ => G (s, (r, η))) c := fun r => hper s r η
    unfold UnforcedLeray.Axi.cellRep
    rw [mul_comm c]
    exact hp.sub_int_mul_eq _
  -- pointwise identification of the chart composite with the ring chart
  have hpt : ∀ x : ℝ × Space, G (NearInst.chartOf R c x.2 x.1)
      = G (UnforcedLeray.Axi.age R x.2,
          (UnforcedLeray.Axi.phase R x.1 x.2, UnforcedLeray.Axi.trans R x.2)) := by
    intro x
    rw [UnforcedLeray.Short.PartIIIb.NearInst.chartOf_eq_ring R c hR hc x.2 x.1, hcr]
  have hFm : Measurable fun x : ℝ × Space =>
      G (UnforcedLeray.Axi.age R x.2, (UnforcedLeray.Axi.phase R x.1 x.2, UnforcedLeray.Axi.trans R x.2)) :=
    hG.comp (((UnforcedLeray.Axi.measurable_age R).comp measurable_snd).prodMk
      ((UnforcedLeray.Axi.measurable_phase R).prodMk
        ((UnforcedLeray.Axi.measurable_trans R).comp measurable_snd)))
  have hm : (volume : Measure (ℝ × Space)).restrict (Ioc 0 P ×ˢ univ)
      = (volume.restrict (Ioc 0 P)).prod volume := by
    rw [Measure.volume_eq_prod, ← Measure.prod_restrict, Measure.restrict_univ]
  have hav := UnforcedLeray.Axi.phaseAvg_ringChart hR hc hP G hG hper
  have hL : ∫⁻ x in phaseCell P, G (NearInst.chartOf R c x.2 x.1)
      = ∫⁻ τ in Ioc 0 P, ∫⁻ y, G (UnforcedLeray.Axi.age R y,
          (UnforcedLeray.Axi.phase R τ y, UnforcedLeray.Axi.trans R y)) := by
    simp only [hpt]
    rw [show phaseCell P = Ioc 0 P ×ˢ univ from rfl, hm, lintegral_prod _ hFm.aemeasurable]
  rw [hL]
  have hne0 : ENNReal.ofReal P ≠ 0 := (ENNReal.ofReal_pos.2 hP0).ne'
  have hnetop : ENNReal.ofReal P ≠ ⊤ := ENNReal.ofReal_ne_top
  rw [mul_assoc (ENNReal.ofReal P), ← hav, ← mul_assoc (ENNReal.ofReal P) (ENNReal.ofReal P)⁻¹,
    ENNReal.mul_inv_cancel hne0 hnetop, one_mul]

end UnforcedLeray.Short.PartIIIb.Concrete
