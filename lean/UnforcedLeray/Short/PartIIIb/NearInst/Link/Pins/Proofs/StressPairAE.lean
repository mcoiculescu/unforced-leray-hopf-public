import UnforcedLeray.Short.PartIIIb.NearInst.Link.Pins.Basic

/-!
# `StressPairAE` (source 1640-1641, 2666-2668, 2683)

The ring chart `(τ, y) ↦ (s, q, η)` carries null sets of `ageμ c (-1/2)` to null sets of
`dτ dy` on `(0, P] × ℝ³` (via `phaseAvg_ringChart`), so the stress pairing of `𝒩_T T` depends only
on the a.e. class of the chart tensor `T`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.NearInst

open MeasureTheory UnforcedLeray.Axi UnforcedLeray.Short.PartIIIb.Concrete
  UnforcedLeray.Cons.C03.Concrete UnforcedLeray.PhaseSpace UnforcedLeray.B0411
open UnforcedLeray.B0220 (HSpace measureH Profile)
open UnforcedLeray.B0223 (MeridC)
open Set
open scoped ENNReal

/-- The chart point of the similarity variables is the ring chart with the cell representative. -/
theorem chartOf_eq_ring (R c : ℝ) (hR : 0 < R) (hc : 0 < c) (y : Space) (τ : ℝ) :
    chartOf R c y τ = (age R y, (cellRep c (phase R τ y), trans R y)) := by
  have hrad : hRad y = ϱ y := rfl
  have hlog : Real.log (age R y) = -2 * Real.log (hRad y / R) := by
    unfold age
    rw [hrad]
    have : R ^ 2 / ϱ y ^ 2 = (R / ϱ y) ^ 2 := by rw [div_pow]
    rw [this, Real.log_pow, ← inv_div, Real.log_inv]
    push_cast; ring
  unfold chartOf
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · simp only [age, hrad]
  · simp only [cellRep, phase, hlog]
    have : (R * Real.log (hRad y / R) + R * τ / 2) / c + 1 / 2
        = (R * τ / 2 - R / 2 * (-2 * Real.log (hRad y / R)) + c / 2) / c := by
      field_simp; ring
    rw [this]
    ring_nf
  · simp only [Axi.trans, hrad]

theorem stressPairAE_null (R c P : ℝ) (hR : 0 < R) (hc : 0 < c) (hP : P = 2 * c / R)
    (N : Set Chart) (hN : MeasurableSet N) (h0 : ageμ c (-5 / 2) N = 0) :
    ∀ᵐ x ∂((volume.restrict (Ioc 0 P)).prod (volume : Measure Space)),
      chartOf R c x.2 x.1 ∉ N := by
  set G : Chart → ℝ≥0∞ := fun p => N.indicator (fun _ => (1 : ℝ≥0∞))
    (p.1, (cellRep c p.2.1, p.2.2)) with hG
  have hGm : Measurable G :=
    (measurable_const.indicator hN).comp (measurable_fst.prodMk
      (((measurable_cellRep c).comp (measurable_fst.comp measurable_snd)).prodMk
        (measurable_snd.comp measurable_snd)))
  have hper : ∀ s q η, G (s, (q + c, η)) = G (s, (q, η)) := by
    intro s q η
    simp only [hG, cellRep_add hc.ne']
  have hP0 : 0 < P := by rw [hP]; exact div_pos (mul_pos two_pos hc) hR
  have hav := phaseAvg_ringChart hR hc hP G hGm hper
  have hrhs : ∫⁻ p in Ioi (0 : ℝ) ×ˢ qCell c,
      ENNReal.ofReal (c⁻¹ * p.1 ^ (-(5 / 2 : ℝ))) * G p = 0 := by
    have h1 : ∫⁻ p in Ioi (0 : ℝ) ×ˢ qCell c,
        ENNReal.ofReal (c⁻¹ * p.1 ^ (-(5 / 2 : ℝ))) * G p =
        ∫⁻ p in Ioi (0 : ℝ) ×ˢ qCell c, ENNReal.ofReal (c⁻¹ * p.1 ^ (-(5 / 2 : ℝ))) *
          N.indicator (fun _ => (1 : ℝ≥0∞)) p := by
      refine setLIntegral_congr_fun (measurableSet_Ioi.prod ?_) fun p hp => ?_
      · exact measurableSet_Ico.prod MeasurableSet.univ
      · have hmem : p.2.1 ∈ Ico (-c / 2) (c / 2) := hp.2.1
        simp only [hG, cellRep_of_mem hc hmem]
    rw [h1, ← lintegral_ageμ hc (-(5 / 2 : ℝ)) (measurable_const.indicator hN)]
    have e : ∫⁻ p, N.indicator (fun _ => (1 : ℝ≥0∞)) p ∂ageμ c (-(5 / 2 : ℝ)) =
        ageμ c (-(5 / 2 : ℝ)) N := lintegral_indicator_one hN
    rw [e]
    have : (-(5 / 2 : ℝ)) = -5 / 2 := by norm_num
    rw [this]; exact h0
  rw [hrhs, mul_zero] at hav
  have hFm : Measurable fun x : ℝ × Space => G (age R x.2, (phase R x.1 x.2, trans R x.2)) :=
    hGm.comp (((measurable_age R).comp measurable_snd).prodMk
      ((measurable_phase R).prodMk ((measurable_trans R).comp measurable_snd)))
  have hint : ∫⁻ x, G (age R x.2, (phase R x.1 x.2, trans R x.2))
      ∂((volume.restrict (Ioc 0 P)).prod (volume : Measure Space)) = 0 := by
    rw [lintegral_prod _ hFm.aemeasurable]
    have h2 : (ENNReal.ofReal P)⁻¹ ≠ 0 := ENNReal.inv_ne_zero.2 ENNReal.ofReal_ne_top
    exact (mul_eq_zero.1 hav).resolve_left h2
  have hz := (lintegral_eq_zero_iff hFm).1 hint
  filter_upwards [hz] with x hx hxN
  have hx' : N.indicator (fun _ => (1 : ℝ≥0∞)) (chartOf R c x.2 x.1) = 0 := by
    rw [chartOf_eq_ring R c hR hc]; exact hx
  rw [Set.indicator_of_mem hxN] at hx'
  exact one_ne_zero hx'

/-- **The stress pairing sees only the a.e. class of the chart tensor** (source 1640-1641,
2666-2668, 2683). -/
theorem stressPairAE : StressPairAE := by
  intro c ε hc hε g g' hg Φ
  have hR : 0 < ε⁻¹ := inv_pos.2 hε
  have hP : 2 * ε * c = 2 * c / ε⁻¹ := by field_simp
  obtain ⟨N, hsub, hNm, hN0⟩ := exists_measurable_superset_of_null
    (s := {p | g p ≠ g' p}) (μ := ageμ c (-1 / 2)) (ae_iff.1 hg)
  have hN5 : ageμ c (-5 / 2) N = 0 := ageμ_absCont c (-5 / 2) (-1 / 2) hN0
  have hnull := stressPairAE_null ε⁻¹ c (2 * ε * c) hR hc hP N hNm hN5
  have hae := Measure.ae_ae_of_ae_prod hnull
  unfold stressPair phaseInt
  congr 1
  refine integral_congr_ae ?_
  filter_upwards [hae] with t ht
  refine integral_congr_ae ?_
  filter_upwards [ht] with y hy
  have hgg : g (chartOf ε⁻¹ c y t) = g' (chartOf ε⁻¹ c y t) := by
    by_contra h
    exact hy (hsub h)
  have : strPhys ε⁻¹ c g (t, y) = strPhys ε⁻¹ c g' (t, y) := by
    simp only [strPhys, cartLift, hgg]
  simp only [this]

end UnforcedLeray.Short.PartIIIb.NearInst
