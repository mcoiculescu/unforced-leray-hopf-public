import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T09_4_2
import UnforcedLeray.Short.PartIIb.Tasks.GradLapNvC.DivVanish.WindowIntegral.RingBridgeNN
import UnforcedLeray.Lib.Axisymmetric.RingMeasure
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Function.L1Space.Integrable

/-!
# Part II-b, task `PartII-b:T09/4/2/5` (`RingBridgeReal`)

Source of record: `the November 2 reference manuscript`, lines 1639-1668, 1912-1916.

Signed real case of the ring-chart bridge, from the nonnegative case `ringBridgeNN`
(`RingBridgeNN.lean`) by the splitting `G = G⁺ - G⁻`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal

namespace UnforcedLeray.Short.IIb

/-- Finiteness of the phase-integrated lintegral of a nonnegative periodic `G` with finite weighted
`L¹`-norm (the lintegral form of `Axi.phaseAvg_ringChart`). -/
private theorem ringChart_lintegral_ne_top (c ε : ℝ) (G : ℝ × (ℝ × ℝ) → ℝ) (hc : 0 < c)
    (hε : 0 < ε) (hG : Measurable G)
    (hper : ∀ s ξ η : ℝ, G (s, (ξ + c, η)) = G (s, (ξ, η)))
    (hfin : ∫⁻ p in Ioi (0 : ℝ) ×ˢ Axi.qCell c,
        ENNReal.ofReal (c⁻¹ * p.1 ^ (-(5 / 2 : ℝ))) * ENNReal.ofReal (G p) < ⊤) :
    ∫⁻ τ in Ioc (0 : ℝ) (2 * ε * c), ∫⁻ y : Space, ENNReal.ofReal (G (Axi.chart ε⁻¹ τ y)) ≠ ⊤ := by
  have hR : (0 : ℝ) < ε⁻¹ := inv_pos.2 hε
  have hP : 2 * ε * c = 2 * c / ε⁻¹ := by
    rw [div_inv_eq_mul]; ring
  have hGm' : Measurable fun x : ℝ × (ℝ × ℝ) => ENNReal.ofReal (G x) :=
    ENNReal.measurable_ofReal.comp hG
  have hper' : ∀ s q η : ℝ, ENNReal.ofReal (G (s, (q + c, η)))
      = ENNReal.ofReal (G (s, (q, η))) := by
    intro s q η
    rw [hper s q η]
  have key : (ENNReal.ofReal (2 * ε * c))⁻¹ *
        ∫⁻ τ in Ioc 0 (2 * ε * c), ∫⁻ y, ENNReal.ofReal (G (Axi.chart ε⁻¹ τ y)) =
      ENNReal.ofReal (Real.pi * (ε⁻¹) ^ 2) *
        ∫⁻ p in Ioi (0 : ℝ) ×ˢ Axi.qCell c,
          ENNReal.ofReal (c⁻¹ * p.1 ^ (-(5 / 2 : ℝ))) * ENNReal.ofReal (G p) :=
    Axi.phaseAvg_ringChart hR hc hP _ hGm' hper'
  intro hZ
  have hlt : (ENNReal.ofReal (2 * ε * c))⁻¹ *
      ∫⁻ τ in Ioc (0 : ℝ) (2 * ε * c), ∫⁻ y : Space, ENNReal.ofReal (G (Axi.chart ε⁻¹ τ y)) < ⊤ := by
    rw [key]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hfin
  rw [hZ, ENNReal.mul_top (ENNReal.inv_ne_zero.2 ENNReal.ofReal_ne_top)] at hlt
  exact lt_irrefl _ hlt

/-- Measurability of `x ↦ H (chart R x.1 x.2)` on `ℝ × Space`. -/
private theorem measurable_chartComp (R : ℝ) {H : ℝ × (ℝ × ℝ) → ℝ} (hH : Measurable H) :
    Measurable fun x : ℝ × Space => H (Axi.chart R x.1 x.2) := by
  refine hH.comp ?_
  exact ((Axi.measurable_age R).comp measurable_snd).prodMk
    ((Axi.measurable_phase R).prodMk ((Axi.measurable_trans R).comp measurable_snd))

/-- Measurability of the phase section `y ↦ H (chart R τ y)`. -/
private theorem sec_measurable {H : ℝ × (ℝ × ℝ) → ℝ} (R : ℝ) (hH : Measurable H) (τ : ℝ) :
    Measurable fun y : Space => H (Axi.chart R τ y) := by
  have h1 : Measurable fun y : Space => ((τ, y) : ℝ × Space) :=
    measurable_const.prodMk measurable_id
  have h2 := (measurable_chartComp R hH).comp h1
  exact h2

/-- Integrability of a nonnegative phase section from finiteness of its lintegral. -/
private theorem sec_integrable {H : ℝ × (ℝ × ℝ) → ℝ} (R : ℝ) (hH : Measurable H)
    (hH0 : ∀ x, 0 ≤ H x) (τ : ℝ)
    (h : ∫⁻ y : Space, ENNReal.ofReal (H (Axi.chart R τ y)) < ⊤) :
    Integrable (fun y : Space => H (Axi.chart R τ y)) :=
  (integrable_toReal_of_lintegral_ne_top
      (ENNReal.measurable_ofReal.comp (sec_measurable R hH τ)).aemeasurable h.ne).congr
    (ae_of_all _ fun _ => ENNReal.toReal_ofReal (hH0 _))

/-- Integrability in the weighted cell measure of `p ↦ p.1^(-5/2) * H p`, from the finiteness of
the weighted lintegral of `H⁺`-type data. -/
private theorem weight_integrable (c : ℝ) (hc : 0 < c) {H : ℝ × (ℝ × ℝ) → ℝ} (hH : Measurable H)
    (hfin : ∫⁻ p in Ioi (0 : ℝ) ×ˢ Axi.qCell c,
        ENNReal.ofReal (c⁻¹ * p.1 ^ (-(5 / 2 : ℝ))) * ENNReal.ofReal (H p) < ⊤)
    (hH0 : ∀ x, 0 ≤ H x) :
    Integrable (fun p : ℝ × (ℝ × ℝ) => p.1 ^ (-(5 / 2 : ℝ)) * H p)
      (volume.restrict (Ioi (0 : ℝ) ×ˢ Axi.qCell c)) := by
  have hS : MeasurableSet (Ioi (0 : ℝ) ×ˢ Axi.qCell c) :=
    measurableSet_Ioi.prod (measurableSet_Ico.prod MeasurableSet.univ)
  have hpt : ∀ p ∈ Ioi (0 : ℝ) ×ˢ Axi.qCell c,
      ‖p.1 ^ (-(5 / 2 : ℝ)) * H p‖ₑ = ENNReal.ofReal c *
        (ENNReal.ofReal (c⁻¹ * p.1 ^ (-(5 / 2 : ℝ))) * ENNReal.ofReal (H p)) := by
    intro p hp
    have hpos : (0 : ℝ) < p.1 := hp.1
    have h1 : 0 ≤ p.1 ^ (-(5 / 2 : ℝ)) := Real.rpow_nonneg hpos.le _
    have h2 : 0 ≤ c⁻¹ * p.1 ^ (-(5 / 2 : ℝ)) := mul_nonneg (inv_nonneg.2 hc.le) h1
    rw [Real.enorm_eq_ofReal (mul_nonneg h1 (hH0 p)), ← ENNReal.ofReal_mul h2,
      ← ENNReal.ofReal_mul hc.le]
    congr 1
    field_simp
  have hlint : ∫⁻ p in Ioi (0 : ℝ) ×ˢ Axi.qCell c, ‖p.1 ^ (-(5 / 2 : ℝ)) * H p‖ₑ < ⊤ := by
    rw [setLIntegral_congr_fun hS hpt, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hfin
  exact ⟨((measurable_fst.pow_const _).mul hH).aestronglyMeasurable, hlint⟩

theorem ringBridgeReal : UnforcedLeray.Short.IIb.RingBridgeReal := by
  intro c ε G hc hε hG hper hfin
  -- positive and negative parts
  obtain ⟨Gp, hGp⟩ : ∃ f : ℝ × (ℝ × ℝ) → ℝ, f = fun x => max (G x) 0 := ⟨_, rfl⟩
  obtain ⟨Gm, hGm⟩ : ∃ f : ℝ × (ℝ × ℝ) → ℝ, f = fun x => max (-G x) 0 := ⟨_, rfl⟩
  have hsplit : ∀ x, G x = Gp x - Gm x := by
    intro x
    simp only [hGp, hGm]
    rcases le_total 0 (G x) with h | h
    · rw [max_eq_left h, max_eq_right (by linarith : -G x ≤ 0)]
      ring
    · rw [max_eq_right h, max_eq_left (by linarith : 0 ≤ -G x)]
      ring
  have hGp_meas : Measurable Gp := by
    rw [hGp]; exact hG.max measurable_const
  have hGm_meas : Measurable Gm := by
    rw [hGm]; exact hG.neg.max measurable_const
  have hGp0 : ∀ x, 0 ≤ Gp x := fun x => by rw [hGp]; exact le_max_right _ _
  have hGm0 : ∀ x, 0 ≤ Gm x := fun x => by rw [hGm]; exact le_max_right _ _
  have hperp : ∀ s ξ η : ℝ, Gp (s, (ξ + c, η)) = Gp (s, (ξ, η)) := by
    intro s ξ η
    rw [hGp]
    simp only [hper s ξ η]
  have hperm : ∀ s ξ η : ℝ, Gm (s, (ξ + c, η)) = Gm (s, (ξ, η)) := by
    intro s ξ η
    rw [hGm]
    simp only [hper s ξ η]
  -- domination by the finite weighted norm
  have hle_p : ∀ x, ENNReal.ofReal (Gp x) ≤ ‖G x‖ₑ := by
    intro x
    rw [Real.enorm_eq_ofReal_abs, hGp]
    exact ENNReal.ofReal_le_ofReal (max_le (le_abs_self _) (abs_nonneg _))
  have hle_m : ∀ x, ENNReal.ofReal (Gm x) ≤ ‖G x‖ₑ := by
    intro x
    rw [Real.enorm_eq_ofReal_abs, hGm]
    exact ENNReal.ofReal_le_ofReal (max_le (neg_le_abs _) (abs_nonneg _))
  have hdomp : ∫⁻ p in Ioi (0 : ℝ) ×ˢ Axi.qCell c,
      ENNReal.ofReal (c⁻¹ * p.1 ^ (-(5 / 2 : ℝ))) * ENNReal.ofReal (Gp p) < ⊤ :=
    (lintegral_mono fun p => mul_le_mul_of_nonneg_left (hle_p p) (by positivity)).trans_lt hfin
  have hdomm : ∫⁻ p in Ioi (0 : ℝ) ×ˢ Axi.qCell c,
      ENNReal.ofReal (c⁻¹ * p.1 ^ (-(5 / 2 : ℝ))) * ENNReal.ofReal (Gm p) < ⊤ :=
    (lintegral_mono fun p => mul_le_mul_of_nonneg_left (hle_m p) (by positivity)).trans_lt hfin
  -- nonnegative bridge identities
  have hNNp := ringBridgeNN c ε Gp hc hε hGp_meas hGp0 hperp hdomp
  have hNNm := ringBridgeNN c ε Gm hc hε hGm_meas hGm0 hperm hdomm
  have hfinp := ringChart_lintegral_ne_top c ε Gp hc hε hGp_meas hperp hdomp
  have hfinm := ringChart_lintegral_ne_top c ε Gm hc hε hGm_meas hperm hdomm
  -- measurability of the phase integrals
  have hGtp := measurable_chartComp ε⁻¹ hGp_meas
  have hGtm := measurable_chartComp ε⁻¹ hGm_meas
  have hZmp : Measurable fun τ : ℝ => ∫⁻ y : Space, ENNReal.ofReal (Gp (Axi.chart ε⁻¹ τ y)) :=
    (ENNReal.measurable_ofReal.comp hGtp).lintegral_prod_right'
  have hZmm : Measurable fun τ : ℝ => ∫⁻ y : Space, ENNReal.ofReal (Gm (Axi.chart ε⁻¹ τ y)) :=
    (ENNReal.measurable_ofReal.comp hGtm).lintegral_prod_right'
  have hpAE : ∀ᵐ τ ∂(volume.restrict (Ioc (0 : ℝ) (2 * ε * c))),
      ∫⁻ y : Space, ENNReal.ofReal (Gp (Axi.chart ε⁻¹ τ y)) < ⊤ :=
    ae_lt_top hZmp hfinp
  have hmAE : ∀ᵐ τ ∂(volume.restrict (Ioc (0 : ℝ) (2 * ε * c))),
      ∫⁻ y : Space, ENNReal.ofReal (Gm (Axi.chart ε⁻¹ τ y)) < ⊤ :=
    ae_lt_top hZmm hfinm
  -- a.e. integrability in the phase variable
  have hIntp : ∀ᵐ τ ∂(volume.restrict (Ioc (0 : ℝ) (2 * ε * c))),
      Integrable (fun y : Space => Gp (Axi.chart ε⁻¹ τ y)) := by
    filter_upwards [hpAE] with τ hτ
    exact sec_integrable ε⁻¹ hGp_meas hGp0 τ hτ
  have hIntm : ∀ᵐ τ ∂(volume.restrict (Ioc (0 : ℝ) (2 * ε * c))),
      Integrable (fun y : Space => Gm (Axi.chart ε⁻¹ τ y)) := by
    filter_upwards [hmAE] with τ hτ
    exact sec_integrable ε⁻¹ hGm_meas hGm0 τ hτ
  -- inner integral splits a.e.
  have hA : ∀ᵐ τ ∂(volume.restrict (Ioc (0 : ℝ) (2 * ε * c))),
      (∫ y : Space, G (Axi.chart ε⁻¹ τ y)) =
        (∫ y : Space, Gp (Axi.chart ε⁻¹ τ y)) - ∫ y : Space, Gm (Axi.chart ε⁻¹ τ y) := by
    filter_upwards [hIntp, hIntm] with τ h1 h2
    rw [← integral_sub h1 h2]
    congr 1
    funext y
    exact hsplit _
  -- outer integrability
  have hZpEq : ∀ τ : ℝ, (∫ y : Space, Gp (Axi.chart ε⁻¹ τ y)) =
      (∫⁻ y : Space, ENNReal.ofReal (Gp (Axi.chart ε⁻¹ τ y))).toReal := fun τ =>
    integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun y => hGp0 _)
      (sec_measurable ε⁻¹ hGp_meas τ).aestronglyMeasurable
  have hZmEq : ∀ τ : ℝ, (∫ y : Space, Gm (Axi.chart ε⁻¹ τ y)) =
      (∫⁻ y : Space, ENNReal.ofReal (Gm (Axi.chart ε⁻¹ τ y))).toReal := fun τ =>
    integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun y => hGm0 _)
      (sec_measurable ε⁻¹ hGm_meas τ).aestronglyMeasurable
  have hZpInt : Integrable (fun τ : ℝ => ∫ y : Space, Gp (Axi.chart ε⁻¹ τ y))
      (volume.restrict (Ioc (0 : ℝ) (2 * ε * c))) :=
    (integrable_toReal_of_lintegral_ne_top hZmp.aemeasurable hfinp).congr
      (ae_of_all _ fun τ => (hZpEq τ).symm)
  have hZmInt : Integrable (fun τ : ℝ => ∫ y : Space, Gm (Axi.chart ε⁻¹ τ y))
      (volume.restrict (Ioc (0 : ℝ) (2 * ε * c))) :=
    (integrable_toReal_of_lintegral_ne_top hZmm.aemeasurable hfinm).congr
      (ae_of_all _ fun τ => (hZmEq τ).symm)
  have hτ : (∫ τ in Ioc (0 : ℝ) (2 * ε * c), ∫ y : Space, G (Axi.chart ε⁻¹ τ y)) =
      ∫ τ in Ioc (0 : ℝ) (2 * ε * c),
        ((∫ y : Space, Gp (Axi.chart ε⁻¹ τ y)) - ∫ y : Space, Gm (Axi.chart ε⁻¹ τ y)) :=
    integral_congr_ae hA
  -- the cell integral splits
  have hpint : (∫ p in Ioi (0 : ℝ) ×ˢ Axi.qCell c, p.1 ^ (-(5 / 2 : ℝ)) * G p) =
      (∫ p in Ioi (0 : ℝ) ×ˢ Axi.qCell c, p.1 ^ (-(5 / 2 : ℝ)) * Gp p) -
        ∫ p in Ioi (0 : ℝ) ×ˢ Axi.qCell c, p.1 ^ (-(5 / 2 : ℝ)) * Gm p := by
    rw [← integral_sub (weight_integrable c hc hGp_meas hdomp hGp0)
      (weight_integrable c hc hGm_meas hdomm hGm0)]
    refine integral_congr_ae (ae_of_all _ fun p => ?_)
    simp only [hsplit p]
    ring
  rw [hτ, integral_sub hZpInt hZmInt, mul_sub, hNNp, hNNm, hpint, mul_sub]

end UnforcedLeray.Short.IIb
