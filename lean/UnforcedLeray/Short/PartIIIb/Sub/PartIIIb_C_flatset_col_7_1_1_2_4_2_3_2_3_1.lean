import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_4_2_3_2_dec
import UnforcedLeray.Units.B0224.FiberHeat

/-!
# `pepsC0SliceMemLp` (task `PartIII-b:C/flatset/col/7/1/1/2/4/2/3/2/3/1`)

Source `the November 2 reference manuscript` 1650-1656, 1676.
Almost every slice of an `L²(measureH c)` field is `L²` on the strip `(0,c] × ℝ`.
Strategy: a measurable version `G` of the field; Tonelli through
`B0224.lintegral_measureH_eq` and `B0224.cellMeasure_eq_prod'`; finiteness of the outer
integral forces the inner strip integral to be finite for a.e. `s > 0`; a.e. equality of
the field and `G` passes to a.e. slices by `Measure.ae_ae_of_ae_prod`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

theorem pepsC0SliceMemLp : PepsC0SliceMemLp := by
  intro c hc F hF
  obtain ⟨G, hGsm, hGae⟩ := hF.aestronglyMeasurable
  have hGm : Measurable G := hGsm.measurable
  -- a.e. identification with the measurable version, stated against the cell measure
  have hGae' : ∀ᵐ p ∂(UnforcedLeray.B0220.cellMeasure c).withDensity UnforcedLeray.B0220.weightH,
      toMC (F p) = G p := hGae
  -- the cell measure lives on `s > 0`
  have hpos : ∀ᵐ z ∂UnforcedLeray.B0220.cellMeasure c,
      z ∈ Ioi (0 : ℝ) ×ˢ UnforcedLeray.B0224.strip c := by
    rw [UnforcedLeray.B0224.cellMeasure_eq_prod' c, Measure.prod_restrict]
    exact ae_restrict_mem (measurableSet_Ioi.prod (UnforcedLeray.B0224.measurableSet_strip c))
  have hcell : ∀ᵐ z ∂UnforcedLeray.B0220.cellMeasure c, toMC (F z) = G z := by
    have h1 := (ae_withDensity_iff UnforcedLeray.B0220.measurable_weightH).1 hGae'
    filter_upwards [h1, hpos] with z hz1 hz2
    apply hz1
    have hz : (0 : ℝ) < z.1 := hz2.1
    show ENNReal.ofReal (z.1 ^ (-(3 / 2 : ℝ))) ≠ 0
    exact (ENNReal.ofReal_pos.2 (Real.rpow_pos_of_pos hz _)).ne'
  have hprod : ∀ᵐ z ∂((volume.restrict (Ioi (0 : ℝ))).prod
      (volume.restrict (UnforcedLeray.B0224.strip c))), toMC (F z) = G z := by
    rw [← UnforcedLeray.B0224.cellMeasure_eq_prod' c]
    exact hcell
  have hslice := Measure.ae_ae_of_ae_prod hprod
  -- measurability of the nonnegative integrand
  have hQ : Measurable (fun p : UnforcedLeray.B0220.Profile => ENNReal.ofReal (‖G p‖ ^ 2)) :=
    ENNReal.measurable_ofReal.comp ((hGm.norm).pow_const 2)
  -- the total mass is finite
  have hfin : ∫⁻ p, ENNReal.ofReal (‖G p‖ ^ 2) ∂UnforcedLeray.B0220.measureH c < ∞ := by
    have hL : Integrable (fun p => ‖toMC (F p)‖ ^ 2) (UnforcedLeray.B0220.measureH c) :=
      (memLp_two_iff_integrable_sq_norm hF.aestronglyMeasurable).1 hF
    have hnn0 : 0 ≤ᵐ[UnforcedLeray.B0220.measureH c] fun p => ‖toMC (F p)‖ ^ 2 :=
      Eventually.of_forall fun p => by positivity
    have h1 := (hasFiniteIntegral_iff_ofReal hnn0).1 hL.2
    have heq : (fun p => ENNReal.ofReal (‖G p‖ ^ 2)) =ᵐ[UnforcedLeray.B0220.measureH c]
        (fun p => ENNReal.ofReal (‖toMC (F p)‖ ^ 2)) :=
      hGae.mono fun p hp => by simp only [hp]
    rw [lintegral_congr_ae heq]
    exact h1
  have hw : Measurable (fun p : UnforcedLeray.B0220.Profile => ENNReal.ofReal (p.1 ^ (-(3 / 2 : ℝ)))) :=
    UnforcedLeray.B0220.measurable_weightH
  -- Tonelli: the outer integral over `s > 0`
  have hT : ∫⁻ p, ENNReal.ofReal (‖G p‖ ^ 2) ∂UnforcedLeray.B0220.measureH c
      = ∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal (s ^ (-(3 / 2 : ℝ)))
          * ∫⁻ x in UnforcedLeray.B0224.strip c, ENNReal.ofReal (‖G (s, x)‖ ^ 2) := by
    have hprodm : Measurable (fun p : UnforcedLeray.B0220.Profile =>
        ENNReal.ofReal (p.1 ^ (-(3 / 2 : ℝ))) * ENNReal.ofReal (‖G p‖ ^ 2)) := hw.mul hQ
    rw [UnforcedLeray.B0224.lintegral_measureH_eq (c := c) _ hQ,
      UnforcedLeray.B0224.cellMeasure_eq_prod' c,
      lintegral_prod _ hprodm.aemeasurable]
    refine lintegral_congr fun s => ?_
    dsimp only
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  have hI : Measurable fun s : ℝ =>
      ∫⁻ x in UnforcedLeray.B0224.strip c, ENNReal.ofReal (‖G (s, x)‖ ^ 2) :=
    hQ.lintegral_prod_right'
  have hw1 : Measurable fun s : ℝ => ENNReal.ofReal (s ^ (-(3 / 2 : ℝ))) :=
    ENNReal.measurable_ofReal.comp (measurable_id.pow_const _)
  have hfinI : ∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal (s ^ (-(3 / 2 : ℝ)))
      * ∫⁻ x in UnforcedLeray.B0224.strip c, ENNReal.ofReal (‖G (s, x)‖ ^ 2) ≠ ∞ := by
    rw [← hT]
    exact hfin.ne
  have hae : ∀ᵐ s ∂(volume.restrict (Ioi (0 : ℝ))),
      ENNReal.ofReal (s ^ (-(3 / 2 : ℝ)))
        * ∫⁻ x in UnforcedLeray.B0224.strip c, ENNReal.ofReal (‖G (s, x)‖ ^ 2) < ∞ :=
    ae_lt_top' (hw1.mul hI).aemeasurable hfinI
  filter_upwards [hae, ae_restrict_mem measurableSet_Ioi, hslice] with s hsfin hs hsl
  have hs0 : (0 : ℝ) < s := hs
  have hw0 : ENNReal.ofReal (s ^ (-(3 / 2 : ℝ))) ≠ 0 :=
    (ENNReal.ofReal_pos.2 (Real.rpow_pos_of_pos hs0 _)).ne'
  have hIfin : ∫⁻ x in UnforcedLeray.B0224.strip c, ENNReal.ofReal (‖G (s, x)‖ ^ 2) ≠ ∞ := by
    intro h
    rw [h, ENNReal.mul_top hw0] at hsfin
    exact lt_irrefl _ hsfin
  have hGm_s : Measurable fun x : ℝ × ℝ => G (s, x) := hGm.comp measurable_prodMk_left
  have hnn : 0 ≤ᵐ[volume.restrict (stripSet c)] fun x : ℝ × ℝ => ‖G (s, x)‖ ^ 2 :=
    Eventually.of_forall fun x => by positivity
  have hGs : MemLp (fun x : ℝ × ℝ => G (s, x)) 2 (volume.restrict (stripSet c)) := by
    refine (memLp_two_iff_integrable_sq_norm hGm_s.aestronglyMeasurable).2
      ⟨(hGm_s.norm.pow_const 2).aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal hnn]
    exact lt_top_iff_ne_top.2 hIfin
  exact hGs.ae_eq (hsl.mono fun x hx => hx.symm)

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
