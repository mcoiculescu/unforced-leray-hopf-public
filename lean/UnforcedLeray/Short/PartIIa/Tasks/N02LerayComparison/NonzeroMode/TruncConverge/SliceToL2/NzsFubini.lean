import UnforcedLeray.Short.PartIIa.Sub.N02_4_11_2

/-!
# Part II-a, `Sub2` of `PartII-a:N02/4/11/2`: Fubini for `measureH c` in `(s, η)`-coordinates

Target: `nzsFubini : NzsFubini` (`Sub/N02_4_11_2.lean`). Source of record:
`the November 2 reference manuscript`, lines 1744-1749.

`measureH c` is `volume.restrict (cell c)` with density `s ^ (-(3/2))`, and `cell c` is the
product `Ioi 0 ×ˢ (Ioc 0 c ×ˢ univ)`. The density depends only on `s`, so the `q`-integral over
`(0, c]` and the `η`-integral can be exchanged (Tonelli) and the density pulled out slice by slice.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace UnforcedLeray.Short.PartIIa

open UnforcedLeray.B0220 UnforcedLeray.B0223 UnforcedLeray.B0226

theorem nzsFubini : NzsFubini := by
  intro c hc F hF
  have hw : Measurable weightH := by
    unfold weightH
    exact (measurable_fst.pow_const _).ennreal_ofReal
  have hwS : Measurable (fun s : ℝ => ENNReal.ofReal (s ^ (-(3 / 2 : ℝ)))) :=
    (measurable_id.pow_const _).ennreal_ofReal
  have hG : Measurable (fun x : ℝ × ℝ => ∫⁻ q in Ioc (0 : ℝ) c, F (x.1, q, x.2)) :=
    Measurable.lintegral_prod_right' (f := fun z : (ℝ × ℝ) × ℝ => F (z.1.1, z.2, z.1.2))
      (hF.comp (by fun_prop))
  have hh : Measurable (fun s : ℝ => ∫⁻ η, ∫⁻ q in Ioc (0 : ℝ) c, F (s, q, η)) :=
    Measurable.lintegral_prod_right' (f := fun z : ℝ × ℝ => ∫⁻ q in Ioc (0 : ℝ) c, F (z.1, q, z.2))
      hG
  have hcell : cellMeasure c = (volume.restrict (Ioi (0 : ℝ))).prod
      ((volume.restrict (Ioc (0 : ℝ) c)).prod volume) := by
    have e : ((volume : Measure ℝ).restrict (Ioc (0 : ℝ) c)).prod (volume : Measure ℝ)
        = ((volume : Measure (ℝ × ℝ))).restrict (Ioc (0 : ℝ) c ×ˢ univ) :=
      Measure.restrict_prod_eq_prod_univ _
    unfold cellMeasure cell
    rw [Measure.volume_eq_prod ℝ (ℝ × ℝ), ← Measure.prod_restrict, ← e]
  unfold measureH NzsMeasureSE
  rw [lintegral_withDensity_eq_lintegral_mul _ hw hF, hcell]
  simp only [Pi.mul_apply]
  rw [lintegral_prod (fun a : Profile => weightH a * F a) (hw.mul hF).aemeasurable,
    lintegral_prod _ hG.aemeasurable,
    lintegral_withDensity_eq_lintegral_mul _ hwS hh]
  refine lintegral_congr (fun s => ?_)
  rw [Pi.mul_apply]
  have hKs : Measurable (fun y : ℝ × ℝ => weightH (s, y) * F (s, y)) :=
    (hw.comp (measurable_const.prodMk measurable_id)).mul
      (hF.comp (measurable_const.prodMk measurable_id))
  rw [lintegral_prod _ hKs.aemeasurable, lintegral_lintegral_swap hKs.aemeasurable]
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_congr (fun η => ?_)
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_congr (fun q => ?_)
  rfl

end UnforcedLeray.Short.PartIIa
