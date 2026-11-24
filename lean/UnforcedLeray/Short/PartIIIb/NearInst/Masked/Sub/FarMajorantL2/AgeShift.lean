import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Sub.FarMajorantL2.Defs

/-!
# Age shift for `FarMajorantL2` (source 2666-2668, Lift.lean `ageμ`)

`ageμ c (a+b) = s^b · ageμ c a` as measures: the density `s^{a+b}` of the age factor is `s^a`
times `s^b` on `(0,∞)`, and the age measure is `(vol|_{(0,∞)}).withDensity (s^a)` times the
cell measure, so the shift is a withDensity identity on the product (`prod_withDensity_left`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory UnforcedLeray.Axi Set
open UnforcedLeray.Short.PartIIIb.Concrete
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.NearInst.Masked

theorem ageShift_holds : AgeShift := by
  intro c a b F hF
  have hsf : SFinite (Cyl.avgμ c) := by
    unfold Cyl.avgμ
    infer_instance
  have h1 : ∀ a' : ℝ, Axi.ageμ c a' =
      ((volume.restrict (Ioi (0 : ℝ))).prod (Cyl.avgμ c)).withDensity
        (fun z : ℝ × (ℝ × ℝ) => ENNReal.ofReal (z.1 ^ a')) := by
    intro a'
    unfold Axi.ageμ
    exact MeasureTheory.prod_withDensity_left (measurable_ofReal_rpow a')
  have hg : ∀ a' : ℝ, Measurable (fun z : ℝ × (ℝ × ℝ) => ENNReal.ofReal (z.1 ^ a')) :=
    fun a' => (measurable_ofReal_rpow a').comp measurable_fst
  have hFb : Measurable (fun x : Chart => ENNReal.ofReal (x.1 ^ b) * F x) :=
    ((measurable_ofReal_rpow b).comp measurable_fst).mul hF
  rw [h1 (a + b), h1 a]
  rw [lintegral_withDensity_eq_lintegral_mul _ (hg (a + b)) hF,
    lintegral_withDensity_eq_lintegral_mul _ (hg a) hFb]
  -- the two integrands agree wherever `s > 0`, which is `μ`-a.e.
  have hpos : ∀ᵐ z ∂((volume.restrict (Ioi (0 : ℝ))).prod (Cyl.avgμ c)), 0 < z.1 := by
    have hqmp := (Measure.quasiMeasurePreserving_fst
      (μ := volume.restrict (Ioi (0 : ℝ))) (ν := Cyl.avgμ c))
    exact hqmp.ae (ae_restrict_mem measurableSet_Ioi)
  refine lintegral_congr_ae ?_
  filter_upwards [hpos] with z hz
  simp only [Pi.mul_apply]
  rw [Real.rpow_add hz, ENNReal.ofReal_mul (Real.rpow_nonneg hz.le _)]
  ring
