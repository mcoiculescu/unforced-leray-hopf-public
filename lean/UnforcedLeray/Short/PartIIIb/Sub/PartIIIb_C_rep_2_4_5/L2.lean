import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_2_4_5.Defs
import UnforcedLeray.Lib.ConvIneq.YoungGroup

/-!
# `PartIII-b:C/rep/2/4/5` : `Vert1DYoung` (task `PartIII-b:C/rep/2/4/5/2`)

Source `the November 2 reference manuscript` 3631-3645 (Young in the dilation
variable), one-dimensional form of `sky_young_conv` (`Sub/PartIII-b_C_rep_2_1_2.lean`) with
`Space` replaced by `ℝ` and `volume` the Lebesgue measure on `ℝ`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem vy_lqNorm1_eq_eLpNorm {q : ℝ} (hq : 1 ≤ q) (f : ℝ → ℝ≥0∞) :
    lqNorm1 q f = eLpNorm f (ENNReal.ofReal q) volume := by
  have hq0 : 0 < q := lt_of_lt_of_le one_pos hq
  have hne0 : ENNReal.ofReal q ≠ 0 := (ENNReal.ofReal_pos.mpr hq0).ne'
  have hneT : ENNReal.ofReal q ≠ ∞ := ENNReal.ofReal_ne_top
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hne0 hneT, ENNReal.toReal_ofReal hq0.le]
  simp only [lqNorm1, enorm_eq_self]

/-- Young's inequality on `ℝ` for `ℝ≥0∞`-valued data, finite kernel, `g` of finite norm. -/
theorem vert1DYoung : Vert1DYoung := by
  intro K g hK hKt hg b p q hb hp hq h hgt
  have hp0 : 0 < p := lt_of_lt_of_le one_pos hp
  have hgfin : ∀ᵐ x ∂(volume : Measure ℝ), g x ≠ ⊤ := by
    have h1 : ∫⁻ x, g x ^ p ≠ ⊤ := by
      intro h0
      apply hgt
      unfold lqNorm1
      rw [h0]
      exact ENNReal.top_rpow_of_pos (by positivity)
    have h2 : ∀ᵐ x ∂(volume : Measure ℝ), g x ^ p < ⊤ :=
      ae_lt_top (hg.pow_const p) h1
    filter_upwards [h2] with x hx
    intro hxt
    rw [hxt, ENNReal.top_rpow_of_pos hp0] at hx
    exact absurd hx (lt_irrefl _)
  set K' : ℝ → ℝ := fun x => (K x).toReal with hK'
  set g' : ℝ → ℝ := fun x => (g x).toReal with hg'
  have hK'm : AEStronglyMeasurable K' volume := (hK.ennreal_toReal).aestronglyMeasurable
  have hg'm : AEStronglyMeasurable g' volume := (hg.ennreal_toReal).aestronglyMeasurable
  have eK : ∀ x, ‖K' x‖ₑ = K x := by
    intro x
    simp only [hK', Real.enorm_eq_ofReal ENNReal.toReal_nonneg, ENNReal.ofReal_toReal (hKt x)]
  have eg : ∀ᵐ x ∂(volume : Measure ℝ), ‖g' x‖ₑ = g x := by
    filter_upwards [hgfin] with x hx
    simp only [hg', Real.enorm_eq_ofReal ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hx]
  have hconv : (fun y => ∫⁻ x, K (y - x) * g x) = Conv.convAbs volume K' g' := by
    funext y
    unfold Conv.convAbs
    refine lintegral_congr_ae ?_
    filter_upwards [eg] with x hx
    rw [eK, hx]
  have hnK : lqNorm1 b K = eLpNorm K' (ENNReal.ofReal b) volume := by
    rw [vy_lqNorm1_eq_eLpNorm hb]
    exact (eLpNorm_congr_enorm_ae (Filter.Eventually.of_forall fun x => by
      rw [eK, enorm_eq_self])).symm
  have hng : lqNorm1 p g = eLpNorm g' (ENNReal.ofReal p) volume := by
    rw [vy_lqNorm1_eq_eLpNorm hp]
    exact (eLpNorm_congr_enorm_ae (by
      filter_upwards [eg] with x hx
      rw [hx, enorm_eq_self])).symm
  rw [vy_lqNorm1_eq_eLpNorm hq, hconv, hnK, hng]
  exact Conv.eLpNorm_convAbs_le_young (μ := volume) hK'm hg'm hb hp hq (by linarith)

end UnforcedLeray.Short.PartIIIb.Concrete
