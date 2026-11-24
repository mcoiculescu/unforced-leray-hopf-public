import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Realization.SubKF3

/-!
# `kf3MemLpDecay` (source 3594-3596): decaying continuous fields are in `L²(dx dτ)`

Route: `physMeasure ε c = (volume.restrict univ).prod (volume.restrict (Ioc 0 P))`; the dominating
function `C/(1+|x|)²` has square `C²(1+|x|)^{-4}`, integrable on `ℝ³` (`integrable_one_add_norm`,
`4 > 3`), times the constant `1` on the finite `τ`-interval (`Integrable.prod_mul`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory UnforcedLeray.Axi Set Filter
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.NearInst.Masked.Realization

theorem kf3MemLpDecay : KF3MemLpDecay := by
  intro ε c f hf hbd
  obtain ⟨C, hC⟩ := hbd
  set μ := UnforcedLeray.B0220.physMeasure ε c with hμ
  have hm : UnforcedLeray.B0220.physMeasure ε c =
      ((volume : Measure Space).restrict univ).prod
        ((volume : Measure ℝ).restrict (Ioc 0 (2 * ε * c))) := by
    rw [UnforcedLeray.B0220.physMeasure, UnforcedLeray.B0220.physDomain, Measure.prod_restrict,
      ← Measure.volume_eq_prod]
  -- the dominating function
  set G : Space × ℝ → ℝ := fun y => |C| / (1 + ‖y.1‖) ^ 2 with hG
  have hGpos : ∀ y : Space × ℝ, 0 < (1 + ‖y.1‖) ^ 2 := fun y => by positivity
  have hGsq : ∀ y : Space × ℝ, ‖G y‖ ^ 2 = |C| ^ 2 * ((1 + ‖y.1‖) ^ 4)⁻¹ := by
    intro y
    have h0 : (0:ℝ) ≤ |C| / (1 + ‖y.1‖) ^ 2 := by positivity
    rw [hG]
    simp only
    rw [Real.norm_of_nonneg h0, div_pow]
    field_simp
  -- integrability of the square on the product
  have hI1 : Integrable (fun x : Space => |C| ^ 2 * ((1 + ‖x‖) ^ 4)⁻¹)
      ((volume : Measure Space).restrict univ) := by
    rw [Measure.restrict_univ]
    have h := (integrable_one_add_norm (E := Space) (μ := volume) (r := 4) (by
      simp [finrank_euclideanSpace]; norm_num)).const_mul (|C| ^ 2)
    refine h.congr (ae_of_all _ fun x => ?_)
    have : (1 + ‖x‖) ^ (-(4:ℝ)) = ((1 + ‖x‖) ^ 4)⁻¹ := by
      rw [Real.rpow_neg (by positivity)]
      congr 1
      exact_mod_cast Real.rpow_natCast (1 + ‖x‖) 4
    simp only [this]
  have hI2 : Integrable (fun _ : ℝ => (1 : ℝ))
      ((volume : Measure ℝ).restrict (Ioc 0 (2 * ε * c))) := by
    have : IsFiniteMeasure ((volume : Measure ℝ).restrict (Ioc 0 (2 * ε * c))) :=
      ⟨by rw [Measure.restrict_apply_univ]; simp⟩
    exact integrable_const 1
  have hprod := MeasureTheory.Integrable.mul_prod hI1 hI2
  have hsq : Integrable (fun y : Space × ℝ => |C| ^ 2 * ((1 + ‖y.1‖) ^ 4)⁻¹)
      (UnforcedLeray.B0220.physMeasure ε c) := by
    rw [hm]
    refine (hprod.congr (ae_of_all _ fun y => ?_))
    simp
  have hGm : MemLp G 2 (UnforcedLeray.B0220.physMeasure ε c) := by
    have hGcont : Continuous G := by
      rw [hG]
      exact continuous_const.div (by fun_prop) (fun y => by positivity)
    rw [memLp_two_iff_integrable_sq_norm hGcont.aestronglyMeasurable]
    refine hsq.congr (ae_of_all _ fun y => ?_)
    simp only
    rw [hGsq]
  refine MemLp.of_le hGm hf.aestronglyMeasurable (ae_of_all _ fun y => ?_)
  have h1 : ‖f y‖ ≤ C / (1 + ‖y.1‖) ^ 2 := hC y
  have h2 : C / (1 + ‖y.1‖) ^ 2 ≤ |C| / (1 + ‖y.1‖) ^ 2 :=
    div_le_div_of_nonneg_right (le_abs_self C) (by positivity)
  rw [hG]
  simp only
  rw [Real.norm_of_nonneg (by positivity)]
  linarith
