import UnforcedLeray.Units.B0224.PlaneHeat
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_3_2_2_1_2

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete.HeatStrong.FiberBoundAux

open UnforcedLeray.Gaussian (Euc gaussKernel)
open UnforcedLeray.B0224

theorem ennreal_add_sq_le' (x y : ℝ≥0∞) : (x + y) ^ 2 ≤ 2 * (x ^ 2 + y ^ 2) := by
  rcases eq_or_ne x ⊤ with rfl | hx
  · simp
  rcases eq_or_ne y ⊤ with rfl | hy
  · simp
  lift x to NNReal using hx
  lift y to NNReal using hy
  have h' : (x + y) ^ 2 ≤ 2 * (x ^ 2 + y ^ 2) := by
    rw [← NNReal.coe_le_coe]
    push_cast
    nlinarith [sq_nonneg ((x : ℝ) - (y : ℝ))]
  exact_mod_cast h'

theorem enorm_sub_sq_le' {E : Type*} [NormedAddCommGroup E] (a b : E) :
    ‖a - b‖ₑ ^ 2 ≤ 2 * ‖a‖ₑ ^ 2 + 2 * ‖b‖ₑ ^ 2 := by
  calc ‖a - b‖ₑ ^ 2 ≤ (‖a‖ₑ + ‖b‖ₑ) ^ 2 := by
        gcongr
        exact enorm_sub_le
    _ ≤ 2 * (‖a‖ₑ ^ 2 + ‖b‖ₑ ^ 2) := ennreal_add_sq_le' _ _
    _ = 2 * ‖a‖ₑ ^ 2 + 2 * ‖b‖ₑ ^ 2 := by ring

theorem stronglyMeasurable_planeHeat_pos' {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {θ : ℝ} (hθ : 0 < θ) {u : ℝ × ℝ → E} (hu : StronglyMeasurable u) :
    StronglyMeasurable (planeHeat θ u) := by
  have hf : StronglyMeasurable (fun q : (ℝ × ℝ) × Euc 2 =>
      gaussKernel 2 θ q.2 • u (q.1 - planeι q.2)) := by
    refine StronglyMeasurable.smul ?_ ?_
    · exact ((UnforcedLeray.Gaussian.continuous_gaussKernel θ).comp continuous_snd).stronglyMeasurable
    · exact hu.comp_measurable (measurable_fst.sub (measurable_planeι.comp measurable_snd))
  have heq : planeHeat θ u = fun z => ∫ y : Euc 2, gaussKernel 2 θ y • u (z - planeι y) := by
    funext z
    exact planeHeat_of_pos hθ u z
  rw [heq]
  exact hf.integral_prod_right

end UnforcedLeray.Short.PartIIIb.Concrete.HeatStrong.FiberBoundAux

open UnforcedLeray.B0224
open UnforcedLeray.Gaussian (Euc gaussKernel)
open UnforcedLeray.Short.PartIIIb.Concrete.HeatStrong.FiberBoundAux
theorem heatFiberBound_holds (c : ℝ) (hc : 0 < c) :
    UnforcedLeray.Short.PartIIIb.Concrete.HeatStrong.HeatFiberBound c := by
  intro u hu hper θ
  unfold UnforcedLeray.Short.PartIIIb.Concrete.HeatStrong.stripN
    UnforcedLeray.Short.PartIIIb.Concrete.HeatStrong.stripM
  by_cases hθ : 0 < θ
  · have hH : StronglyMeasurable (planeHeat θ u) :=
      stronglyMeasurable_planeHeat_pos' hθ hu
    have hm1 : Measurable (fun z : ℝ × ℝ => ‖planeHeat θ u z‖ₑ ^ 2) :=
      (hH.measurable.enorm).pow_const 2
    have hm2 : Measurable (fun z : ℝ × ℝ => ‖u z‖ₑ ^ 2) :=
      (hu.measurable.enorm).pow_const 2
    have hφ : UnforcedLeray.Cyl.IsPeriodic c (fun z : ℝ × ℝ => ‖u z‖ₑ ^ 2) :=
      fun z => by simp only [hper z]
    have hcontr : ∫⁻ z in strip c, ‖planeHeat θ u z‖ₑ ^ 2 ≤ ∫⁻ z in strip c, ‖u z‖ₑ ^ 2 := by
      calc ∫⁻ z in strip c, ‖planeHeat θ u z‖ₑ ^ 2
          ≤ ∫⁻ z in strip c, ∫⁻ y : Euc 2,
              ENNReal.ofReal (gaussKernel 2 θ y) * ‖u (z - planeι y)‖ₑ ^ 2 := by
            refine lintegral_mono fun z => ?_
            rw [planeHeat_of_pos hθ u z]
            exact enorm_integral_gauss_sq_le hθ
              (hu.comp_measurable (measurable_const.sub measurable_planeι)).aestronglyMeasurable
        _ = ∫⁻ z in strip c, ‖u z‖ₑ ^ 2 :=
            UnforcedLeray.B0224.lintegral_strip_gauss hc hθ hm2 hφ
    have hpt : ∀ z : ℝ × ℝ, ‖planeHeat θ u z - u z‖ₑ ^ 2 ≤
        2 * ‖planeHeat θ u z‖ₑ ^ 2 + 2 * ‖u z‖ₑ ^ 2 := fun z => enorm_sub_sq_le' _ _
    calc ∫⁻ z in strip c, ‖planeHeat θ u z - u z‖ₑ ^ 2
        ≤ ∫⁻ z in strip c, (2 * ‖planeHeat θ u z‖ₑ ^ 2 + 2 * ‖u z‖ₑ ^ 2) :=
          lintegral_mono (fun z => hpt z)
      _ = (∫⁻ z in strip c, 2 * ‖planeHeat θ u z‖ₑ ^ 2) + (∫⁻ z in strip c, 2 * ‖u z‖ₑ ^ 2) :=
          lintegral_add_left (f := fun z : ℝ × ℝ => 2 * ‖planeHeat θ u z‖ₑ ^ 2)
            (measurable_const.mul hm1) _
      _ = 2 * (∫⁻ z in strip c, ‖planeHeat θ u z‖ₑ ^ 2) + 2 * (∫⁻ z in strip c, ‖u z‖ₑ ^ 2) := by
          rw [lintegral_const_mul' _ _ (by norm_num), lintegral_const_mul' _ _ (by norm_num)]
      _ ≤ 2 * (∫⁻ z in strip c, ‖u z‖ₑ ^ 2) + 2 * (∫⁻ z in strip c, ‖u z‖ₑ ^ 2) :=
          add_le_add (mul_le_mul_of_nonneg_left hcontr (by norm_num)) le_rfl
      _ = 4 * (∫⁻ z in strip c, ‖u z‖ₑ ^ 2) := by ring
  · rw [planeHeat_of_nonpos (not_lt.1 hθ)]
    simp
