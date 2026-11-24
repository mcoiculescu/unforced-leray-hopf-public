import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D2_1_3_1_2_1_4_1_3_3

/-!
# `selNormEq`: the phase-normalized `L²` norm on one period

Source `the November 2 reference manuscript` lines 1341-1344.
`phaseLpNorm P 2 g = (P⁻¹)^{1/2} ‖g‖_{L²((0,P]×ℝ³)}` by Tonelli on the product measure.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ContDiff ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem selNormEq : SelNormEq := by
  intro P hP g hg
  have key : (volume : Measure (ℝ × Space)).restrict (Ioc (0 : ℝ) P ×ˢ (Set.univ : Set Space))
      = (volume.restrict (Ioc (0 : ℝ) P)).prod (volume : Measure Space) := by
    rw [Measure.volume_eq_prod, ← Measure.prod_restrict, Measure.restrict_univ]
  have hg' : AEStronglyMeasurable g ((volume.restrict (Ioc (0 : ℝ) P)).prod (volume : Measure Space)) := by
    rw [← key]
    exact hg.restrict
  have hmeas : AEMeasurable (fun z : ℝ × Space => ‖g z‖ₑ ^ (2 : ℝ))
      ((volume.restrict (Ioc (0 : ℝ) P)).prod (volume : Measure Space)) :=
    (hg'.enorm).pow_const (2 : ℝ)
  unfold UnforcedLeray.Short.IIb.phaseLpNorm
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num), ENNReal.toReal_ofNat,
    key, lintegral_prod _ hmeas, ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 1 / 2)]
