import UnforcedLeray.Short.Interface.Sub.I05
import UnforcedLeray.Lib.BochnerTime.Slices

/-!
# Interface leaf 3, sub-lemma 1: the slab `L²` bound from phase-wise bounds

Source of record: `the November 2 reference manuscript`, lines 6071-6075.
Tonelli on `B0005.IsY2.slab_eq`: `‖F‖²_{L²(slab)} = ∫_{(0,P]} ‖F(τ, ·)‖₂² dτ ≤ c² ∫ ‖D(τ, ·)‖₂² dτ`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter
open scoped ENNReal NNReal ContDiff Topology

namespace UnforcedLeray.Short.Interface

open UnforcedLeray.Blueprint UnforcedLeray.SobolevGraph UnforcedLeray.Cons.C08

theorem slab_memLp_of_phase_bound : SlabMemLpOfPhaseBound := by
  intro P F D c hF hD hbound
  have hFm : AEStronglyMeasurable F (volume.restrict (periodSlab P)) := hF.restrict
  rw [B0005.IsY2.slab_eq] at hD hFm ⊢
  have h2 : (2 : ℝ≥0∞) ≠ 0 := two_ne_zero
  have h2' : (2 : ℝ≥0∞) ≠ ⊤ := ENNReal.ofNat_ne_top
  refine ⟨hFm, ?_⟩
  have hDint := (eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top h2 h2').1 hD.2
  rw [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top h2 h2']
  rw [lintegral_prod _ (hFm.enorm.pow_const _)]
  rw [lintegral_prod _ (hD.1.enorm.pow_const _)] at hDint
  calc ∫⁻ τ, ∫⁻ y, ‖F (τ, y)‖ₑ ^ (2 : ℝ≥0∞).toReal ∂volume ∂(volume.restrict (Ioc (0 : ℝ) P))
      = ∫⁻ τ, eLpNorm (fun y => F (τ, y)) 2 volume ^ (2 : ℝ≥0∞).toReal
          ∂(volume.restrict (Ioc (0 : ℝ) P)) := by
        congr 1; funext τ
        rw [UnforcedLeray.BochnerTime.eLpNorm_rpow_eq_lintegral h2 h2']
    _ ≤ ∫⁻ τ, ((c : ℝ≥0∞) * eLpNorm (fun y => D (τ, y)) 2 volume) ^ (2 : ℝ≥0∞).toReal
          ∂(volume.restrict (Ioc (0 : ℝ) P)) :=
        lintegral_mono_ae (hbound.mono fun τ hτ => by gcongr)
    _ = (c : ℝ≥0∞) ^ (2 : ℝ≥0∞).toReal * ∫⁻ τ, eLpNorm (fun y => D (τ, y)) 2 volume ^
          (2 : ℝ≥0∞).toReal ∂(volume.restrict (Ioc (0 : ℝ) P)) := by
        simp_rw [ENNReal.mul_rpow_of_nonneg _ _ ENNReal.toReal_nonneg]
        rw [lintegral_const_mul']
        exact ENNReal.rpow_ne_top_of_nonneg ENNReal.toReal_nonneg ENNReal.coe_ne_top
    _ < ⊤ := by
        refine ENNReal.mul_lt_top (ENNReal.rpow_lt_top_of_nonneg ENNReal.toReal_nonneg
          ENNReal.coe_ne_top) ?_
        have : ∫⁻ τ, eLpNorm (fun y => D (τ, y)) 2 volume ^ (2 : ℝ≥0∞).toReal
            ∂(volume.restrict (Ioc (0 : ℝ) P)) =
            ∫⁻ τ, ∫⁻ y, ‖D (τ, y)‖ₑ ^ (2 : ℝ≥0∞).toReal ∂volume
              ∂(volume.restrict (Ioc (0 : ℝ) P)) := by
          congr 1; funext τ
          rw [UnforcedLeray.BochnerTime.eLpNorm_rpow_eq_lintegral h2 h2']
        rw [this]
        exact hDint

end UnforcedLeray.Short.Interface
