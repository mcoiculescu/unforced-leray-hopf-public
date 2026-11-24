import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_near_masked_15
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_near_masked_15.Helpers

/-!
# Leaf 2 of `PartIII-b:C/near/masked/15`: `MaskedLiftMoment`

Source `the November 2 reference manuscript`
3905-3912, 4155-4156.

For a box tensor `f` with band `s₁ ≤ age ≤ s₂`, `|η| ≤ L` and bound `‖f‖ ≤ B`, the masked lift
is bounded by `3·9·|s₂|·B` and vanishes outside the ball of squared radius `(R²+L²)/s₁`.
The finite `L²_τ L²_z` moment follows.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory UnforcedLeray.Axi Set
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.NearInst.Masked

open UnforcedLeray.Short.PartIIIb.Concrete
open UnforcedLeray.Short.PartIIIb.NearInst

theorem maskedLiftMoment : MaskedLiftMoment := by
  intro R c δ s hR hc hδ hs f hf
  obtain ⟨s1, s2, L, hs1, hband⟩ := hf.band
  obtain ⟨B, hB⟩ := hf.bounded
  have hB0 : 0 ≤ B := le_trans (norm_nonneg _) (hB 0)
  have hS0 : 0 ≤ |s2| := abs_nonneg _
  have h9 : (0 : ℝ) ≤ 9 * (|s2| * B) := mul_nonneg (by norm_num) (mul_nonneg hS0 hB0)
  -- entry bound
  have hent : ∀ (τ : ℝ) (z : Space) (i j : Fin 3),
      |maskedLift R c δ s f τ z i j| ≤ 9 * (|s2| * B) := by
    intro τ z i j
    unfold maskedLift
    dsimp only
    split_ifs with hm
    · by_cases hfp : f (chartOf R c z τ) = 0
      · simpa [cartLift, hfp, H15.nsSym_zero'] using h9
      · obtain ⟨h1, h2, _⟩ := hband _ hfp
        have hage : |(chartOf R c z τ).1| ≤ |s2| := by
          rw [abs_of_nonneg (le_trans hs1.le h1)]
          exact le_trans h2 (le_abs_self s2)
        exact H15.abs_cartLift_le R c f τ z |s2| B hS0 hB0 (hB _) hage i j
    · simpa using h9
  -- support
  have hsupp : ∀ (τ : ℝ) (z : Space), ¬ (z 0 ^ 2 + z 1 ^ 2 + z 2 ^ 2 ≤ (R ^ 2 + L ^ 2) / s1) →
      maskedLift R c δ s f τ z = 0 := by
    intro τ z hz
    unfold maskedLift
    dsimp only
    split_ifs with hm
    · by_cases hfp : f (chartOf R c z τ) = 0
      · simp [cartLift, hfp, H15.nsSym_zero']
      · exfalso
        obtain ⟨h1, h2, h3⟩ := hband _ hfp
        apply hz
        exact H15.sumsq_le_of_band R L s1 hR hs1 z h1 h3
    · rfl
  -- pointwise bound on the norm
  set KK : ℝ := 3 * (9 * (|s2| * B)) with hKK
  have hKK0 : 0 ≤ KK := by
    rw [hKK]; exact mul_nonneg (by norm_num) h9
  set Zb : Set Space := Metric.closedBall (0 : Space) (Real.sqrt ((R ^ 2 + L ^ 2) / s1)) with hZb
  have hZbfin : volume Zb < ⊤ := measure_closedBall_lt_top
  have hsrc : ∀ (τ : ℝ) (y : Space),
      IIIa.srcNorm (maskedLift R c δ s f) τ y ^ (2 : ℝ) ≤
        Zb.indicator (fun _ => ENNReal.ofReal KK ^ 2) y := by
    intro τ y
    rw [ENNReal.rpow_two]
    by_cases hy : y ∈ Zb
    · rw [indicator_of_mem hy]
      apply ENNReal.pow_le_pow_left
      unfold IIIa.srcNorm
      apply ENNReal.ofReal_le_ofReal
      exact H15.tensorNorm_le_of_entries _ _ (by positivity) (fun i j => hent τ y i j)
    · rw [indicator_of_notMem hy]
      have h0 : maskedLift R c δ s f τ y = 0 :=
        hsupp τ y (fun h => hy (H15.mem_closedBall_of_sumsq y _ h))
      unfold IIIa.srcNorm
      rw [h0]
      simp [IIIa.tensorNorm]
  have hint : ∀ τ : ℝ, (∫⁻ y, IIIa.srcNorm (maskedLift R c δ s f) τ y ^ (2 : ℝ)) ≤
      ENNReal.ofReal KK ^ 2 * volume Zb := by
    intro τ
    calc (∫⁻ y, IIIa.srcNorm (maskedLift R c δ s f) τ y ^ (2 : ℝ))
        ≤ ∫⁻ y, Zb.indicator (fun _ => ENNReal.ofReal KK ^ 2) y := lintegral_mono (hsrc τ)
      _ = ENNReal.ofReal KK ^ 2 * volume Zb := lintegral_indicator_const measurableSet_closedBall _
  have hP : 0 < 2 * c / R := div_pos (by linarith) hR
  unfold SepMoment IIIa.ltauLq
  have hτ : (∫⁻ τ in Ioc 0 (2 * c / R),
      (∫⁻ y, IIIa.srcNorm (maskedLift R c δ s f) τ y ^ (2 : ℝ)) ^ ((2 : ℝ) / 2))
        ≤ ∫⁻ _τ in Ioc 0 (2 * c / R), ENNReal.ofReal KK ^ 2 * volume Zb := by
    apply lintegral_mono
    intro τ
    have h21 : ((2 : ℝ) / 2) = 1 := by norm_num
    show (∫⁻ y, IIIa.srcNorm (maskedLift R c δ s f) τ y ^ (2 : ℝ)) ^ ((2 : ℝ) / 2) ≤ _
    rw [h21, ENNReal.rpow_one]
    exact hint τ
  have hfin : (∫⁻ _τ in Ioc 0 (2 * c / R), ENNReal.ofReal KK ^ 2 * volume Zb) < ⊤ := by
    rw [lintegral_const, Measure.restrict_apply_univ, Real.volume_Ioc]
    exact ENNReal.mul_lt_top (ENNReal.mul_lt_top
      (lt_top_iff_ne_top.2 (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)) hZbfin)
      ENNReal.ofReal_lt_top
  have hI : (∫⁻ τ in Ioc 0 (2 * c / R),
      (∫⁻ y, IIIa.srcNorm (maskedLift R c δ s f) τ y ^ (2 : ℝ)) ^ ((2 : ℝ) / 2)) < ⊤ :=
    lt_of_le_of_lt hτ hfin
  exact ENNReal.rpow_lt_top_of_nonneg (by norm_num)
    (ENNReal.mul_ne_top (ENNReal.inv_ne_top.2 (ENNReal.ofReal_pos.2 hP).ne') hI.ne)
