import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T16_1_1.Defs

/-!
# `PartIII-a:T16/1/1/7` : `SepDiffMajIntegrable` (integrability of the order-`0` majorant)

Source `the November 2 reference manuscript` lines 3618-3623 (radial gap).
At a receiver `|y'| ≥ r_i` with finite gap-truncated order-`0` majorant, the majorant
`λ^{2Re μ+2}|y-λz|^{-4}|T(z,τ+2log λ)|` is `ρ`-integrable.  Tonelli (`lintegral_prod`) reduces
the `ρ`-integral to `∫_0^1 λ^{2Re μ+2} ∫ |y-λz|^{-4}|T| dz dλ`; on the support `|z'| ≤ r_o`
the radial gap `radial_gap` gives `|y-λz| ≥ r_i - r_o`, so the truncation `sepKd` is inactive,
and off the support `T = 0`.  The measurability argument is that of `sepWDiffUnder_of`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal

namespace UnforcedLeray.Short.IIIa

/-- **`PartIII-a:T16/1/1/7`**: the order-`0` majorant is `sepDiffRho`-integrable at a receiver
`|y'| ≥ r_i` where the gap-truncated order-`0` majorant is finite. -/
theorem sepDiffMajIntegrable : UnforcedLeray.Short.IIIa.SepDiffMajIntegrable := by
  intro μ rOut rIn P T hrO hrr hS τ y hy hfin
  -- measurability of the real-valued majorant on `ℝ × ℝ³`
  have hφ : Measurable fun q : ℝ × Space => (τ + 2 * Real.log q.1, q.2) :=
    (measurable_const.add (measurable_const.mul
      (Real.measurable_log.comp measurable_fst))).prodMk measurable_snd
  have hTn : Measurable fun q : ℝ × Space => tensorNorm (T (τ + 2 * Real.log q.1) q.2) := by
    unfold tensorNorm
    refine Measurable.sqrt ?_
    refine Finset.measurable_sum _ fun i _ => ?_
    refine Finset.measurable_sum _ fun j _ => ?_
    exact ((hS.measurable i j).comp hφ).pow_const 2
  have hM : Measurable (sepDiffMaj μ T τ y) := by
    unfold sepDiffMaj
    exact ((measurable_fst.pow_const _).mul
      ((measurable_const.sub (measurable_fst.smul measurable_snd)).norm.pow_const _)).mul hTn
  -- pointwise domination on `λ ∈ (0,1)`, all `z`
  have key : ∀ l ∈ Ioo (0 : ℝ) 1, ∀ z : Space,
      ‖sepDiffMaj μ T τ y (l, z)‖ₑ ≤ ENNReal.ofReal (l ^ (2 * μ.re + 2)) *
        (sepKd 0 (rIn - rOut) (y - l • z) * srcNorm T (τ + 2 * Real.log l) z) := by
    intro l hl z
    by_cases hz : Real.sqrt (z 0 ^ 2 + z 1 ^ 2) ≤ rOut
    · have hg := radial_gap y z l rOut rIn hl hz hy
      have hl0 : 0 ≤ l ^ (2 * μ.re + 2) := Real.rpow_nonneg hl.1.le _
      have hn0 : 0 ≤ ‖y - l • z‖ ^ (-4 : ℝ) := Real.rpow_nonneg (norm_nonneg _) _
      have ht0 : 0 ≤ tensorNorm (T (τ + 2 * Real.log l) z) := by
        unfold tensorNorm; positivity
      unfold sepKd srcNorm sepDiffMaj
      dsimp only
      rw [if_pos hg]
      simp only [Nat.cast_zero, sub_zero]
      rw [← ofReal_norm, Real.norm_of_nonneg (mul_nonneg (mul_nonneg hl0 hn0) ht0),
        ENNReal.ofReal_mul (mul_nonneg hl0 hn0), ENNReal.ofReal_mul hl0, mul_assoc]
    · push_neg at hz
      have hT0 := hS.support (τ + 2 * Real.log l) z hz
      have h0 : tensorNorm (T (τ + 2 * Real.log l) z) = 0 := by
        unfold tensorNorm; rw [hT0]; simp
      have hs : srcNorm T (τ + 2 * Real.log l) z = 0 := by
        unfold srcNorm; rw [h0]; simp
      have hz0 : sepDiffMaj μ T τ y (l, z) = 0 := by
        unfold sepDiffMaj; dsimp only; rw [h0, mul_zero]
      rw [hz0, hs]
      simp
  -- Tonelli on the product measure
  have hmeasE : Measurable fun p : ℝ × Space => ‖sepDiffMaj μ T τ y p‖ₑ :=
    hM.enorm
  have hfin' : ∫⁻ p, ‖sepDiffMaj μ T τ y p‖ₑ ∂sepDiffRho < ⊤ := by
    unfold sepDiffRho
    rw [lintegral_prod _ hmeasE.aemeasurable]
    calc ∫⁻ l in Ioo (0 : ℝ) 1, ∫⁻ z : Space, ‖sepDiffMaj μ T τ y (l, z)‖ₑ
        ≤ ∫⁻ l in Ioo (0 : ℝ) 1, ENNReal.ofReal (l ^ (2 * μ.re + 2)) *
            ∫⁻ z : Space, sepKd 0 (rIn - rOut) (y - l • z) * srcNorm T (τ + 2 * Real.log l) z :=
          setLIntegral_mono' measurableSet_Ioo fun l hl => by
            calc ∫⁻ z : Space, ‖sepDiffMaj μ T τ y (l, z)‖ₑ
                ≤ ∫⁻ z : Space, ENNReal.ofReal (l ^ (2 * μ.re + 2)) *
                    (sepKd 0 (rIn - rOut) (y - l • z) * srcNorm T (τ + 2 * Real.log l) z) :=
                  lintegral_mono fun z => key l hl z
              _ = ENNReal.ofReal (l ^ (2 * μ.re + 2)) *
                    ∫⁻ z : Space, sepKd 0 (rIn - rOut) (y - l • z) *
                      srcNorm T (τ + 2 * Real.log l) z :=
                  lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ = sepDom (2 * μ.re + 2) 0 (rIn - rOut) (srcNorm T) τ y := rfl
      _ < ⊤ := hfin
  exact ⟨hM.aestronglyMeasurable, hfin'⟩

end UnforcedLeray.Short.IIIa
