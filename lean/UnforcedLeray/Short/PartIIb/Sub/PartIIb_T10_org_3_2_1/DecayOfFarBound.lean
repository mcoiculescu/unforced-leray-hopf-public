import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T10_org_3_2_1_defs
import UnforcedLeray.Cons.L2.BackgroundConcrete.SpatialProductBounds

/-!
# `PartII-b:T10/org/3/2/1`: uniform decay from a far-field bound (`DecayOfFarBound`)

Source of record `the November 2 reference manuscript`,
lines 1498-1500 (representatives in `C(ℝ/Pℤ; L^r)`; here the decay that makes the slices of the
smooth Leray test continuous into `L²`).

A continuous `P`-periodic field is bounded by some `B` on `[0, P] × B̄_ρ`; every phase reduces to
`[0, P)` (`Function.Periodic.exists_mem_Ico₀`).  For `|y| < ρ`,
`B ≤ B (1 + ρ)^n (1 + |y|)^{-n}`; for `|y| ≥ ρ`,
`|y|^{-n} ≤ ((1 + ρ)/ρ)^n (1 + |y|)^{-n}` since `1 + |y| ≤ ((1 + ρ)/ρ) |y|`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology

namespace UnforcedLeray.Short.IIb.LTS

open UnforcedLeray.PhaseSpace UnforcedLeray.Cons.C03.Concrete

/-- **`DecayOfFarBound`**. -/
theorem decayOfFarBound_proof : DecayOfFarBound := by
  intro P hP n F hF hper ρ C hρ hfar
  obtain ⟨B, hB0, hB⟩ := exists_norm_bound_on_compact F hF
    ((isCompact_Icc (a := (0 : ℝ)) (b := P)).prod (isCompact_closedBall (0 : Space) ρ))
  refine ⟨B * (1 + ρ) ^ n + |C| * ((1 + ρ) / ρ) ^ n, fun τ y => ?_⟩
  have hper' : Function.Periodic (fun t => F (t, y)) P := fun t => hper t y
  obtain ⟨t, ht, he⟩ := hper'.exists_mem_Ico₀ hP τ
  have htI : t ∈ Icc (0 : ℝ) P := Ico_subset_Icc_self ht
  have he' : F (τ, y) = F (t, y) := he
  rw [he']
  have h1y : 0 < 1 + ‖y‖ := by positivity
  have hrp : (1 + ‖y‖) ^ (-(n : ℝ)) = ((1 + ‖y‖) ^ n)⁻¹ := by
    rw [Real.rpow_neg h1y.le, Real.rpow_natCast]
  rw [hrp]
  have hpos : 0 < (1 + ‖y‖) ^ n := pow_pos h1y n
  have hw : 0 ≤ ((1 + ‖y‖) ^ n)⁻¹ := inv_nonneg.2 hpos.le
  have hA : 0 ≤ B * (1 + ρ) ^ n := mul_nonneg hB0 (pow_nonneg (by linarith) n)
  have hA' : 0 ≤ |C| * ((1 + ρ) / ρ) ^ n :=
    mul_nonneg (abs_nonneg _) (pow_nonneg (div_nonneg (by linarith) hρ.le) n)
  rcases lt_or_ge ‖y‖ ρ with hy | hy
  · have hb : ‖F (t, y)‖ ≤ B := hB (t, y) ⟨htI, by
      simpa [Metric.mem_closedBall, dist_zero_right] using hy.le⟩
    have hle : (1 + ‖y‖) ^ n ≤ (1 + ρ) ^ n :=
      pow_le_pow_left₀ h1y.le (by linarith) n
    have hq : 1 ≤ (1 + ρ) ^ n * ((1 + ‖y‖) ^ n)⁻¹ := by
      rw [← div_eq_mul_inv, one_le_div hpos]
      exact hle
    calc ‖F (t, y)‖ ≤ B := hb
      _ ≤ B * ((1 + ρ) ^ n * ((1 + ‖y‖) ^ n)⁻¹) := le_mul_of_one_le_right hB0 hq
      _ = B * (1 + ρ) ^ n * ((1 + ‖y‖) ^ n)⁻¹ := by ring
      _ ≤ (B * (1 + ρ) ^ n + |C| * ((1 + ρ) / ρ) ^ n) * ((1 + ‖y‖) ^ n)⁻¹ :=
        mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hA') hw
  · have hyp : 0 < ‖y‖ := lt_of_lt_of_le hρ hy
    have hyn : 0 < ‖y‖ ^ n := pow_pos hyp n
    have hlin : 1 + ‖y‖ ≤ (1 + ρ) / ρ * ‖y‖ := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hρ]
      nlinarith
    have hpow : (1 + ‖y‖) ^ n ≤ ((1 + ρ) / ρ) ^ n * ‖y‖ ^ n := by
      rw [← mul_pow]
      exact pow_le_pow_left₀ h1y.le hlin n
    have hinv : (‖y‖ ^ n)⁻¹ ≤ ((1 + ρ) / ρ) ^ n * ((1 + ‖y‖) ^ n)⁻¹ := by
      rw [← div_eq_mul_inv, le_div_iff₀ hpos, inv_mul_le_iff₀ hyn, mul_comm]
      exact hpow
    have hf := hfar t htI y hy
    calc ‖F (t, y)‖ ≤ C * (‖y‖ ^ n)⁻¹ := hf
      _ ≤ |C| * (‖y‖ ^ n)⁻¹ := mul_le_mul_of_nonneg_right (le_abs_self C) (inv_nonneg.2 hyn.le)
      _ ≤ |C| * (((1 + ρ) / ρ) ^ n * ((1 + ‖y‖) ^ n)⁻¹) :=
        mul_le_mul_of_nonneg_left hinv (abs_nonneg C)
      _ = |C| * ((1 + ρ) / ρ) ^ n * ((1 + ‖y‖) ^ n)⁻¹ := by ring
      _ ≤ (B * (1 + ρ) ^ n + |C| * ((1 + ρ) / ρ) ^ n) * ((1 + ‖y‖) ^ n)⁻¹ :=
        mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hA) hw

#print axioms decayOfFarBound_proof

end UnforcedLeray.Short.IIb.LTS
