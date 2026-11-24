import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# A scalar integration by parts on `(0,1]` (source 4776-4782, 5383-5387)

If `φ` is bounded and continuous on `(0,1]` with `t φ'(t) = -4φ(t) - Θ(t)`, then
`∫₀¹ t^p Θ = (p-3) ∫₀¹ t^p φ - φ(1)`  (`p > 0`): the integrand `t ↦ t^{p+1} φ(t)` has derivative
`(p-3) t^p φ - t^p Θ` and vanishes at `0`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem ibp_pow_dilation {φ Θ : ℝ → ℝ} {B p : ℝ} (hp : 0 < p)
    (hbd : ∀ t ∈ Ioc (0 : ℝ) 1, |φ t| ≤ B)
    (hcont : ContinuousOn φ (Ioc (0 : ℝ) 1))
    (hder : ∀ t ∈ Ioo (0 : ℝ) 1, HasDerivAt φ (-(4 * φ t + Θ t) / t) t)
    (hΘ : IntegrableOn (fun t : ℝ => t ^ p * Θ t) (Ioc (0 : ℝ) 1)) :
    ∫ t in Ioc (0 : ℝ) 1, t ^ p * Θ t =
      (p - 3) * (∫ t in Ioc (0 : ℝ) 1, t ^ p * φ t) - φ 1 := by
  have hB : 0 ≤ B := le_trans (abs_nonneg _) (hbd 1 ⟨one_pos, le_rfl⟩)
  set g : ℝ → ℝ := fun t => t ^ (p + 1) * φ t with hg
  have hpow_cont : Continuous (fun t : ℝ => t ^ p) := Real.continuous_rpow_const hp.le
  -- φ-weighted integrability
  have hφint : IntegrableOn (fun t : ℝ => t ^ p * φ t) (Ioc (0 : ℝ) 1) := by
    have hm : AEStronglyMeasurable (fun t : ℝ => t ^ p * φ t) (volume.restrict (Ioc (0 : ℝ) 1)) :=
      (hpow_cont.continuousOn.mul hcont).aestronglyMeasurable measurableSet_Ioc
    refine Integrable.mono' (g := fun t : ℝ => t ^ p * B) ?_ hm ?_
    · exact (hpow_cont.mul continuous_const).integrableOn_Ioc
    · filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg ht.1.le _)]
      exact mul_le_mul_of_nonneg_left (hbd t ht) (Real.rpow_nonneg ht.1.le _)
  -- continuity of `g` on `[0,1]`
  have hgc : ContinuousOn g (Icc (0 : ℝ) 1) := by
    intro t ht
    rcases eq_or_lt_of_le ht.1 with h0 | hpos
    · -- t = 0
      subst h0
      have hg0 : g 0 = 0 := by
        simp [hg, Real.zero_rpow (by linarith : p + 1 ≠ 0)]
      rw [ContinuousWithinAt, hg0]
      refine squeeze_zero_norm' (a := fun t : ℝ => t ^ (p + 1) * B) ?_ ?_
      · filter_upwards [self_mem_nhdsWithin] with s hs
        rcases eq_or_lt_of_le hs.1 with h0' | hpos'
        · subst h0'
          simp [hg, Real.zero_rpow (by linarith : p + 1 ≠ 0)]
        · rw [hg, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs,
            abs_of_nonneg (Real.rpow_nonneg hpos'.le _)]
          exact mul_le_mul_of_nonneg_left (hbd s ⟨hpos', hs.2⟩) (Real.rpow_nonneg hpos'.le _)
      · have : Continuous (fun t : ℝ => t ^ (p + 1) * B) :=
          (Real.continuous_rpow_const (by linarith)).mul continuous_const
        have h := this.tendsto 0
        rw [Real.zero_rpow (by linarith : p + 1 ≠ 0), zero_mul] at h
        exact h.mono_left nhdsWithin_le_nhds
    · have hc1 : ContinuousWithinAt φ (Ioc (0 : ℝ) 1) t := hcont t ⟨hpos, ht.2⟩
      have hnhds : Ioc (0 : ℝ) 1 ∈ 𝓝[Icc (0 : ℝ) 1] t := by
        refine mem_nhdsWithin.2 ⟨Ioi 0, isOpen_Ioi, hpos, ?_⟩
        intro s hs
        exact ⟨hs.1, hs.2.2⟩
      have hc2 : ContinuousWithinAt φ (Icc (0 : ℝ) 1) t := hc1.mono_of_mem_nhdsWithin hnhds
      exact ((Real.continuousAt_rpow_const _ _ (Or.inl hpos.ne')).continuousWithinAt).mul hc2
  -- the derivative of `g` on `(0,1)`
  have hgd : ∀ t ∈ Ioo (0 : ℝ) 1,
      HasDerivAt g ((p - 3) * (t ^ p * φ t) - t ^ p * Θ t) t := by
    intro t ht
    have h1 : HasDerivAt (fun s : ℝ => s ^ (p + 1)) ((p + 1) * t ^ p) t := by
      have := Real.hasDerivAt_rpow_const (x := t) (p := p + 1) (Or.inl ht.1.ne')
      simpa using this
    have h2 := h1.mul (hder t ht)
    refine HasDerivAt.congr_deriv h2 ?_
    have hne : t ≠ 0 := ht.1.ne'
    have : t ^ (p + 1) = t ^ p * t := by rw [Real.rpow_add_one hne]
    rw [this]
    field_simp
    ring
  have hint : IntervalIntegrable (fun t : ℝ => (p - 3) * (t ^ p * φ t) - t ^ p * Θ t)
      volume 0 1 := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one]
    exact (hφint.const_mul (p - 3)).sub hΘ
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le zero_le_one hgc hgd hint
  have hg1 : g 1 = φ 1 := by simp [hg]
  have hg0 : g 0 = 0 := by simp [hg, Real.zero_rpow (by linarith : p + 1 ≠ 0)]
  have h3 : ∫ t in Ioc (0 : ℝ) 1, ((p - 3) * (t ^ p * φ t) - t ^ p * Θ t) = φ 1 := by
    rw [← intervalIntegral.integral_of_le zero_le_one, hFTC, hg1, hg0, sub_zero]
  rw [integral_sub (hφint.const_mul (p - 3)) hΘ, integral_const_mul] at h3
  linarith

end UnforcedLeray.Short.PartIIIb.Concrete
