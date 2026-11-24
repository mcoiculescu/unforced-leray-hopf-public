import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_3

/-!
# `flatXiSmall : FlatXiSmall` (decomposition of `PartIII-b:C/flatset/col/3`, leaf 4)

Source of record `the November 2 reference manuscript` lines 4610, 4614-4615.
`ξ_B(s) = s^{-μ} ∫_{(0,s]} t^μ 𝒰(s,t) g_B(t) dt` (`xiD_apply`), with `‖𝒰(s,t)‖ ≤ C₁` on
`0 ≤ t ≤ s ≤ 1` (`TrainEvolution.locBdd 1`) and `‖g_B(t)‖ ≤ C t^{3/2}` (hypothesis).
The integrand is bounded by `(C₁C) t^{μ+3/2}`, whose integral over `(0,s]` is
`s^{μ+5/2}/(μ+5/2)` (`integral_rpow`); the factor `s^{-μ}` gives `s^{5/2}`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

theorem flatXiSmall : FlatXiSmall := by
  intro κ ν c m _ _ tr D μ B C hμ hG
  obtain ⟨C1, hC1⟩ := D.ev.locBdd 1
  have hC1nn : 0 ≤ C1 := le_trans (norm_nonneg (D.ev.U 0 0)) (hC1 0 0 le_rfl le_rfl zero_le_one)
  have hCnn : 0 ≤ C := by
    have h := hG 1 ⟨one_pos, le_rfl⟩
    rw [Real.one_rpow, mul_one] at h
    exact le_trans (norm_nonneg _) h
  have hden : (0 : ℝ) < μ + 3 / 2 + 1 := by linarith
  refine ⟨C1 * C / (μ + 3 / 2 + 1), ?_⟩
  intro s hs
  have hs0 : 0 < s := hs.1
  have hs1 : s ≤ 1 := hs.2
  -- pointwise bound of the integrand on (0, s]
  have hpt : ∀ t ∈ Ioc (0 : ℝ) s,
      ‖(t : ℂ) ^ (μ : ℂ) • (D.ev.U s t) (gBD D B t)‖ ≤ (C1 * C) * t ^ (μ + 3 / 2 : ℝ) := by
    intro t ht
    have ht0 : 0 < t := ht.1
    have hts : t ≤ s := ht.2
    have ht1 : t ≤ 1 := le_trans hts hs1
    have hn1 : ‖(t : ℂ) ^ (μ : ℂ)‖ = t ^ μ := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos ht0]
      simp
    rw [norm_smul, hn1]
    have hU : ‖(D.ev.U s t) (gBD D B t)‖ ≤ C1 * ‖gBD D B t‖ :=
      (ContinuousLinearMap.le_opNorm (D.ev.U s t) _).trans
        (mul_le_mul_of_nonneg_right (hC1 s t ht0.le hts hs1) (norm_nonneg _))
    have hg : ‖gBD D B t‖ ≤ C * t ^ (3 / 2 : ℝ) := hG t ⟨ht0, ht1⟩
    have hpow : t ^ μ * (C1 * (C * t ^ (3 / 2 : ℝ))) = (C1 * C) * t ^ (μ + 3 / 2 : ℝ) := by
      rw [Real.rpow_add ht0]
      ring
    calc t ^ μ * ‖(D.ev.U s t) (gBD D B t)‖
        ≤ t ^ μ * (C1 * ‖gBD D B t‖) :=
          mul_le_mul_of_nonneg_left hU (Real.rpow_nonneg ht0.le _)
      _ ≤ t ^ μ * (C1 * (C * t ^ (3 / 2 : ℝ))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hg hC1nn) (Real.rpow_nonneg ht0.le _)
      _ = (C1 * C) * t ^ (μ + 3 / 2 : ℝ) := hpow
  have hint : Integrable (fun t : ℝ => (C1 * C) * t ^ (μ + 3 / 2 : ℝ))
      (volume.restrict (Ioc 0 s)) := by
    have h1 : IntervalIntegrable (fun t : ℝ => t ^ (μ + 3 / 2 : ℝ)) volume 0 s :=
      intervalIntegral.intervalIntegrable_rpow' (by linarith)
    exact h1.1.const_mul (C1 * C)
  have hae : ∀ᵐ t : ℝ ∂(volume.restrict (Ioc (0 : ℝ) s)),
      ‖(t : ℂ) ^ (μ : ℂ) • (D.ev.U s t) (gBD D B t)‖ ≤ (C1 * C) * t ^ (μ + 3 / 2 : ℝ) :=
    (ae_restrict_mem measurableSet_Ioc).mono fun t ht => hpt t ht
  have hJ : ∫ t in Ioc (0 : ℝ) s, t ^ (μ + 3 / 2 : ℝ) = s ^ (μ + 3 / 2 + 1) / (μ + 3 / 2 + 1) := by
    rw [← intervalIntegral.integral_of_le hs0.le,
      integral_rpow (Or.inl (by linarith))]
    rw [Real.zero_rpow hden.ne', sub_zero]
  have hexp : s ^ (-μ) * s ^ (μ + 3 / 2 + 1) = s ^ (5 / 2 : ℝ) := by
    rw [← Real.rpow_add hs0]
    congr 1
    ring
  have hscal : ‖(s : ℂ) ^ (-(μ : ℂ))‖ = s ^ (-μ) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hs0]
    simp
  rw [xiD_apply, norm_smul, hscal]
  calc s ^ (-μ) * ‖∫ t in Ioc 0 s, (t : ℂ) ^ (μ : ℂ) • (D.ev.U s t) (gBD D B t)‖
      ≤ s ^ (-μ) * ∫ t in Ioc (0 : ℝ) s, (C1 * C) * t ^ (μ + 3 / 2 : ℝ) :=
        mul_le_mul_of_nonneg_left (norm_integral_le_of_norm_le hint hae)
          (Real.rpow_nonneg hs0.le _)
    _ = s ^ (-μ) * ((C1 * C) * (s ^ (μ + 3 / 2 + 1) / (μ + 3 / 2 + 1))) := by
        rw [integral_const_mul, hJ]
    _ = (C1 * C / (μ + 3 / 2 + 1)) * (s ^ (-μ) * s ^ (μ + 3 / 2 + 1)) := by ring
    _ = (C1 * C / (μ + 3 / 2 + 1)) * s ^ (5 / 2 : ℝ) := by rw [hexp]

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
