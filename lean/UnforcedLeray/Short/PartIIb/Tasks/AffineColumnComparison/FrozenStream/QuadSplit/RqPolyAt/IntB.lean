import UnforcedLeray.Short.PartIIb.Sub.PartIIb_G4_2_2_1_5
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.FrozenStream.QuadSplit.XGInt
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.FrozenStream.QuadSplit.PolyZpow
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.FrozenStream.QuadSplit.GaussTail
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.FrozenStream.QuadSplit.RqPolyAt.MulPoly

/-!
# Part II-b, task `PartII-b:G4/2/2/1/5/4`: `PolyIntB`

Source of record: `the November 2 reference manuscript`, lines 2349-2352.

Route: `B r = ∫_{(r,∞)} s⁻¹ q`. Order `0`: for `r ≥ 1`, `‖B r‖ ≤ ∫_{(1,∞)} ‖s⁻¹ q‖ < ∞`
(`xGInt`), a constant bound. Order `k+1`: `B' = -r⁻¹ q` on `(0,∞)` (`gt_hasDerivAt_tail`), so
`B^{(k+1)} = -(r⁻¹ q)^{(k)}` near each `r > 0`, polynomially bounded by `polyMulPoly` applied to
`r⁻¹ = r^(-1)` and `q`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

open UnforcedLeray.Blueprint

theorem polyIntB : UnforcedLeray.Short.IIb.PolyIntB := by
  intro q hq hS j hG i hi
  have hM : UnforcedLeray.Short.IIb.PolyMulPoly := polyMulPoly
  have hP : UnforcedLeray.Short.IIb.PolyZpow := polyZpow
  -- Gaussian derivatives of `q` are polynomially bounded (with exponent `0`)
  have hGP : ∀ m < j, PolyAt q m := by
    intro m hm
    obtain ⟨C, κ, hκ, hb⟩ := hG m hm
    refine ⟨|C|, 0, fun r hr => ?_⟩
    have hexp : Real.exp (-(κ * r ^ 2)) ≤ 1 :=
      Real.exp_le_one_iff.mpr (neg_nonpos.mpr (mul_nonneg hκ.le (sq_nonneg r)))
    have h2 : C * Real.exp (-(κ * r ^ 2)) ≤ |C| := by
      calc C * Real.exp (-(κ * r ^ 2)) ≤ |C| * Real.exp (-(κ * r ^ 2)) :=
            mul_le_mul_of_nonneg_right (le_abs_self C) (Real.exp_pos _).le
        _ ≤ |C| * 1 := mul_le_mul_of_nonneg_left hexp (abs_nonneg C)
        _ = |C| := mul_one _
    simpa using (hb r hr).trans h2
  have hzinv : (fun s : ℝ => (s : ℂ)⁻¹ * q s) = (fun s : ℝ => (s : ℂ) ^ (-1 : ℤ) * q s) := by
    funext s
    rw [zpow_neg_one]
  have hcont : ContinuousOn (fun s : ℝ => (s : ℂ)⁻¹ * q s) (Ioi (0 : ℝ)) := by
    rw [hzinv]
    exact ((hP (-1)).1.continuousOn).mul hS.continuousOn
  have hint : ∀ ρ : ℝ, 0 < ρ → IntegrableOn (fun s : ℝ => (s : ℂ)⁻¹ * q s) (Ioi ρ) :=
    fun ρ hρ => (xGInt q hq).2 ρ hρ
  -- order zero: a uniform bound on `[1,∞)`
  have hB0 : ∀ r : ℝ, 1 ≤ r →
      ‖∫ s in Ioi r, (s : ℂ)⁻¹ * q s‖ ≤ ∫ s in Ioi (1 : ℝ), ‖(s : ℂ)⁻¹ * q s‖ := by
    intro r hr
    refine (norm_integral_le_integral_norm _).trans ?_
    exact setIntegral_mono_set (hint 1 one_pos).norm
      (Filter.Eventually.of_forall fun x => norm_nonneg _)
      (Filter.Eventually.of_forall fun x (hx : x ∈ Ioi r) =>
        (Ioi_subset_Ioi hr hx : x ∈ Ioi (1 : ℝ)))
  rcases Nat.eq_zero_or_pos i with rfl | hipos
  · refine ⟨∫ s in Ioi (1 : ℝ), ‖(s : ℂ)⁻¹ * q s‖, 0, fun r hr => ?_⟩
    rw [iteratedDeriv_zero, pow_zero, mul_one]
    exact hB0 r hr
  · obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
    -- derivative of the tail integral on `(0,∞)`
    have hderiv : ∀ r : ℝ, 0 < r →
        deriv (fun ρ : ℝ => ∫ s in Ioi ρ, (s : ℂ)⁻¹ * q s) r = -((r : ℂ)⁻¹ * q r) :=
      fun r hr => (gt_hasDerivAt_tail hcont hint hr).deriv
    have hev : ∀ x : ℝ, 0 < x →
        deriv (fun ρ : ℝ => ∫ s in Ioi ρ, (s : ℂ)⁻¹ * q s) =ᶠ[𝓝 x]
          (fun r : ℝ => -((r : ℂ)⁻¹ * q r)) := by
      intro x hx
      filter_upwards [isOpen_Ioi.mem_nhds hx] with y hy
      exact hderiv y hy
    -- polynomial bound for `r⁻¹ q`, its orders `≤ k`
    have hG1 : PolyAt (fun r : ℝ => (r : ℂ) ^ (-1 : ℤ) * q r) k :=
      hM (fun r : ℝ => (r : ℂ) ^ (-1 : ℤ)) q (k + 1) (hP (-1)).1 hS
        (fun m _ => (hP (-1)).2 m) (fun m hm => hGP m (by omega)) k (by omega)
    have hGpoly : PolyAt (fun r : ℝ => (r : ℂ)⁻¹ * q r) k := by
      rw [hzinv]
      exact hG1
    obtain ⟨C, N, hb⟩ := hGpoly
    refine ⟨C, N, fun r hr => ?_⟩
    have hr0 : 0 < r := by linarith
    rw [iteratedDeriv_succ', Filter.EventuallyEq.iteratedDeriv_eq k (hev r hr0)]
    rw [show (fun r : ℝ => -((r : ℂ)⁻¹ * q r)) = -(fun r : ℝ => (r : ℂ)⁻¹ * q r) from rfl,
      iteratedDeriv_neg, norm_neg]
    exact hb r hr

end UnforcedLeray.Short.IIb
