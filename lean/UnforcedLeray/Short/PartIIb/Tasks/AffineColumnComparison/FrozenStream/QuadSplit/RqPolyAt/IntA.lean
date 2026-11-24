import UnforcedLeray.Short.PartIIb.Sub.PartIIb_G4_2_2_1_5
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.FrozenStream.QuadSplit.XGInt
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.FrozenStream.QuadSplit.PolyZpow
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.FrozenStream.QuadSplit.RqPolyAt.MulPoly

/-!
# Part II-b, task `PartII-b:G4/2/2/1/5/3`: `PolyIntA`

Source of record: `the November 2 reference manuscript`, lines 2349-2352.

Route: `A r = ∫₀^r s³ q`. Order `0`: `‖A r‖ ≤ ∫_{(0,∞)} ‖s³ q‖ < ∞` (`xGInt`), a constant bound.
Order `k+1`: `A' = r³ q` on `(0,∞)` (`integral_hasDerivAt_right`), so `A^{(k+1)} = (r³ q)^{(k)}`
near each `r > 0`, which is polynomially bounded by the Leibniz rule `polyMulPoly` applied to the
polynomial `r³` and `q`, whose orders `< k+1` are Gaussian, hence polynomially, bounded.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

open UnforcedLeray.Blueprint

theorem polyIntA : UnforcedLeray.Short.IIb.PolyIntA := by
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
  have hfc : ContinuousOn (fun s : ℝ => (s : ℂ) ^ 3 * q s) (Ioi 0) :=
    ContinuousOn.mul (Complex.continuous_ofReal.pow 3).continuousOn hS.continuousOn
  have hfI : IntegrableOn (fun s : ℝ => (s : ℂ) ^ 3 * q s) (Ioi 0) := (xGInt q hq).1
  -- order zero: a uniform bound on `[0,∞)`
  have hA0 : ∀ r : ℝ, 0 < r →
      ‖∫ s in (0 : ℝ)..r, (s : ℂ) ^ 3 * q s‖ ≤ ∫ s in Ioi (0 : ℝ), ‖(s : ℂ) ^ 3 * q s‖ := by
    intro r hr
    refine (intervalIntegral.norm_integral_le_integral_norm hr.le).trans ?_
    rw [intervalIntegral.integral_of_le hr.le]
    exact setIntegral_mono_set hfI.norm (Filter.Eventually.of_forall fun x => norm_nonneg _)
      (Filter.Eventually.of_forall fun x (hx : x ∈ Ioc (0 : ℝ) r) => (Ioc_subset_Ioi_self hx :
        x ∈ Ioi (0 : ℝ)))
  rcases Nat.eq_zero_or_pos i with rfl | hipos
  · refine ⟨∫ s in Ioi (0 : ℝ), ‖(s : ℂ) ^ 3 * q s‖, 0, fun r hr => ?_⟩
    rw [iteratedDeriv_zero, pow_zero, mul_one]
    exact hA0 r (by linarith)
  · obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
    -- derivative of the Volterra integral on `(0,∞)`
    have hderiv : ∀ r : ℝ, 0 < r →
        HasDerivAt (fun u : ℝ => ∫ s in (0 : ℝ)..u, (s : ℂ) ^ 3 * q s) ((r : ℂ) ^ 3 * q r) r := by
      intro r hr
      have hII : IntervalIntegrable (fun s : ℝ => (s : ℂ) ^ 3 * q s) volume 0 r := by
        rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hr.le]
        exact hfI.mono_set Ioc_subset_Ioi_self
      have hmeas : StronglyMeasurableAtFilter (fun s : ℝ => (s : ℂ) ^ 3 * q s) (𝓝 r) :=
        hfc.stronglyMeasurableAtFilter isOpen_Ioi r hr
      exact intervalIntegral.integral_hasDerivAt_right hII hmeas
        (hfc.continuousAt (Ioi_mem_nhds hr))
    have hev : ∀ x : ℝ, 0 < x →
        deriv (fun u : ℝ => ∫ s in (0 : ℝ)..u, (s : ℂ) ^ 3 * q s) =ᶠ[𝓝 x]
          (fun r : ℝ => (r : ℂ) ^ 3 * q r) := by
      intro x hx
      filter_upwards [isOpen_Ioi.mem_nhds hx] with y hy
      exact (hderiv y hy).deriv
    -- polynomial bound for `r³ q`, its orders `≤ k`
    have hfun : (fun r : ℝ => (r : ℂ) ^ 3 * q r) = (fun r : ℝ => (r : ℂ) ^ (3 : ℤ) * q r) := by
      funext r
      simp
    have hG3 : PolyAt (fun r : ℝ => (r : ℂ) ^ (3 : ℤ) * q r) k :=
      hM (fun r : ℝ => (r : ℂ) ^ (3 : ℤ)) q (k + 1) ((hP 3).1) hS
        (fun m _ => (hP 3).2 m) (fun m hm => hGP m (by omega)) k (by omega)
    have hGpoly : PolyAt (fun r : ℝ => (r : ℂ) ^ 3 * q r) k := by
      rw [hfun]
      exact hG3
    obtain ⟨C, N, hb⟩ := hGpoly
    refine ⟨C, N, fun r hr => ?_⟩
    have hr0 : 0 < r := by linarith
    rw [iteratedDeriv_succ', Filter.EventuallyEq.iteratedDeriv_eq k (hev r hr0)]
    exact hb r hr

end UnforcedLeray.Short.IIb
