import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Sub.PositiveKernel

/-!
# Separation of the source radius from the output radius (source 3997-3998)

Proves `farSeparation_holds : FarSeparation` (defined in `Sub/PositiveKernel.lean`).
If `|y'| = R/√s`, the mask `e^δ s < R²/|z'|²` holds, and `0 < l < 1`, then
`|y - l z| ≥ (1 - e^{-δ/2}) R/√s`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory UnforcedLeray.Axi Set
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.NearInst.Masked

open UnforcedLeray.Short.PartIIIb.NearInst

/-- **Separation** (source 3997-3998). -/
theorem farSeparation_holds : FarSeparation := by
  intro R δ s hR hδ hs y z l hl0 hl1 hy hmask
  obtain ⟨ρ, hρdef⟩ : ∃ ρ : ℝ, ρ = R / Real.sqrt s := ⟨_, rfl⟩
  rw [← hρdef]
  have hρpos : 0 < ρ := by
    rw [hρdef]
    exact div_pos hR (Real.sqrt_pos.mpr hs)
  have hρs : ρ ^ 2 * s = R ^ 2 := by
    rw [hρdef, div_pow, Real.sq_sqrt hs.le, div_mul_cancel₀ _ hs.ne']
  have hρ2 : ρ ^ 2 = y 0 ^ 2 + y 1 ^ 2 := by
    have hy' : Real.sqrt (y 0 ^ 2 + y 1 ^ 2) = ρ := by
      rw [hρdef]
      exact hy
    rw [← hy', Real.sq_sqrt (by positivity)]
  -- the mask forces `z'` to be nonzero
  have hq : 0 < z 0 ^ 2 + z 1 ^ 2 := by
    by_contra hcon
    have h0 : z 0 ^ 2 + z 1 ^ 2 = 0 := le_antisymm (not_lt.mp hcon) (by positivity)
    rw [h0, div_zero] at hmask
    have := mul_pos (Real.exp_pos δ) hs
    linarith
  have hm2 : Real.exp δ * s * (z 0 ^ 2 + z 1 ^ 2) < R ^ 2 := (lt_div_iff₀ hq).mp hmask
  obtain ⟨w, hwdef⟩ : ∃ w : ℝ, w = Real.sqrt (z 0 ^ 2 + z 1 ^ 2) := ⟨_, rfl⟩
  have hw2 : w ^ 2 = z 0 ^ 2 + z 1 ^ 2 := by
    rw [hwdef, Real.sq_sqrt (by positivity)]
  have hw0 : 0 ≤ w := by
    rw [hwdef]
    exact Real.sqrt_nonneg _
  -- `|z'| < e^{-δ/2} ρ`
  have h4 : s * (Real.exp δ * (z 0 ^ 2 + z 1 ^ 2)) < s * ρ ^ 2 := by
    linarith [hm2, hρs]
  have h4' : Real.exp δ * (z 0 ^ 2 + z 1 ^ 2) < ρ ^ 2 := lt_of_mul_lt_mul_left h4 hs.le
  have ht : Real.exp (-δ / 2) ^ 2 * Real.exp δ = 1 := by
    rw [sq, ← Real.exp_add, ← Real.exp_add, show -δ / 2 + -δ / 2 + δ = 0 by ring,
      Real.exp_zero]
  have h5 : Real.exp (-δ / 2) ^ 2 * (Real.exp δ * (z 0 ^ 2 + z 1 ^ 2)) <
      Real.exp (-δ / 2) ^ 2 * ρ ^ 2 :=
    mul_lt_mul_of_pos_left h4' (by positivity)
  have e1 : Real.exp (-δ / 2) ^ 2 * (Real.exp δ * (z 0 ^ 2 + z 1 ^ 2)) = z 0 ^ 2 + z 1 ^ 2 := by
    calc Real.exp (-δ / 2) ^ 2 * (Real.exp δ * (z 0 ^ 2 + z 1 ^ 2))
        = (Real.exp (-δ / 2) ^ 2 * Real.exp δ) * (z 0 ^ 2 + z 1 ^ 2) := by ring
      _ = z 0 ^ 2 + z 1 ^ 2 := by rw [ht, one_mul]
  have hsq : w ^ 2 < (Real.exp (-δ / 2) * ρ) ^ 2 := by
    rw [hw2, mul_pow]
    linarith [h5, e1]
  have hpos : 0 < Real.exp (-δ / 2) * ρ := by positivity
  have hwlt : w < Real.exp (-δ / 2) * ρ :=
    (pow_lt_pow_iff_left₀ hw0 hpos.le two_ne_zero).mp hsq
  -- Cauchy-Schwarz for the first two coordinates
  have hCS : y 0 * z 0 + y 1 * z 1 ≤ ρ * w := by
    have hsq2 : (y 0 * z 0 + y 1 * z 1) ^ 2 ≤ (ρ * w) ^ 2 := by
      rw [mul_pow, hρ2, hw2]
      nlinarith [sq_nonneg (y 0 * z 1 - y 1 * z 0)]
    calc y 0 * z 0 + y 1 * z 1 ≤ |y 0 * z 0 + y 1 * z 1| := le_abs_self _
      _ = Real.sqrt ((y 0 * z 0 + y 1 * z 1) ^ 2) := (Real.sqrt_sq_eq_abs _).symm
      _ ≤ Real.sqrt ((ρ * w) ^ 2) := Real.sqrt_le_sqrt hsq2
      _ = ρ * w := Real.sqrt_sq (by positivity)
  -- reverse triangle inequality in the first two coordinates
  have key : (y 0 - l * z 0) ^ 2 + (y 1 - l * z 1) ^ 2 - (ρ - l * w) ^ 2 =
      2 * l * (ρ * w - (y 0 * z 0 + y 1 * z 1)) := by
    linear_combination (-l ^ 2) * hw2 + (-1 : ℝ) * hρ2
  have h2l : 0 ≤ 2 * l * (ρ * w - (y 0 * z 0 + y 1 * z 1)) :=
    mul_nonneg (by positivity) (sub_nonneg.mpr hCS)
  have hineq : (ρ - l * w) ^ 2 ≤ (y 0 - l * z 0) ^ 2 + (y 1 - l * z 1) ^ 2 := by
    linarith [key, h2l]
  have hA : ρ - l * w ≤ Real.sqrt ((y 0 - l * z 0) ^ 2 + (y 1 - l * z 1) ^ 2) := by
    calc ρ - l * w ≤ |ρ - l * w| := le_abs_self _
      _ = Real.sqrt ((ρ - l * w) ^ 2) := (Real.sqrt_sq_eq_abs _).symm
      _ ≤ _ := Real.sqrt_le_sqrt hineq
  -- the Euclidean norm dominates the norm of the first two coordinates
  have hnorm : Real.sqrt ((y 0 - l * z 0) ^ 2 + (y 1 - l * z 1) ^ 2) ≤ ‖y - l • z‖ := by
    rw [EuclideanSpace.norm_eq, Fin.sum_univ_three]
    apply Real.sqrt_le_sqrt
    simp only [PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul, Real.norm_eq_abs, sq_abs]
    linarith [sq_nonneg (y 2 - l * z 2)]
  have hfinal : (1 - Real.exp (-δ / 2)) * ρ ≤ ρ - l * w := by
    have h1 : l * w ≤ w := mul_le_of_le_one_left hw0 hl1.le
    have h2 : (1 - Real.exp (-δ / 2)) * ρ = ρ - Real.exp (-δ / 2) * ρ := by ring
    rw [h2]
    linarith
  linarith [hA, hnorm, hfinal]

end UnforcedLeray.Short.PartIIIb.NearInst.Masked
