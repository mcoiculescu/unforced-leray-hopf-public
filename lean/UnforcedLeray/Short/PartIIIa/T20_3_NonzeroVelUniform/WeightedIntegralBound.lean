import UnforcedLeray.Short.PartIIIa.Sub.T20_3

/-!
# Part III-a, task `PartIII-a:T20/3`, leaf `/8`: `WeightedIntegralBound`

Proves `UnforcedLeray.Short.IIIa.CTE.T20_3.WeightedIntegralBound` (defined in
`Sub/T20_3.lean`). Source of record: `the November 2 reference manuscript`,
lines 3236-3240 (low frequencies of modulus at most one against high frequencies).

Proof sketch. Write `w ξ = κ² + (2πξ)² > 0`.
* If `|κ| ≥ 1`, then `w ξ ≥ 1`, so `φ ξ / w ξ ≤ φ ξ` pointwise.
* If `|κ| < 1`, let `Lo = [-(1/(2π)), 1/(2π)]`, a set of measure `1/π`. A.e. the integrand is
  bounded by `φ ξ + 2A² · 1_{Lo} ξ`: on `Lo`, `φ ξ ≤ A²(|κ| + |2πξ|)²` and
  `(a + b)² ≤ 2(a² + b²)` give `φ ξ / w ξ ≤ 2A²`; off `Lo`, `(2πξ)² ≥ 1`, so `w ξ ≥ 1`
  and `φ ξ / w ξ ≤ φ ξ`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology FourierTransform
open scoped ENNReal InnerProductSpace Real

namespace UnforcedLeray.Short.IIIa.CTE.T20_3

/-- **Low/high frequency split** (task `/8`; SP 3238-3240). The Prop `WeightedIntegralBound`
is proved here. -/
theorem weightedIntegralBound : WeightedIntegralBound := by
  unfold WeightedIntegralBound
  intro κ A φ hκ hA hφ hφnn hbound
  have hκ2 : 0 < κ ^ 2 := lt_of_le_of_ne (sq_nonneg κ) (Ne.symm (pow_ne_zero 2 hκ))
  have hw_pos : ∀ ξ : ℝ, 0 < κ ^ 2 + (2 * π * ξ) ^ 2 := fun ξ =>
    add_pos_of_pos_of_nonneg hκ2 (sq_nonneg _)
  have hnn : 0 ≤ᵐ[volume] (fun ξ : ℝ => φ ξ / (κ ^ 2 + (2 * π * ξ) ^ 2)) :=
    ae_of_all _ fun ξ => div_nonneg (hφnn ξ) (hw_pos ξ).le
  by_cases hκ1 : |κ| < 1
  · -- Case `|κ| < 1`: the low frequencies `|2πξ| ≤ 1` carry the constant `2A²/π`.
    rw [if_pos hκ1]
    obtain ⟨Lo, hLo⟩ : ∃ Lo : Set ℝ, Lo = Set.Icc (-(1 / (2 * π))) (1 / (2 * π)) :=
      ⟨_, rfl⟩
    have hπ2 : (0 : ℝ) < 2 * π := by positivity
    have hkey : 2 * π * (1 / (2 * π)) = 1 := mul_one_div_cancel hπ2.ne'
    have hLoMeas : MeasurableSet Lo := by
      rw [hLo]
      exact measurableSet_Icc
    have hvol : (volume Lo).toReal = 1 / π := by
      rw [hLo, Real.volume_Icc, ENNReal.toReal_ofReal]
      · ring
      · rw [sub_neg_eq_add]
        positivity
    have hLoFin : volume Lo ≠ ⊤ := by
      rw [hLo, Real.volume_Icc]
      exact ENNReal.ofReal_ne_top
    have hind : Integrable (Lo.indicator (fun _ : ℝ => 2 * A ^ 2)) volume := by
      rw [integrable_indicator_iff hLoMeas]
      exact integrableOn_const hLoFin
    have hind_eq : ∫ ξ : ℝ, Lo.indicator (fun _ : ℝ => 2 * A ^ 2) ξ = 2 * A ^ 2 / π := by
      rw [integral_indicator_const _ hLoMeas, smul_eq_mul, measureReal_def, hvol]
      ring
    have hpt : ∀ ξ : ℝ, φ ξ ≤ A ^ 2 * (|κ| + 2 * π * |ξ|) ^ 2 →
        φ ξ / (κ ^ 2 + (2 * π * ξ) ^ 2) ≤ φ ξ + Lo.indicator (fun _ : ℝ => 2 * A ^ 2) ξ := by
      intro ξ hξ
      by_cases hmem : ξ ∈ Lo
      · simp only [Set.indicator_of_mem hmem]
        have hw := hw_pos ξ
        have hb : |2 * π * ξ| = 2 * π * |ξ| := by
          rw [abs_mul, abs_of_pos hπ2]
        have hsq : (2 * π * ξ) ^ 2 = (2 * π * |ξ|) ^ 2 := by
          rw [← sq_abs (2 * π * ξ), hb]
        have key2 : (|κ| + 2 * π * |ξ|) ^ 2 ≤ 2 * (κ ^ 2 + (2 * π * ξ) ^ 2) := by
          rw [hsq]
          nlinarith [sq_nonneg (|κ| - 2 * π * |ξ|), sq_abs κ]
        have h1 : φ ξ / (κ ^ 2 + (2 * π * ξ) ^ 2) ≤ 2 * A ^ 2 := by
          rw [div_le_iff₀ hw]
          nlinarith [mul_le_mul_of_nonneg_left key2 (sq_nonneg A), hξ]
        linarith [hφnn ξ]
      · have hout : ¬ (ξ ∈ Set.Icc (-(1 / (2 * π))) (1 / (2 * π))) := by
          rw [← hLo]
          exact hmem
        simp only [Set.indicator_of_notMem hmem, add_zero]
        simp only [Set.mem_Icc, not_and_or, not_le] at hout
        have ht : 1 ≤ (2 * π * ξ) ^ 2 := by
          rcases hout with h | h
          · have h' : 2 * π * ξ < -1 := by
              linarith [mul_lt_mul_of_pos_left h hπ2]
            nlinarith
          · have h' : 1 < 2 * π * ξ := by
              linarith [mul_lt_mul_of_pos_left h hπ2]
            nlinarith
        have hw1 : 1 ≤ κ ^ 2 + (2 * π * ξ) ^ 2 := by nlinarith [sq_nonneg κ]
        exact div_le_self (hφnn ξ) hw1
    have hae : ∀ᵐ ξ : ℝ, φ ξ / (κ ^ 2 + (2 * π * ξ) ^ 2) ≤
        φ ξ + Lo.indicator (fun _ : ℝ => 2 * A ^ 2) ξ := by
      filter_upwards [hbound] with ξ hξ
      exact hpt ξ hξ
    have hgi : Integrable (fun ξ : ℝ => φ ξ + Lo.indicator (fun _ : ℝ => 2 * A ^ 2) ξ) volume :=
      hφ.add hind
    have hmono := integral_mono_of_nonneg hnn hgi hae
    have hsplit : ∫ ξ : ℝ, (φ ξ + Lo.indicator (fun _ : ℝ => 2 * A ^ 2) ξ) =
        (∫ ξ : ℝ, φ ξ) + ∫ ξ : ℝ, Lo.indicator (fun _ : ℝ => 2 * A ^ 2) ξ :=
      integral_add hφ hind
    rw [hsplit, hind_eq] at hmono
    exact hmono
  · -- Case `|κ| ≥ 1`: the weight is at least one, so the integrand is dominated by `φ`.
    rw [if_neg hκ1, add_zero]
    have hκ1' : 1 ≤ |κ| := not_lt.mp hκ1
    have hκsq : 1 ≤ κ ^ 2 := by nlinarith [sq_abs κ, abs_nonneg κ]
    refine integral_mono_of_nonneg hnn hφ (ae_of_all _ fun ξ => ?_)
    exact div_le_self (hφnn ξ) (by nlinarith [sq_nonneg (2 * π * ξ)])

end UnforcedLeray.Short.IIIa.CTE.T20_3
