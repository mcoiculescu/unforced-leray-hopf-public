import UnforcedLeray.Short.PartIIb.Sub.T15_2_10

/-!
# Part II-b, task `PartII-b:T15/2/10/3`: pointwise Cauchy-Schwarz for the averaged slice

Source: `the November 2 reference manuscript`, lines 1975-1979.
Proves `LogAcCS` (`Sub/T15_2_10.lean`): `‖h⁻¹ ∫_0^h f‖ₑ² ≤ |h|⁻¹ ∫⁻_{uIoc 0 h} ‖f‖ₑ²`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal

namespace UnforcedLeray.Short.IIb

/-- Enorm of an interval integral is bounded by the lintegral of the enorm over `uIoc`. -/
theorem logAcCS_enorm_le (h : ℝ) (f : ℝ → ℂ) :
    ‖∫ σ in (0 : ℝ)..h, f σ‖ₑ ≤ ∫⁻ σ in Set.uIoc (0 : ℝ) h, ‖f σ‖ₑ := by
  rcases le_total 0 h with h0 | h0
  · rw [intervalIntegral.integral_of_le h0, Set.uIoc_of_le h0]
    exact enorm_integral_le_lintegral_enorm f
  · rw [intervalIntegral.integral_symm, enorm_neg, intervalIntegral.integral_of_le h0,
      Set.uIoc_of_ge h0]
    exact enorm_integral_le_lintegral_enorm f

/-- Cauchy-Schwarz for lintegrals on a set: `(∫⁻_S g)² ≤ vol(S) ∫⁻_S g²`. -/
theorem logAcCS_cs (S : Set ℝ) (g : ℝ → ℝ≥0∞) (hg : AEMeasurable g (volume.restrict S)) :
    (∫⁻ σ in S, g σ) ^ 2 ≤ volume S * ∫⁻ σ in S, g σ ^ 2 := by
  have key := ENNReal.lintegral_mul_le_Lp_mul_Lq (volume.restrict S) (p := 2) (q := 2)
    Real.HolderConjugate.two_two (f := fun _ => (1 : ℝ≥0∞)) aemeasurable_const hg
  have hsq : ∀ x y : ℝ≥0∞, ((x ^ (1 / (2 : ℝ))) * (y ^ (1 / (2 : ℝ)))) ^ 2 = x * y := by
    intro x y
    rw [mul_pow, ← ENNReal.rpow_natCast, ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul,
      ← ENNReal.rpow_mul]
    norm_num
  have h1 : (∫⁻ σ in S, g σ) ^ 2 ≤ ((∫⁻ a, (fun _ => (1 : ℝ≥0∞)) a ^ (2 : ℝ) ∂(volume.restrict S)) ^ (1 / (2 : ℝ)) *
      (∫⁻ a, g a ^ (2 : ℝ) ∂(volume.restrict S)) ^ (1 / (2 : ℝ))) ^ 2 := by
    gcongr
    simpa using key
  rw [hsq] at h1
  simpa [ENNReal.rpow_two, Measure.restrict_apply_univ] using h1

/-- **Leaf `PartII-b:T15/2/10/3`** (pointwise Cauchy-Schwarz). For `f` interval integrable on
`[0, h]`: `‖h⁻¹ ∫_0^h f‖ₑ² ≤ |h|⁻¹ ∫⁻_{uIoc 0 h} ‖f‖ₑ²`. -/
theorem logAcCS : UnforcedLeray.Short.IIb.LogAcCS := by
  intro h f hf
  by_cases h0 : h = 0
  · subst h0
    simp
  · have habs : 0 < |h| := abs_pos.mpr h0
    have hnorm : ‖(h⁻¹ : ℝ) • ∫ σ in (0 : ℝ)..h, f σ‖ₑ =
        ENNReal.ofReal |h|⁻¹ * ‖∫ σ in (0 : ℝ)..h, f σ‖ₑ := by
      rw [enorm_smul, Real.enorm_eq_ofReal_abs, abs_inv]
    have hc : ENNReal.ofReal |h|⁻¹ ^ 2 * ENNReal.ofReal |h| = ENNReal.ofReal |h|⁻¹ := by
      rw [← ENNReal.ofReal_pow (by positivity), ← ENNReal.ofReal_mul (by positivity)]
      congr 1
      field_simp
    have hV : volume (Set.uIoc (0 : ℝ) h) = ENNReal.ofReal |h| := by
      rw [Real.volume_uIoc, sub_zero]
    have hmeas : AEMeasurable (fun σ => ‖f σ‖ₑ) (volume.restrict (Set.uIoc (0 : ℝ) h)) :=
      hf.def'.aestronglyMeasurable.enorm
    have hCS := logAcCS_cs (Set.uIoc (0 : ℝ) h) (fun σ => ‖f σ‖ₑ) hmeas
    rw [hV] at hCS
    have hI := logAcCS_enorm_le h f
    have hI2 : ‖∫ σ in (0 : ℝ)..h, f σ‖ₑ ^ 2 ≤ ENNReal.ofReal |h| *
        ∫⁻ σ in Set.uIoc (0 : ℝ) h, ‖f σ‖ₑ ^ 2 := by
      refine le_trans ?_ hCS
      gcongr
    rw [hnorm, mul_pow]
    calc (ENNReal.ofReal |h|⁻¹) ^ 2 * ‖∫ σ in (0 : ℝ)..h, f σ‖ₑ ^ 2
        ≤ (ENNReal.ofReal |h|⁻¹) ^ 2 * (ENNReal.ofReal |h| *
            ∫⁻ σ in Set.uIoc (0 : ℝ) h, ‖f σ‖ₑ ^ 2) := by gcongr
      _ = ENNReal.ofReal |h|⁻¹ * ∫⁻ σ in Set.uIoc (0 : ℝ) h, ‖f σ‖ₑ ^ 2 := by
        rw [← mul_assoc, hc]

end UnforcedLeray.Short.IIb
