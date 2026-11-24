import UnforcedLeray.Analysis.Sturm.FreeResolvent

/-!
# Actual energy estimate for the free real-mass resolvent

The estimates here are derived from the Green-kernel weak equation and
integration by parts for compactly supported L² data. They provide the norm
bound needed to extend the concrete convolution operator to all L² data.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped ComplexConjugate
namespace UnforcedLeray.Sturm
open NonUniqueEuler.Sob NonUniqueEuler.Sob.EnergyAux

theorem norm_psi0_uniform_le {L : ℝ} (hL : 0 ≤ L) {f : ℝ → ℂ}
    (hf : Integrable f) (x : ℝ) : ‖psi0 L f x‖ ≤ ∫ y, ‖f y‖ := by
  apply norm_integral_le_of_norm_le hf.norm
  filter_upwards [] with y
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (k0_pos _ _)]
  exact mul_le_of_le_one_left (norm_nonneg _) (k0_le_one hL _)

theorem exists_freeResolvent_bdd {L : ℝ} (hL : 0 < L) {f : ℝ → ℂ}
    (hf : Integrable f) : ∃ M, ∀ x, ‖freeResolvent L f x‖ ≤ M := by
  refine ⟨‖((((2 * L)⁻¹ : ℝ) : ℂ))‖ * (∫ y, ‖f y‖), fun x => ?_⟩
  rw [freeResolvent, norm_mul]
  exact mul_le_mul_of_nonneg_left (norm_psi0_uniform_le hL.le hf x) (norm_nonneg _)

section Energy
variable {L : ℝ} (hL : 0 < L) {f : ℝ → ℂ} (hf2 : MemLp f 2 volume)
  {a b : ℝ} (hfab : ∀ᵐ x, x ∉ Icc a b → f x = 0)
include hL hf2 hfab

/-- Integration by parts for the actual resolvent against its conjugate. -/
theorem integral_freeResolventDeriv_mul_conj :
    (∫ x, freeResolventDeriv L f x * conj (freeResolventDeriv L f x)) =
      -∫ x, freeResolventSecond L f x * conj (freeResolvent L f x) := by
  have hf := integrable_of_memLp_two hf2 hfab
  obtain ⟨M, hM⟩ := exists_freeResolvent_bdd hL hf
  have hφ : TestLike (fun x => conj (freeResolvent L f x))
      (fun x => conj (freeResolventDeriv L f x)) :=
    { deriv := fun x => (hasDerivAt_freeResolvent hL hf x).star
      int := integrable_conj (integrable_freeResolvent hL hf hfab)
      int' := integrable_conj (integrable_freeResolventDeriv hL hf hfab)
      bdd := ⟨M, fun x => by simpa only [Complex.norm_conj] using hM x⟩ }
  have hbdd : ∀ᵐ x, ‖conj (freeResolvent L f x)‖ ≤ M :=
    Eventually.of_forall fun x => by simpa only [Complex.norm_conj] using hM x
  have hmeas : AEStronglyMeasurable (fun x => conj (freeResolvent L f x)) :=
    (continuous_freeResolvent hL hf).star.aestronglyMeasurable
  exact integral_freeResolventDeriv_mul_deriv hL hf hφ (hf.mul_bdd hmeas hbdd)
    ((integrable_freeResolvent hL hf hfab).mul_bdd hmeas hbdd)

/-- The actual elliptic energy identity for every real positive mass. -/
theorem freeResolvent_energy_integral :
    (∫ x, ‖f x‖ ^ 2) = L ^ 4 * (∫ x, ‖freeResolvent L f x‖ ^ 2) +
      2 * L ^ 2 * (∫ x, ‖freeResolventDeriv L f x‖ ^ 2) +
      (∫ x, ‖freeResolventSecond L f x‖ ^ 2) := by
  have hf := integrable_of_memLp_two hf2 hfab
  have hu := memLp_freeResolvent hL hf hfab
  have h1 := memLp_freeResolventDeriv hL hf hfab
  have h2 := memLp_freeResolventSecond hL hf2 hfab
  have hpt : ∀ x, ‖f x‖ ^ 2 = ‖freeResolventSecond L f x‖ ^ 2 -
      2 * (L ^ 2) * (freeResolventSecond L f x * conj (freeResolvent L f x)).re +
      (L ^ 2) ^ 2 * ‖freeResolvent L f x‖ ^ 2 := by
    intro x
    rw [← norm_sub_real_mul_sq]
    have heq : freeResolventSecond L f x - ((L ^ 2 : ℝ) : ℂ) * freeResolvent L f x =
        -f x := by
      unfold freeResolventSecond
      push_cast
      ring
    rw [heq, norm_neg]
  have hprod : Integrable fun x => freeResolventSecond L f x * conj (freeResolvent L f x) := by
    have h := h2.integrable_mul hu.star
    simpa [Pi.mul_def] using h
  have hre : Integrable fun x =>
      (freeResolventSecond L f x * conj (freeResolvent L f x)).re := hprod.re
  have i2 := integrable_norm_sq h2
  have iu := integrable_norm_sq hu
  have hA : Integrable fun x => ‖freeResolventSecond L f x‖ ^ 2 -
      2 * (L ^ 2) * (freeResolventSecond L f x * conj (freeResolvent L f x)).re :=
    i2.sub (hre.const_mul _)
  simp_rw [hpt]
  rw [integral_add hA (iu.const_mul _), integral_sub i2 (hre.const_mul _),
    integral_const_mul, integral_const_mul]
  have hkey : (∫ x, (freeResolventSecond L f x * conj (freeResolvent L f x)).re) =
      -∫ x, ‖freeResolventDeriv L f x‖ ^ 2 := by
    have e1 : (∫ x, (freeResolventSecond L f x * conj (freeResolvent L f x)).re) =
        (∫ x, freeResolventSecond L f x * conj (freeResolvent L f x)).re := integral_re hprod
    have e2 : (∫ x, freeResolventDeriv L f x * conj (freeResolventDeriv L f x)) =
        ((∫ x, ‖freeResolventDeriv L f x‖ ^ 2 : ℝ) : ℂ) := by
      rw [← integral_complex_ofReal]
      congr 1
      funext x
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
    have e3 := integral_freeResolventDeriv_mul_conj hL hf2 hfab
    rw [e2] at e3
    have e4 : (∫ x, freeResolventSecond L f x * conj (freeResolvent L f x)) =
        -((∫ x, ‖freeResolventDeriv L f x‖ ^ 2 : ℝ) : ℂ) := by
      rw [e3]
      ring
    rw [e1, e4]
    simp
  rw [hkey]
  ring

/-- A support-independent squared L² bound for the actual Green operator. -/
theorem freeResolvent_integral_sq_bound :
    L ^ 4 * (∫ x, ‖freeResolvent L f x‖ ^ 2) ≤ ∫ x, ‖f x‖ ^ 2 := by
  rw [freeResolvent_energy_integral hL hf2 hfab]
  have h1 : 0 ≤ ∫ x, ‖freeResolventDeriv L f x‖ ^ 2 := integral_nonneg fun _ => sq_nonneg _
  have h2 : 0 ≤ ∫ x, ‖freeResolventSecond L f x‖ ^ 2 := integral_nonneg fun _ => sq_nonneg _
  have ht : 0 ≤ 2 * L ^ 2 * (∫ x, ‖freeResolventDeriv L f x‖ ^ 2) :=
    mul_nonneg (by positivity) h1
  linarith

/-- The exact `L⁻²` L² norm estimate needed for a continuous extension. -/
theorem l2_freeResolvent_le :
    l2 (freeResolvent L f) ≤ (L ^ 2)⁻¹ * l2 f := by
  have hf := integrable_of_memLp_two hf2 hfab
  have hu := memLp_freeResolvent hL hf hfab
  have hbound := freeResolvent_integral_sq_bound hL hf2 hfab
  rw [← l2_sq_eq_integral hu, ← l2_sq_eq_integral hf2] at hbound
  have hfn : 0 ≤ l2 f := ENNReal.toReal_nonneg
  have hun : 0 ≤ l2 (freeResolvent L f) := ENNReal.toReal_nonneg
  have hL2 : 0 < L ^ 2 := sq_pos_of_pos hL
  have hs : L ^ 2 * l2 (freeResolvent L f) ≤ l2 f := by
    nlinarith [sq_nonneg (L ^ 2 * l2 (freeResolvent L f) + l2 f)]
  exact (le_inv_mul_iff₀ hL2).mpr hs

end Energy
end UnforcedLeray.Sturm
