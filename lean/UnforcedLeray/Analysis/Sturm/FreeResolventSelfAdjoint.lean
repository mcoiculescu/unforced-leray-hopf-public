import UnforcedLeray.Analysis.Sturm.FreeResolventOperator
import Mathlib.Analysis.InnerProductSpace.Positive

/-!
# Selfadjointness of the actual free Green resolvent

Symmetry of the explicit real even convolution kernel first gives symmetry on
the dense compact-support L² domain. Continuity of the bounded extension then
proves selfadjointness on the whole Hilbert space. No spectral hypothesis is
part of the construction.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped ComplexConjugate InnerProductSpace
namespace UnforcedLeray.Sturm

variable {L : ℝ} (hL : 0 < L)
include hL

theorem freeResolventOperator_symmetric_compact (f g : compactL2) :
    ⟪freeResolventOperator hL (f : ComplexL2), (g : ComplexL2)⟫_ℂ =
      ⟪(f : ComplexL2), freeResolventOperator hL (g : ComplexL2)⟫_ℂ := by
  calc
    ⟪freeResolventOperator hL (f : ComplexL2), (g : ComplexL2)⟫_ℂ =
        ∫ x, (g : ComplexL2) x * conj (freeResolvent L (f : ComplexL2) x) := by
      rw [L2.inner_def]
      apply integral_congr_ae
      filter_upwards [coeFn_freeResolventOperator_on_compact hL f] with x hx
      simp only [RCLike.inner_apply, hx]
    _ = ∫ x, freeResolvent L (g : ComplexL2) x * conj ((f : ComplexL2) x) :=
      (integral_freeResolvent_mul_conj hL (CompactL2.integrable g) (CompactL2.integrable f)).symm
    _ = ⟪(f : ComplexL2), freeResolventOperator hL (g : ComplexL2)⟫_ℂ := by
      rw [L2.inner_def]
      apply integral_congr_ae
      filter_upwards [coeFn_freeResolventOperator_on_compact hL g] with x hx
      simp only [RCLike.inner_apply, hx]

/-- The actual Green resolvent is selfadjoint on all complex Lebesgue L². -/
theorem freeResolventOperator_isSelfAdjoint : IsSelfAdjoint (freeResolventOperator hL) := by
  apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
  intro f g
  change ⟪freeResolventOperator hL f, g⟫_ℂ = ⟪f, freeResolventOperator hL g⟫_ℂ
  apply denseRange_compactL2_subtypeL.induction_on₂
    (p := fun u v => ⟪freeResolventOperator hL u, v⟫_ℂ =
      ⟪u, freeResolventOperator hL v⟫_ℂ)
    (isClosed_eq (by fun_prop) (by fun_prop))
  exact fun u v => freeResolventOperator_symmetric_compact hL u v

/-- The positive quadratic pairing follows from the actual weak equation and integration by parts. -/
theorem freeResolvent_pairing_energy {f : ℝ → ℂ} (hf2 : MemLp f 2 volume)
    {a b : ℝ} (hfab : ∀ᵐ x, x ∉ Icc a b → f x = 0) :
    (∫ x, f x * conj (freeResolvent L f x)) =
      (((∫ x, ‖freeResolventDeriv L f x‖ ^ 2) +
        L ^ 2 * (∫ x, ‖freeResolvent L f x‖ ^ 2) : ℝ) : ℂ) := by
  have hf := NonUniqueEuler.Sob.EnergyAux.integrable_of_memLp_two hf2 hfab
  have hu := memLp_freeResolvent hL hf hfab
  have huprod : Integrable (fun x => freeResolvent L f x * conj (freeResolvent L f x)) := by
    simpa [Pi.mul_def] using hu.integrable_mul hu.star
  have hfprod : Integrable (fun x => f x * conj (freeResolvent L f x)) := by
    simpa [Pi.mul_def] using hf2.integrable_mul hu.star
  have hsplit : (∫ x, freeResolventSecond L f x * conj (freeResolvent L f x)) =
      (L : ℂ) ^ 2 * (∫ x, freeResolvent L f x * conj (freeResolvent L f x)) -
        (∫ x, f x * conj (freeResolvent L f x)) := by
    simp only [freeResolventSecond, sub_mul, mul_assoc]
    rw [integral_sub (huprod.const_mul _) hfprod, integral_const_mul]
  have hibp := integral_freeResolventDeriv_mul_conj hL hf2 hfab
  rw [hsplit] at hibp
  have hinorm (g : ℝ → ℂ) :
      (∫ x, g x * conj (g x)) = ((∫ x, ‖g x‖ ^ 2 : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    apply integral_congr_ae
    exact Eventually.of_forall fun x => by
      change g x * conj (g x) = ((‖g x‖ ^ 2 : ℝ) : ℂ)
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  calc
    (∫ x, f x * conj (freeResolvent L f x)) =
        (∫ x, freeResolventDeriv L f x * conj (freeResolventDeriv L f x)) +
          (L : ℂ) ^ 2 * (∫ x, freeResolvent L f x * conj (freeResolvent L f x)) := by
      linear_combination -hibp
    _ = _ := by rw [hinorm, hinorm]; push_cast; rfl

theorem freeResolventOperator_pairing_energy_compact (f : compactL2) :
    ⟪freeResolventOperator hL (f : ComplexL2), (f : ComplexL2)⟫_ℂ =
      (((∫ x, ‖freeResolventDeriv L (f : ComplexL2) x‖ ^ 2) +
        L ^ 2 * (∫ x, ‖freeResolvent L (f : ComplexL2) x‖ ^ 2) : ℝ) : ℂ) := by
  obtain ⟨a, b, hab⟩ := CompactL2.exists_interval f
  calc
    ⟪freeResolventOperator hL (f : ComplexL2), (f : ComplexL2)⟫_ℂ =
        ∫ x, (f : ComplexL2) x * conj (freeResolvent L (f : ComplexL2) x) := by
      rw [L2.inner_def]
      apply integral_congr_ae
      filter_upwards [coeFn_freeResolventOperator_on_compact hL f] with x hx
      simp only [RCLike.inner_apply, hx]
    _ = _ := freeResolvent_pairing_energy hL (Lp.memLp (f : ComplexL2)) hab

theorem re_inner_freeResolventOperator_nonneg (f : ComplexL2) :
    0 ≤ (⟪freeResolventOperator hL f, f⟫_ℂ).re := by
  refine denseRange_compactL2_subtypeL.induction_on
    (p := fun u => 0 ≤ (⟪freeResolventOperator hL u, u⟫_ℂ).re) f
    (isClosed_le continuous_const (by fun_prop)) ?_
  intro g
  change 0 ≤ (⟪freeResolventOperator hL (g : ComplexL2), (g : ComplexL2)⟫_ℂ).re
  rw [freeResolventOperator_pairing_energy_compact]
  simp only [Complex.ofReal_re]
  exact add_nonneg (integral_nonneg fun x => sq_nonneg _)
    (mul_nonneg (sq_nonneg L) (integral_nonneg fun x => sq_nonneg _))

/-- Positivity of the actual extended free resolvent. -/
theorem freeResolventOperator_isPositive : (freeResolventOperator hL).IsPositive := by
  apply ContinuousLinearMap.isPositive_def'.mpr
  refine ⟨freeResolventOperator_isSelfAdjoint hL, fun f => ?_⟩
  exact re_inner_freeResolventOperator_nonneg hL f

end UnforcedLeray.Sturm
