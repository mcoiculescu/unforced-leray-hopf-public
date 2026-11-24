import UnforcedLeray.Analysis.Rayleigh.WeakExtraction
import UnforcedLeray.Analysis.Rayleigh.ComplexWeakPairing

/-!
# Actual distributional limits of the extracted annular sequences

Real Hilbert weak convergence yields full complex test-pairing convergence.
The actual global first weak derivative relation passes to the limit. No
global second derivative is claimed for the zero-extended residual sequence.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace UnforcedLeray.Rayleigh
open Sturm NonUniqueEuler.Sob

namespace ShiftedAnnularMode
variable {q : ℝ → ℝ} {z : ℂ} {F : ℝ → ℂ} {l r : ℝ}
  (h : ShiftedAnnularMode q z F l r)

lemma integral_fieldL2_mul (ψ : ℝ → ℂ) :
    (∫ t, h.fieldL2 t * ψ t) = ∫ t, zeroExtension l r F t * ψ t := by
  apply integral_congr_ae
  filter_upwards [h.coeFn_fieldL2] with t ht
  rw [ht]

lemma integral_derivativeL2_mul (ψ : ℝ → ℂ) :
    (∫ t, h.derivativeL2 t * ψ t) = ∫ t, zeroExtension l r (deriv F) t * ψ t := by
  apply integral_congr_ae
  filter_upwards [h.coeFn_derivativeL2] with t ht
  rw [ht]

lemma integral_residualL2_mul (ψ : ℝ → ℂ) :
    (∫ t, h.residualL2 t * ψ t) =
      ∫ t, zeroExtension l r (fun x => deriv (deriv F) x - 4 * F x) t * ψ t := by
  apply integral_congr_ae
  filter_upwards [h.coeFn_residualL2] with t ht
  rw [ht]

/-- The quotient classes carry the genuine weak derivative relation already
proved for the actual zero-extended functions. -/
theorem fieldL2_hasWeakDerivative :
    HasWeakDerivOn univ [1] (h.fieldL2 : ℝ → ℂ) (h.derivativeL2 : ℝ → ℂ) := by
  intro ψ hψ
  rw [h.integral_fieldL2_mul, h.integral_derivativeL2_mul]
  exact zeroExtension_hasWeakDeriv h.regularity h.ordered
    h.left_endpoint h.right_endpoint ψ hψ

end ShiftedAnnularMode

/-- Actual distributional derivative identities are closed under weak L²
convergence, because each test pairing converges as a complex number. -/
theorem hasWeakDerivOn_of_weak_limits {u v : ℕ → ComplexL2} {f g : ComplexL2}
    (hu : WeakL2.WeakTendsto u atTop f) (hv : WeakL2.WeakTendsto v atTop g)
    (hder : ∀ n, HasWeakDerivOn univ [1] (u n : ℝ → ℂ) (v n : ℝ → ℂ)) :
    HasWeakDerivOn univ [1] (f : ℝ → ℂ) (g : ℝ → ℂ) := by
  intro ψ hψ
  have hl := weakTendsto_integral_mul hu (iterDirDeriv [1] ψ)
    (testFn_memLp (hψ.iterDirDeriv [1]))
  have hr := (weakTendsto_integral_mul hv ψ (testFn_memLp hψ)).const_mul
    ((-1 : ℂ) ^ ([1] : List ℝ).length)
  apply tendsto_nhds_unique hl
  exact hr.congr' (Filter.Eventually.of_forall fun n => (hder n ψ hψ).symm)

/-- One common subsequence, genuine first derivative of the limit, and full
complex pairings against every L² test for the three actual raw sequences. -/
theorem exists_common_distributional_subsequence
    {q : ℕ → ℝ → ℝ} {z : ℕ → ℂ} {F : ℕ → ℝ → ℂ} {l r : ℕ → ℝ}
    (h : ∀ n, ShiftedAnnularMode (q n) (z n) (F n) (l n) (r n))
    (hmass : ∀ n, (∫ t in Ioc (l n) (r n), ‖F n t‖ ^ 2) = 1) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ f g k : ComplexL2,
      ‖f‖ ≤ 1 ∧ ‖g‖ ≤ 2 ∧ ‖k‖ ≤ 8 ∧
      HasWeakDerivOn univ [1] (f : ℝ → ℂ) (g : ℝ → ℂ) ∧
      ∀ ψ : ℝ → ℂ, MemLp ψ 2 volume →
        Tendsto (fun n => ∫ t, zeroExtension (l (φ n)) (r (φ n)) (F (φ n)) t * ψ t)
          atTop (𝓝 (∫ t, f t * ψ t)) ∧
        Tendsto (fun n => ∫ t, zeroExtension (l (φ n)) (r (φ n)) (deriv (F (φ n))) t * ψ t)
          atTop (𝓝 (∫ t, g t * ψ t)) ∧
        Tendsto (fun n => ∫ t, zeroExtension (l (φ n)) (r (φ n))
          (fun x => deriv (deriv (F (φ n))) x - 4 * F (φ n) x) t * ψ t)
          atTop (𝓝 (∫ t, k t * ψ t)) := by
  obtain ⟨φ, hφ, f, g, k, hf, hg, hk, hfu, hgu, hku⟩ :=
    exists_common_weak_subsequence h hmass
  refine ⟨φ, hφ, f, g, k, hf, hg, hk, ?_, ?_⟩
  · exact hasWeakDerivOn_of_weak_limits hfu hgu
      (fun n => (h (φ n)).fieldL2_hasWeakDerivative)
  · intro ψ hψ
    refine ⟨?_, ?_, ?_⟩
    · simpa only [ShiftedAnnularMode.integral_fieldL2_mul] using
        weakTendsto_integral_mul hfu ψ hψ
    · simpa only [ShiftedAnnularMode.integral_derivativeL2_mul] using
        weakTendsto_integral_mul hgu ψ hψ
    · simpa only [ShiftedAnnularMode.integral_residualL2_mul] using
        weakTendsto_integral_mul hku ψ hψ

end UnforcedLeray.Rayleigh
