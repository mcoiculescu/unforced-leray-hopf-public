import UnforcedLeray.Analysis.Rayleigh.InteriorSecondPairing
import UnforcedLeray.Analysis.Rayleigh.ExpandingIntervals

/-!
# Genuine H² regularity of the expanding-annulus weak limit

Every fixed compact test is eventually inside the expanding annulus. The
actual interior twice-IBP identity can therefore pass to the complex weak
limits, giving f'' = k + 4f globally in distributions. Each finite-annulus
zero extension was asserted only to be H¹; the second-order boundary jumps
are removed here by eventual interior testing, not ignored.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace UnforcedLeray.Rayleigh
open Sturm NonUniqueEuler.Sob

lemma iterDirDeriv_two_eq_deriv_deriv (ψ : ℝ → ℂ) :
    iterDirDeriv ([1, 1] : List ℝ) ψ = deriv (deriv ψ) := by
  simpa [derivList, iteratedDeriv_succ, iteratedDeriv_zero] using
    iterDirDeriv_derivList 2 ψ

/-- Passage to the actual global weak second derivative along expanding annuli. -/
theorem hasWeakSecond_of_expanding_annular_weak_limits
    {q : ℕ → ℝ → ℝ} {z : ℕ → ℂ} {F : ℕ → ℝ → ℂ} {l r : ℕ → ℝ}
    (h : ∀ n, ShiftedAnnularMode (q n) (z n) (F n) (l n) (r n))
    (hl : Tendsto l atTop atBot) (hr : Tendsto r atTop atTop)
    {f k : ComplexL2}
    (hfu : WeakL2.WeakTendsto (fun n => (h n).fieldL2) atTop f)
    (hku : WeakL2.WeakTendsto (fun n => (h n).residualL2) atTop k) :
    HasWeakDerivOn univ [1, 1] (f : ℝ → ℂ) ((k + (4 : ℂ) • f : ComplexL2) : ℝ → ℂ) := by
  intro ψ hψ
  have hdψ : MemLp (deriv (deriv ψ)) 2 volume := by
    simpa only [iterDirDeriv_two_eq_deriv_deriv]
      using testFn_memLp (hψ.iterDirDeriv ([1, 1] : List ℝ))
  have hψ2 : MemLp ψ 2 volume := testFn_memLp hψ
  have hleft := weakTendsto_integral_mul hfu (deriv (deriv ψ)) hdψ
  have hright := (weakTendsto_integral_mul hku ψ hψ2).add
    ((weakTendsto_integral_mul hfu ψ hψ2).const_mul (4 : ℂ))
  have hevent : ∀ᶠ n : ℕ in atTop,
      (∫ t, (h n).residualL2 t * ψ t) + 4 * (∫ t, (h n).fieldL2 t * ψ t) =
        ∫ t, (h n).fieldL2 t * deriv (deriv ψ) t := by
    filter_upwards [eventually_test_endpoints_zero hl hr hψ.compact] with n hn
    exact ((h n).fieldL2_second_pairing (hψ.smooth.of_le (by simp)) hn.1 hn.2).symm
  have he := tendsto_nhds_unique hleft (hright.congr' hevent)
  have hsum : (∫ t, (k + (4 : ℂ) • f : ComplexL2) t * ψ t) =
      (∫ t, k t * ψ t) + 4 * (∫ t, f t * ψ t) := by
    rw [← l2Pairing_apply ψ hψ2, map_add, map_smul,
      l2Pairing_apply ψ hψ2, l2Pairing_apply ψ hψ2]
    rfl
  rw [iterDirDeriv_two_eq_deriv_deriv]
  norm_num only [List.length_cons, List.length_nil, zero_add, Nat.reduceAdd, neg_sq, one_pow, one_mul]
  exact he.trans hsum.symm

/-- Explicit first and second L² weak derivatives give genuine whole-line H² membership. -/
theorem memH2_of_L2_weak_derivatives (f g j : ComplexL2)
    (h₁ : HasWeakDerivOn univ [1] (f : ℝ → ℂ) (g : ℝ → ℂ))
    (h₂ : HasWeakDerivOn univ [1, 1] (f : ℝ → ℂ) (j : ℝ → ℂ)) :
    MemH1On 2 univ (f : ℝ → ℂ) := by
  refine ⟨by simpa using Lp.memLp f, ?_⟩
  intro i hi
  interval_cases i
  · refine ⟨f, by simpa using Lp.memLp f, ?_⟩
    intro ψ hψ
    simp [derivList, iterDirDeriv]
  · refine ⟨g, by simpa using Lp.memLp g, ?_⟩
    simpa [derivList] using h₁
  · refine ⟨j, by simpa using Lp.memLp j, ?_⟩
    simpa [derivList] using h₂

/-- Actual common weak extraction with a global H² limit; expanding geometry
is supplied only through the two endpoint limits. -/
theorem exists_common_H2_weak_subsequence
    {q : ℕ → ℝ → ℝ} {z : ℕ → ℂ} {F : ℕ → ℝ → ℂ} {l r : ℕ → ℝ}
    (h : ∀ n, ShiftedAnnularMode (q n) (z n) (F n) (l n) (r n))
    (hmass : ∀ n, (∫ t in Ioc (l n) (r n), ‖F n t‖ ^ 2) = 1)
    (hl : Tendsto l atTop atBot) (hr : Tendsto r atTop atTop) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ f g k : ComplexL2,
      ‖f‖ ≤ 1 ∧ ‖g‖ ≤ 2 ∧ ‖k‖ ≤ 8 ∧
      MemH1On 2 univ (f : ℝ → ℂ) ∧
      HasWeakDerivOn univ [1] (f : ℝ → ℂ) (g : ℝ → ℂ) ∧
      HasWeakDerivOn univ [1, 1] (f : ℝ → ℂ) ((k + (4 : ℂ) • f : ComplexL2) : ℝ → ℂ) ∧
      WeakL2.WeakTendsto (fun n => (h (φ n)).fieldL2) atTop f ∧
      WeakL2.WeakTendsto (fun n => (h (φ n)).derivativeL2) atTop g ∧
      WeakL2.WeakTendsto (fun n => (h (φ n)).residualL2) atTop k := by
  obtain ⟨φ, hφ, f, g, k, hf, hg, hk, hfu, hgu, hku⟩ :=
    exists_common_weak_subsequence h hmass
  have h₁ := hasWeakDerivOn_of_weak_limits hfu hgu
    (fun n => (h (φ n)).fieldL2_hasWeakDerivative)
  have h₂ := hasWeakSecond_of_expanding_annular_weak_limits (fun n => h (φ n))
    (hl.comp hφ.tendsto_atTop) (hr.comp hφ.tendsto_atTop) hfu hku
  exact ⟨φ, hφ, f, g, k, hf, hg, hk, memH2_of_L2_weak_derivatives f g (k + (4 : ℂ) • f) h₁ h₂,
    h₁, h₂, hfu, hgu, hku⟩

end UnforcedLeray.Rayleigh
