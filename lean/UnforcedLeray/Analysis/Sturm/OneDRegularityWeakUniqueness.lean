import UnforcedLeray.Analysis.Sturm.OneDRegularitySmooth
import UnforcedLeray.Analysis.Sturm.OneDRegularityL2Limits
import UnforcedLeray.Analysis.Sturm.GlobalH2ComplexCutoff
import UnforcedLeray.Analysis.Sturm.FreeResolventInverse

/-!
# Uniqueness of the actual weak free equation in L²

Smooth compact tests are replaced by explicit H²-convergent compact cutoffs
of the actual smooth Green solution. Passing the weak identity to that limit
shows that a homogeneous L² solution annihilates every compact smooth test.
The fundamental lemma for distributions then proves it vanishes a.e.
No Sobolev embedding or weak uniqueness theorem is assumed.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped Topology ContDiff
namespace UnforcedLeray.Sturm
open NonUniqueEuler.Sob

/-- The weak free equation paired with an ordinary compact smooth test. -/
theorem weakFree_pairing_test {L : ℝ} {u : ℝ → ℂ}
    (hw : HasWeakDerivOn univ (derivList 2) u (fun x => (L : ℂ) ^ 2 * u x))
    {φ : ℝ → ℂ} (hφ : IsTestFn univ φ) :
    (∫ x, u x * deriv (deriv φ) x) = (L : ℂ) ^ 2 * ∫ x, u x * φ x := by
  have h := hw φ hφ
  rw [iterDirDeriv_two_eq] at h
  simp only [derivList_length, neg_one_sq, one_mul, mul_assoc] at h
  rw [integral_const_mul] at h
  exact h

/-- The weak identity extends along an actual H² approximation sequence. -/
theorem weakFree_pairing_limit {L : ℝ} {u v : ℝ → ℂ}
    (hu : MemLp u 2 volume)
    (hw : HasWeakDerivOn univ (derivList 2) u (fun x => (L : ℂ) ^ 2 * u x))
    (hv : MemLp v 2 volume) (hddv : MemLp (deriv (deriv v)) 2 volume)
    (φ : ℕ → ℝ → ℂ) (hφ : ∀ n, IsTestFn univ (φ n))
    (hφ2 : ∀ n, MemLp (φ n) 2 volume)
    (hddφ2 : ∀ n, MemLp (deriv (deriv (φ n))) 2 volume)
    (herr : Tendsto (fun n => ∫ x, ‖φ n x - v x‖ ^ 2) atTop (𝓝 0))
    (hddErr : Tendsto (fun n => ∫ x,
      ‖deriv (deriv (φ n)) x - deriv (deriv v) x‖ ^ 2) atTop (𝓝 0)) :
    (∫ x, u x * deriv (deriv v) x) = (L : ℂ) ^ 2 * ∫ x, u x * v x := by
  have hl := tendsto_integral_mul_of_integral_sq_sub hddφ2 hddv hu hddErr
  have hr := (tendsto_integral_mul_of_integral_sq_sub hφ2 hv hu herr).const_mul ((L : ℂ) ^ 2)
  have he : (fun n => ∫ x, u x * deriv (deriv (φ n)) x) =
      fun n => (L : ℂ) ^ 2 * ∫ x, u x * φ n x := by
    funext n
    exact weakFree_pairing_test hw (hφ n)
  rw [he] at hl
  exact tendsto_nhds_unique hl hr

/-- Testing with the actual Green solution is justified by explicit compact cutoffs. -/
theorem weakFree_pairing_smoothH2 {L : ℝ} {u v : ℝ → ℂ}
    (hu : MemLp u 2 volume)
    (hw : HasWeakDerivOn univ (derivList 2) u (fun x => (L : ℂ) ^ 2 * u x))
    (hvs : ContDiff ℝ ∞ v) (hv : MemLp v 2 volume)
    (hdv : MemLp (deriv v) 2 volume) (hddv : MemLp (deriv (deriv v)) 2 volume) :
    (∫ x, u x * deriv (deriv v) x) = (L : ℂ) ^ 2 * ∫ x, u x * v x := by
  have hv2 : ContDiff ℝ 2 v := hvs.of_le (by simp)
  apply weakFree_pairing_limit hu hw hv hddv (GlobalH2ComplexCutoff.approximationC v)
  · intro n
    exact ⟨GlobalH2ComplexCutoff.approximationC_contDiff_infty hvs n,
      GlobalH2ComplexCutoff.approximationC_hasCompactSupport v n, subset_univ _⟩
  · exact fun n => GlobalH2ComplexCutoff.approximationC_memLp_two hv2 n
  · exact fun n => GlobalH2ComplexCutoff.second_deriv_approximationC_memLp_two hv2 n
  · exact GlobalH2ComplexCutoff.integral_value_error_tendsto_zero hv2 hv
  · exact GlobalH2ComplexCutoff.integral_second_error_tendsto_zero hv2 hv hdv hddv

/-- A homogeneous weak free L² solution pairs to zero with every compact smooth test. -/
theorem weakFree_integral_test_eq_zero {L : ℝ} (hL : 0 < L) {u : ℝ → ℂ}
    (hu : MemLp u 2 volume)
    (hw : HasWeakDerivOn univ (derivList 2) u (fun x => (L : ℂ) ^ 2 * u x))
    {φ : ℝ → ℂ} (hφ : IsTestFn univ φ) : (∫ x, u x * φ x) = 0 := by
  have hφ2 := testFn_memLp hφ
  have hvs := contDiff_freeResolvent_of_memLp hL hφ2 hφ.smooth
  have hv := memLp_freeResolvent_of_memLp hL hφ2
  have hdv := memLp_deriv_freeResolvent_of_memLp hL hφ2
  have hddv := memLp_deriv_two_freeResolvent_of_memLp_continuous hL hφ2 hφ.continuous
  have h := weakFree_pairing_smoothH2 hu hw hvs hv hdv hddv
  rw [deriv_freeResolvent_of_memLp hL hφ2,
    deriv_freeResolventDeriv_of_memLp_continuous hL hφ2 hφ.continuous] at h
  simp only [mul_sub, ← mul_assoc] at h
  have huv : Integrable (fun x => u x * freeResolvent L φ x) := hu.integrable_mul hv
  have huφ : Integrable (fun x => u x * φ x) := hu.integrable_mul hφ2
  have he (x : ℝ) : u x * (L : ℂ) ^ 2 * freeResolvent L φ x =
      (L : ℂ) ^ 2 * (u x * freeResolvent L φ x) := by ring
  simp_rw [he] at h
  rw [integral_sub (huv.const_mul _) huφ, integral_const_mul] at h
  exact sub_eq_self.mp h

/-- The actual positive-mass free differential equation has no nonzero L² weak kernel. -/
theorem ae_eq_zero_of_weakFree {L : ℝ} (hL : 0 < L) {u : ℝ → ℂ}
    (hu : MemLp u 2 volume)
    (hw : HasWeakDerivOn univ (derivList 2) u (fun x => (L : ℂ) ^ 2 * u x)) :
    u =ᵐ[volume] 0 := by
  have h := WeakDerivAux.ae_eq_of_integral_testFn isOpen_univ
    ((hu.locallyIntegrable (by norm_num)).locallyIntegrableOn univ)
    (locallyIntegrableOn_zero (s := (univ : Set ℝ)))
    (fun φ hφ => by simpa using weakFree_integral_test_eq_zero hL hu hw hφ)
  filter_upwards [h] with x hx
  exact hx (mem_univ x)

/-- L²-equivalence-class version, with no regularity of the representative assumed. -/
theorem eq_zero_of_weakFree {L : ℝ} (hL : 0 < L) (u : ComplexL2)
    (hw : HasWeakDerivOn univ (derivList 2) (u : ℝ → ℂ)
      (((L : ℂ) ^ 2 • u : ComplexL2) : ℝ → ℂ)) : u = 0 := by
  have hraw : HasWeakDerivOn univ (derivList 2) (u : ℝ → ℂ)
      (fun x => (L : ℂ) ^ 2 * u x) := by
    apply hw.congr_ae (Eventually.of_forall fun _ _ => rfl)
    filter_upwards [Lp.coeFn_smul ((L : ℂ) ^ 2) u] with x hx
    intro _
    simpa only [Pi.smul_apply, smul_eq_mul] using hx
  apply Lp.ext
  exact (ae_eq_zero_of_weakFree hL (Lp.memLp u) hraw).trans
    (Lp.coeFn_zero ℂ 2 (volume : Measure ℝ)).symm

end UnforcedLeray.Sturm
