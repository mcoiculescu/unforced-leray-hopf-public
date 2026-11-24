import UnforcedLeray.Lib.PlanarSectorsB.TransportDuhamel
import UnforcedLeray.Lib.PlanarSectorsB.Coupling
import UnforcedLeray.Lib.PlanarSectorsB.Sector
import Mathlib.Analysis.Normed.Operator.Compact.Basic

set_option autoImplicit false

noncomputable section

open Filter Topology UnforcedLeray.Planar

namespace UnforcedLeray.Short.IIIa.CouplingCompactL2

/-- Norm of the coupling in sector `n` tends to zero as `|n| → ∞`. -/
theorem exists_tail_small {M : ℝ} (hM : 1 < M) {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n : ℤ, N < n.natAbs → ‖couplingSec hM n‖ ≤ ε := by
  obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.1 (tendsto_norm_couplingSec hM)) ε hε
  refine ⟨N, fun n hn => ?_⟩
  have hn' : N ≤ n.natAbs := hn.le
  have h := hN n.natAbs hn'
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (norm_nonneg _)] at h
  rcases Int.natAbs_eq n with he | he
  · rw [he]; exact h.le
  · rw [he, couplingSec_neg, norm_neg]; exact h.le

/-- The truncation of `couplingW` to sectors `|n| ≤ N`. -/
def trunc {M : ℝ} (hM : 1 < M) (N : ℕ) : L2w M →L[ℂ] L2w M :=
  ∑ n ∈ Finset.Icc (-(N : ℤ)) N,
    (secEmb M n).toContinuousLinearMap ∘L couplingSec hM n ∘L secProf M n

theorem isCompactOperator_sum {M : ℝ} (hM : 1 < M) (s : Finset ℤ) :
    IsCompactOperator ⇑(∑ n ∈ s,
      (secEmb M n).toContinuousLinearMap ∘L couplingSec hM n ∘L secProf M n) := by
  induction s using Finset.induction_on with
  | empty => simpa using isCompactOperator_zero
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, ContinuousLinearMap.coe_add']
    exact (((isCompactOperator_couplingSec hM a).comp_clm (secProf M a)).clm_comp
      (secEmb M a).toContinuousLinearMap).add ih

theorem isCompactOperator_trunc {M : ℝ} (hM : 1 < M) (N : ℕ) :
    IsCompactOperator (trunc hM N) := isCompactOperator_sum hM _

theorem secProf_trunc {M : ℝ} (hM : 1 < M) (N : ℕ) (f : L2w M) (m : ℤ) :
    secProf M m (trunc hM N f) =
      if m ∈ Finset.Icc (-(N : ℤ)) N then couplingSec hM m (secProf M m f) else 0 := by
  unfold trunc
  rw [sum_apply, map_sum]
  simp only [ContinuousLinearMap.comp_apply, LinearIsometry.coe_toContinuousLinearMap,
    secProf_secEmb]
  simp [Finset.sum_ite_eq']

theorem norm_sub_trunc_le {M : ℝ} (hM : 1 < M) {ε : ℝ} (hε : 0 < ε) {N : ℕ}
    (hN : ∀ n : ℤ, N < n.natAbs → ‖couplingSec hM n‖ ≤ ε) :
    ‖couplingW hM - trunc hM N‖ ≤ ε := by
  let A : ℤ → ProfL2 M →L[ℂ] ProfL2 M := fun n =>
    if n ∈ Finset.Icc (-(N : ℤ)) N then 0 else couplingSec hM n
  have hA : ∀ n, ‖A n‖ ≤ ε := by
    intro n
    by_cases h : n ∈ Finset.Icc (-(N : ℤ)) N
    · simp only [A, if_pos h, norm_zero]; exact hε.le
    · simp only [A, h, if_false]
      apply hN
      simp only [Finset.mem_Icc, not_and_or, not_le] at h
      omega
  have heq : couplingW hM - trunc hM N = sectorSum A hA hε.le := by
    refine ContinuousLinearMap.ext fun f => UnforcedLeray.Planar.eq_of_secProf fun m => ?_
    rw [ContinuousLinearMap.sub_apply]
    rw [map_sub, secProf_couplingW, secProf_trunc, secProf_sectorSum]
    by_cases h : m ∈ Finset.Icc (-(N : ℤ)) N
    · simp only [A, if_pos h, ContinuousLinearMap.zero_apply, sub_self]
    · simp only [A, if_neg h, sub_zero]
  rw [heq]
  exact norm_sectorSum_le A hA hε.le

theorem isCompactOperator_couplingW {M : ℝ} (hM : 1 < M) :
    IsCompactOperator (couplingW hM) := by
  refine isCompactOperator_of_tendsto (l := atTop) (F := trunc hM) ?_
    (Eventually.of_forall (isCompactOperator_trunc hM))
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N0, hN0⟩ := exists_tail_small hM (half_pos hε)
  refine ⟨N0, fun n hn => ?_⟩
  rw [dist_eq_norm, ← norm_neg, neg_sub]
  refine lt_of_le_of_lt (norm_sub_trunc_le hM (half_pos hε) (N := n) fun k hk => ?_) (half_lt_self hε)
  exact hN0 k (lt_of_le_of_lt hn hk)

end UnforcedLeray.Short.IIIa.CouplingCompactL2
