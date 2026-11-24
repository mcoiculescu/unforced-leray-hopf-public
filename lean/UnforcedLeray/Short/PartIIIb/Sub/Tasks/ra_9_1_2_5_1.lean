import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_asrc_ra_9_1_2_5

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem localTsumSmooth : LocalTsumSmooth := by
  unfold LocalTsumSmooth
  intro F _ _ _ U hU f n hf hloc x hx
  obtain ⟨V, hVnhds, hVU, u, hu, hb⟩ := hloc x hx
  obtain ⟨ε, hε, hballV⟩ := Metric.mem_nhds_iff.mp hVnhds
  obtain ⟨χ, hrIn, hrOut⟩ : ∃ χ : ContDiffBump x, χ.rIn = ε / 4 ∧ χ.rOut = ε / 2 :=
    ⟨⟨ε / 4, ε / 2, by positivity, by linarith⟩, rfl, rfl⟩
  have htsupp : tsupport χ ⊆ V := by
    have h2 : ε / 2 < ε := by linarith
    rw [χ.tsupport_eq, hrOut]
    exact (Metric.closedBall_subset_ball h2).trans hballV
  have hχ1 : ∀ y ∈ Metric.ball x (ε / 4), χ y = 1 := fun y hy =>
    χ.one_of_mem_closedBall (by rw [hrIn]; exact Metric.ball_subset_closedBall hy)
  have hCχ : ∀ i : ℕ, ∃ C : ℝ, ∀ y, ‖iteratedFDeriv ℝ i χ y‖ ≤ C := by
    intro i
    have hsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ := χ.contDiff
    have hc : Continuous (iteratedFDeriv ℝ i χ) :=
      hsm.continuous_iteratedFDeriv (by exact_mod_cast le_top)
    have hs : HasCompactSupport (iteratedFDeriv ℝ i χ) :=
      χ.hasCompactSupport.iteratedFDeriv i
    obtain ⟨C, hC⟩ := hc.bounded_above_of_compact_support hs
    exact ⟨C, fun y => hC y⟩
  choose C hC using hCχ
  have hCnn : ∀ i, 0 ≤ C i := fun i => le_trans (norm_nonneg _) (hC i 0)
  have hgC : ∀ j : ℤ, ContDiff ℝ n (fun y => χ y • f j y) := by
    intro j
    rw [contDiff_iff_contDiffAt]
    intro y
    by_cases hy : y ∈ U
    · exact χ.contDiffAt.smul ((hf j).contDiffAt (hU.mem_nhds hy))
    · have hy' : y ∉ tsupport χ := fun h => hy (hVU (htsupp h))
      have heq : (fun z => χ z • f j z) =ᶠ[𝓝 y] fun _ => (0 : F) := by
        filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hy'] with z hz
        simp [hz]
      exact contDiffAt_const.congr_of_eventuallyEq heq
  have hbd : ∀ k : ℕ, k ≤ n → ∀ j : ℤ, ∀ y : Chart,
      ‖iteratedFDeriv ℝ k (fun z => χ z • f j z) y‖
        ≤ (∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) * C i) * |u j| := by
    intro k hk j y
    by_cases hy : y ∈ tsupport χ
    · have hyV : y ∈ V := htsupp hy
      have hyU : y ∈ U := hVU hyV
      have e0 : iteratedFDerivWithin ℝ k (fun z => χ z • f j z) U y
          = iteratedFDeriv ℝ k (fun z => χ z • f j z) y :=
        iteratedFDerivWithin_of_isOpen k hU hyU
      rw [← e0]
      refine le_trans (norm_iteratedFDerivWithin_smul_le χ.contDiff.contDiffOn (hf j)
        hU.uniqueDiffOn hyU (by exact_mod_cast hk)) ?_
      rw [Finset.sum_mul]
      refine Finset.sum_le_sum (fun i hi => ?_)
      have hi' : i ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
      have ec : iteratedFDerivWithin ℝ i χ U y = iteratedFDeriv ℝ i χ y :=
        iteratedFDerivWithin_of_isOpen i hU hyU
      have ef : iteratedFDerivWithin ℝ (k - i) (f j) U y = iteratedFDeriv ℝ (k - i) (f j) y :=
        iteratedFDerivWithin_of_isOpen (k - i) hU hyU
      rw [ec, ef]
      have h1 : ‖iteratedFDeriv ℝ i χ y‖ ≤ C i := hC i y
      have h2 : ‖iteratedFDeriv ℝ (k - i) (f j) y‖ ≤ |u j| :=
        le_trans (hb j (k - i) (by omega) y hyV) (le_abs_self _)
      have h4 : ‖iteratedFDeriv ℝ i χ y‖ * ‖iteratedFDeriv ℝ (k - i) (f j) y‖
          ≤ C i * |u j| := mul_le_mul h1 h2 (norm_nonneg _) (hCnn i)
      have key := mul_le_mul_of_nonneg_left h4 (Nat.cast_nonneg (α := ℝ) (k.choose i))
      exact le_trans (le_of_eq (by ring)) (le_trans key (le_of_eq (by ring)))
    · have hnot : y ∉ tsupport (fun z => χ z • f j z) := fun h => hy (tsupport_smul_subset_left _ _ h)
      have h0 : iteratedFDeriv ℝ k (fun z => χ z • f j z) y = 0 :=
        image_eq_zero_of_notMem_tsupport (fun h => hnot (tsupport_iteratedFDeriv_subset k h))
      rw [h0, norm_zero]
      exact mul_nonneg (Finset.sum_nonneg (fun i _ => mul_nonneg (Nat.cast_nonneg _) (hCnn i)))
        (abs_nonneg _)
  have hsum : ∀ k : ℕ, Summable (fun j : ℤ =>
      (∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) * C i) * |u j|) :=
    fun k => hu.abs.mul_left _
  have hglob : ContDiff ℝ n (fun y => ∑' j, χ y • f j y) := by
    refine contDiff_tsum (v := fun k j => (∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) * C i) * |u j|)
      (N := (n : ℕ∞)) (fun j => hgC j) (fun k _ => hsum k) (fun k i y hk => ?_)
    have hkn : k ≤ n := by exact_mod_cast hk
    exact hbd k hkn i y
  have hEq : (fun y => ∑' j, f j y) =ᶠ[𝓝 x] (fun y => ∑' j, χ y • f j y) := by
    filter_upwards [Metric.ball_mem_nhds x (by linarith : (0:ℝ) < ε / 4)] with y hy
    simp only [hχ1 y hy, one_smul]
  exact ((hglob.contDiffAt).congr_of_eventuallyEq hEq).contDiffWithinAt

end UnforcedLeray.Short.PartIIIb.Concrete
