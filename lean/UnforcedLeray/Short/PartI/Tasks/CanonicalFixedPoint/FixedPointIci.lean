import UnforcedLeray.Short.PartI.Sub.PartI_C06
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.UniformSpace.UniformApproximation
import Mathlib.Topology.UniformSpace.Cauchy
import Mathlib.Topology.Basic

open MeasureTheory Set Filter Topology

namespace UnforcedLeray.Short.PartI

theorem fixedPointIci : FixedPointIci := by
  intro b T H1 H2
  obtain ⟨seq, hseq0, hseqS⟩ : ∃ seq : ℕ → ℝ → ℂ,
      seq 0 = (fun _ => 0) ∧ ∀ n, seq (n + 1) = T (seq n) :=
    ⟨fun n => Nat.rec (motive := fun _ => ℝ → ℂ) (fun _ => 0) (fun _ A => T A) n, rfl,
      fun n => rfl⟩
  have hit : ∀ n, ContinuousOn (seq n) (Ici b) ∧ ∃ M, ∀ θ, b ≤ θ → ‖seq n θ‖ ≤ M := by
    intro n
    induction n with
    | zero => rw [hseq0]; exact ⟨continuousOn_const, 0, fun θ _ => by simp⟩
    | succ n ih => rw [hseqS n]; exact H1 (seq n) ih.1 ih.2
  have h0 : ∀ θ, seq 0 θ = 0 := fun θ => by rw [hseq0]
  obtain ⟨M1, hM1⟩ := (H1 (seq 0) (hit 0).1 (hit 0).2).2
  obtain ⟨K, hK0, hK⟩ : ∃ K : ℝ, 0 ≤ K ∧ ∀ θ, b ≤ θ → ‖seq 1 θ - seq 0 θ‖ ≤ K := by
    refine ⟨M1 + 1, ?_, fun θ hθ => ?_⟩
    · have h1 := hM1 b le_rfl
      have h2 := norm_nonneg (T (seq 0) b)
      linarith
    · have e1 : seq 1 θ = T (seq 0) θ := congrFun (hseqS 0) θ
      rw [e1, h0 θ, sub_zero]
      linarith [hM1 θ hθ]
  have hstep : ∀ n, ∀ θ, b ≤ θ → ‖seq (n + 1) θ - seq n θ‖ ≤ K * (1/2) ^ n := by
    intro n
    induction n with
    | zero => intro θ hθ; rw [pow_zero, mul_one]; exact hK θ hθ
    | succ n ih =>
      intro θ hθ
      have e2 : seq (n + 1 + 1) θ - seq (n + 1) θ = T (seq (n + 1)) θ - T (seq n) θ := by
        rw [hseqS (n + 1), hseqS n]
      have key := H2 (seq (n + 1)) (seq n) (hit (n + 1)).1 (hit (n + 1)).2 (hit n).1
        (hit n).2 (K * (1/2) ^ n) ih θ hθ
      rw [e2]
      refine key.trans (le_of_eq ?_)
      rw [pow_succ]
      ring
  have htel : ∀ θ, b ≤ θ → ∀ n m, n ≤ m →
      ‖seq m θ - seq n θ‖ ≤ 2 * K * (1/2) ^ n - 2 * K * (1/2) ^ m := by
    intro θ hθ n m hnm
    induction m, hnm using Nat.le_induction with
    | base => simp
    | succ m hm ih =>
      have h1 := hstep m θ hθ
      have h2 : seq (m + 1) θ - seq n θ =
          (seq (m + 1) θ - seq m θ) + (seq m θ - seq n θ) := by ring
      have h3 : K * (1/2 : ℝ) ^ (m + 1) = K * (1/2) ^ m / 2 := by rw [pow_succ]; ring
      rw [h2]
      have h4 := norm_add_le (seq (m + 1) θ - seq m θ) (seq m θ - seq n θ)
      linarith
  have hcau : ∀ θ, b ≤ θ → CauchySeq (fun n => seq n θ) := by
    intro θ hθ
    refine cauchySeq_of_le_geometric (1/2) K (by norm_num) (fun n => ?_)
    rw [dist_comm, dist_eq_norm]
    exact hstep n θ hθ
  obtain ⟨A, hA⟩ : ∃ A : ℝ → ℂ, ∀ θ, b ≤ θ → Tendsto (fun n => seq n θ) atTop (𝓝 (A θ)) :=
    ⟨fun θ => limUnder atTop (fun n => seq n θ),
      fun θ hθ => tendsto_nhds_limUnder (cauchySeq_tendsto_of_complete (hcau θ hθ))⟩
  have hgeo : ∀ C : ℝ, Tendsto (fun n : ℕ => C * (1/2 : ℝ) ^ n) atTop (𝓝 0) := by
    intro C
    have := (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0:ℝ) ≤ 1/2)
      (by norm_num : (1/2:ℝ) < 1)).const_mul C
    rw [mul_zero] at this
    exact this
  have hAbd : ∀ θ, b ≤ θ → ∀ n, ‖A θ - seq n θ‖ ≤ 2 * K * (1/2) ^ n := by
    intro θ hθ n
    have ht : Tendsto (fun m => ‖seq m θ - seq n θ‖) atTop (𝓝 ‖A θ - seq n θ‖) :=
      ((hA θ hθ).sub_const (seq n θ)).norm
    refine le_of_tendsto ht (eventually_atTop.2 ⟨n, fun m hm => ?_⟩)
    have h0' : 0 ≤ K * (1/2 : ℝ) ^ m := mul_nonneg hK0 (pow_nonneg (by norm_num) m)
    linarith [htel θ hθ n m hm]
  have hAb0 : ∀ θ, b ≤ θ → ‖A θ‖ ≤ 2 * K := by
    intro θ hθ
    have h := hAbd θ hθ 0
    rw [h0 θ, sub_zero, pow_zero, mul_one] at h
    exact h
  have hAcont : ContinuousOn A (Ici b) := by
    have hc : ∃ᶠ n in atTop, ContinuousOn (fun θ => seq n θ) (Ici b) :=
      Eventually.frequently (Eventually.of_forall fun n => (hit n).1)
    refine TendstoUniformlyOn.continuousOn (F := fun n θ => seq n θ) (p := atTop) ?_ hc
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    filter_upwards [(hgeo (2 * K)).eventually (gt_mem_nhds hε)] with n hn
    intro θ hθ
    rw [dist_eq_norm]
    exact lt_of_le_of_lt (hAbd θ hθ n) hn
  have hfix : ∀ θ, b ≤ θ → T A θ = A θ := by
    intro θ hθ
    have hbd : ∀ n, ‖T A θ - A θ‖ ≤ 2 * K * (1/2) ^ n := by
      intro n
      have hδ := H2 A (seq n) hAcont ⟨2 * K, hAb0⟩ (hit n).1 (hit n).2 (2 * K * (1/2) ^ n)
        (fun θ' hθ' => hAbd θ' hθ' n) θ hθ
      have e : seq (n + 1) θ = T (seq n) θ := congrFun (hseqS n) θ
      rw [← e] at hδ
      have hA1 := hAbd θ hθ (n + 1)
      have hpow : 2 * K * (1/2 : ℝ) ^ (n + 1) = K * (1/2) ^ n := by rw [pow_succ]; ring
      have htri := norm_add_le (T A θ - seq (n + 1) θ) (seq (n + 1) θ - A θ)
      rw [sub_add_sub_cancel] at htri
      have hrev := norm_sub_rev (seq (n + 1) θ) (A θ)
      linarith
    have hz : ‖T A θ - A θ‖ ≤ 0 := ge_of_tendsto (hgeo (2 * K)) (Eventually.of_forall hbd)
    exact sub_eq_zero.mp (norm_le_zero_iff.mp hz)
  refine ⟨A, hAcont, ⟨2 * K, hAb0⟩, hfix, ?_⟩
  intro A' hA'c hA'b hA'fix θ0 hθ0
  obtain ⟨M', hM'⟩ := hA'b
  have hD : ∀ θ, b ≤ θ → ‖A' θ - A θ‖ ≤ M' + 2 * K := fun θ hθ =>
    (norm_sub_le _ _).trans (by linarith [hM' θ hθ, hAb0 θ hθ])
  have hconv : ∀ n, ∀ θ, b ≤ θ → ‖A' θ - A θ‖ ≤ (M' + 2 * K) * (1/2) ^ n := by
    intro n
    induction n with
    | zero => intro θ hθ; rw [pow_zero, mul_one]; exact hD θ hθ
    | succ n ih =>
      intro θ hθ
      have key := H2 A' A hA'c ⟨M', hM'⟩ hAcont ⟨2 * K, hAb0⟩ ((M' + 2 * K) * (1/2) ^ n) ih
        θ hθ
      rw [hA'fix θ hθ, hfix θ hθ] at key
      rw [pow_succ]
      linarith
  have hz : ‖A' θ0 - A θ0‖ ≤ 0 :=
    ge_of_tendsto (hgeo (M' + 2 * K)) (Eventually.of_forall fun n => hconv n θ0 hθ0)
  exact sub_eq_zero.mp (norm_le_zero_iff.mp hz)

end UnforcedLeray.Short.PartI
