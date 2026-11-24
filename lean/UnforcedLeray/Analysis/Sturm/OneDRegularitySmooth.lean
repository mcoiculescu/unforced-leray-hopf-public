import UnforcedLeray.Analysis.Sturm.OneDRegularitySecond

/-!
# Smooth Green representatives and their actual L² derivatives

The explicit Green convolution and its first two derivatives belong to L².
For a smooth source, the classical equations `u' = v`, `v' = L²u - f`
bootstrap the two actual representatives to every finite differentiability
order, hence to smoothness. No regularity assumption on the solution is used.
-/

noncomputable section

open MeasureTheory Filter
open scoped ContDiff

namespace UnforcedLeray.Sturm

theorem memLp_freeResolvent_of_memLp {L : ℝ} (hL : 0 < L) {f : ℝ → ℂ}
    (hf : MemLp f 2 (volume : Measure ℝ)) :
    MemLp (freeResolvent L f) 2 (volume : Measure ℝ) := by
  have hrep := coeFn_freeResolventOperator hL (hf.toLp f)
  rw [freeResolvent_congr_ae L hf.coeFn_toLp] at hrep
  exact (Lp.memLp (freeResolventOperator hL (hf.toLp f))).ae_eq hrep

theorem memLp_freeResolventDeriv_of_memLp {L : ℝ} (hL : 0 < L) {f : ℝ → ℂ}
    (hf : MemLp f 2 (volume : Measure ℝ)) :
    MemLp (freeResolventDeriv L f) 2 (volume : Measure ℝ) := by
  have hrep := coeFn_freeResolventDerivativeOperator hL (hf.toLp f)
  rw [freeResolventDeriv_congr_ae L hf.coeFn_toLp] at hrep
  exact (Lp.memLp (freeResolventDerivativeOperator hL (hf.toLp f))).ae_eq hrep

theorem memLp_freeResolventSecond_of_memLp {L : ℝ} (hL : 0 < L) {f : ℝ → ℂ}
    (hf : MemLp f 2 (volume : Measure ℝ)) :
    MemLp (freeResolventSecond L f) 2 (volume : Measure ℝ) :=
  ((memLp_freeResolvent_of_memLp hL hf).const_mul _).sub hf

theorem memLp_deriv_freeResolvent_of_memLp {L : ℝ} (hL : 0 < L) {f : ℝ → ℂ}
    (hf : MemLp f 2 (volume : Measure ℝ)) :
    MemLp (deriv (freeResolvent L f)) 2 (volume : Measure ℝ) := by
  rw [deriv_freeResolvent_of_memLp hL hf]
  exact memLp_freeResolventDeriv_of_memLp hL hf

theorem memLp_deriv_two_freeResolvent_of_memLp_continuous {L : ℝ} (hL : 0 < L)
    {f : ℝ → ℂ} (hf : MemLp f 2 (volume : Measure ℝ)) (hc : Continuous f) :
    MemLp (deriv (deriv (freeResolvent L f))) 2 (volume : Measure ℝ) := by
  rw [deriv_freeResolvent_of_memLp hL hf,
    deriv_freeResolventDeriv_of_memLp_continuous hL hf hc]
  exact memLp_freeResolventSecond_of_memLp hL hf

/-- Simultaneous finite-order bootstrap of the actual solution and its derivative. -/
theorem contDiff_freeResolvent_pair_nat_of_memLp {L : ℝ} (hL : 0 < L)
    {f : ℝ → ℂ} (hf : MemLp f 2 (volume : Measure ℝ)) (hs : ContDiff ℝ ∞ f)
    (n : ℕ) :
    ContDiff ℝ n (freeResolvent L f) ∧ ContDiff ℝ n (freeResolventDeriv L f) := by
  induction n with
  | zero =>
      exact ⟨contDiff_zero.mpr (contDiff_one_freeResolvent_of_memLp hL hf).continuous,
        contDiff_zero.mpr (continuous_freeResolventDeriv_of_memLp hL hf)⟩
  | succ n ih =>
      rw [Nat.cast_add, Nat.cast_one]
      constructor
      · apply contDiff_succ_iff_deriv.mpr
        refine ⟨fun x => (hasDerivAt_freeResolvent_of_memLp hL hf x).differentiableAt,
          ?_, ?_⟩
        · intro h
          simp at h
        · rw [deriv_freeResolvent_of_memLp hL hf]
          exact ih.2
      · apply contDiff_succ_iff_deriv.mpr
        refine ⟨fun x =>
          (hasDerivAt_freeResolventDeriv_of_memLp_continuous hL hf hs.continuous x).differentiableAt,
          ?_, ?_⟩
        · intro h
          simp at h
        · rw [deriv_freeResolventDeriv_of_memLp_continuous hL hf hs.continuous]
          exact (contDiff_const.mul ih.1).sub (contDiff_infty.mp hs n)

/-- A smooth L² source gives a smooth actual Green convolution. -/
theorem contDiff_freeResolvent_of_memLp {L : ℝ} (hL : 0 < L) {f : ℝ → ℂ}
    (hf : MemLp f 2 (volume : Measure ℝ)) (hs : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (freeResolvent L f) :=
  contDiff_infty.mpr fun n => (contDiff_freeResolvent_pair_nat_of_memLp hL hf hs n).1

theorem contDiff_freeResolventDeriv_of_memLp {L : ℝ} (hL : 0 < L) {f : ℝ → ℂ}
    (hf : MemLp f 2 (volume : Measure ℝ)) (hs : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (freeResolventDeriv L f) :=
  contDiff_infty.mpr fun n => (contDiff_freeResolvent_pair_nat_of_memLp hL hf hs n).2

end UnforcedLeray.Sturm
