import Mathlib.Analysis.Calculus.SmoothSeries
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_4_2.Sub.PartIIIb_IIIb_D2_4_2_1

/-!
# (L1) Local termwise `C²` for a `tsum` over `ℤ` (task `PartIII-b:IIIb-D2/4/2/1/1`)

Mathlib's `contDiff_tsum_of_eventually` needs global bounds.  Here the bounds are local: each
point of an open set `U` has a neighbourhood on which all terms and their derivatives of order
`≤ N` are dominated by a summable sequence.  The engine is an induction on `N`: on a ball inside
the good neighbourhood the series is differentiable with derivative the series of the derivatives
(`hasFDerivAt_tsum_of_isPreconnected`), and the derivatives satisfy the same hypotheses one order
lower (`norm_iteratedFDeriv_fderiv`).
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- Induction engine: local termwise `C^N` for a series over `ℤ` on an open set. -/
theorem localTsum_aux (N : ℕ) : ∀ {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [CompleteSpace F] (f : ℤ → Chart → F) (U : Set Chart), IsOpen U →
    (∀ j, ContDiffOn ℝ N (f j) U) →
    (∀ x ∈ U, ∃ u : ℤ → ℝ, Summable u ∧ ∃ V ∈ 𝓝 x, ∀ j : ℤ, ∀ y ∈ V, ∀ k : ℕ, k ≤ N →
      ‖iteratedFDeriv ℝ k (f j) y‖ ≤ u j) →
    ContDiffOn ℝ N (fun p => ∑' j : ℤ, f j p) U := by
  induction N with
  | zero =>
    intro F _ _ _ f U hU hf hloc
    rw [Nat.cast_zero] at hf ⊢
    rw [contDiffOn_zero]
    intro x hx
    obtain ⟨u, hu, V, hV, hbd⟩ := hloc x hx
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 (inter_mem hV (hU.mem_nhds hx))
    have hcont : ContinuousOn (fun p => ∑' j : ℤ, f j p) (Metric.ball x ε) := by
      refine continuousOn_tsum (fun j => ?_) hu (fun j y hy => ?_)
      · exact (contDiffOn_zero.1 (hf j)).mono (fun y hy => (hball hy).2)
      · simpa using hbd j y (hball hy).1 0 (Nat.zero_le _)
    exact (hcont.continuousAt (Metric.isOpen_ball.mem_nhds
      (Metric.mem_ball_self hε))).continuousWithinAt
  | succ N ih =>
    intro F _ _ _ f U hU hf hloc
    rw [Nat.cast_succ] at hf ⊢
    rw [contDiffOn_succ_iff_fderiv_of_isOpen hU]
    have key : ∀ x ∈ U, HasFDerivAt (fun p => ∑' j : ℤ, f j p)
        (∑' j : ℤ, fderiv ℝ (f j) x) x := by
      intro x hx
      obtain ⟨u, hu, V, hV, hbd⟩ := hloc x hx
      obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 (inter_mem hV (hU.mem_nhds hx))
      have hdiff : ∀ j : ℤ, ∀ y ∈ Metric.ball x ε,
          HasFDerivAt (f j) (fderiv ℝ (f j) y) y := by
        intro j y hy
        have hc : ContDiffAt ℝ ((N : WithTop ℕ∞) + 1) (f j) y :=
          (hf j).contDiffAt (hU.mem_nhds (hball hy).2)
        exact (hc.differentiableAt (by exact_mod_cast Nat.succ_ne_zero N)).hasFDerivAt
      have hbound : ∀ j : ℤ, ∀ y ∈ Metric.ball x ε, ‖fderiv ℝ (f j) y‖ ≤ u j := by
        intro j y hy
        have h1 : ‖iteratedFDeriv ℝ 0 (fderiv ℝ (f j)) y‖ =
            ‖iteratedFDeriv ℝ (0 + 1) (f j) y‖ := norm_iteratedFDeriv_fderiv
        simp only [norm_iteratedFDeriv_zero] at h1
        rw [h1]
        exact hbd j y (hball hy).1 1 (Nat.le_add_left 1 N)
      have hf0 : Summable fun j : ℤ => f j x := by
        refine Summable.of_norm_bounded hu (fun j => ?_)
        simpa using hbd j x (hball (Metric.mem_ball_self hε)).1 0 (Nat.zero_le _)
      exact hasFDerivAt_tsum_of_isPreconnected (f := fun j : ℤ => f j)
        (f' := fun j y => fderiv ℝ (f j) y) hu Metric.isOpen_ball
        (convex_ball x ε).isPreconnected (fun j y hy => hdiff j y hy)
        (fun j y hy => hbound j y hy) (Metric.mem_ball_self hε) hf0 (Metric.mem_ball_self hε)
    refine ⟨fun x hx => (key x hx).differentiableAt.differentiableWithinAt, ?_, ?_⟩
    · intro h
      exact absurd h (WithTop.natCast_ne_top N)
    · have hgs : ∀ j : ℤ, ContDiffOn ℝ (N : WithTop ℕ∞) (fun y => fderiv ℝ (f j) y) U :=
        fun j => (hf j).fderiv_of_isOpen hU le_rfl
      have hgloc : ∀ x ∈ U, ∃ u : ℤ → ℝ, Summable u ∧ ∃ V ∈ 𝓝 x, ∀ j : ℤ, ∀ y ∈ V,
          ∀ k : ℕ, k ≤ N → ‖iteratedFDeriv ℝ k (fun y => fderiv ℝ (f j) y) y‖ ≤ u j := by
        intro x hx
        obtain ⟨u, hu, V, hV, hbd⟩ := hloc x hx
        refine ⟨u, hu, V, hV, fun j y hy k hk => ?_⟩
        have h1 : ‖iteratedFDeriv ℝ k (fderiv ℝ (f j)) y‖ =
            ‖iteratedFDeriv ℝ (k + 1) (f j) y‖ := norm_iteratedFDeriv_fderiv
        rw [show (fun y => fderiv ℝ (f j) y) = fderiv ℝ (f j) from rfl, h1]
        exact hbd j y hy (k + 1) (by omega)
      have hcongr : ∀ x ∈ U, fderiv ℝ (fun p => ∑' j : ℤ, f j p) x =
          ∑' j : ℤ, fderiv ℝ (f j) x :=
        fun x hx => (key x hx).fderiv
      exact ContDiffOn.congr
        (ih (F := Chart →L[ℝ] F) (fun j => fderiv ℝ (f j)) U hU hgs hgloc) hcongr

/-- (L1) Local termwise `C²` for a `tsum` over `ℤ` on an open set (the target). -/
theorem localTsumC2_proof : LocalTsumC2 := by
  unfold LocalTsumC2
  intro f U hU hf hloc
  have h := localTsum_aux 2 f U hU (fun j => by exact_mod_cast hf j) hloc
  exact_mod_cast h

end UnforcedLeray.Short.PartIIIb.Concrete
