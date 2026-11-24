import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Finite-order differentiation under the integral (helpers for `SCParamInt7`)

Generic statement: if `F t : H → E` is `C^N` on an open `U` for every `t > 1`, the jets
`t ↦ D^k (F t) x` (`k ≤ N`) are a.e.-strongly measurable, and locally in `x ∈ U` they are
dominated by one integrable function of `t`, then `x ↦ ∫_{(1,∞)} F t x dt` is `C^N` on `U`.
Proof by induction on `N`: differentiate once under the integral and apply the induction
hypothesis to the family of first derivatives.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Metric Filter Topology

namespace UnforcedLeray.Short.PartIIIb.Concrete.ParamInt7Aux

variable {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]

/-- The value of a function is a continuous linear image of its zeroth jet. -/
theorem aesm_zero {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {μ : Measure ℝ}
    (g : ℝ → H → E) (x : H)
    (h : AEStronglyMeasurable (fun t => iteratedFDeriv ℝ 0 (g t) x) μ) :
    AEStronglyMeasurable (fun t => g t x) μ := by
  have e : (fun t => g t x) = fun t =>
      (continuousMultilinearCurryFin0 ℝ H E) (iteratedFDeriv ℝ 0 (g t) x) := by
    funext t
    have h0 : iteratedFDeriv ℝ 0 (g t) x = (continuousMultilinearCurryFin0 ℝ H E).symm (g t x) :=
      rfl
    rw [h0, LinearIsometryEquiv.apply_symm_apply]
  rw [e]
  exact (continuousMultilinearCurryFin0 ℝ H E).continuous.comp_aestronglyMeasurable h

/-- The jets of the derivative family are continuous linear images of the next jets. -/
theorem aesm_jet_fderiv {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {μ : Measure ℝ}
    (k : ℕ) (g : ℝ → H → E) (x : H)
    (h : AEStronglyMeasurable (fun t => iteratedFDeriv ℝ (k + 1) (g t) x) μ) :
    AEStronglyMeasurable (fun t => iteratedFDeriv ℝ k (fun y => fderiv ℝ (g t) y) x) μ := by
  have e : ∀ t, iteratedFDeriv ℝ k (fun y => fderiv ℝ (g t) y) x =
      (continuousMultilinearCurryRightEquiv' ℝ k H E) (iteratedFDeriv ℝ (k + 1) (g t) x) := by
    intro t
    rw [iteratedFDeriv_succ_eq_comp_right]
    simp
  have hfun : (fun t => iteratedFDeriv ℝ k (fun y => fderiv ℝ (g t) y) x) = fun t =>
      (continuousMultilinearCurryRightEquiv' ℝ k H E) (iteratedFDeriv ℝ (k + 1) (g t) x) :=
    funext e
  rw [hfun]
  exact (continuousMultilinearCurryRightEquiv' ℝ k H E).continuous.comp_aestronglyMeasurable h

/-- Almost every `t > 1` (for the restricted measure on `(1,∞)`). -/
theorem ae_Ioi_one_of {p : ℝ → Prop} (h : ∀ t : ℝ, 1 < t → p t) :
    ∀ᵐ t ∂(volume.restrict (Ioi (1 : ℝ))), p t :=
  (ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall fun t ht => h t ht)

/-- Finite-order differentiation under the integral over `(1,∞)`, for a general normed target. -/
theorem paramDiff (N : ℕ) : ∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (U : Set H) (F : ℝ → H → E), IsOpen U →
    (∀ t : ℝ, 1 < t → ContDiffOn ℝ (N : WithTop ℕ∞) (F t) U) →
    (∀ k : ℕ, k ≤ N → ∀ x ∈ U,
      AEStronglyMeasurable (fun t => iteratedFDeriv ℝ k (F t) x) (volume.restrict (Ioi (1 : ℝ)))) →
    (∀ x₀ ∈ U, ∃ ε : ℝ, 0 < ε ∧ ∃ bd : ℝ → ℝ, IntegrableOn bd (Ioi (1 : ℝ)) ∧
      ∀ k : ℕ, k ≤ N → ∀ t : ℝ, 1 < t → ∀ x ∈ U ∩ ball x₀ ε,
        ‖iteratedFDeriv ℝ k (F t) x‖ ≤ bd t) →
    ContDiffOn ℝ (N : WithTop ℕ∞) (fun x => ∫ t in Ioi (1 : ℝ), F t x) U := by
  induction N with
  | zero =>
    intro E _ _ U F hU hF hM hD
    rw [Nat.cast_zero, contDiffOn_zero]
    intro x hx
    apply ContinuousAt.continuousWithinAt
    obtain ⟨ε, hε, bd, hbd, hb⟩ := hD x hx
    have hs : U ∩ ball x ε ∈ 𝓝 x := (hU.inter isOpen_ball).mem_nhds ⟨hx, mem_ball_self hε⟩
    refine MeasureTheory.continuousAt_of_dominated (bound := bd) ?_ ?_ hbd ?_
    · filter_upwards [hs] with y hy
      exact aesm_zero F y (hM 0 (Nat.zero_le _) y hy.1)
    · filter_upwards [hs] with y hy
      exact ae_Ioi_one_of fun t ht => by simpa using hb 0 (Nat.zero_le _) t ht y hy
    · exact ae_Ioi_one_of fun t ht => (hF t ht).continuousOn.continuousAt (hU.mem_nhds hx)
  | succ N ih =>
    intro E _ _ U F hU hF hM hD
    have hdiff : ∀ x ∈ U, HasFDerivAt (fun y => ∫ t in Ioi (1 : ℝ), F t y)
        (∫ t in Ioi (1 : ℝ), fderiv ℝ (F t) x) x := by
      intro x hx
      obtain ⟨ε, hε, bd, hbd, hb⟩ := hD x hx
      have hs : U ∩ ball x ε ∈ 𝓝 x := (hU.inter isOpen_ball).mem_nhds ⟨hx, mem_ball_self hε⟩
      have hbdae : ∀ y ∈ U ∩ ball x ε, ∀ᵐ t ∂(volume.restrict (Ioi (1 : ℝ))), ‖F t y‖ ≤ bd t :=
        fun y hy => ae_Ioi_one_of fun t ht => by
          simpa using hb 0 (Nat.zero_le _) t ht y hy
      refine hasFDerivAt_integral_of_dominated_of_fderiv_le
        (μ := volume.restrict (Ioi (1 : ℝ))) (F := fun y t => F t y)
        (F' := fun y t => fderiv ℝ (F t) y) (x₀ := x) (bound := bd) (s := U ∩ ball x ε)
        hs ?_ ?_ ?_ ?_ hbd ?_
      · filter_upwards [hs] with y hy
        exact aesm_zero F y (hM 0 (Nat.zero_le _) y hy.1)
      · exact hbd.mono' (aesm_zero F x (hM 0 (Nat.zero_le _) x hx))
          (hbdae x ⟨hx, mem_ball_self hε⟩)
      · exact aesm_zero (fun t y => fderiv ℝ (F t) y) x
          (aesm_jet_fderiv 0 F x (hM 1 (by omega) x hx))
      · exact ae_Ioi_one_of fun t ht y hy => by
          simpa using hb 1 (by omega) t ht y hy
      · exact ae_Ioi_one_of fun t ht y hy =>
          ((((hF t ht).differentiableOn (by simp)).differentiableAt
            (hU.mem_nhds hy.1)).hasFDerivAt)
    have hcongr : ∀ x ∈ U, fderiv ℝ (fun y => ∫ t in Ioi (1 : ℝ), F t y) x =
        ∫ t in Ioi (1 : ℝ), fderiv ℝ (F t) x := fun x hx => (hdiff x hx).fderiv
    have hF' : ∀ t : ℝ, 1 < t → ContDiffOn ℝ (N : WithTop ℕ∞) (fun y => fderiv ℝ (F t) y) U :=
      fun t ht => (hF t ht).fderiv_of_isOpen hU (by push_cast; exact le_rfl)
    have hM' : ∀ k : ℕ, k ≤ N → ∀ x ∈ U,
        AEStronglyMeasurable (fun t => iteratedFDeriv ℝ k (fun y => fderiv ℝ (F t) y) x)
          (volume.restrict (Ioi (1 : ℝ))) :=
      fun k hk x hx => aesm_jet_fderiv k F x (hM (k + 1) (by omega) x hx)
    have hD' : ∀ x₀ ∈ U, ∃ ε : ℝ, 0 < ε ∧ ∃ bd : ℝ → ℝ, IntegrableOn bd (Ioi (1 : ℝ)) ∧
        ∀ k : ℕ, k ≤ N → ∀ t : ℝ, 1 < t → ∀ x ∈ U ∩ ball x₀ ε,
          ‖iteratedFDeriv ℝ k (fun y => fderiv ℝ (F t) y) x‖ ≤ bd t := by
      intro x₀ hx₀
      obtain ⟨ε, hε, bd, hbd, hb⟩ := hD x₀ hx₀
      refine ⟨ε, hε, bd, hbd, fun k hk t ht x hx => ?_⟩
      have e := norm_iteratedFDeriv_fderiv (𝕜 := ℝ) (f := F t) (x := x) (n := k)
      exact e.trans_le (hb (k + 1) (by omega) t ht x hx)
    have hG : ContDiffOn ℝ (N : WithTop ℕ∞) (fun x => ∫ t in Ioi (1 : ℝ), fderiv ℝ (F t) x) U :=
      ih (E := H →L[ℝ] E) U (fun t y => fderiv ℝ (F t) y) hU hF' hM' hD'
    rw [Nat.cast_succ, contDiffOn_succ_iff_fderiv_of_isOpen hU]
    refine ⟨fun x hx => (hdiff x hx).differentiableAt.differentiableWithinAt,
      fun hω => absurd hω (by simp), ?_⟩
    exact hG.congr hcongr

end UnforcedLeray.Short.PartIIIb.Concrete.ParamInt7Aux
