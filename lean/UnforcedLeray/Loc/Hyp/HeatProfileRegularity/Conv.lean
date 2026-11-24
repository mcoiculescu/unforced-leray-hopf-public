import UnforcedLeray.Units.B0306.Conv

/-!
# `HeatProfileRegularity` helper: differentiation of a convolution to finite order

Helper module of `Loc/Hyp/HeatProfileRegularity.lean` (hypothesis `HeatProfileRegularity`,
infrastructure INF04, blueprint unit B0710; `paper/main.tex` lines 274–281).

`Units/B0306/Conv.lean` (`iteratedFDeriv_bconv`) differentiates `y ↦ ∫ x, L (w x) (g (y - x))`
under the integral sign at every order when `g` has bounded derivatives of *every* order. The
manuscript's datum has derivative bounds only up to a finite order (lines 152–156, `k ≤ 4`), so
we prove the same statement to order `n` assuming bounded derivatives only up to order `n + 1`
(`iteratedFDeriv_bconv_upTo`). The proof is the B0306 induction, with the bound hypothesis
restricted to the orders it uses.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Metric
open scoped ContDiff Topology

namespace UnforcedLeray.HeatProfileReg

open UnforcedLeray.B0306

variable {E' : Type} [NormedAddCommGroup E'] [NormedSpace ℝ E']

/-- The derivatives of `g` of order `≤ N` are bounded on all of space. -/
def BddDerivsUpTo {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] (N : ℕ) (g : Space → F) :
    Prop :=
  ∀ k : ℕ, k ≤ N → ∃ M : ℝ, ∀ x, ‖iteratedFDeriv ℝ k g x‖ ≤ M

theorem BddDerivsUpTo.fderiv {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] {N : ℕ}
    {g : Space → F} (hg : BddDerivsUpTo (N + 1) g) : BddDerivsUpTo N (fderiv ℝ g) := by
  intro k hk
  obtain ⟨M, hM⟩ := hg (k + 1) (by omega)
  exact ⟨M, fun x => by rw [norm_iteratedFDeriv_fderiv]; exact hM x⟩

/-- **Differentiation under the integral sign to order `n`** (finite-order version of
`B0306.iteratedFDeriv_bconv`): if `w` is integrable and `g` is smooth with bounded derivatives
of order `≤ n + 1`, then `bconv L w g` is `C^n` with `n`-th derivative
`∫ x, L (w x) ∘ Dⁿ g (y - x)`. -/
theorem iteratedFDeriv_bconv_upTo {w : Space → E'} (hw : Integrable w) (n : ℕ) :
    ∀ {F H : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup H]
      [NormedSpace ℝ H] [CompleteSpace H] (L : E' →L[ℝ] F →L[ℝ] H) (g : Space → F),
      ContDiff ℝ ∞ g → BddDerivsUpTo (n + 1) g →
      ContDiff ℝ n (bconv L w g) ∧
      iteratedFDeriv ℝ n (bconv L w g) =
        fun y => ∫ x, (L (w x)).compContinuousMultilinearMap (iteratedFDeriv ℝ n g (y - x)) := by
  induction n with
  | zero =>
    intro F H _ _ _ _ _ L g hg hgb
    obtain ⟨M0, hM0⟩ := hgb 0 (by omega)
    obtain ⟨M1, hM1⟩ := hgb 1 (by omega)
    simp only [norm_iteratedFDeriv_zero] at hM0
    simp only [norm_iteratedFDeriv_one] at hM1
    have hd : ∀ y, HasFDerivAt (bconv L w g) _ y := fun y =>
      hasFDerivAt_bconv L hw (hg.of_le (by exact_mod_cast le_top)) hM0 hM1 y
    refine ⟨contDiff_zero.mpr (continuous_iff_continuousAt.mpr fun y => (hd y).continuousAt), ?_⟩
    funext y
    simp only [iteratedFDeriv_zero_eq_comp, Function.comp_apply]
    have hpt : ∀ x, (L (w x)).compContinuousMultilinearMap
        ((continuousMultilinearCurryFin0 ℝ Space F).symm (g (y - x))) =
        (continuousMultilinearCurryFin0 ℝ Space H).symm (L (w x) (g (y - x))) := by
      intro x; ext m; simp
    simp only [hpt]
    exact (LinearIsometry.integral_comp_comm
      (continuousMultilinearCurryFin0 ℝ Space H).symm.toLinearIsometry _).symm
  | succ n ih =>
    intro F H _ _ _ _ _ L g hg hgb
    obtain ⟨M0, hM0⟩ := hgb 0 (by omega)
    obtain ⟨M1, hM1⟩ := hgb 1 (by omega)
    simp only [norm_iteratedFDeriv_zero] at hM0
    simp only [norm_iteratedFDeriv_one] at hM1
    have hd : ∀ y, HasFDerivAt (bconv L w g) _ y := fun y =>
      hasFDerivAt_bconv L hw (hg.of_le (by exact_mod_cast le_top)) hM0 hM1 y
    have hfd : fderiv ℝ (bconv L w g) = bconv (L.precompR Space) w (fderiv ℝ g) :=
      funext fun y => (hd y).fderiv
    have hg' : ContDiff ℝ ∞ (fderiv ℝ g) := (contDiff_infty_iff_fderiv.mp hg).2
    obtain ⟨ihc, ihe⟩ := ih (L.precompR Space) (fderiv ℝ g) hg' hgb.fderiv
    refine ⟨?_, ?_⟩
    · have : ((n + 1 : ℕ) : WithTop ℕ∞) = (n : WithTop ℕ∞) + 1 := by push_cast; rfl
      rw [this, contDiff_succ_iff_fderiv]
      exact ⟨fun y => (hd y).differentiableAt, by simp, hfd ▸ ihc⟩
    · funext y
      rw [iteratedFDeriv_succ_eq_comp_right, Function.comp_apply]
      have hfd' : (fun y => fderiv ℝ (bconv L w g) y) = bconv (L.precompR Space) w (fderiv ℝ g) :=
        hfd
      rw [hfd', ihe]
      have hpt : ∀ x, (L (w x)).compContinuousMultilinearMap
          (iteratedFDeriv ℝ (n + 1) g (y - x)) =
          (continuousMultilinearCurryRightEquiv' ℝ n Space H).symm
            (((L.precompR Space) (w x)).compContinuousMultilinearMap
              (iteratedFDeriv ℝ n (fderiv ℝ g) (y - x))) := by
        intro x
        rw [iteratedFDeriv_succ_eq_comp_right, Function.comp_apply]
        ext m
        simp
      simp only [hpt]
      exact (ContinuousLinearEquiv.integral_comp_comm (𝕜 := ℝ) (μ := (volume : Measure Space))
        (E := Space [×n]→L[ℝ] Space →L[ℝ] H) (F := Space [×n.succ]→L[ℝ] H)
        (continuousMultilinearCurryRightEquiv' ℝ n Space H).symm.toContinuousLinearEquiv _).symm

end UnforcedLeray.HeatProfileReg
