import UnforcedLeray.Statement
import Mathlib.Analysis.Calculus.ParametricIntegral

/-!
# B0306 helper: iterated derivatives of a bilinear convolution

Helper module of blueprint unit B0306 (`background:eq:2.48`, `paper/main.tex` lines
5909--5921). The heat smoothing `e^{νΔ}b` is a convolution `∫ x, L (w x) (g (y - x))` of an
integrable factor `w` with a smooth factor `g` whose derivatives of every order are bounded.
We differentiate under the integral sign at every order (Mathlib supplies the first-order rule
`hasFDerivAt_integral_of_dominated_of_fderiv_le`): the convolution is `C^n` and its `n`-th
derivative is the convolution of `w` with `Dⁿ g` (`iteratedFDeriv_bconv`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Metric
open scoped ContDiff Topology

namespace UnforcedLeray.B0306

variable {E' : Type} [NormedAddCommGroup E'] [NormedSpace ℝ E']

/-- The bilinear convolution `y ↦ ∫ x, L (w x) (g (y - x))`. -/
def bconv {F H : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup H]
    [NormedSpace ℝ H] (L : E' →L[ℝ] F →L[ℝ] H) (w : Space → E') (g : Space → F)
    (y : Space) : H :=
  ∫ x, L (w x) (g (y - x))

/-- Every iterated derivative of `g` is bounded on all of space. -/
def BddDerivs {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] (g : Space → F) : Prop :=
  ∀ k : ℕ, ∃ M : ℝ, ∀ x, ‖iteratedFDeriv ℝ k g x‖ ≤ M

theorem BddDerivs.fderiv {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] {g : Space → F}
    (hg : BddDerivs g) : BddDerivs (fderiv ℝ g) := by
  intro k
  obtain ⟨M, hM⟩ := hg (k + 1)
  exact ⟨M, fun x => by rw [norm_iteratedFDeriv_fderiv]; exact hM x⟩

/-- One differentiation under the integral sign. -/
theorem hasFDerivAt_bconv {F H : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup H] [NormedSpace ℝ H] [CompleteSpace H]
    (L : E' →L[ℝ] F →L[ℝ] H) {w : Space → E'} (hw : Integrable w)
    {g : Space → F} (hg : ContDiff ℝ 1 g) {M0 M1 : ℝ} (h0 : ∀ x, ‖g x‖ ≤ M0)
    (h1 : ∀ x, ‖fderiv ℝ g x‖ ≤ M1) (y₀ : Space) :
    HasFDerivAt (bconv L w g) (bconv (L.precompR Space) w (fderiv ℝ g) y₀) y₀ := by
  have hgd : Differentiable ℝ g := hg.differentiable one_ne_zero
  have hgc : Continuous (fderiv ℝ g) := hg.continuous_fderiv one_ne_zero
  have hM0 : 0 ≤ M0 := (norm_nonneg _).trans (h0 0)
  have hM1 : 0 ≤ M1 := (norm_nonneg _).trans (h1 0)
  have hsub : Continuous (fun x : Space => y₀ - x) := continuous_const.sub continuous_id
  unfold bconv
  refine hasFDerivAt_integral_of_dominated_of_fderiv_le (s := Set.univ)
    (F' := fun y x => L.precompR Space (w x) (fderiv ℝ g (y - x)))
    (bound := fun x => ‖L‖ * ‖w x‖ * M1) Filter.univ_mem ?_ ?_ ?_ ?_ ?_ ?_
  · filter_upwards with y
    exact L.aestronglyMeasurable_comp₂ hw.aestronglyMeasurable
      (hgd.continuous.comp (continuous_const.sub continuous_id)).aestronglyMeasurable
  · refine Integrable.mono' ((hw.norm.const_mul ‖L‖).mul_const M0)
      (L.aestronglyMeasurable_comp₂ hw.aestronglyMeasurable
        (hgd.continuous.comp hsub).aestronglyMeasurable) ?_
    filter_upwards with x
    calc ‖L (w x) (g (y₀ - x))‖ ≤ ‖L (w x)‖ * ‖g (y₀ - x)‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ ‖L‖ * ‖w x‖ * M0 :=
        mul_le_mul (L.le_opNorm _) (h0 _) (norm_nonneg _) (by positivity)
  · exact (L.precompR Space).aestronglyMeasurable_comp₂ hw.aestronglyMeasurable
      (hgc.comp hsub).aestronglyMeasurable
  · filter_upwards with x y _
    calc ‖L.precompR Space (w x) (fderiv ℝ g (y - x))‖
        = ‖(L (w x)).comp (fderiv ℝ g (y - x))‖ := rfl
      _ ≤ ‖L (w x)‖ * ‖fderiv ℝ g (y - x)‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ ‖L‖ * ‖w x‖ * M1 :=
        mul_le_mul (L.le_opNorm _) (h1 _) (norm_nonneg _) (by positivity)
  · exact (hw.norm.const_mul ‖L‖).mul_const M1
  · filter_upwards with x y _
    have h2 : HasFDerivAt (fun y : Space => y - x) (ContinuousLinearMap.id ℝ Space) y :=
      (hasFDerivAt_id y).sub_const x
    have hin : HasFDerivAt (fun y : Space => g (y - x)) (fderiv ℝ g (y - x)) y :=
      ((hgd (y - x)).hasFDerivAt.comp y h2).congr_fderiv (ContinuousLinearMap.comp_id _)
    exact (L (w x)).hasFDerivAt.comp y hin

/-- **Iterated differentiation under the integral sign.** If `w` is integrable and `g` is
smooth with bounded derivatives of every order, then `bconv L w g` is `C^n` and its `n`-th
derivative is `∫ x, L (w x) ∘ Dⁿ g (y - x)`. -/
theorem iteratedFDeriv_bconv {w : Space → E'} (hw : Integrable w) (n : ℕ) :
    ∀ {F H : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup H]
      [NormedSpace ℝ H] [CompleteSpace H] (L : E' →L[ℝ] F →L[ℝ] H) (g : Space → F),
      ContDiff ℝ ∞ g → BddDerivs g →
      ContDiff ℝ n (bconv L w g) ∧
      iteratedFDeriv ℝ n (bconv L w g) =
        fun y => ∫ x, (L (w x)).compContinuousMultilinearMap (iteratedFDeriv ℝ n g (y - x)) := by
  induction n with
  | zero =>
    intro F H _ _ _ _ _ L g hg hgb
    obtain ⟨M0, hM0⟩ := hgb 0
    obtain ⟨M1, hM1⟩ := hgb 1
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
    obtain ⟨M0, hM0⟩ := hgb 0
    obtain ⟨M1, hM1⟩ := hgb 1
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

end UnforcedLeray.B0306
