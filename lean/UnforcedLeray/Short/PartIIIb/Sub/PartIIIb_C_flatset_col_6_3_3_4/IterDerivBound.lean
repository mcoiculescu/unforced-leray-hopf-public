import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Module.Multilinear.Basic

/-!
# Directional derivative of an iterated derivative (helper for the flat-setting jets)

For `g : ℝ × ℝ → E` smooth, `z ↦ iteratedFDeriv ℝ n g z m` has derivative in direction `d`
equal to `iteratedFDeriv ℝ (n+1) g x (Fin.cons d m)`, so it is bounded by the `(n+1)`-st
derivative norm when all the vectors have norm at most `1`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

theorem fderiv_iteratedFDeriv_apply_eq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {g : ℝ × ℝ → E} (hg : ContDiff ℝ ∞ g) (n : ℕ) (x d : ℝ × ℝ) (m : Fin n → ℝ × ℝ) :
    fderiv ℝ (fun z => iteratedFDeriv ℝ n g z m) x d =
      iteratedFDeriv ℝ (n + 1) g x (Fin.cons d m : Fin (n + 1) → ℝ × ℝ) := by
  have hdiff : Differentiable ℝ (iteratedFDeriv ℝ n g) :=
    hg.differentiable_iteratedFDeriv (by exact_mod_cast WithTop.coe_lt_top _)
  have hfun : (fun z => iteratedFDeriv ℝ n g z m) =
      fun z => (ContinuousMultilinearMap.apply ℝ (fun _ : Fin n => ℝ × ℝ) E m) (iteratedFDeriv ℝ n g z) :=
    rfl
  have hD : HasFDerivAt (fun z => iteratedFDeriv ℝ n g z m)
      ((ContinuousMultilinearMap.apply ℝ (fun _ : Fin n => ℝ × ℝ) E m).comp
        (fderiv ℝ (iteratedFDeriv ℝ n g) x)) x := by
    rw [hfun]
    exact (ContinuousMultilinearMap.apply ℝ (fun _ : Fin n => ℝ × ℝ) E m).hasFDerivAt.comp x
      (hdiff x).hasFDerivAt
  rw [hD.fderiv, ContinuousLinearMap.comp_apply, iteratedFDeriv_succ_apply_left]
  simp

theorem norm_fderiv_iteratedFDeriv_apply_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {g : ℝ × ℝ → E} (hg : ContDiff ℝ ∞ g) (n : ℕ) (x d : ℝ × ℝ) (m : Fin n → ℝ × ℝ)
    (hd : ‖d‖ ≤ 1) (hm : ∀ i, ‖m i‖ ≤ 1) :
    ‖fderiv ℝ (fun z => iteratedFDeriv ℝ n g z m) x d‖ ≤ ‖iteratedFDeriv ℝ (n + 1) g x‖ := by
  rw [fderiv_iteratedFDeriv_apply_eq hg n x d m]
  have hle := ContinuousMultilinearMap.le_opNorm (iteratedFDeriv ℝ (n + 1) g x)
    (Fin.cons d m : Fin (n + 1) → ℝ × ℝ)
  have hprod : ∏ i, ‖(Fin.cons d m : Fin (n + 1) → ℝ × ℝ) i‖ ≤ 1 := by
    rw [Fin.prod_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ]
    have h1 : ∏ i : Fin n, ‖m i‖ ≤ 1 :=
      Finset.prod_le_one (fun i _ => norm_nonneg _) (fun i _ => hm i)
    have h0 : ‖d‖ ≤ 1 := hd
    calc ‖d‖ * ∏ i : Fin n, ‖m i‖ ≤ 1 * 1 :=
          mul_le_mul h0 h1 (Finset.prod_nonneg fun i _ => norm_nonneg _) zero_le_one
      _ = 1 := one_mul 1
  exact hle.trans (mul_le_of_le_one_right (norm_nonneg _) hprod)

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
