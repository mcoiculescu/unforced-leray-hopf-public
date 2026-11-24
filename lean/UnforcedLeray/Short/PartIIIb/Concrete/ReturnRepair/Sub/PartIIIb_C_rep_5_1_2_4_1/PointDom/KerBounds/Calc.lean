import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Operator.Banach

/-!
# Generic calculus helpers for `PDKerBounds` (`PointDom/KerBounds`)

* `kb_fderiv_apply_norm`: the `n`-th derivative of `y ↦ ∂_v f y` is at most `‖v‖ ‖D^{n+1} f‖`.
* `kb_norm_le_sum`: the Euclidean norm on `ℝ³` is at most the sum of the absolute coordinates.
* `kb_norm_iteratedFDeriv_vec`: a `ℝ³`-valued map has `n`-th derivative at most the sum of the
  norms of the `n`-th derivatives of its coordinates (the `Fin 3` version of
  `Spine.norm_iteratedFDeriv_euclid2_le`).
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete.KB

abbrev Sp := EuclideanSpace ℝ (Fin 3)

theorem kb_fderiv_apply_norm {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : Sp → F} {x : Sp} {n : ℕ}
    (hf : ContDiffAt ℝ ((n + 1 : ℕ) : WithTop ℕ∞) f x) (v : Sp) :
    ‖iteratedFDeriv ℝ n (fun y => fderiv ℝ f y v) x‖ ≤ ‖v‖ * ‖iteratedFDeriv ℝ (n + 1) f x‖ := by
  have hd : ContDiffAt ℝ (n : WithTop ℕ∞) (fderiv ℝ f) x :=
    hf.fderiv_right (m := (n : WithTop ℕ∞)) (by norm_cast)
  have h1 := norm_iteratedFDeriv_clm_apply_const (f := fderiv ℝ f) (c := v) (x := x)
    (N := (n : WithTop ℕ∞)) (n := n) hd le_rfl
  rw [norm_iteratedFDeriv_fderiv] at h1
  exact h1

theorem kb_norm_le_sum (v : Sp) : ‖v‖ ≤ ∑ i : Fin 3, ‖v i‖ := by
  rw [EuclideanSpace.norm_eq]
  simp only [Fin.sum_univ_three]
  have h0 := norm_nonneg (v 0)
  have h1 := norm_nonneg (v 1)
  have h2 := norm_nonneg (v 2)
  rw [Real.sqrt_le_left (by positivity)]
  nlinarith [mul_nonneg h0 h1, mul_nonneg h1 h2, mul_nonneg h0 h2]

theorem kb_norm_iteratedFDeriv_vec {f : Sp → Sp} {x : Sp} {n : ℕ} {N : WithTop ℕ∞}
    (hf : ContDiffAt ℝ N f x) (hn : (n : WithTop ℕ∞) ≤ N) :
    ‖iteratedFDeriv ℝ n f x‖ ≤ ∑ i : Fin 3, ‖iteratedFDeriv ℝ n (fun y => f y i) x‖ := by
  have hcomp : ∀ i : Fin 3,
      iteratedFDeriv ℝ n (fun y => f y i) x =
        (EuclideanSpace.proj i : Sp →L[ℝ] ℝ).compContinuousMultilinearMap
          (iteratedFDeriv ℝ n f x) := by
    intro i
    exact ContinuousLinearMap.iteratedFDeriv_comp_left
      (EuclideanSpace.proj i : Sp →L[ℝ] ℝ) hf hn
  have hcoord : ∀ (i : Fin 3) (m : Fin n → Sp),
      ‖iteratedFDeriv ℝ n (fun y => f y i) x m‖ ≤
        ‖iteratedFDeriv ℝ n (fun y => f y i) x‖ * ∏ k, ‖m k‖ :=
    fun i m => (iteratedFDeriv ℝ n (fun y => f y i) x).le_opNorm m
  refine ContinuousMultilinearMap.opNorm_le_bound ?_ ?_
  · exact Finset.sum_nonneg fun i _ => norm_nonneg _
  intro m
  have hsplit : ‖iteratedFDeriv ℝ n f x m‖ ≤ ∑ i : Fin 3, ‖iteratedFDeriv ℝ n f x m i‖ :=
    kb_norm_le_sum _
  have hval : ∀ i : Fin 3, ‖iteratedFDeriv ℝ n f x m i‖ =
      ‖iteratedFDeriv ℝ n (fun y => f y i) x m‖ := by
    intro i
    rw [hcomp i]
    rfl
  calc ‖iteratedFDeriv ℝ n f x m‖ ≤ ∑ i : Fin 3, ‖iteratedFDeriv ℝ n (fun y => f y i) x m‖ := by
        simpa [hval] using hsplit
    _ ≤ ∑ i : Fin 3, ‖iteratedFDeriv ℝ n (fun y => f y i) x‖ * ∏ k, ‖m k‖ :=
        Finset.sum_le_sum fun i _ => hcoord i m
    _ = (∑ i : Fin 3, ‖iteratedFDeriv ℝ n (fun y => f y i) x‖) * ∏ k, ‖m k‖ := by
        rw [Finset.sum_mul]

end UnforcedLeray.Short.PartIIIb.Concrete.KB

end
