import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Std.Tactic.BVDecide.LRAT.Internal.Formula.RupAddResult

/-!
# Spine: Euclidean-two derivative bridge (`norm_iteratedFDeriv_euclid2_le`)

Generic bridge for the train velocity fields. Their values lie in `Train.Vec = Cyl.Vec2 =
EuclideanSpace ℝ (Fin 2)` (`Lib/Train/Ops.lean`, `Lib/Cylinder/Basic.lean`). The norm of the
`j`-th Fréchet derivative of a two-component field is at most the sum of the norms of the `j`-th
derivatives of its two coordinate functions.

No single line of `the November 2 reference manuscript` states this bridge; it is
a general fact used when the Part I/II/III velocity estimates are transferred to coordinates.

Proof outline:
* `ContinuousLinearMap.iteratedFDeriv_comp_left` applied to the coordinate functional
  `EuclideanSpace.proj k` gives `iteratedFDeriv ℝ j (fun x => f x k) z = (proj k)∘ (iteratedFDeriv f z)`.
* `ContinuousMultilinearMap.le_opNorm` bounds each coordinate of the derivative by its operator norm.
* `EuclideanSpace.norm_eq` and `√(a² + b²) ≤ a + b` for `a, b ≥ 0` give the bound on the full norm,
  and `ContinuousMultilinearMap.opNorm_le_bound` converts it to an operator-norm bound.
-/

set_option autoImplicit false

noncomputable section

open scoped ContDiff

namespace UnforcedLeray.Short.Spine

/-- Two-component bridge: for smooth `f : ℝ × ℝ → EuclideanSpace ℝ (Fin 2)`, the norm of the
`j`-th derivative is at most the sum of the norms of the `j`-th derivatives of the coordinate
functions `x ↦ f x 0` and `x ↦ f x 1`. -/
theorem norm_iteratedFDeriv_euclid2_le {f : ℝ × ℝ → EuclideanSpace ℝ (Fin 2)}
    (hf : ContDiff ℝ ∞ f) (j : ℕ) (z : ℝ × ℝ) :
    ‖iteratedFDeriv ℝ j f z‖ ≤
      ‖iteratedFDeriv ℝ j (fun x => f x 0) z‖ + ‖iteratedFDeriv ℝ j (fun x => f x 1) z‖ := by
  have hfz : ContDiffAt ℝ ∞ f z := hf.contDiffAt
  have hj : (j : WithTop ℕ∞) ≤ ∞ := by exact_mod_cast le_top
  -- The `k`-th coordinate of the `j`-th derivative is the `j`-th derivative of the coordinate.
  have hcomp : ∀ k : Fin 2,
      iteratedFDeriv ℝ j (fun x => f x k) z =
        (EuclideanSpace.proj k : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ).compContinuousMultilinearMap
          (iteratedFDeriv ℝ j f z) := by
    intro k
    show iteratedFDeriv ℝ j
        ((EuclideanSpace.proj k : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ) ∘ f) z = _
    exact ContinuousLinearMap.iteratedFDeriv_comp_left
      (EuclideanSpace.proj k : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ) hfz hj
  rw [hcomp 0, hcomp 1]
  -- Each coordinate of a value of the derivative is bounded by the operator norm of that coordinate.
  have hcoord : ∀ (k : Fin 2) (m : Fin j → ℝ × ℝ),
      ‖(iteratedFDeriv ℝ j f z m) k‖ ≤
        ‖(EuclideanSpace.proj k : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ).compContinuousMultilinearMap
          (iteratedFDeriv ℝ j f z)‖ * ∏ i, ‖m i‖ := by
    intro k m
    exact ((EuclideanSpace.proj k : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ).compContinuousMultilinearMap
      (iteratedFDeriv ℝ j f z)).le_opNorm m
  refine ContinuousMultilinearMap.opNorm_le_bound ?_ ?_
  · positivity
  intro m
  have hA0 : 0 ≤ ‖(iteratedFDeriv ℝ j f z m) 0‖ := norm_nonneg _
  have hA1 : 0 ≤ ‖(iteratedFDeriv ℝ j f z m) 1‖ := norm_nonneg _
  have hsq : ‖iteratedFDeriv ℝ j f z m‖ ≤
      ‖(iteratedFDeriv ℝ j f z m) 0‖ + ‖(iteratedFDeriv ℝ j f z m) 1‖ := by
    rw [EuclideanSpace.norm_eq, Fin.sum_univ_two, Real.sqrt_le_left (add_nonneg hA0 hA1)]
    nlinarith [mul_nonneg hA0 hA1]
  exact hsq.trans ((add_le_add (hcoord 0 m) (hcoord 1 m)).trans (le_of_eq (by ring)))

end UnforcedLeray.Short.Spine
