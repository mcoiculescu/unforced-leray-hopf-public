import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Std.Tactic.BVDecide.LRAT.Internal.Formula.RupAddResult

/-!
# Derivatives of an iterated derivative applied to fixed vectors (helper for INF22 K1–K4)

Helper module of `Lib/Kernels.lean`. For `f` smooth near `x` and fixed vectors `m`, the function
`y ↦ Dᵏf(y)[m]` has `j`-th derivative of norm at most ‖D^{j+k} f(x)‖ ∏ ‖mᵢ‖. This is how
directional (coordinate) derivatives of the Newton potential, of the heat-time potential and of the
Oseen kernel inherit the bounds on the full iterated derivative (scoping note
`INF22-INF27-Kernels.md`, §5 K1–K4).
-/

set_option autoImplicit false

noncomputable section

open Set Filter
open scoped ContDiff Topology

namespace UnforcedLeray.Kernels

universe u

theorem infty_add_one_le : (∞ : ℕ∞ω) + 1 ≤ ∞ := le_of_eq rfl

theorem infty_add_nat_le {k : ℕ} : (∞ : ℕ∞ω) + k ≤ ∞ := le_of_eq rfl

/-- `‖Dʲ (y ↦ Dᵏ f(y)[m])(x)‖ ≤ ‖D^{j+k} f(x)‖ ∏ ‖mᵢ‖` for `f` smooth near `x`. -/
theorem norm_iteratedFDeriv_apply_le {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (k : ℕ) : ∀ {F : Type u} [NormedAddCommGroup F] [NormedSpace ℝ F] (f : E → F) (x : E),
    ContDiffAt ℝ ∞ f x → ∀ (m : Fin k → E) (j : ℕ),
    ‖iteratedFDeriv ℝ j (fun y => iteratedFDeriv ℝ k f y m) x‖ ≤
      ‖iteratedFDeriv ℝ (j + k) f x‖ * ∏ i, ‖m i‖ := by
  induction k with
  | zero =>
    intro F _ _ f x _ m j
    simp only [iteratedFDeriv_zero_apply, Finset.univ_eq_empty, Finset.prod_empty, mul_one,
      add_zero]
    exact le_rfl
  | succ k ih =>
    intro F _ _ f x hf m j
    have hfun : (fun y => iteratedFDeriv ℝ (k + 1) f y m) =
        (ContinuousLinearMap.apply ℝ F (m (Fin.last k))) ∘
          (fun y => iteratedFDeriv ℝ k (fderiv ℝ f) y (Fin.init m)) := by
      funext y
      simp [iteratedFDeriv_succ_apply_right]
    rw [hfun]
    have h1 : ContDiffAt ℝ ∞ (fderiv ℝ f) x := hf.fderiv_right infty_add_one_le
    have hsm : ContDiffAt ℝ ∞ (fun y => iteratedFDeriv ℝ k (fderiv ℝ f) y (Fin.init m)) x := by
      have h2 : ContDiffAt ℝ ∞ (iteratedFDeriv ℝ k (fderiv ℝ f)) x :=
        h1.iteratedFDeriv_right infty_add_nat_le
      exact (ContinuousMultilinearMap.apply ℝ (fun _ : Fin k => E) (E →L[ℝ] F)
        (Fin.init m)).contDiff.contDiffAt.comp x h2
    have hap : ‖ContinuousLinearMap.apply ℝ F (m (Fin.last k))‖ ≤ ‖m (Fin.last k)‖ :=
      ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun L => by
        simpa [mul_comm] using L.le_opNorm (m (Fin.last k))
    calc ‖iteratedFDeriv ℝ j ((ContinuousLinearMap.apply ℝ F (m (Fin.last k))) ∘
          (fun y => iteratedFDeriv ℝ k (fderiv ℝ f) y (Fin.init m))) x‖
        ≤ ‖ContinuousLinearMap.apply ℝ F (m (Fin.last k))‖ *
          ‖iteratedFDeriv ℝ j (fun y => iteratedFDeriv ℝ k (fderiv ℝ f) y (Fin.init m)) x‖ :=
          ContinuousLinearMap.norm_iteratedFDeriv_comp_left _ hsm (by exact_mod_cast le_top)
      _ ≤ ‖m (Fin.last k)‖ * (‖iteratedFDeriv ℝ (j + k) (fderiv ℝ f) x‖ *
            ∏ i, ‖Fin.init m i‖) := by
          gcongr
          exact ih (fderiv ℝ f) x h1 (Fin.init m) j
      _ = ‖iteratedFDeriv ℝ (j + (k + 1)) f x‖ * ∏ i, ‖m i‖ := by
          rw [norm_iteratedFDeriv_fderiv, Fin.prod_univ_castSucc]
          simp only [Fin.init]
          rw [show j + k + 1 = j + (k + 1) by omega]
          ring

/-- Smoothness near `x` of `y ↦ Dᵏ f(y)[m]`. -/
theorem contDiffAt_iteratedFDeriv_apply {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E → F} {x : E} (hf : ContDiffAt ℝ ∞ f x)
    (k : ℕ) (m : Fin k → E) :
    ContDiffAt ℝ ∞ (fun y => iteratedFDeriv ℝ k f y m) x := by
  have h2 : ContDiffAt ℝ ∞ (iteratedFDeriv ℝ k f) x :=
    hf.iteratedFDeriv_right infty_add_nat_le
  exact (ContinuousMultilinearMap.apply ℝ (fun _ : Fin k => E) F m).contDiff.contDiffAt.comp x h2

end UnforcedLeray.Kernels
