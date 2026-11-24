import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_7_2_1_2_1_4
import Mathlib.Analysis.Normed.Group.Constructions
import Mathlib.Topology.Algebra.Module.Multilinear.Basic
import Mathlib.Analysis.Normed.Module.Multilinear.Basic

/-!
# `PartIII-a:T21/2/7/2/1/2/1/4`, task `basisExpansion`: expansion in the basis `stDir`

Proves `BasisExpansion` (defined in `Sub/PartIII-a_T21_2_7_2_1_2_1_4.lean`, SP 3060-3073, calculus
only). Each argument `v = v.1 • stDir 0 + v.2.1 • stDir 1 + v.2.2 • stDir 2` has coordinates bounded
by `‖v‖` (sup norm), so multilinearity expands `M v` into `Σ_i (Π_k c_{i k}(v k)) • M (stDir ∘ i)`
with `|Π_k c| ≤ Π_k ‖v k‖`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.IIIa

theorem basisExpansion : UnforcedLeray.Short.IIIa.BasisExpansion := by
  intro n M
  set c : ℝ × (ℝ × ℝ) → Fin 3 → ℝ := fun v => ![v.1, v.2.1, v.2.2] with hc
  have hexp : ∀ v : ℝ × (ℝ × ℝ), v = ∑ a : Fin 3, c v a • stDir a := by
    intro v
    simp [Prod.ext_iff, hc, Fin.sum_univ_three, stDir]
  have hbound : ∀ (v : ℝ × (ℝ × ℝ)) (a : Fin 3), |c v a| ≤ ‖v‖ := by
    intro v a
    have h1 : |v.1| ≤ ‖v‖ := by
      rw [← Real.norm_eq_abs]
      exact norm_fst_le v
    have h2 : |v.2.1| ≤ ‖v‖ := by
      rw [← Real.norm_eq_abs]
      exact (norm_fst_le v.2).trans (norm_snd_le v)
    have h3 : |v.2.2| ≤ ‖v‖ := by
      rw [← Real.norm_eq_abs]
      exact (norm_snd_le v.2).trans (norm_snd_le v)
    fin_cases a
    · exact h1
    · exact h2
    · exact h3
  have hM : ∀ v : Fin n → ℝ × (ℝ × ℝ), M v =
      ∑ i : Fin n → Fin 3, (∏ k, c (v k) (i k)) • M (fun k => stDir (i k)) := by
    intro v
    have h1 : M v = M (fun k => ∑ a : Fin 3, c (v k) a • stDir a) :=
      congrArg M (funext fun k => hexp (v k))
    rw [h1, ContinuousMultilinearMap.map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [ContinuousMultilinearMap.map_smul_univ]
  refine ContinuousMultilinearMap.opNorm_le_bound (Finset.sum_nonneg fun i _ => norm_nonneg _)
    (fun v => ?_)
  rw [hM v]
  calc ‖∑ i : Fin n → Fin 3, (∏ k, c (v k) (i k)) • M (fun k => stDir (i k))‖
      ≤ ∑ i : Fin n → Fin 3, ‖(∏ k, c (v k) (i k)) • M (fun k => stDir (i k))‖ :=
        norm_sum_le _ _
    _ ≤ ∑ i : Fin n → Fin 3, (∏ k, ‖v k‖) * ‖M (fun k => stDir (i k))‖ := by
        refine Finset.sum_le_sum fun i _ => ?_
        rw [norm_smul, Real.norm_eq_abs, Finset.abs_prod]
        refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
        exact Finset.prod_le_prod (fun k _ => abs_nonneg _) (fun k _ => hbound (v k) (i k))
    _ = (∑ i : Fin n → Fin 3, ‖M (fun k => stDir (i k))‖) * ∏ k, ‖v k‖ := by
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun i _ => mul_comm _ _

end UnforcedLeray.Short.IIIa
