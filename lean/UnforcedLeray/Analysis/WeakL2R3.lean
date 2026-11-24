import UnforcedLeray.Statement
import UnforcedLeray.Analysis.WeakCompactness
import Mathlib.MeasureTheory.Function.L2Space

/-!
Concrete R³ vector-valued L² applications of the Hilbert-space infrastructure
adapted from NonUniqueEuler. The weak limits below are actual L² classes and
convergence is tested by actual Lebesgue integrals.
-/
noncomputable section
open MeasureTheory Filter
open scoped InnerProductSpace Topology
namespace UnforcedLeray

/-- L² inner products of the chosen classes are the actual vector-field integrals. -/
theorem inner_toL2_eq_integral {f g : SpatialField}
    (hf : MemLp f 2 volume) (hg : MemLp g 2 volume) :
    ⟪toL2 f, toL2 g⟫_ℝ = ∫ x : Space, ⟪f x, g x⟫_ℝ := by
  rw [MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  filter_upwards [coeFn_toL2 hf, coeFn_toL2 hg] with x hx hy
  rw [hx, hy]

/-- Every bounded sequence of actual R³ vector fields has a weak L² subsequence. -/
theorem exists_weak_L2_subsequence (u : ℕ → SpatialField) (M : ℝ)
    (hu : ∀ n, MemLp (u n) 2 volume)
    (hbound : ∀ n, l2Norm (u n) ≤ M) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ v : L2Space, ‖v‖ ≤ M ∧
      ∀ ψ : SpatialField, MemLp ψ 2 volume →
        Tendsto (fun n => ∫ x : Space, ⟪u (φ n) x, ψ x⟫_ℝ) atTop
          (𝓝 (∫ x : Space, ⟪v x, ψ x⟫_ℝ)) := by
  obtain ⟨φ, hφ, v, hv, hw⟩ := WeakL2.exists_subseq_weakTendsto
    (u := fun n => toL2 (u n)) (M := M)
    (fun n => by simpa only [norm_toL2 (hu n)] using hbound n)
  refine ⟨φ, hφ, v, hv, fun ψ hψ => ?_⟩
  have h := hw (toL2 ψ)
  have hvψ : ⟪v, toL2 ψ⟫_ℝ = ∫ x : Space, ⟪v x, ψ x⟫_ℝ := by
    rw [MeasureTheory.L2.inner_def]
    apply integral_congr_ae
    filter_upwards [coeFn_toL2 hψ] with x hx
    rw [hx]
  simpa only [Function.comp_apply, inner_toL2_eq_integral (hu _) hψ, hvψ] using h

end UnforcedLeray
