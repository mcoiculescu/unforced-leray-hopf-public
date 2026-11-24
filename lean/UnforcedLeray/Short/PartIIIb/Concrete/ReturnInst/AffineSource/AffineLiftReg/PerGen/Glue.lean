import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Complex.Exponential

/-!
# Helpers for the generic lattice-sum smoothness (task `PerGen`)

* `perGen_glue`: a smooth cutoff times a function that is `C^n` on an open set `O` containing the
  support of the cutoff is `C^n` on the whole space.
* `perGen_gauss_summable`: `j ↦ exp(-b j²)` is summable over `ℤ` for `b > 0`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem perGen_glue {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {n : WithTop ℕ∞} (ψ : ℝ × (ℝ × ℝ) → ℝ) (g : ℝ × (ℝ × ℝ) → E) (O : Set (ℝ × (ℝ × ℝ)))
    (hO : IsOpen O) (hψ : ContDiff ℝ n ψ) (hsupp : tsupport ψ ⊆ O)
    (hg : ContDiffOn ℝ n g O) :
    ContDiff ℝ n (fun p => ψ p • g p) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x ∈ O
  · exact ((hψ.contDiffOn).smul hg).contDiffAt (hO.mem_nhds hx)
  · have hxn : x ∉ tsupport ψ := fun h => hx (hsupp h)
    have hev : ψ =ᶠ[𝓝 x] (0 : ℝ × (ℝ × ℝ) → ℝ) := notMem_tsupport_iff_eventuallyEq.mp hxn
    have h2 : (fun p => ψ p • g p) =ᶠ[𝓝 x] (fun _ => (0 : E)) := by
      filter_upwards [hev] with p hp
      simp [hp]
    exact contDiffAt_const.congr_of_eventuallyEq h2

theorem perGen_gauss_summable (b : ℝ) (hb : 0 < b) :
    Summable (fun j : ℤ => Real.exp (-(b * (j : ℝ) ^ 2))) := by
  have hsum : Summable (fun j : ℤ => (2 / b ^ 2) * (1 / (j : ℝ) ^ 4)) :=
    ((Real.summable_one_div_int_pow (p := 4)).mpr (by norm_num)).mul_left _
  refine Summable.of_norm_bounded_eventually hsum ?_
  have hfin : ({(0 : ℤ)} : Set ℤ)ᶜ ∈ cofinite :=
    (Set.finite_singleton (0 : ℤ)).compl_mem_cofinite
  filter_upwards [hfin] with j hj
  have hj0 : (j : ℝ) ≠ 0 := by
    intro h
    have : j = 0 := by exact_mod_cast h
    exact hj (by simp [this])
  have hx : 0 ≤ b * (j : ℝ) ^ 2 := by positivity
  have hq := Real.quadratic_le_exp_of_nonneg hx
  have hpos : 0 < (b * (j : ℝ) ^ 2) ^ 2 / 2 := by
    have : 0 < (j : ℝ) ^ 2 := by positivity
    positivity
  have h2 : (b * (j : ℝ) ^ 2) ^ 2 / 2 ≤ Real.exp (b * (j : ℝ) ^ 2) := by
    nlinarith [hq]
  rw [Real.norm_of_nonneg (Real.exp_pos _).le, Real.exp_neg]
  calc (Real.exp (b * (j : ℝ) ^ 2))⁻¹ ≤ ((b * (j : ℝ) ^ 2) ^ 2 / 2)⁻¹ :=
        inv_anti₀ hpos h2
    _ = (2 / b ^ 2) * (1 / (j : ℝ) ^ 4) := by
        field_simp

end UnforcedLeray.Short.PartIIIb.Concrete
