import Mathlib.Analysis.Complex.AbsMax

/-!
# B0034 helper: a zero forced by minimum modulus

*Provenance (Wave 2 block 2H PLAN1b).* Copy of the compiled draft

`Lib/ComplexODE` (the copies `Lib/ComplexODE/NeutralSolution` and `Lib/ComplexODE/L1Dependence`
replace the drafts `Analysis/Rayleigh/Evans/NeutralSolution` and `L1ContinuousGronwall`), with
namespace `UnforcedLeray.ComplexODEB` in place of `UnforcedLeray.B0034`. Do not import it
together with `Units/B0034` helpers that pull in those drafts.

Copied from the draft

(which does not currently compile: one `simpa` needs `mem_setOf_eq`), repaired and
placed in the B0034 namespace. Used for the Hurwitz openness step of the
continuation behind B0034 (`paper/main.tex`, lines 1012–1014). The proof is the
maximum-modulus theorem applied to the reciprocal; no argument principle is assumed.
-/

set_option autoImplicit false

noncomputable section
open Set Metric
namespace UnforcedLeray.ComplexODEB

/-- If the center has smaller modulus than every boundary value, a holomorphic
function on a disk has a zero in that disk's closure. -/
theorem exists_zero_of_center_norm_lt_sphere {f : ℂ → ℂ} {z₀ : ℂ} {r : ℝ}
    (hr : 0 < r) (hf : DiffContOnCl ℂ f (ball z₀ r))
    (hsep : ∀ z ∈ sphere z₀ r, ‖f z₀‖ < ‖f z‖) :
    ∃ z ∈ closedBall z₀ r, f z = 0 := by
  by_contra h
  push Not at h
  have hni : ∀ z ∈ closure (ball z₀ r), f z ≠ 0 :=
    fun z hz => h z (closure_ball_subset_closedBall hz)
  obtain ⟨z, hz, hmax⟩ := Complex.exists_mem_frontier_isMaxOn_norm
    (Metric.isBounded_ball : Bornology.IsBounded (ball z₀ r))
    ⟨z₀, mem_ball_self hr⟩ (hf.inv hni)
  have hlt := hsep z (frontier_ball_subset_sphere hz)
  have hpos : 0 < ‖f z₀‖ := norm_pos_iff.mpr (h z₀ (mem_closedBall_self hr.le))
  have hle := hmax (subset_closure (mem_ball_self hr))
  have hi := one_div_lt_one_div_of_lt hpos hlt
  have hle' : (‖f z₀‖)⁻¹ ≤ (‖f z‖)⁻¹ := by
    simpa only [mem_ofPred_eq, Function.comp_apply, Pi.inv_apply, norm_inv] using hle
  exact (not_lt_of_ge hle') (by simpa only [one_div] using hi)

/-- A sufficiently small actual uniform error from an affine function forces
an actual zero. This form is convenient for a rescaled local bifurcation. -/
theorem exists_zero_of_affine_approximation {f : ℂ → ℂ} {z₀ A : ℂ} {r η : ℝ}
    (hr : 0 < r) (hf : DiffContOnCl ℂ f (ball z₀ r))
    (herr : 2 * η < ‖A‖ * r)
    (happrox : ∀ z ∈ closedBall z₀ r, ‖f z - A * (z - z₀)‖ ≤ η) :
    ∃ z ∈ closedBall z₀ r, f z = 0 := by
  apply exists_zero_of_center_norm_lt_sphere hr hf
  intro z hz
  have hcenter := happrox z₀ (mem_closedBall_self hr.le)
  simp only [sub_self, mul_zero, sub_zero] at hcenter
  have hboundary := happrox z (sphere_subset_closedBall hz)
  have htriangle : ‖A * (z - z₀)‖ ≤ ‖f z - A * (z - z₀)‖ + ‖f z‖ := by
    calc
      ‖A * (z - z₀)‖ = ‖f z - (f z - A * (z - z₀))‖ := by congr 1; ring
      _ ≤ ‖f z‖ + ‖f z - A * (z - z₀)‖ := norm_sub_le _ _
      _ = _ := add_comm _ _
  rw [norm_mul, mem_sphere_iff_norm.mp hz] at htriangle
  linarith

end UnforcedLeray.ComplexODEB
