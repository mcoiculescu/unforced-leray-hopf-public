import Mathlib.Analysis.Complex.AbsMax

/-!
# A zero forced by a genuine affine approximation (copy of a draft; O4/O5 input)

Copy, for compilation inside `Lib/ComplexODE`, of the uncompiled draft

which is not edited; do not import both. Scoping note `INF10-INF12-INF18-Planar.md` §5, inputs of
O4 and O5 (bypass B8 (ii)--(iii)).

The minimum-modulus argument below is proved from the maximum-modulus theorem
for the reciprocal. It gives an actual zero from explicit analytic estimates;
no zero, winding certificate, or argument-principle axiom is assumed.
-/

set_option autoImplicit false

noncomputable section
open Set Metric
namespace UnforcedLeray.Rayleigh.Evans

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
    simpa [Function.comp_apply, Pi.inv_apply, norm_inv] using hle
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

end UnforcedLeray.Rayleigh.Evans
