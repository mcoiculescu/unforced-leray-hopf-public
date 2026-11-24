import UnforcedLeray.Short.PartI.Sub.PartI_S11_1_1_2

/-!
# Part I, task `PartI:S11/1/1/2/4`: `SecGreenODE`

For `n ≥ 1`, `φ` smooth with compact support in `(0,∞)`, and `g = greenN n φ`, the pointwise
radial Poisson equation `g'' + g'/r - n²g/r² = φ` holds on `(0,∞)`.

Proof: `greenN n φ` solves the integrated equation (`Planar.isRadialPoissonSol_greenN`), and for
continuous right-hand side the integrated form is classical (`B0079.IsDeltaNSol.deltaN_eq`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Real
open scoped ContDiff

namespace UnforcedLeray.Short.PartI

open UnforcedLeray UnforcedLeray.Planar.NUE

theorem smoothCpt_contDiff_ode {φ : ℝ → ℂ} (h : SmoothCptFun φ) : ContDiff ℝ ∞ φ :=
  h.1

theorem smoothCpt_wprof_ode {φ : ℝ → ℂ} (h : SmoothCptFun φ) : UnforcedLeray.B0011.WProf φ := by
  obtain ⟨hc, hK, -⟩ := h
  have hcont : Continuous φ := hc.continuous
  refine ⟨hcont.aestronglyMeasurable, ?_⟩
  have hf : Continuous (fun ρ : ℝ => ρ * ‖φ ρ‖) := continuous_id.mul hcont.norm
  have hcs : HasCompactSupport (fun ρ : ℝ => ρ * ‖φ ρ‖) := hK.norm.mul_left
  exact (hf.integrable_of_hasCompactSupport hcs).restrict

/-- **Leaf `PartI:S11/1/1/2/4`** (lines 841-889 of the shorter proof): the radial Poisson equation
`g'' + g'/r - n²g/r² = φ` holds pointwise on `(0,∞)` for `g = greenN n φ`. -/
theorem secGreenODE_proof : UnforcedLeray.Short.PartI.SecGreenODE := by
  intro n hn φ hφ r hr
  have hsol : B0079.IsDeltaNSol n φ (Planar.greenN n φ) :=
    Planar.isRadialPoissonSol_greenN hn (smoothCpt_wprof_ode hφ)
  have hφC : ContinuousOn φ (Ioi 0) := (smoothCpt_contDiff_ode hφ).continuous.continuousOn
  exact (B0079.IsDeltaNSol.deltaN_eq hsol hφC hr).2.2

end UnforcedLeray.Short.PartI
