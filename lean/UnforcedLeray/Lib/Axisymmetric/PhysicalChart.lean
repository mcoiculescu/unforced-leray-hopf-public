import UnforcedLeray.Lib.Axisymmetric.RingChart
import UnforcedLeray.Analysis.RingLift.Chart

/-!
# AX03 bridge: the similarity ring chart is the physical ring chart in similarity variables


§5 Layer 3, target AX03 (deps `RingLift/Chart.lean`). Blueprint units B0184
(`eq:st18-t00187`, tex 2837–2850) and B0186 (`eq:m3-ring-lift`, tex 2070–2075).

The manuscript gives two charts (tex 2070–2075): the physical chart
`s = (R/r)² t`, `ξ = R log(r/R)`, `η = R x₃/r` — the audited
`UnforcedLeray.RingLift.{ageCoordinate, logRadius, transverseCoordinate}` used by the unit draft
`Units/B0184.lean` — and the similarity chart `s = R²/ϱ²`, `ξ = Rτ/2 − (R/2) log s`,
`η = R y₃/ϱ` (`Axi.chart`). With `y = x/√t` and `τ = log t` they agree
(`chart_similarity`), so the physical differentiation rules of B0184 and the similarity rules
of `RingChart.lean` describe the same profiles.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Axi

theorem ϱ_smul (c : ℝ) (x : Space) : ϱ (c • x) = |c| * ϱ x := by
  unfold ϱ
  simp only [PiLp.smul_apply, smul_eq_mul]
  rw [show (c * x 0) ^ 2 + (c * x 1) ^ 2 = c ^ 2 * (x 0 ^ 2 + x 1 ^ 2) by ring,
    Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq_eq_abs]

/-- **Similarity chart = physical chart** (tex 2070–2075). For `R, t > 0` and `x` off the
axis, the similarity chart at `y = x/√t`, `τ = log t` is the physical chart at `(r, z, t)`
with `r = ϱ(x)`, `z = x₃`: `(s, ξ, η) = ((R/r)² t, R log(r/R), (R/r) z)`. -/
theorem chart_similarity {R t : ℝ} (hR : 0 < R) (ht : 0 < t) {x : Space} (hx : x ∉ axis) :
    chart R (Real.log t) ((√t)⁻¹ • x) =
      (RingLift.ageCoordinate R (ϱ x) t,
        (RingLift.logRadius R (ϱ x), RingLift.transverseCoordinate R (ϱ x) (x 2))) := by
  have hρ := ϱ_pos hx
  have hst : 0 < √t := Real.sqrt_pos.2 ht
  have hϱs : ϱ ((√t)⁻¹ • x) = (√t)⁻¹ * ϱ x := by
    rw [ϱ_smul, abs_of_pos (inv_pos.2 hst)]
  have hz : ((√t)⁻¹ • x) 2 = (√t)⁻¹ * x 2 := by
    simp only [PiLp.smul_apply, smul_eq_mul]
  have hage : age R ((√t)⁻¹ • x) = (R / ϱ x) ^ 2 * t := by
    rw [age, hϱs, mul_pow, inv_pow, Real.sq_sqrt ht.le, div_pow]
    first
    | (field_simp; done)
    | (field_simp; ring)
  have hphase : phase R (Real.log t) ((√t)⁻¹ • x) = R * Real.log (ϱ x / R) := by
    rw [phase, hage, Real.log_mul (pow_pos (div_pos hR hρ) 2).ne' ht.ne', Real.log_pow,
      Real.log_div hR.ne' hρ.ne', Real.log_div hρ.ne' hR.ne']
    push_cast
    ring
  have htrans : trans R ((√t)⁻¹ • x) = R / ϱ x * x 2 := by
    rw [trans, hϱs, hz]
    first
    | (field_simp; done)
    | (field_simp; ring)
  rw [chart, hage, hphase, htrans]
  rfl

end UnforcedLeray.Axi
