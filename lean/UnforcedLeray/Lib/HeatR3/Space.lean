import UnforcedLeray.Lib.HeatR3.LpOp
import UnforcedLeray.Analysis.Heat.StrongContinuity

/-!
# The generic heat operator on `ℝ³`: bridge to `Heat.average`, rotations, dilations (INF04 T5)


bypass BP2. Covers the heat parts of units B0414(iv), B0688, B0697, B0727, B1025.

On `Space = ℝ³` with `ι = id`, `heatConv` is the compiled pointwise heat integral
`Heat.average` (`lean/UnforcedLeray/Analysis/Heat/Averaging.lean`), and `heatLp` at `p = 2` is
the compiled `Heat.heatOperator` (`StrongContinuity.lean`). Rotations and dilations commute with
the heat flow because the Gaussian is radial (`Gaussian.gaussKernel_isometry`) and
`G_{λ²θ}(λx) = λ^{-3}G_θ(x)` (`Gaussian.gaussKernel_scale`); tex 7411–7427 (B0418–B0420) and
the similarity identity of tex 5205–5216 / B0697.

Main results:
* `heatConv_space_eq_average`: `heatConv (AddMonoidHom.id Space) θ u = Heat.average θ u`
  (every `θ`, every `u`);
* `heatLp_space_two`: `heatLp (AddMonoidHom.id Space) _ θ = Heat.heatOperator θ` on `L²`;
* `average_comp_isometry`, `average_isometry`: rotation covariance (no integrability needed);
* `average_dilate`: `e^{θΔ}[u(λ·)] = (e^{λ²θΔ}u)(λ·)`, `λ, θ > 0` (no integrability needed).
-/

noncomputable section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace UnforcedLeray.Heat

open MeasureTheory Filter Set Topology
open scoped ENNReal
open UnforcedLeray.Gaussian (Euc gaussKernel)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **INF04 T5 `heatConv_space_eq_average`.** On `ℝ³` with `ι = id`, the generic heat integral
is the compiled `Heat.average`, for every time and every field (both are the same Bochner
integral, `Gaussian.gaussKernel_three_eq`). -/
theorem heatConv_space_eq_average (θ : ℝ) (u : Space → E) :
    heatConv (AddMonoidHom.id Space) θ u = average θ u := by
  funext x
  simp only [heatConv, average, AddMonoidHom.id_apply, Gaussian.gaussKernel_three_eq]

/-- **INF04 T3 `heatLp_space_two`.** At `p = 2` on `ℝ³`, `heatLp` is the compiled
`Heat.heatOperator`. -/
theorem heatLp_space_two (θ : ℝ) (u : L2Space) :
    heatLp (AddMonoidHom.id Space) continuous_id θ u = heatOperator θ u := by
  by_cases hθ : 0 < θ
  · refine Lp.ext ?_
    have h1 := heatLp_rep (AddMonoidHom.id Space) continuous_id hθ u
    have h2 := heatOperator_rep hθ u
    rw [heatConv_space_eq_average] at h1
    exact h1.trans h2.symm
  · rw [heatLp_of_nonpos _ _ (not_lt.mp hθ), heatOperator_nonpos (not_lt.mp hθ)]

/-- **INF04 T5, rotations of the variable.** For a linear isometry `g` of `ℝ³`,
`e^{θΔ}[u ∘ g⁻¹] = (e^{θΔ}u) ∘ g⁻¹`, for every `θ` and every `u`. -/
theorem average_comp_isometry (g : Space ≃ₗᵢ[ℝ] Space) (θ : ℝ) (u : Space → E) :
    average θ (fun x => u (g.symm x)) = fun x => average θ u (g.symm x) := by
  funext x
  simp only [average]
  have hmp : MeasurePreserving g (volume : Measure Space) volume :=
    LinearIsometryEquiv.measurePreserving g
  rw [← hmp.integral_comp g.toHomeomorph.measurableEmbedding]
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  simp only [LinearIsometryEquiv.coe_toHomeomorph, ← Gaussian.gaussKernel_three_eq,
    Gaussian.gaussKernel_isometry, map_sub, LinearIsometryEquiv.symm_apply_apply]

/-- **INF04 T5 `average_isometry`.** Rotation covariance of the heat flow of a vector field:
`e^{θΔ}[g u(g⁻¹·)] = g (e^{θΔ}u)(g⁻¹·)` for every linear isometry `g` of `ℝ³` (B0688, B0727). -/
theorem average_isometry (g : Space ≃ₗᵢ[ℝ] Space) (θ : ℝ) (u : SpatialField) :
    average θ (fun x => g (u (g.symm x))) = fun x => g (average θ u (g.symm x)) := by
  rw [average_comp_isometry g θ (fun x => g (u x))]
  funext x
  simp only [average]
  have h := (g.toLinearIsometry).integral_comp_comm
    (μ := (volume : Measure Space)) (fun y => kernel θ y • u (g.symm x - y))
  simp only [LinearIsometryEquiv.coe_toLinearIsometry, LinearIsometryEquiv.map_smul] at h
  exact h

/-- **INF04 T5 `average_dilate`.** `e^{θΔ}[u(λ·)](x) = (e^{λ²θΔ}u)(λx)` for `λ, θ > 0` and
every `u` (dilation identity of B0697; adapted from the draft
-/
theorem average_dilate {lam θ : ℝ} (hlam : 0 < lam) (hθ : 0 < θ) (u : Space → E) :
    average θ (fun x => u (lam • x)) = fun x => average (lam ^ 2 * θ) u (lam • x) := by
  funext x
  let F : Space → E := fun w => kernel (lam ^ 2 * θ) w • u (lam • x - w)
  have hJac := Measure.integral_comp_smul_of_nonneg (volume : Measure Space) F lam
    (hR := hlam.le)
  have hd : Module.finrank ℝ Space = 3 := by simp [Space]
  rw [hd] at hJac
  have hscale : ∀ y : Space, kernel θ y = lam ^ 3 * kernel (lam ^ 2 * θ) (lam • y) := by
    intro y
    rw [← Gaussian.gaussKernel_three_eq, Gaussian.gaussKernel_scale hlam hθ, ← mul_assoc,
      show (3 : ℕ) = ((3 : ℕ) : ℝ) by norm_num]
    rw [show lam ^ 3 * lam ^ (-((3 : ℕ) : ℝ)) = 1 by
      rw [Real.rpow_neg hlam.le, Real.rpow_natCast, mul_inv_cancel₀ (pow_ne_zero _ hlam.ne')],
      one_mul]
  simp only [average]
  have hl : (fun y : Space => kernel θ y • u (lam • (x - y))) =
      fun y : Space => lam ^ 3 • F (lam • y) := by
    funext y
    simp only [F, smul_sub]
    rw [hscale y, mul_smul]
  simp_rw [smul_sub] at hl ⊢
  rw [show (fun y : Space => kernel θ y • u (lam • x - lam • y)) =
      fun y : Space => lam ^ 3 • F (lam • y) by
    funext y; simpa only [smul_sub] using congrFun hl y]
  rw [integral_smul, hJac, smul_smul, mul_inv_cancel₀ (pow_ne_zero _ hlam.ne'), one_smul]

end UnforcedLeray.Heat
