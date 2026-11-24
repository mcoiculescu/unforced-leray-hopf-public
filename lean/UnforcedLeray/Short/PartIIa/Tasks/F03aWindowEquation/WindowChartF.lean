import UnforcedLeray.Short.PartIIa.Sub.F03_1

/-!


Source of record: `the November 2 reference manuscript`, lines 1431-1434.
Proves `WindowChartF` (`Sub/F03_1.lean`) unconditionally: the pull-back of
`∫ windowForce · φ` along `θ = e^t`, `x = e^{t/2} y` (`B0424.integral_expChart`, then
`B0424.integral_dilChart`), with total weight `e^{3t/2} · e^t · e^{-3t/2} = e^t`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace UnforcedLeray.Short.PartIIa

open UnforcedLeray.PhaseSpace UnforcedLeray.Parabolic UnforcedLeray.B0424

/-- Helper (prefix `wcf`): `e^{-t/2} • (e^{t/2} • y) = y`. -/
theorem wcf_expNeg_smul_expPos (t : ℝ) (y : Space) :
    Real.exp (-(t / 2)) • (Real.exp (t / 2) • y) = y := by
  rw [smul_smul, ← Real.exp_add, neg_add_cancel, Real.exp_zero, one_smul]

/-- Helper (prefix `wcf`): `windowForce` at the chart point `(e^t, e^{t/2} y)`. -/
theorem wcf_windowForce_expDil (μ : ℂ) (χ : ℝ → ℝ) (τ₀ : ℝ) (W Fr : ℝ × Space → CVec3)
    (c : Fin 3) (t : ℝ) (y : Space) :
    windowForce μ χ τ₀ W Fr c (Real.exp t, Real.exp (t / 2) • y) =
      ((Real.exp (-(3 * t / 2)) : ℝ) : ℂ) *
        ((((deriv χ t : ℝ) : ℂ) - μ * (χ t : ℂ)) * W (τ₀ + t, y) c +
          (χ t : ℂ) * Fr (τ₀ + t, y) c) := by
  simp only [windowForce, Real.exp_pos, ite_true, Real.log_exp, wcf_expNeg_smul_expPos]

/-- **`WindowChartF`** (task `PartII-a:F03/1/5`, unconditional): `∫ windowForce · φ` equals
`∫ e^t [(χ' - μχ) W_c + χ Fr_c](τ₀ + t, y) φ(e^t, e^{t/2} y) dt dy`. -/
theorem windowChartF : WindowChartF := by
  intro μ χ τ₀ W Fr c φ
  have hzero : ∀ X ∉ Ioi (0 : ℝ) ×ˢ (univ : Set Space),
      windowForce μ χ τ₀ W Fr c X * (φ X : ℂ) = 0 := by
    intro X hX
    have hX1 : ¬ (0 < X.1) := fun h => hX ⟨h, trivial⟩
    simp [windowForce, hX1]
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hzero, integral_expChart]
  refine (integral_dilChart _).trans ?_
  congr 1
  funext p
  obtain ⟨t, y⟩ := p
  simp only [dilChart, expChart]
  rw [wcf_windowForce_expDil]
  have he : Real.exp (3 * t / 2) * Real.exp (-(3 * t / 2)) = 1 := by
    rw [← Real.exp_add]; simp
  have hw : Real.exp (3 * t / 2) * Real.exp t * Real.exp (-(3 * t / 2)) = Real.exp t := by
    rw [mul_right_comm, he, one_mul]
  have hc : ((Real.exp (3 * t / 2) : ℝ) : ℂ) * ((Real.exp t : ℝ) : ℂ) *
      ((Real.exp (-(3 * t / 2)) : ℝ) : ℂ) = ((Real.exp t : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul, ← Complex.ofReal_mul, hw]
  simp only [Complex.real_smul]
  linear_combination ((((deriv χ t : ℝ) : ℂ) - μ * (χ t : ℂ)) * W (τ₀ + t, y) c +
    (χ t : ℂ) * Fr (τ₀ + t, y) c) * (φ (Real.exp t, Real.exp (t / 2) • y) : ℂ) * hc

end UnforcedLeray.Short.PartIIa
