import UnforcedLeray.Short.PartIIb.Sub.T11_6

/-!


Source of record: `the November 2 reference manuscript`, SP 2618 (the 2D Liouville
step of the flat-uniqueness argument). The proposition `CRDifferentiable` is defined in
`Short/PartII-b/Sub/T11_6.lean`; this file proves it exactly as stated.

Proof sketch. Fix `z`, put `L = fderiv ℝ f z : ℂ →L[ℝ] ℂ` and `a = L 1`.
1. The hypothesis `L 1 + I * L I = 0` gives `L I = I * a` (multiply by `-I`).
2. Every `h : ℂ` satisfies `h = h.re • 1 + h.im • I`, so `L h = h.re • a + h.im • (I * a) = a * h`.
3. Hence `L = (ContinuousLinearMap.mul ℂ ℂ a).restrictScalars ℝ`, and `DifferentiableAt ℂ f z`
   follows from `differentiableAt_iff_restrictScalars`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

/-- Helper: a real-linear map `L : ℂ →L[ℝ] ℂ` with `L 1 + I * L I = 0` satisfies `L I = I * L 1`. -/
theorem crd_I_eq (L : ℂ →L[ℝ] ℂ) (h : L 1 + Complex.I * L Complex.I = 0) :
    L Complex.I = Complex.I * L 1 := by
  linear_combination (-Complex.I) * h + (L Complex.I) * Complex.I_mul_I

/-- Helper: a real-linear map `L : ℂ →L[ℝ] ℂ` with `L I = I * L 1` is multiplication by `L 1`. -/
theorem crd_apply_eq (L : ℂ →L[ℝ] ℂ) (hI : L Complex.I = Complex.I * L 1) (h : ℂ) :
    L h = L 1 * h := by
  have hre : (h.re : ℂ) + (h.im : ℂ) * Complex.I = h := Complex.re_add_im h
  have hdec : h = h.re • (1 : ℂ) + h.im • Complex.I := by
    simp only [Complex.real_smul, mul_one]
    exact hre.symm
  have hL : L h = h.re • L 1 + h.im • L Complex.I := by
    conv_lhs => rw [hdec]
    rw [map_add, map_smul, map_smul]
  rw [hL, hI]
  simp only [Complex.real_smul]
  linear_combination (L 1) * hre

/-- Helper: the `ℂ`-linear map `w ↦ a * w`, restricted to `ℝ`, is the real derivative `L` when
`L I = I * L 1`. -/
theorem crd_restrict_eq (L : ℂ →L[ℝ] ℂ) (hI : L Complex.I = Complex.I * L 1) :
    (ContinuousLinearMap.mul ℂ ℂ (L 1)).restrictScalars ℝ = L := by
  ext h
  simp only [ContinuousLinearMap.coe_restrictScalars', ContinuousLinearMap.mul_apply']
  exact (crd_apply_eq L hI h).symm

/-- **Leaf `PartII-b:T11/6/3`** (Cauchy-Riemann criterion). A real-`C¹` function `f : ℂ → ℂ`
whose real derivative `L = fderiv ℝ f z` satisfies `L 1 + I * L I = 0` for every `z` is complex
differentiable everywhere. Proved by `crd_I_eq`, `crd_restrict_eq` and
`differentiableAt_iff_restrictScalars`. -/
theorem crDifferentiable : UnforcedLeray.Short.IIb.CRDifferentiable := by
  intro f hf hcr z
  have hR : DifferentiableAt ℝ f z := (hf.differentiable one_ne_zero) z
  have hI : fderiv ℝ f z Complex.I = Complex.I * fderiv ℝ f z 1 :=
    crd_I_eq (fderiv ℝ f z) (hcr z)
  exact (differentiableAt_iff_restrictScalars ℝ hR).mpr
    ⟨ContinuousLinearMap.mul ℂ ℂ (fderiv ℝ f z 1), crd_restrict_eq (fderiv ℝ f z) hI⟩

end UnforcedLeray.Short.IIb
