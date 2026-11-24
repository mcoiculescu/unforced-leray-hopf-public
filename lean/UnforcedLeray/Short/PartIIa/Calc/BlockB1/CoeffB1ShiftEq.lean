import UnforcedLeray.Short.PartIIa.Calc.BlockB1.CoeffB1Eq

/-!
# Part II-a, block `B₁`: the leaf `CoeffB1ShiftEq` (task `PartII-a:R02/9/3`)

Target: `coeffB1ShiftEq : CoeffB1ShiftEq`, i.e. for `g` smooth on `{s > 0}` and `0 < s`,
`ageShift 3 (coeffB₁ ν g) x = ν * (6 * jet 1 1 0 g x + 5 * jet 2 1 0 g x + jet 3 1 0 g x)`.

Source of record: `the November 2 reference manuscript` line 1272.

Route: `ageShift 3 X x = K X x + 3 X x`. On `{s > 0}`, `X = coeffB₁ ν g = 2ν A + ν B` with
`A = K∂_ηg` and `B = KA` (`coeffB1Eq`), so `K X x = 2ν KA x + ν KB x = 2ν B x + ν KB x`
(linearity of `K` at `x`, `B0188`-style via `fderiv_fun_add`).
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.PartIIa.BlockB1

open UnforcedLeray.B0184 UnforcedLeray.B0185 UnforcedLeray.B0188 UnforcedLeray.B0190

/-- Derivative of a linear combination of two profiles differentiable at `x`, in a direction. -/
theorem shift_fderiv_lin_apply {F G : ProfilePoint → ℝ} {x : ProfilePoint}
    (hF : DifferentiableAt ℝ F x) (hG : DifferentiableAt ℝ G x) (a b : ℝ) (w : ProfilePoint) :
    fderiv ℝ (fun y => a * F y + b * G y) x w = a * fderiv ℝ F x w + b * fderiv ℝ G x w := by
  rw [fderiv_fun_add (hF.const_mul a) (hG.const_mul b), fderiv_const_mul hF a,
    fderiv_const_mul hG b]
  simp

/-- `K` of a linear combination of two profiles differentiable at `x`. -/
theorem shift_ageLin {F G : ProfilePoint → ℝ} {x : ProfilePoint}
    (hF : DifferentiableAt ℝ F x) (hG : DifferentiableAt ℝ G x) (a b : ℝ) :
    ageOperator (fun y => a * F y + b * G y) x = a * ageOperator F x + b * ageOperator G x := by
  unfold ageOperator partialEta partialAge
  rw [shift_fderiv_lin_apply hF hG a b eηDir, shift_fderiv_lin_apply hF hG a b esDir]
  ring

/-- **Leaf `CoeffB1ShiftEq`** (source line 1272). -/
theorem coeffB1ShiftEq : CoeffB1ShiftEq := by
  unfold CoeffB1ShiftEq
  intro ν g hg x hx
  have hD : ContDiffOn ℝ ∞ (partialEta g) {y : ProfilePoint | 0 < y.2.2} :=
    contDiffOn_partialEta_iter hg 1
  have hA : ContDiffOn ℝ ∞ (ageOperator (partialEta g)) {y : ProfilePoint | 0 < y.2.2} :=
    contDiffOn_ageOperator hD
  have hB : ContDiffOn ℝ ∞ (ageOperator (ageOperator (partialEta g)))
      {y : ProfilePoint | 0 < y.2.2} :=
    contDiffOn_ageOperator hA
  -- the target, unfolded to the explicit profile operators
  show ageOperator (coeffB₁ ν g) x + 3 * coeffB₁ ν g x
    = ν * (6 * ageOperator (partialEta g) x + 5 * ageOperator (ageOperator (partialEta g)) x
      + ageOperator (ageOperator (ageOperator (partialEta g))) x)
  -- `B₁` on `{s > 0}` as a linear combination of `A` and `B`
  have hEq : EqOn (coeffB₁ ν g)
      (fun y => (2 * ν) * ageOperator (partialEta g) y
        + ν * ageOperator (ageOperator (partialEta g)) y)
      {y : ProfilePoint | 0 < y.2.2} := by
    intro y hy
    show coeffB₁ ν g y = (2 * ν) * ageOperator (partialEta g) y
        + ν * ageOperator (ageOperator (partialEta g)) y
    have h := coeffB1Eq ν g hg y hy
    have h' : coeffB₁ ν g y = ν * (2 * ageOperator (partialEta g) y
        + ageOperator (ageOperator (partialEta g)) y) := h
    rw [h']
    ring
  have hfun : coeffB₁ ν g =ᶠ[𝓝 x]
      (fun y => (2 * ν) * ageOperator (partialEta g) y
        + ν * ageOperator (ageOperator (partialEta g)) y) :=
    eventuallyEq_of_late hEq hx
  have hXval : coeffB₁ ν g x = (2 * ν) * ageOperator (partialEta g) x
      + ν * ageOperator (ageOperator (partialEta g)) x := hEq hx
  have hKX : ageOperator (coeffB₁ ν g) x = ageOperator (fun y => (2 * ν) * ageOperator (partialEta g) y
      + ν * ageOperator (ageOperator (partialEta g)) y) x :=
    kx_ageOp_congr hfun
  rw [hKX, shift_ageLin (differentiableAt_of_late hA hx) (differentiableAt_of_late hB hx),
    hXval]
  ring

end UnforcedLeray.Short.PartIIa.BlockB1
