import UnforcedLeray.Short.PartIIa.Calc.BlockB1.CoeffB1Eq
import UnforcedLeray.Short.PartIIa.Tasks.R02.Commutators

/-!
# Part II-a, block `B₁`: the leaf `CoeffB1EtaEq` (task `PartII-a:R02/9/2`)

Target: `coeffB1EtaEq : CoeffB1EtaEq`, i.e. for `g` smooth on `{s > 0}` and `0 < s`,
`partialEta (coeffB₁ ν g) x = ν * (3 * jet 0 2 0 g x + 4 * jet 1 2 0 g x + jet 2 2 0 g x)`.

Source of record: `the November 2 reference manuscript` line 1255 and 1268-1270.

Route: `coeffB₁ ν g = 2ν A + ν B` on `{s > 0}` with `A = K∂_ηg`, `B = KA` (`coeffB1Eq`).
The commutator `[K, ∂_η] = -∂_η` (`profileCommutators`, part 1) gives `∂_ηA = K E + E` on
`{s > 0}` with `E = ∂_η²g`, and then `∂_ηB = K(∂_ηA) + ∂_ηA = K²E + 2KE + E`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.PartIIa.BlockB1

open UnforcedLeray.B0184 UnforcedLeray.B0185 UnforcedLeray.B0188 UnforcedLeray.B0190

/-- `∂_η` of a linear combination of two profiles differentiable at `x`. -/
theorem fderiv_lin_apply {F G : ProfilePoint → ℝ} {x : ProfilePoint}
    (hF : DifferentiableAt ℝ F x) (hG : DifferentiableAt ℝ G x) (a b : ℝ) (w : ProfilePoint) :
    fderiv ℝ (fun y => a * F y + b * G y) x w = a * fderiv ℝ F x w + b * fderiv ℝ G x w := by
  rw [fderiv_fun_add (hF.const_mul a) (hG.const_mul b), fderiv_const_mul hF a,
    fderiv_const_mul hG b]
  simp

/-- `∂_η` of a linear combination of two profiles differentiable at `x`. -/
theorem etaLin_fderiv {F G : ProfilePoint → ℝ} {x : ProfilePoint}
    (hF : DifferentiableAt ℝ F x) (hG : DifferentiableAt ℝ G x) (a b : ℝ) :
    partialEta (fun y => a * F y + b * G y) x = a * partialEta F x + b * partialEta G x :=
  fderiv_lin_apply hF hG a b eηDir

/-- `∂_s` of a linear combination of two profiles differentiable at `x`. -/
theorem ageLin_partialAge {F G : ProfilePoint → ℝ} {x : ProfilePoint}
    (hF : DifferentiableAt ℝ F x) (hG : DifferentiableAt ℝ G x) (a b : ℝ) :
    partialAge (fun y => a * F y + b * G y) x = a * partialAge F x + b * partialAge G x :=
  fderiv_lin_apply hF hG a b esDir

/-- `K` of a linear combination of two profiles differentiable at `x`. -/
theorem ageLin_ageOperator {F G : ProfilePoint → ℝ} {x : ProfilePoint}
    (hF : DifferentiableAt ℝ F x) (hG : DifferentiableAt ℝ G x) (a b : ℝ) :
    ageOperator (fun y => a * F y + b * G y) x = a * ageOperator F x + b * ageOperator G x := by
  unfold ageOperator
  rw [etaLin_fderiv hF hG a b, ageLin_partialAge hF hG a b]
  ring

/-- **Leaf `CoeffB1EtaEq`** (source lines 1255, 1268-1270). -/
theorem coeffB1EtaEq : CoeffB1EtaEq := by
  unfold CoeffB1EtaEq
  intro ν g hg x hx
  -- smoothness of the profiles involved
  have hD : ContDiffOn ℝ ∞ (partialEta g) {y : ProfilePoint | 0 < y.2.2} :=
    contDiffOn_partialEta_iter hg 1
  have hE : ContDiffOn ℝ ∞ (partialEta (partialEta g)) {y : ProfilePoint | 0 < y.2.2} :=
    contDiffOn_partialEta_iter hg 2
  have hA : ContDiffOn ℝ ∞ (ageOperator (partialEta g)) {y : ProfilePoint | 0 < y.2.2} :=
    contDiffOn_ageOperator hD
  have hB : ContDiffOn ℝ ∞ (ageOperator (ageOperator (partialEta g)))
      {y : ProfilePoint | 0 < y.2.2} :=
    contDiffOn_ageOperator hA
  -- the target, unfolded to the explicit profile operators
  show partialEta (coeffB₁ ν g) x = ν * (3 * partialEta (partialEta g) x
    + 4 * ageOperator (partialEta (partialEta g)) x
    + ageOperator (ageOperator (partialEta (partialEta g))) x)
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
  have hX : partialEta (coeffB₁ ν g) x =
      partialEta (fun y => (2 * ν) * ageOperator (partialEta g) y
        + ν * ageOperator (ageOperator (partialEta g)) y) x := by
    show fderiv ℝ (coeffB₁ ν g) x eηDir = fderiv ℝ (fun y => (2 * ν) * ageOperator (partialEta g) y
        + ν * ageOperator (ageOperator (partialEta g)) y) x eηDir
    rw [hfun.fderiv_eq]
  -- commutator `[K, ∂_η] = -∂_η` at every point of `{s > 0}`
  have hAU : EqOn (partialEta (ageOperator (partialEta g)))
      (fun y => ageOperator (partialEta (partialEta g)) y + 1 * partialEta (partialEta g) y)
      {y : ProfilePoint | 0 < y.2.2} := by
    intro y hy
    have h := (profileCommutators (partialEta g) y (contDiffAt_two_of_late hD hy)).1
    show partialEta (ageOperator (partialEta g)) y
      = ageOperator (partialEta (partialEta g)) y + 1 * partialEta (partialEta g) y
    linarith [h]
  have hA1 : partialEta (ageOperator (partialEta g)) x =
      ageOperator (partialEta (partialEta g)) x + partialEta (partialEta g) x := by
    have h := hAU hx
    simp only at h
    linarith [h]
  have hAeq : partialEta (ageOperator (partialEta g)) =ᶠ[𝓝 x]
      (fun y => ageOperator (partialEta (partialEta g)) y + 1 * partialEta (partialEta g) y) :=
    eventuallyEq_of_late hAU hx
  have hKdA : ageOperator (partialEta (ageOperator (partialEta g))) x =
      ageOperator (ageOperator (partialEta (partialEta g))) x
        + 1 * ageOperator (partialEta (partialEta g)) x := by
    rw [kx_ageOp_congr hAeq]
    exact ageOperator_add_mul (differentiableAt_of_late (contDiffOn_ageOperator hE) hx)
      (differentiableAt_of_late hE hx) 1
  -- `∂_η B = K(∂_η A) + ∂_η A` (commutator at `x`, `A` is `C²` at `x`)
  have hB' : partialEta (ageOperator (ageOperator (partialEta g))) x =
      ageOperator (ageOperator (partialEta (partialEta g))) x
        + 2 * ageOperator (partialEta (partialEta g)) x + partialEta (partialEta g) x := by
    have hc2 := (profileCommutators (ageOperator (partialEta g)) x
      (contDiffAt_two_of_late hA hx)).1
    linarith [hc2, hKdA, hA1]
  rw [hX, etaLin_fderiv (differentiableAt_of_late hA hx) (differentiableAt_of_late hB hx),
    hA1, hB']
  ring

end UnforcedLeray.Short.PartIIa.BlockB1
