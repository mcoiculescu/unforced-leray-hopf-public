import UnforcedLeray.Short.PartIIa.Calc.BlockB1.CoeffB1Eq
import UnforcedLeray.Short.PartIIa.Tasks.R02.Commutators
import UnforcedLeray.Short.PartIIa.Tasks.R02.FluctuationProfile.ProfileCommute

/-!
# Part II-a, block `B₁`: the leaf `CoeffB1QEq` (task `PartII-a:R02/9/4`)

Target: `coeffB1QEq : CoeffB1QEq`, i.e. for `g` smooth on `{s > 0}` and `0 < s`,
`partialQ (coeffB₁ ν g) x = ν * (2 * jet 1 1 1 g x + jet 2 1 1 g x)`.

Source of record: `the November 2 reference manuscript` lines 1259-1276.

Route: on `{s > 0}`, `coeffB₁ = 2ν A + ν B` with `A = K∂_ηg`, `B = KA` (`coeffB1Eq`). Then
`∂_q A = K(∂_η∂_q g)` (commutator `[K, ∂_q] = 0` applied to `∂_ηg`, together with the mixed
partials `∂_q∂_ηg = ∂_η∂_qg`, `profile_fderiv_comm_at`) and `∂_q B = K(∂_q A)` (commutator applied
to `A`). Hence `∂_q B = K(K∂_η∂_qg)` at `x`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.PartIIa.BlockB1

open UnforcedLeray.B0184 UnforcedLeray.B0185 UnforcedLeray.B0188 UnforcedLeray.B0190

/-- Derivative of a linear combination of two profiles differentiable at `x`, in a direction. -/
theorem q_fderiv_lin_apply {F G : ProfilePoint → ℝ} {x : ProfilePoint}
    (hF : DifferentiableAt ℝ F x) (hG : DifferentiableAt ℝ G x) (a b : ℝ) (w : ProfilePoint) :
    fderiv ℝ (fun y => a * F y + b * G y) x w = a * fderiv ℝ F x w + b * fderiv ℝ G x w := by
  rw [fderiv_fun_add (hF.const_mul a) (hG.const_mul b), fderiv_const_mul hF a,
    fderiv_const_mul hG b]
  simp

/-- **Leaf `CoeffB1QEq`** (source lines 1259-1276). -/
theorem coeffB1QEq : CoeffB1QEq := by
  unfold CoeffB1QEq
  intro ν g hg x hx
  have hD : ContDiffOn ℝ ∞ (partialEta g) {y : ProfilePoint | 0 < y.2.2} :=
    contDiffOn_partialEta_iter hg 1
  have hA : ContDiffOn ℝ ∞ (ageOperator (partialEta g)) {y : ProfilePoint | 0 < y.2.2} :=
    contDiffOn_ageOperator hD
  have hB : ContDiffOn ℝ ∞ (ageOperator (ageOperator (partialEta g)))
      {y : ProfilePoint | 0 < y.2.2} :=
    contDiffOn_ageOperator hA
  -- the target, unfolded to the explicit profile operators
  show partialQ (coeffB₁ ν g) x = ν * (2 * ageOperator (partialEta (partialQ g)) x
    + ageOperator (ageOperator (partialEta (partialQ g))) x)
  -- mixed partials `∂_q∂_η g = ∂_η∂_q g` on `{s > 0}`
  have hmix : EqOn (partialQ (partialEta g)) (partialEta (partialQ g))
      {y : ProfilePoint | 0 < y.2.2} := by
    intro y hy
    show fderiv ℝ (fun z => fderiv ℝ g z eηDir) y eqDir
      = fderiv ℝ (fun z => fderiv ℝ g z eqDir) y eηDir
    exact UnforcedLeray.Short.PartIIa.FluctuationProfile.profile_fderiv_comm_at
      (contDiffAt_two_of_late hg hy) eηDir eqDir
  -- `∂_q A = K(∂_η∂_q g)` on `{s > 0}`, from `[K, ∂_q] = 0` at `∂_η g`
  have hAq : EqOn (partialQ (ageOperator (partialEta g)))
      (fun y => ageOperator (partialEta (partialQ g)) y) {y : ProfilePoint | 0 < y.2.2} := by
    intro y hy
    have c := (profileCommutators (partialEta g) y (contDiffAt_two_of_late hD hy)).2.1
    have m : partialQ (partialEta g) =ᶠ[𝓝 y] partialEta (partialQ g) :=
      eventuallyEq_of_late hmix hy
    show partialQ (ageOperator (partialEta g)) y = ageOperator (partialEta (partialQ g)) y
    rw [← c]
    exact kx_ageOp_congr m
  have hqA : partialQ (ageOperator (partialEta g)) x = ageOperator (partialEta (partialQ g)) x :=
    hAq hx
  -- `∂_q B = K(∂_q A)` at `x`, from `[K, ∂_q] = 0` at `A`
  have hBq : partialQ (ageOperator (ageOperator (partialEta g))) x
      = ageOperator (partialQ (ageOperator (partialEta g))) x :=
    ((profileCommutators (ageOperator (partialEta g)) x
      (contDiffAt_two_of_late hA hx)).2.1).symm
  have hKqA : ageOperator (partialQ (ageOperator (partialEta g))) x
      = ageOperator (ageOperator (partialEta (partialQ g))) x :=
    kx_ageOp_congr (eventuallyEq_of_late hAq hx)
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
  have hX : partialQ (coeffB₁ ν g) x = partialQ (fun y => (2 * ν) * ageOperator (partialEta g) y
      + ν * ageOperator (ageOperator (partialEta g)) y) x := by
    show fderiv ℝ (coeffB₁ ν g) x eqDir = fderiv ℝ (fun y => (2 * ν) * ageOperator (partialEta g) y
      + ν * ageOperator (ageOperator (partialEta g)) y) x eqDir
    rw [hfun.fderiv_eq]
  have hlin : partialQ (fun y => (2 * ν) * ageOperator (partialEta g) y
      + ν * ageOperator (ageOperator (partialEta g)) y) x
      = (2 * ν) * partialQ (ageOperator (partialEta g)) x
        + ν * partialQ (ageOperator (ageOperator (partialEta g))) x :=
    q_fderiv_lin_apply (differentiableAt_of_late hA hx) (differentiableAt_of_late hB hx)
      (2 * ν) ν eqDir
  rw [hX, hlin, hqA, hBq, hKqA]
  ring

end UnforcedLeray.Short.PartIIa.BlockB1
