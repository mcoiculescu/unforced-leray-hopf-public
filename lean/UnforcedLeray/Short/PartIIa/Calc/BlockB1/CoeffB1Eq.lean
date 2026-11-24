import UnforcedLeray.Short.PartIIa.Calc.BlockB1

/-!
# Part II-a, block `B₁`: the leaf `CoeffB1Eq` (task `PartII-a:R02/9/1`)

Target: `coeffB1Eq : CoeffB1Eq`, i.e. for `g` smooth on `{s > 0}` and `0 < s`,
`coeffB₁ ν g x = ν * (2 * jet 1 1 0 g x + jet 2 1 0 g x)`.

Source of record: `the November 2 reference manuscript` line 1255
(`B₁ = -νK(K+2)v₁`, `v₁ = -∂_ηψ`).

Route: `K` commutes with negation (no differentiability needed), so
`K + 2` applied to `streamV1 g = -∂_ηg` is `-(K∂_ηg + 2∂_ηg)`; then `K` of the sum
is computed at `x` by `ageOperator_add_mul`, using differentiability of `K∂_ηg` and `∂_ηg`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.PartIIa.BlockB1

open UnforcedLeray.B0184 UnforcedLeray.B0185 UnforcedLeray.B0188 UnforcedLeray.B0190

/-- `K` commutes with negation (pointwise, no differentiability needed). -/
theorem ageOperator_neg_apply (H : ProfilePoint → ℝ) (y : ProfilePoint) :
    ageOperator (fun z => -H z) y = -ageOperator H y := by
  unfold ageOperator partialEta partialAge
  simp
  ring

/-- **Leaf `CoeffB1Eq`** (source line 1255): `B₁[g] = ν(2K∂_ηg + K²∂_ηg)` on `{s > 0}`. -/
theorem coeffB1Eq : CoeffB1Eq := by
  unfold CoeffB1Eq
  intro ν g hg x hx
  have hE : ContDiffOn ℝ ∞ (partialEta g) {y : ProfilePoint | 0 < y.2.2} := by
    simpa only [Function.iterate_one] using contDiffOn_partialEta_iter hg 1
  have hF : DifferentiableAt ℝ (ageOperator (partialEta g)) x :=
    differentiableAt_of_late (contDiffOn_ageOperator hE) hx
  have hG : DifferentiableAt ℝ (partialEta g) x := differentiableAt_of_late hE hx
  have h1 : ageOperator (streamV1 g) = fun y => -ageOperator (partialEta g) y := by
    funext y
    exact ageOperator_neg_apply (partialEta g) y
  have hshift : ageShift 2 (streamV1 g) =
      fun y => -(ageOperator (partialEta g) y + 2 * partialEta g y) := by
    funext y
    unfold ageShift
    rw [congrFun h1 y]
    simp only [streamV1]
    ring
  have key : ageOperator (ageShift 2 (streamV1 g)) x =
      -(ageOperator (ageOperator (partialEta g)) x + 2 * ageOperator (partialEta g) x) := by
    rw [hshift, ageOperator_neg_apply, ageOperator_add_mul hF hG 2]
  have hj1 : jet 1 1 0 g x = ageOperator (partialEta g) x := rfl
  have hj2 : jet 2 1 0 g x = ageOperator (ageOperator (partialEta g)) x := rfl
  unfold coeffB₁
  rw [key, hj1, hj2]
  ring

end UnforcedLeray.Short.PartIIa.BlockB1
