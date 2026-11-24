import UnforcedLeray.Short.PartI.Sub.T02_3_8

/-!
# Part I, task `PartI:T02/3/8/QAvgReal`: the zeroth mode of a real function is its horizontal average

Source of record: `the November 2 reference manuscript`, lines 276-288.

Target: `CylPoisQAvgReal` (`Short/PartI/Sub/T02_3_8.lean`): for every `c`, every real `q` and
every `η`, `Cyl.qAvg c (fun z => ↑(q z)) η = ↑(hmean c q η)`.

Proof.  Unfold both sides.  The `Ico` and `Ioc` integrals agree (`integral_Ico_eq_integral_Ioc`,
since Lebesgue measure has no atoms).  `integral_ofReal` commutes the coercion `ℝ → ℂ` with the
integral.  The remaining scalar identities are `Complex.ofReal_mul` and `Complex.ofReal_inv`.
No hypothesis on `c` or `q` is needed.
-/

set_option autoImplicit false

namespace UnforcedLeray.Short.PartI

open MeasureTheory Set

/-- **Leaf O6** (the zeroth mode of a real function is its horizontal average):
`Cyl.qAvg c (↑∘q) η = ↑(hmean c q η)` for all `c`, `q`, `η`. -/
theorem cylPoisQAvgReal : CylPoisQAvgReal := by
  unfold CylPoisQAvgReal
  intro c q η
  unfold UnforcedLeray.Cyl.qAvg hmean
  -- `integral_ofReal` lives in the root namespace (Mathlib `Bochner/ContinuousLinearMap.lean`).
  have hint : ∫ t in Ioc (-c / 2) (c / 2), ((q (t, η) : ℝ) : ℂ)
      = ((∫ t in Ioc (-c / 2) (c / 2), q (t, η) : ℝ) : ℂ) :=
    integral_ofReal
  rw [MeasureTheory.integral_Ico_eq_integral_Ioc]
  simp only [hint]
  simp [smul_eq_mul, Complex.ofReal_mul, Complex.ofReal_inv]

end UnforcedLeray.Short.PartI
