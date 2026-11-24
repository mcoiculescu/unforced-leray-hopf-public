import UnforcedLeray.Infra.RieszProjection.Basic
import UnforcedLeray.Infra.RieszProjection.Projection
import UnforcedLeray.Infra.RieszProjection.Bounds
import UnforcedLeray.Infra.RieszProjection.Restriction

/-!
# Riesz projections for a bounded operator on a complex Banach space

Let `X` be a complex Banach space, `T : X →L[ℂ] X` and `r > 0` with the circle `|z| = r`
contained in the resolvent set of `T`. The Riesz projection is

  `rieszProj T r = (2πi)⁻¹ ∮_{|z|=r} (z - T)⁻¹ dz`

(Mathlib's `circleIntegral` of `resolvent T z = Ring.inverse (algebraMap ℂ _ z - T)`, positively
oriented circle). This is the localization of `paper/main.tex`, lines 359-368 (`P_-` is
`rieszProj T r`, `P_+ = 1 - P_-`, `ℳ_+ = ℳ|_{P_+X}`), for the circle `|ξ| = e^{βT}`.

Files:

* `RieszProjection/Basic.lean`: contour operators, commutation, moments `T ^ n P`, independence
  of the radius on an annulus free of spectrum, existence of such an annulus;
* `RieszProjection/Projection.lean`: `P ^ 2 = P`, the outer inverse
  `S = -(2πi)⁻¹ ∮ z⁻¹ (z - T)⁻¹ dz` with `T S = S T = 1 - P`, `S P = P S = 0` and
  `S ^ (m + 1) = -(2πi)⁻¹ ∮ z^{-(m+1)} (z - T)⁻¹ dz`;
* `RieszProjection/Bounds.lean`: `‖T ^ n P‖ ≤ C ρ ^ n` (`ρ < r`), `‖S ^ n‖ ≤ C R⁻¹ ^ n`
  (`R > r`), and spectral bounds from power bounds in a Banach algebra;
* `RieszProjection/Restriction.lean`: the subspaces `range P = ker (1 - P)` and
  `range (1 - P) = ker P`, the restricted operators, invertibility of `T` on `range (1 - P)`,
  the rates there, and the location of the two spectra.

This file collects the statement of the specification in `riesz_projection`.
-/

set_option autoImplicit false

noncomputable section

open Metric Complex
open scoped Real

namespace UnforcedLeray.Infra.RieszProjection

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
  {T : X →L[ℂ] X} {r : ℝ}

/-- **Riesz projection for a circle in the resolvent set.** Let `X` be a complex Banach space,
`T : X →L[ℂ] X`, and `r > 0` with the circle `|z| = r` in the resolvent set. Then
`P = (2πi)⁻¹ ∮_{|z|=r} (z - T)⁻¹ dz` is a (continuous linear) idempotent commuting with `T`, with
moments `T ^ n P = (2πi)⁻¹ ∮ z ^ n (z - T)⁻¹ dz`. The restriction of `T` to `range (1 - P)`
(`= ker P`) is invertible, and there are `0 < ρ < r < R` and `C ≥ 1` with
`‖T ^ n P‖ ≤ C ρ ^ n`, `‖(T|_{range P}) ^ n‖ ≤ C ρ ^ n` and `‖(T|_{range (1 - P)})^{-n}‖ ≤ C R⁻¹ ^ n`
for all `n`. The spectrum of `T|_{range P}` lies in `|z| < r`, that of `T|_{range (1 - P)}` in
`|z| > r`. -/
theorem riesz_projection (hr : 0 < r) (hT : sphere (0 : ℂ) r ⊆ resolventSet ℂ T) :
    IsIdempotentElem (rieszProj T r) ∧ Commute T (rieszProj T r) ∧
      (∀ n : ℕ, T ^ n * rieszProj T r =
        (2 * π * I)⁻¹ • ∮ z in C(0, r), z ^ n • resolvent T z) ∧
      LinearMap.range (rieszProj T r : X →ₗ[ℂ] X) = innerSubspace T r ∧
      LinearMap.range ((1 - rieszProj T r : X →L[ℂ] X) : X →ₗ[ℂ] X) = outerSubspace T r ∧
      IsUnit (outerPart T r) ∧
      (∃ ρ R C : ℝ, 0 < ρ ∧ ρ < r ∧ r < R ∧ 1 ≤ C ∧
        (∀ n : ℕ, ‖T ^ n * rieszProj T r‖ ≤ C * ρ ^ n) ∧
        (∀ n : ℕ, ‖innerPart T r ^ n‖ ≤ C * ρ ^ n) ∧
        (∀ n : ℕ, ‖Ring.inverse (outerPart T r) ^ n‖ ≤ C * R⁻¹ ^ n)) ∧
      spectrum ℂ (innerPart T r) ⊆ ball (0 : ℂ) r ∧
      spectrum ℂ (outerPart T r) ⊆ {z : ℂ | r < ‖z‖} := by
  refine ⟨isIdempotentElem_rieszProj hr hT, commute_self_rieszProj hr.le hT,
    pow_mul_rieszProj_eq_integral hr.le hT, range_rieszProj hr hT,
    range_one_sub_rieszProj hr hT, isUnit_outerPart hr hT, ?_,
    spectrum_innerPart_subset_ball hr hT, spectrum_outerPart_subset hr hT⟩
  obtain ⟨ρ, R, C, hρ, hρr, hR, hC, h₁, h₂⟩ := exists_rates hr hT
  refine ⟨ρ, R, C, hρ, hρr, hR, hC, h₁, fun n => (norm_innerPart_pow_le n).trans (h₁ n),
    fun n => ?_⟩
  rw [ringInverse_outerPart hr hT]
  exact (norm_outerPartInv_pow_le n).trans (h₂ n)

end UnforcedLeray.Infra.RieszProjection
