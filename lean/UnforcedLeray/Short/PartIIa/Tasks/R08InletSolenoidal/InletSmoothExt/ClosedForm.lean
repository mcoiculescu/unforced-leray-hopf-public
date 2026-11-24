import UnforcedLeray.Short.PartIIa.Sub.R08_2
import UnforcedLeray.Short.PartIIa.Tasks.R08InletSolenoidal.InletBound

/-!
# Part II-a, task `PartII-a:R08/2/2`: the closed form of the raw inlet

Source of record: `the November 2 reference manuscript`, line 1210 (stream form
`q = R log(r/R)`, `η = Rz/r`) and lines 1330-1334.

Off the axis, `inletRaw c R y` is `-(1/r) ∂_z 𝒫 • eR + (1/r) ∂_r 𝒫 • e₃` with
`𝒫 = inletStream c R`, `r = ϱ y`, `z = y 2`. The two partial derivatives are supplied by
`hasDerivAt_inletStream_z` and `hasDerivAt_inletStream_r` (`InletBound.lean`). The lattice
sum `inletTheta c = -2 * inletSum0 c` has derivative `inletSum1 c` (`hasDerivAt_inletSum0`).
Comparing the two coefficients with `inletClosed` (`Sub/R08_2.lean`) gives the claim.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIa

/-- The profile `θ_c` is `-2` times the lattice sum `S₀`. -/
theorem cfTheta_eq (c q : ℝ) : inletTheta c q = -2 * inletSum0 c q := by
  simp only [inletTheta, inletSum0, neg_div, tsum_mul_left]

/-- The profile `θ_c` as a function. -/
theorem cfTheta_fun (c : ℝ) : inletTheta c = fun q => -2 * inletSum0 c q :=
  funext fun q => cfTheta_eq c q

/-- The derivative of `θ_c` is `S₁`. -/
theorem cfTheta_deriv {c : ℝ} (hc : c ≠ 0) (q : ℝ) :
    deriv (inletTheta c) q = inletSum1 c q := by
  rw [cfTheta_fun c, ((hasDerivAt_inletSum0 hc q).const_mul (-2)).deriv]
  ring

/-- The two forms of the Gaussian exponent `e^{-(Rz/r)²/4}` agree. -/
theorem cfExp_eq (R z r : ℝ) :
    Real.exp (-(R ^ 2 / 4) * z ^ 2 * r⁻¹ ^ 2) = Real.exp (-((R * z / r) ^ 2) / 4) := by
  congr 1
  ring

/-- **Closed form of the raw inlet** (task `PartII-a:R08/2/2`): off the axis,
`inletRaw c R y = inletClosed c R y`. -/
theorem inletRawClosedForm : UnforcedLeray.Short.PartIIa.InletRawClosedForm := by
  intro c R hc hR y hy
  have hr : 0 < Axi.ϱ y := Axi.ϱ_pos hy
  have hcne : c ≠ 0 := hc.ne'
  have hrne : Axi.ϱ y ≠ 0 := hr.ne'
  have hRne : R ≠ 0 := hR.ne'
  unfold inletRaw inletClosed
  rw [(hasDerivAt_inletStream_z c R (Axi.ϱ y) (y 2) hcne hrne).deriv,
    (hasDerivAt_inletStream_r c R (y 2) (Axi.ϱ y) hcne hrne hRne).deriv,
    cfTheta_deriv hcne, cfExp_eq R (y 2) (Axi.ϱ y)]
  simp only [cfTheta_eq]
  congr 1
  · congr 1
    ring
  · congr 1
    ring

end UnforcedLeray.Short.PartIIa
