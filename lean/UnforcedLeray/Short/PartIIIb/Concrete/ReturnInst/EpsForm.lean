import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Complex.Exponential

/-!
# The closed form of the phase-locked amplitude `ε_n` (source 5936-5940, 4109-4124)

Source of record: `the November 2 reference manuscript` (73 pages), lines 5936-5940
and 4109-4124: the phase-locked amplitude has the form `ε = C_* ν^r e^{-d₀/ν}` with
`d₀ = γ/3`, `C_* = (2|𝒞(σ₀)|)^{-1/3}`, `r = (Re κ - 5 - 2σ₀)/3`.

`retEps Pl σ₀ n = (e^{-(γ/ν)} ν^{Re κ-5-2σ₀} / (2‖𝒞(σ₀)‖))^{1/3}` (definition in `ReturnInst.lean`),
and the cube root splits multiplicatively, `(a b / d)^{1/3} = a^{1/3} b^{1/3} / d^{1/3}`, with
`a^{1/3} = e^{-(γ/3)/ν}`, `b^{1/3} = ν^{r/3}` and `d^{-1/3} = (d^{1/3})⁻¹`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411
open UnforcedLeray.Cons.C03.Concrete (pairF phaseInt IsSolTest Params)
open UnforcedLeray.Blueprint.Planar (PlanarData)

theorem retEps_eq_form {Pl : PlanarData} {σ₀ : ℝ} (hC : Pl.signedCoeff σ₀ ≠ 0) (n : ℕ) : retEps Pl σ₀ n = (2 * ‖Pl.signedCoeff σ₀‖) ^ (-(1 / 3 : ℝ)) * retNu Pl σ₀ n ^ ((Pl.kappa.re - 5 - 2 * σ₀) / 3) * Real.exp (-(Pl.eigenvalue.re / 3) / retNu Pl σ₀ n) := by
  have hν : 0 < retNu Pl σ₀ n := retNu_pos Pl σ₀ n
  have ha : 0 < Real.exp (-(Pl.eigenvalue.re / retNu Pl σ₀ n)) := Real.exp_pos _
  have hb : 0 < retNu Pl σ₀ n ^ (Pl.kappa.re - 5 - 2 * σ₀) := Real.rpow_pos_of_pos hν _
  have hd : 0 < 2 * ‖Pl.signedCoeff σ₀‖ := mul_pos two_pos (norm_pos_iff.2 hC)
  have e1 : Real.exp (-(Pl.eigenvalue.re / retNu Pl σ₀ n)) ^ (1 / 3 : ℝ) =
      Real.exp (-(Pl.eigenvalue.re / 3) / retNu Pl σ₀ n) := by
    rw [← Real.exp_mul]
    congr 1
    ring
  have e2 : (retNu Pl σ₀ n ^ (Pl.kappa.re - 5 - 2 * σ₀)) ^ (1 / 3 : ℝ) =
      retNu Pl σ₀ n ^ ((Pl.kappa.re - 5 - 2 * σ₀) / 3) := by
    rw [← Real.rpow_mul hν.le]
    congr 1
    ring
  unfold retEps
  rw [Real.div_rpow (mul_pos ha hb).le hd.le, Real.mul_rpow ha.le hb.le, e1, e2,
    Real.rpow_neg hd.le]
  ring

end UnforcedLeray.Short.PartIIIb.Concrete

end
