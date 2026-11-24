import UnforcedLeray.Short.PartIIIb.Concrete.Spaces
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnAff

/-!
# Concrete data of `ret:general-affine-bounds` (source 2681-2689, 4955-4962, 5009-5016)

Source: `the November 2 reference manuscript`.

* `affM ν χ A` : the conormal size `M(A) = sup_{0<s≤1.1/ν} s^{-5/2} Σ_{j=0}^6 |(s∂_s)^j A^y(s)|`,
  `A^y = χ_f A` (lines 4955-4962), the right side of `ret:general-affine-bounds`.  It is the
  concrete value of the functional `MA` of `GeneralAffineBounds` (StatementsA.lean).
* `gradMeasure c`, `GrdG c` : the tensor space carrying the gradient `∇ĥ_A` of the affine lift
  with the normalized norm `R⁻¹‖·‖_{Y_2}` (lines 5009-5016, 5078-5079).  As for every body field,
  a physical tensor field is recorded by its coefficient in the tensor lift `𝒩_T T = sT`
  (lines 2681-2689), so that `R⁻¹‖𝒩_T T‖_{Y_2} = √π ‖T‖_{H_T}`, `H_T = L²(s^{-1/2} dς)`; the
  ambient value space is all `3×3` tensors (`Ten3`), since `∇ĥ_A` is not symmetric.  This is
  the space `Grd n` of `ReturnSeq` for the concrete instance.

Conventions as in `Concrete/ReturnOps.lean`: `SrcG c` is `L²(π s^{-3/2} dς; ℝ²)` (vector lift
`𝒩_v b = √s b`), and `GrdG c` is its tensor analogue `L²(π s^{-1/2} dς; ℝ^{3×3})`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- `M(A) = sup_{0<s≤1.1/ν} s^{-5/2} Σ_{j=0}^6 |(s∂_s)^j A^y(s)|`, `A^y = χ_f A`
(source 4955-4962; `χ` is the profile `χ̂_f`, `χ_f(s) = χ̂_f(νs)`). -/
def affM (ν : ℝ) (χ : ℝ → ℝ) (A : ℝ → Mat3) : ℝ :=
  sSup ((fun s => s ^ (-(5 / 2 : ℝ)) * affSum 6 (Ay ν χ A) s) '' Ioc 0 ((11 / 10) / ν))

/-- The measure `π s^{-1/2} dς` of the normalized tensor body norm
`R⁻¹‖𝒩_T T‖_{Y_2} = √π ‖T‖_{H_T}`, `𝒩_T T = sT` (source 2681-2689). -/
def gradMeasure (c : ℝ) : Measure Chart := ENNReal.ofReal Real.pi • ageμ c (-1 / 2)

/-- Tensor coefficients `T = s⁻¹ ∇ĥ` of gradients of body velocities, with the normalized norm
`R⁻¹‖∇ĥ‖_{Y_2} = √π ‖T‖_{H_T}` (source 2681-2689, 5009-5016). -/
abbrev GrdG (c : ℝ) := Lp (α := Chart) Ten3 2 (gradMeasure c)

example (c : ℝ) : CompleteSpace (GrdG c) := inferInstance

/-- `M(A)` only sees `A` on the age range: it depends on `A` through `A^y = χ_f A`. -/
theorem affM_congr {ν : ℝ} {χ : ℝ → ℝ} {A B : ℝ → Mat3} (h : Ay ν χ A = Ay ν χ B) :
    affM ν χ A = affM ν χ B := by
  unfold affM
  rw [h]

end UnforcedLeray.Short.PartIIIb.Concrete
