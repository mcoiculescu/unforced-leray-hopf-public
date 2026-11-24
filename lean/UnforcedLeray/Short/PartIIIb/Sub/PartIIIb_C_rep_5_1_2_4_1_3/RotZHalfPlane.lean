import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_5_1_2_4_1_3.Kernel
import UnforcedLeray.Lib.AxisymmetricB.Average

/-!
# `PartIII-b:C/rep/5/1/2/4/1/3/3/7`: every point is rotated into the half plane `φ = 0`

Source `the November 2 reference manuscript` 2672-2674 (geometry of the half
plane `φ = 0`).  For `y ∈ ℝ³` take `α = -arg(y₀ + i y₁)`.  Then
`rotZ α y = cylMap((ϱ y, 0), y₂) = !₂[ϱ y, 0, y₂]`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete.WYCore

/-- **Half plane** (source 2672-2674): every point is rotated into the half plane `φ = 0` by some
`rotZ α`, namely `α = -arg(y₀ + i y₁)`. -/
theorem rotZHalfPlane : RotZHalfPlane := by
  intro y
  refine ⟨-Complex.arg ⟨y 0, y 1⟩, ?_⟩
  have h : Axi.rotZ (-Complex.arg ⟨y 0, y 1⟩) y =
      Axi.rotFun (-Complex.arg ⟨y 0, y 1⟩)
        (Axi.cylMap ((ϱ y, Complex.arg ⟨y 0, y 1⟩), y 2)) := by
    rw [Axi.cylMap_polar, Axi.rotZ_apply]
  rw [h, Axi.rotFun_cylMap]
  ext i
  fin_cases i <;> simp [Axi.cylMap]

end UnforcedLeray.Short.PartIIIb.Concrete.WYCore

end
