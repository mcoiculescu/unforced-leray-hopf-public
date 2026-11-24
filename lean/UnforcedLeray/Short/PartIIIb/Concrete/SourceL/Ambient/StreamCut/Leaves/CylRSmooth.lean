import UnforcedLeray.Short.PartIIIb.Concrete.SourceL.Sub.PartIIIb_C_srcL_9_5_3

/-!
# Proof of `SCCylRSmooth` (source 4178-4186)

`cylR y = √(y₀² + y₁²)` is `C^7` at every point where it is positive, since the radicand is then
nonzero and polynomial.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem scCylRSmooth : SCCylRSmooth := by
  intro y hy
  have hq : ContDiffAt ℝ 7 (fun z : Vec3 => z 0 ^ 2 + z 1 ^ 2) y := by
    fun_prop
  have hne : (fun z : Vec3 => z 0 ^ 2 + z 1 ^ 2) y ≠ 0 := by
    intro h
    have h' : cylR y = 0 := by
      unfold cylR
      simp only at h
      rw [h, Real.sqrt_zero]
    exact hy.ne' h'
  exact hq.sqrt hne

end UnforcedLeray.Short.PartIIIb.Concrete
