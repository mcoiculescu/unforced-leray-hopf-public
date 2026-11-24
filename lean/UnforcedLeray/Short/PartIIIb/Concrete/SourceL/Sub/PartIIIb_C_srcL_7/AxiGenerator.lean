import UnforcedLeray.Short.PartIIIb.Concrete.SourceL.Sub.PartIIIb_C_srcL_7

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- The angular derivative of the rotation at the identity. -/
theorem rotAx_hasDerivAt_zero (v : Vec3) : HasDerivAt (fun θ => rotAx θ v) ![-v 1, v 0, 0] 0 := by
  have h0 : HasDerivAt (fun θ => rotAx θ v 0) (-v 1) 0 := by
    have h := ((Real.hasDerivAt_cos 0).mul_const (v 0)).sub
      ((Real.hasDerivAt_sin 0).mul_const (v 1))
    have e : -Real.sin 0 * v 0 - Real.cos 0 * v 1 = -v 1 := by simp
    exact h.congr_deriv e
  have h1 : HasDerivAt (fun θ => rotAx θ v 1) (v 0) 0 := by
    have h := ((Real.hasDerivAt_sin 0).mul_const (v 0)).add
      ((Real.hasDerivAt_cos 0).mul_const (v 1))
    have e : Real.cos 0 * v 0 + -Real.sin 0 * v 1 = v 0 := by simp
    exact h.congr_deriv e
  have h2 : HasDerivAt (fun θ => rotAx θ v 2) 0 0 := by
    have hf : (fun θ => rotAx θ v 2) = fun _ => v 2 := by
      funext θ
      simp [rotAx]
    rw [hf]
    exact hasDerivAt_const _ _
  refine hasDerivAt_pi.2 fun i => ?_
  fin_cases i
  · exact h0
  · exact h1
  · exact h2

theorem axiGenerator : AxiGenerator := by
  intro Z p hZ hdiff
  have hp0 : rotAx 0 p = p := by
    funext i
    fin_cases i <;> simp [rotAx]
  have hZd : HasFDerivAt Z (fderiv ℝ Z p) (rotAx 0 p) := by
    rw [hp0]
    exact hdiff.hasFDerivAt
  have hcomp : HasDerivAt (Z ∘ fun θ => rotAx θ p) (fderiv ℝ Z p ![-p 1, p 0, 0]) 0 :=
    hZd.comp_hasDerivAt 0 (rotAx_hasDerivAt_zero p)
  have heq : (Z ∘ fun θ => rotAx θ p) = fun θ => rotAx θ (Z p) :=
    funext fun θ => hZ θ
  have hother : HasDerivAt (Z ∘ fun θ => rotAx θ p) ![-Z p 1, Z p 0, 0] 0 := by
    rw [heq]
    exact rotAx_hasDerivAt_zero (Z p)
  exact hcomp.unique hother

end UnforcedLeray.Short.PartIIIb.Concrete
