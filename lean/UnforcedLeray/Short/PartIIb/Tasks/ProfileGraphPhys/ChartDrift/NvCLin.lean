import UnforcedLeray.Short.PartIIb.Tasks.ProfileGraphPhys.ChartDrift.Lift

/-!
# `PartII-b:T10/6/3/1/3b`: `ℂ`-linearity of the complex ring lift `NvC`

`NvC R (a • b - b') = a • NvC R b - NvC R b'` for `a : ℂ`. The real and imaginary meridional
parts split a complex scalar (`reM (a • v) = a.re • reM v - a.im • imM v`, and similarly for
`imM`), and `Axi.Nv` and `B0412.realC` are real-linear.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology

namespace UnforcedLeray.Short.IIb

open UnforcedLeray.PhaseSpace

theorem nvCLin_realC_sub (x y : Space) :
    B0412.realC (x - y) = B0412.realC x - B0412.realC y := by
  ext i
  simp [B0412.realC_apply]

theorem nvCLin_realC_add (x y : Space) :
    B0412.realC (x + y) = B0412.realC x + B0412.realC y := by
  ext i
  simp [B0412.realC_apply]

theorem nvCLin_realC_smul (k : ℝ) (x : Space) :
    B0412.realC (k • x) = (k : ℂ) • B0412.realC x := by
  ext i
  simp [B0412.realC_apply]

theorem nvCLin_I_mul_I_smul (v : CVec3) : (Complex.I * Complex.I) • v = -v := by
  rw [Complex.I_mul_I, neg_smul, one_smul]

theorem nvCLin_alg (a : ℂ) (X1 X2 X3 X4 : CVec3) :
    ((a.re : ℂ) • X1 - (a.im : ℂ) • X2 - X3) +
        Complex.I • ((a.re : ℂ) • X2 + (a.im : ℂ) • X1 - X4) =
      a • (X1 + Complex.I • X2) - (X3 + Complex.I • X4) := by
  have h := nvCLin_I_mul_I_smul X2
  conv_rhs => rw [← Complex.re_add_im a]
  linear_combination (norm := module) (-(a.im : ℂ)) • h

theorem nvCLin_proof : UnforcedLeray.Short.IIb.ChartLift.NvCLin := by
  intro R a b b' p
  have hre : (fun z => reM (a • b z - b' z)) =
      (a.re • (fun z => reM (b z)) - a.im • (fun z => imM (b z))) - (fun z => reM (b' z)) := by
    funext z
    ext i
    simp [reM, imM]
  have him : (fun z => imM (a • b z - b' z)) =
      (a.re • (fun z => imM (b z)) + a.im • (fun z => reM (b z))) - (fun z => imM (b' z)) := by
    funext z
    ext i
    simp [reM, imM]
  simp only [NvC]
  rw [hre, him]
  simp only [Axi.Nv_sub, Axi.Nv_add, Axi.Nv_smul, nvCLin_realC_sub, nvCLin_realC_add,
    nvCLin_realC_smul]
  exact nvCLin_alg a _ _ _ _

end UnforcedLeray.Short.IIb
