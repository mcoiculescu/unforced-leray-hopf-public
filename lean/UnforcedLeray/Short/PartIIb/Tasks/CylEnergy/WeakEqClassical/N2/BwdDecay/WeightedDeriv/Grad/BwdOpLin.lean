import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T22_2_3_2_2_1

/-!


Source: `the November 2 reference manuscript` lines 2100-2105.
The time derivative is linear by `HasDerivAt.const_mul` and `HasDerivAt.add`; the spatial
partials and the planar Laplacian are linear on `C²` slices (`pd` is `fderiv` along `dir j`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology

namespace UnforcedLeray.Short.IIb

/-- The first partial of a `C²` function is differentiable. -/
theorem bwdOpLin_pd_diff (f : B0579.Plane → ℝ) (hf : ContDiff ℝ 2 f) (j : Fin 2) :
    Differentiable ℝ (B0579.pd j f) := by
  have hC1 : ContDiff ℝ 1 (fderiv ℝ f) := hf.fderiv_right (m := 1) (by norm_num)
  have e : B0579.pd j f = fun y => fderiv ℝ f y (B0579.dir j) := rfl
  rw [e]
  exact (hC1.differentiable (by norm_num)).clm_apply (differentiable_const _)

/-- Pointwise linearity of `pd`. -/
theorem bwdOpLin_pd_lin (f g : B0579.Plane → ℝ) (hf : Differentiable ℝ f)
    (hg : Differentiable ℝ g) (a : ℝ) (j : Fin 2) (y : B0579.Plane) :
    B0579.pd j (fun z => a * f z + g z) y = a * B0579.pd j f y + B0579.pd j g y := by
  have hh : HasFDerivAt (fun z => a * f z + g z) (a • fderiv ℝ f y + fderiv ℝ g y) y :=
    ((hf y).hasFDerivAt.const_mul a).add (hg y).hasFDerivAt
  unfold B0579.pd
  rw [hh.fderiv]
  simp

/-- Linearity of the planar Laplacian on `C²` functions. -/
theorem bwdOpLin_lapP (U W : B0579.Plane → ℝ) (hU : ContDiff ℝ 2 U) (hW : ContDiff ℝ 2 W)
    (a : ℝ) (x : B0579.Plane) :
    lapP (fun z => a * U z + W z) x = a * lapP U x + lapP W x := by
  have hUd : Differentiable ℝ U := hU.differentiable (by norm_num)
  have hWd : Differentiable ℝ W := hW.differentiable (by norm_num)
  have e0 : B0579.pd 0 (fun z => a * U z + W z) =
      fun z => a * B0579.pd 0 U z + B0579.pd 0 W z :=
    funext (fun y => bwdOpLin_pd_lin U W hUd hWd a 0 y)
  have e1 : B0579.pd 1 (fun z => a * U z + W z) =
      fun z => a * B0579.pd 1 U z + B0579.pd 1 W z :=
    funext (fun y => bwdOpLin_pd_lin U W hUd hWd a 1 y)
  have e00 : B0579.pd 0 (fun z => a * B0579.pd 0 U z + B0579.pd 0 W z) =
      fun z => a * B0579.pd 0 (B0579.pd 0 U) z + B0579.pd 0 (B0579.pd 0 W) z :=
    funext (fun y => bwdOpLin_pd_lin (B0579.pd 0 U) (B0579.pd 0 W)
      (bwdOpLin_pd_diff U hU 0) (bwdOpLin_pd_diff W hW 0) a 0 y)
  have e11 : B0579.pd 1 (fun z => a * B0579.pd 1 U z + B0579.pd 1 W z) =
      fun z => a * B0579.pd 1 (B0579.pd 1 U) z + B0579.pd 1 (B0579.pd 1 W) z :=
    funext (fun y => bwdOpLin_pd_lin (B0579.pd 1 U) (B0579.pd 1 W)
      (bwdOpLin_pd_diff U hU 1) (bwdOpLin_pd_diff W hW 1) a 1 y)
  simp only [lapP, e0, e1, e00, e11]
  ring

theorem bwdOpLin : UnforcedLeray.Short.IIb.BwdOpLin := by
  intro ν b0 b1 U W r x a FU FW hU hW hUa hWa
  obtain ⟨DU, hDU, eU⟩ := hUa
  obtain ⟨DW, hDW, eW⟩ := hWa
  refine ⟨a * DU + DW, (hDU.const_mul a).add hDW, ?_⟩
  show a * DU + DW + ν * lapP (fun z => a * U r z + W r z) x +
      (b0 r x * B0579.pd 0 (fun z => a * U r z + W r z) x +
        b1 r x * B0579.pd 1 (fun z => a * U r z + W r z) x) = a * FU + FW
  rw [bwdOpLin_lapP (U r) (W r) hU hW a x,
    bwdOpLin_pd_lin (U r) (W r) (hU.differentiable (by norm_num))
      (hW.differentiable (by norm_num)) a 0 x,
    bwdOpLin_pd_lin (U r) (W r) (hU.differentiable (by norm_num))
      (hW.differentiable (by norm_num)) a 1 x]
  linear_combination a * eU + eW

end UnforcedLeray.Short.IIb
