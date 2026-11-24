import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_3_3
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_3.MovingPhiH1.WeakFromSmooth
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_3.MovingPhiH1.ScaleMemLp
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_3.MovingPhiH1.PdScale

/-!
# Part III-a, task `PartIII-a:T21/2/3/3` (`MovingPhiH1`): the target theorem

Source of record: `the November 2 reference manuscript`, lines 3044, 3074-3075.
`movingPhiH1` is `movingPhiH1_of` applied to the three leaf theorems.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.IIIa

/-- The moving adjoint at the initial age is an `H¹_{-m,d_t}` function (SP 3044, 3074-3075). -/
theorem movingPhiH1 (m : ℝ) : MovingPhiH1 m :=
  movingPhiH1_of m mpWeakFromSmooth mpScaleMemLp mpPdScale

end UnforcedLeray.Short.IIIa
