import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_3_1_8_1
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_1.KernelAdjoint
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_3.LinAdjDuality.AdjWeakChi.Field
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_3.LinAdjDuality.AdjWeakChi.XNorm
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_3.LinAdjDuality.AdjWeakChi.Identify

/-!
# Part III-a, task `PartIII-a:T21/2/3/1/8/1` (`adjWeakChiBound`)

Source of record: `the November 2 reference manuscript` lines 3052-3058.
Assembly of `AdjWeakChiBound m` from the kernel adjoint bound (`kernelAdjointBound`), the weighted
field bound (`adjWFieldBound`), the uniform `X_{-m}` bound (`adjWXNormBdd`) and the identification
of `ladChi` (`adjWChiIdentify`), via `adjWeakChiBound_of`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.IIIa

theorem adjWeakChiBound (m : ℝ) (hm : 8 < m) : UnforcedLeray.Short.IIIa.AdjWeakChiBound m :=
  adjWeakChiBound_of m (kernelAdjointBound m) (adjWFieldBound m) (adjWXNormBdd m)
    (adjWChiIdentify m) hm

end UnforcedLeray.Short.IIIa
