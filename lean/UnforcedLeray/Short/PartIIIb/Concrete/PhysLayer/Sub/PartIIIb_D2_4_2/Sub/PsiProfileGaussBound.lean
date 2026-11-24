import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_4_2.Sub.PartIIIb_IIIb_D2_4_2_1_3
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_4_2.Sub.PsiProfileGaussBound.GaussFactor
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_4_2.Sub.PsiProfileGaussBound.PolyFactor
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_4_2.Sub.PsiProfileGaussBound.LeibnizMul

/-!
# `PsiProfileGaussBound` assembled from its three leaves (task `PartIII-b:IIIb-D2/4/2/1/3`)

Source of record: `the November 2 reference manuscript` lines 4963-4991.
The Gaussian factor leaf (`psiGaussFactor_proof`), the polynomial factor leaf
(`psiPolyFactor_proof`) and the Leibniz product leaf (`leibnizMulBound_proof`) are combined by the
decomposition lemma `psiProfileGaussBound_of` (`PartIII-b_IIIb-D2_4_2_1_3.lean`).
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem psiProfileGaussBound_proof (as : ℝ) (χf : ℝ → ℝ) : PsiProfileGaussBound as χf :=
  psiProfileGaussBound_of as χf psiGaussFactor_proof (psiPolyFactor_proof as χf)
    leibnizMulBound_proof

end UnforcedLeray.Short.PartIIIb.Concrete
