import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_4_2.Defs
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_4_2.Sub.PartIIIb_IIIb_D2_4_2_1
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_4_2.Sub.LocalTsumC2
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_4_2.Sub.PsiProfileSmooth
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_4_2.Sub.PsiTermLocalBound

/-!
# `PsiRingSmooth` (task `PartIII-b:IIIb-D2/4/2/1`)

Source of record: `the November 2 reference manuscript` lines 4963-4991.
Assembles the three analytic inputs `LocalTsumC2` (L1), `PsiProfileSmooth` (L2) and
`PsiTermLocalBound` (L4) through `psiRingSmooth_of`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem psiRingSmooth_proof (as : ℝ) (χf : ℝ → ℝ) : PsiRingSmooth as χf :=
  psiRingSmooth_of as χf localTsumC2_proof (psiProfileSmooth_proof as χf)
    (psiTermLocalBound_proof as χf)

end UnforcedLeray.Short.PartIIIb.Concrete
