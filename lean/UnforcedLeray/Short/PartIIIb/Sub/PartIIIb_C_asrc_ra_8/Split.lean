import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_asrc_ra_8.Split.Leaves
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_asrc_ra_8.Split.BrkDerivSClosed
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_asrc_ra_8.Split.LatticeFDerivSum
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_asrc_ra_8.Split.BrkGaussBound1
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_asrc_ra_8.Split.BrkGaussBound2
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_asrc_ra_8.Split.VjGaussBound
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_asrc_ra_8.Split.PsiAjGaussBound
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_asrc_ra_8.Split.HpASumS
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_asrc_ra_8.Split.TsumBilinSplit

/-!
# `PartIII-b:C/asrc/ra/8/1` : `RPerSplit` (source 5022-5027, 4963-4978, 2040-2051)

The bracket split `RPerSplit` follows from the open leaves, which are all proved in the
`Split/` folder: `rPerSplit_of_leaves` (Split/Leaves.lean) takes the leaves `BrkDerivSClosed`,
`LatticeFDerivSum`, `BrkGaussBound1`, `BrkGaussBound2`, `VjGaussBound`, `PsiAjGaussBound`,
`HpASumS`, `TsumBilinSplit`, and the proof instantiates each of them by its proved theorem.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- **`RPerSplit`** (source 5022-5027): the bracket split, from the proved leaves. -/
theorem rPerSplit (as : ℝ) (χf : ℝ → ℝ) : RPerSplit as χf :=
  rPerSplit_of_leaves as χf brkDerivSClosed latticeFDerivSum brkGaussBound1 brkGaussBound2
    vjGaussBound psiAjGaussBound (hpASumS as χf) tsumBilinSplit

end UnforcedLeray.Short.PartIIIb.Concrete
