import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_1.GeomY.GeomYB.TaylorWidth.Of
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_1.GeomY.GeomYB.TaylorWidth.SepComm.Defs
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_1.GeomY.GeomYB.TaylorWidth.SepComm.MainLeibniz
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_1.GeomY.GeomYB.TaylorWidth.SepComm.MainDiff0
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_1.GeomY.GeomYB.TaylorWidth.SepComm.MainDiff2
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_1.GeomY.GeomYB.TaylorWidth.SepComm.PsiDiff

/-!
# `PartIII-b:C/rep/8/1/1/2/5/2/1` (`YBWidth.SepCommMeanFar`): reduction to transition-annulus
sub-leaves and quantifier-order note

Source `the November 2 reference manuscript`
lines 5427-5432, 5383-5387, 5415-5427; SP 3604-3610, 3700-3712, 3735-3766, 4195-4215.

All leaf definitions (`SepCommMainLeibniz`, `SepCommMainDiff0`, `SepCommMainDiff1`,
`SepCommMainDiff2`, `SepCommPsiDiff`), the unconditional proof of the order-1 leaf
`sepCommMainDiff1 : SepCommMainDiff1` (from `sepMeanFar`), the young-interior vanishing
`fderiv_comm_eq_zero_of_gt`, the all-order separated kernel comparison `sepKernelDiffIter`, and the
conditional assembly `sepCommMeanFarFixed_of` are in `TaylorWidth/SepComm/Defs.lean`.

## Quantifier-order fix in `Of.lean` (task `PartIII-b:C/rep/8/1/1/2/5/2/1/org`)

In `Of.lean:62-64`, `YBWidth.SepCommMeanFar` places `∃ (C : ℝ) (k : ℕ)` before
`∀ χy : ℝ → ℝ, IsStreamCutoff χy`. Because `IsStreamCutoff χy` (`Concrete/SourceL.lean:55`)
constrains only `0 ≤ χy ≤ 1`, `χy = 1` on `(-∞, 4/5]`, and `χy = 0` on `[1, ∞)` without bounding
`deriv^[m] χy` (`1 ≤ m ≤ 3`) on `(4/5, 1)`, the constant `C` must depend on `χy` (`∀ χy : ℝ → ℝ,
IsStreamCutoff χy → ∃ (C : ℝ) (k : ℕ), 0 ≤ C ∧ ...`, matching `StreamCutAlgStmt` in
`GeomX/Asm/Defs.lean:109`, `TCCoeff` in `PartIII-b_C_rep_5_2_2_11.lean:163`, and
`SepCommMeanFarFixed` in `SepComm/Defs.lean:488`). Once `Of.lean` is updated by
`PartIII-b:C/rep/8/1/1/2/5/2/1/org` so `SepCommMeanFar` equals `SepCommMeanFarFixed`,
`sepCommMeanFar` is assembled directly by:
`YBWidth.sepCommMeanFarFixed_of YBWidth.sepCommMainLeibniz YBWidth.sepCommMainDiff0 YBWidth.sepCommMainDiff2 YBWidth.sepCommPsiDiff`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.Short.IIIa

namespace YBWidth

open YBComm PhasePrim

/-- **`SepCommMeanFar` from the four remaining transition-annulus sub-leaves**
(`SepCommMainDiff1` is already discharged by `sepCommMainDiff1` in `SepComm/Defs.lean`). -/
theorem sepCommMeanFar_of (hL : SepCommMainLeibniz) (h0 : SepCommMainDiff0)
    (h2 : SepCommMainDiff2) (hP : SepCommPsiDiff) : SepCommMeanFar :=
  sepCommMeanFarFixed_of hL h0 h2 hP

end YBWidth

/-- **Finite width and heat-to-Newton for the commutator** (`PartIII-b:C/rep/8/1/1/2/5/2/1`;
source 5427-5432, 5383-5387, 5415-5427). Assembled from the four transition-annulus sub-leaves
`sepCommMainLeibniz`, `sepCommMainDiff0`, `sepCommMainDiff2`, and `sepCommPsiDiff` via
`YBWidth.sepCommMeanFar_of`. -/
theorem YBWidth.sepCommMeanFar : YBWidth.SepCommMeanFar :=
  YBWidth.sepCommMeanFar_of
    YBWidth.sepCommMainLeibniz
    YBWidth.sepCommMainDiff0
    YBWidth.sepCommMainDiff2
    YBWidth.sepCommPsiDiff

end UnforcedLeray.Short.PartIIIb.Concrete
