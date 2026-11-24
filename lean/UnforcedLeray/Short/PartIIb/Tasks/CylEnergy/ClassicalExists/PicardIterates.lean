import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T22_1_14
import UnforcedLeray.Short.PartIIb.Tasks.CylEnergy.ClassicalExists.PicardIterates.PicRegSub
import UnforcedLeray.Short.PartIIb.Tasks.CylEnergy.ClassicalExists.PicardIterates.W2AddLe
import UnforcedLeray.Short.PartIIb.Tasks.CylEnergy.ClassicalExists.PicardIterates.W2Neg
import UnforcedLeray.Short.PartIIb.Tasks.CylEnergy.ClassicalExists.PicardIterates.PicStep
import UnforcedLeray.Short.PartIIb.Tasks.CylEnergy.ClassicalExists.PicardIterates.DuhamelPhiSub
import UnforcedLeray.Short.PartIIb.Tasks.CylEnergy.ClassicalExists.PicardIterates.VolterraStepBound
import UnforcedLeray.Short.PartIIb.Tasks.CylEnergy.ClassicalExists.PicardIterates.GammaSeriesSummable
import UnforcedLeray.Short.PartIIb.Tasks.CylEnergy.ClassicalExists.FreePart

/-!


Source: `the November 2 reference manuscript` lines 2074-2093, 2103-2105.
The proof is `picardIterates_of` (Sub/PartII-b_T22_1_14.lean) applied to the seven leaf
theorems and `freePart`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open UnforcedLeray.Cons.C03.Concrete

namespace UnforcedLeray.Short.IIb

namespace CylPDE

/-- **`PartII-b:T22/1/14`** `PicardIterates`, assembled from the leaves. -/
theorem picardIterates : UnforcedLeray.Short.IIb.CylPDE.PicardIterates :=
  picardIterates_of picRegSub_proof w2AddLe_proof w2Neg_proof picStep_proof
    duhamelPhiSub_proof volterraStepBound_proof gammaSeriesSummable_proof freePart

end CylPDE

end UnforcedLeray.Short.IIb

end
