import UnforcedLeray.Short.PartIIIa.Sub.AdjInterior.Train.BSRep.HasFDeriv
import UnforcedLeray.Short.PartIIIa.Sub.AdjInterior.Train.Assembly

/-!
# `PartIII-a:T21/2/7/2/1/1/2/10`: `TjTrainBSRep m` from the train leaves of `Train/Defs.lean`

Source: `the November 2 reference manuscript` (SP) lines 261-266, 270-288,
2081-2084. The Biot-Savart law of the train needs, beyond the leaves proved in `BSRep/`, only the
train leaves `TjTrainVort` (task `PartIII-a:T21/2/7/2/1/1/2/5`), `TjLadGrad m` (`/9`),
`TjDecayOfGrad` (`/8`), `TjCirculationBdd` (`/17`) (through `tjVortDecay_of`) and `TjKcBound`
(`/11`).
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.IIIa

/-- **`TjTrainBSRep m` from the train leaves** (`tjVortDecay_of` and `tjTrainBSRep_of_train`). -/
theorem tjTrainBSRep_of_trainLeaves (m : ℝ) (hm : 8 < m) (hV : TjTrainVort) (hG : TjLadGrad m)
    (hDG : TjDecayOfGrad) (hCi : TjCirculationBdd) (hKb : TjKcBound) : TjTrainBSRep m :=
  tjTrainBSRep_of_train m hm hV (tjVortDecay_of m hm hV hG hDG hCi) hG hKb

end UnforcedLeray.Short.IIIa

#print axioms UnforcedLeray.Short.IIIa.tjTrainBSRep_of_trainLeaves
