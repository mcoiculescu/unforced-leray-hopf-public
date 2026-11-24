import UnforcedLeray.Short.PartIIa.Sub.N02
import UnforcedLeray.Short.PartIIa.Tasks.N02LerayComparison.GradMember
import UnforcedLeray.Short.PartIIa.Tasks.N02LerayComparison.StreamMember
import UnforcedLeray.Short.PartIIa.Tasks.N02LerayComparison.ZeroMode
import UnforcedLeray.Short.PartIIa.Tasks.N02LerayComparison.NonzeroMode
import UnforcedLeray.Short.PartIIa.Tasks.N02LerayComparison.ModeSplit

/-!


Target: `theorem nearLerayComparison : NearLerayComparison`
(`Short/PartII-a/StatementsNear.lean`, line 224). Source of record:
`the November 2 reference manuscript`, lines 1724-1751.

The proof is the composition of the five lemma Props, each proved in its own task module:

* `nearLerayComparison_of` (`Sub/N02.lean`): the reduction from the five lemma Props to
  `NearLerayComparison`;
* `nearGradMember_proof` (`Tasks/N02LerayComparison/GradMember.lean`);
* `nearStreamMember_proof` (`Tasks/N02LerayComparison/StreamMember.lean`);
* `nearLerayZeroMode_proof` (`Tasks/N02LerayComparison/ZeroMode.lean`);
* `nearLerayNonzeroMode_proof` (`Tasks/N02LerayComparison/NonzeroMode.lean`);
* `nearLerayModeSplit_proof` (`Tasks/N02LerayComparison/ModeSplit.lean`).
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIa

theorem nearLerayComparison : NearLerayComparison :=
  nearLerayComparison_of nearGradMember_proof nearStreamMember_proof nearLerayZeroMode_proof
    nearLerayNonzeroMode_proof nearLerayModeSplit_proof

end UnforcedLeray.Short.PartIIa
