import UnforcedLeray.Short.PartIIb.Sub.PartIIb_G4_3_6_2_3
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.Column.RawJet.Leaves.PsiJets.EtaSwap
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.Column.RawJet.Leaves.PsiJets.QSwap
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.Column.RawJet.Leaves.PsiJets.FirstJets
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.Column.RawJet.Leaves.PsiJets.D2Jet
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.Column.RawJet.Leaves.PsiJets.EtaSegment

/-!
# Part II-b, task `PartII-b:G4/3/6/2/3` (`RawPsiJets`): assembly from the leaves

Source of record: `the November 2 reference manuscript` (SP) 2419-2423 (jets of
the stream). The assembly lemma `rawPsiJets_of_lemmas` (Sub `PartII-b_G4_3_6_2_3`) takes the four
leaf properties as hypotheses; they are discharged by the leaf theorems
`psiFirstJets_proof`, `psiD2Jet_proof`, `psiEtaSegment_proof` (root namespace), and the mixed
swaps used inside them.
-/

theorem rawPsiJets_of (ht : UnforcedLeray.Short.IIb.RawPsiTailJets)
    (hv : UnforcedLeray.Short.IIb.RawVelJets)
    (hS : UnforcedLeray.Short.IIb.TrainVelSmooth) :
    UnforcedLeray.Short.IIb.RawPsiJets :=
  UnforcedLeray.Short.IIb.rawPsiJets_of_lemmas ht hv hS psiFirstJets_proof psiD2Jet_proof
    psiEtaSegment_proof
