import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_2_3.PtOrg
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_2_3.Pt.DilJet
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_2_3.Pt.JointVec
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_2_3.Pt.AgeJetJoint
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_2_3.Pt.StreamShift
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_2_3.Pt.GradShift
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_2_3.Pt.EtaSeg
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_2_3.Pt.TailW
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_2_3.Pt.SupV
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_2_3.Pt.FixedBandP
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_2_3.Pt.PcTheta
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_2_3.Pt.TtJet
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_2_3.Pt.PcEnv
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_2_3.Pt.TtComp
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_2_3.Pt.PcJoint
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_2_3.Pt.PcSmooth
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_2_3.Pt.PcJetSup
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_2_3.Pt.BandP
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_2_3.Pt.WJetV
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_2_3.Pt.WJetP
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_2_3.Pt.WJetPsi
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_2_3.Pt.WDilV
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_2_3.Pt.WDilP
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_2_3.Pt.WDilPsi
import UnforcedLeray.Short.PartI.Tasks.OverlapHighNorm
import UnforcedLeray.Short.PartI.Tasks.OverlapFluctuationDecay
import UnforcedLeray.Short.PartI.Tasks.OverlapMeanPrimitive
import UnforcedLeray.Short.PartI.Tasks.OverlapMeanDecay
import UnforcedLeray.Short.PartI.Tasks.TrainOverlapProof
import UnforcedLeray.Short.PartI.Tasks.TrainVorticityTail
import UnforcedLeray.Short.PartI.Tasks.TrainStreamTails
import UnforcedLeray.Short.PartI.Tasks.TrainFluctuationDecayProof
import UnforcedLeray.Short.PartI.Tasks.TrainTransverseTailsProof
import UnforcedLeray.Short.PartI.Tasks.TrainFixedBandProof
import UnforcedLeray.Short.PartI.Tasks.TrainMeanEquations.StreamSmooth

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- Pointwise weighted train bound `TMPt` (source lines 5464-5465, 5477-5482, 5484-5495, 460-478). -/
theorem tmPt (D : SeqData) {dm dp : ℝ} : TMPt D dm dp := by
  have hHN := UnforcedLeray.Short.PartI.overlap_highnorm_uniform
  have hOFD := UnforcedLeray.Short.PartI.overlap_fluctuation_decay hHN
  have hOMP := UnforcedLeray.Short.PartI.overlap_mean_primitive
  have hOMD := UnforcedLeray.Short.PartI.overlap_mean_decay hHN hOFD hOMP
  have hOv := UnforcedLeray.Short.PartI.trainOverlap_proof hOFD hOMD
  have hVort := UnforcedLeray.Short.PartI.train_vorticity_gaussian_tail hOv
  have hTails := UnforcedLeray.Short.PartI.train_stream_velocity_pressure_tails hOv hVort
  have hFD := UnforcedLeray.Short.PartI.trainFluctuationDecay_proof hTails hOFD hOv
  have hT := UnforcedLeray.Short.PartI.trainTransverseTails_proof hVort hTails
  have hF := UnforcedLeray.Short.PartI.trainFixedBand_proof hTails hFD
  have hS := UnforcedLeray.Short.PartI.trainStreamSmooth
  have hPS := pcSmooth_of pcTheta
  have hPJ := pcJetSup_of hPS (pcJointJet_of pcTheta pcEnvJet (ttCompJet_of ttJetBound)) ageJetLeJoint
  have hB := bandP_of (fixedBandP_of hF) hPS hPJ (gradJetShift_of streamShift)
  have hTW := tailW_of hT
  have hSV := supV_of hF
  have hWV := wJetV_of hTW hSV
  exact tmPt_of D (wDilV_of dilJetBound jointAgeVec hWV)
    (wDilP_of dilJetBound (wJetP_of hTW hB etaSegment))
    (wDilPsi_of dilJetBound hS (wJetPsi_of hS hWV hTW hSV streamShift etaSegment))

end UnforcedLeray.Short.PartIIIb.Concrete
