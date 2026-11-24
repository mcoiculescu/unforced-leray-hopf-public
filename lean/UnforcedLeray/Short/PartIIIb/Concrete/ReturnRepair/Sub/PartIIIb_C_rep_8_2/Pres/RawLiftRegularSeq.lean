import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_2.Pres.RawLiftRegular

/-!
# Standing hypotheses on the sequence for the raw-lift regularity
(task `PartIII-b:C/rep/8/2/pres/6/2/thread`)

Source `the November 2 reference manuscript`:
the BUC class of the train 270-288; the lift is smooth through the axis 1205-1225.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

namespace SeqData

/-- Every level's train is in the BUC class (source 270-288). -/
def BUCTrains (D : SeqData) : Prop :=
  ∀ n, UnforcedLeray.Short.PartI.IsBUCTrain (D.train n)

/-- Every level's raw coefficient has its axis value as the continuous extension (source 1205-1225). -/
def RawAxisCont (D : SeqData) : Prop :=
  ∀ n, RawAxisContinuous D.Pl (D.level n)

/-- The BUC class holds along the sequence (it is part of `SeqData`). -/
theorem bucTrains (D : SeqData) : D.BUCTrains := D.train_buc

end SeqData

end UnforcedLeray.Short.PartIIIb.Concrete
