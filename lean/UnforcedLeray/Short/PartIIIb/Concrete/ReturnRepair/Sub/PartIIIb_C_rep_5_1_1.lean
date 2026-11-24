import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_5_1_cancelOrg
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_5_1_1.SopSubIsFar
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_5_1_1.PerBin
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_5_1_2_4_3
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_5_1_1.GainedLevel
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_5_1_1.GainedSeq
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_5_1_1.EarlyThin

/-!
# `PartIII-b:C/rep/5/1/1`: `FarBinsSeq`

Source `the November 2 reference manuscript` lines 5585-5599, 3902-3920.
-/

set_option autoImplicit false

noncomputable section

open UnforcedLeray.Blueprint.Planar (PlanarData)

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem farBins (Pl : PlanarData) (σ₀ mZ dm dp : ℝ) : FarBinsSeq Pl σ₀ mZ dm dp :=
  farBinsSeq_of Pl σ₀ mZ dm dp (sopSubIsFarSeq Pl σ₀ mZ dm dp) (perBinVelocitySeq Pl σ₀ mZ dm dp)
    binNormToAge z1TailGained earlyZ1Gained earlyPartThin

end UnforcedLeray.Short.PartIIIb.Concrete

end
