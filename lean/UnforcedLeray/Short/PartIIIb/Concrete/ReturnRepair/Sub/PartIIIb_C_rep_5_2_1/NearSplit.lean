import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.Inverses.Seq
import UnforcedLeray.Short.PartIIIb.NearInst.Link.Pins.Proofs.StressPairAE
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Estimates
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_5_1_1.HW
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_5_1_1.HU

/-!
# `PartIII-b:C/rep/5/2/1/13`: the near split along the sequence

Source `the November 2 reference manuscript` 3888-3920, 5785.

At an actual level with large `n` and `z ∈ [-1, 1]`, the actual near operators are the field
`near` of the pinned operators `RegimePins` (`SeqData.RepairStanding.pins`, `Estimates.lean`), so
the near split `S_N = S - S_far` of the concrete base is `concreteBase_isNearSplit`
(`ReturnInst/Inverses/Level.lean`) with the closed inputs `stressMapWeakSolC` (`HW.lean`),
`NearInst.stressPairAE` and `freeWeakUniquenessAll` (`HU.lean`); the parameter conditions are read
off `inv_seq_large` and the standing hypotheses.  No global existence statement
(`NearInst.NearOpsExistC`) is used.
-/

set_option autoImplicit false

noncomputable section

open Filter Set

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- **The near split `S_N = S - S_far` along the sequence** (source 3888-3920, 5785), from the
standing hypotheses of the repair section. -/
theorem seqNearSplitStanding (D : SeqData) {dm dp : ℝ}
    (hst : D.RepairStanding dm dp) : SeqNearSplit D dm dp := by
  intro hact
  filter_upwards [inv_seq_large D hst.dm_pos hst.omega_ne hst.sigma_pos hst.sigma_lt hact,
    hst.pins] with n hn hp z hz h
  obtain ⟨-, hP, -, hμ⟩ := hn
  have hμ' : -(1 / 4) < D.mu n z := by linarith [(hμ z hz).1, hst.sigma_pos]
  exact concreteBase_isNearSplit stressMapWeakSolC NearInst.stressPairAE
    (freeWeakUniquenessAll _ _ _ _ _ (cOf_pos (retNu_pos D.Pl D.σ₀ n)) (retNu_pos D.Pl D.σ₀ n)
      (retEps_pos D.coeff_ne n) hP (by linarith))
    hP hμ' (by linarith [hst.mZ_gt]) (inv_rhoB_pos hst.C0_pos) (hp z hz).near h

end UnforcedLeray.Short.PartIIIb.Concrete
