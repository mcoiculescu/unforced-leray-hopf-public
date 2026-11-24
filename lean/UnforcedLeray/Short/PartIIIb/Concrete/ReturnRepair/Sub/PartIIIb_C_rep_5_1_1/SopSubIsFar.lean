import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_5_1_1Org
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.Inverses.Seq
import UnforcedLeray.Short.PartIIIb.NearInst.Link.Pins.Proofs.StressPairAE
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_5_1_1.HW
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_5_1_1.HU
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_5_2_1.NearSplit

/-!
# `PartIII-b:C/rep/5/1/1/1`: the far mask `Sop - SNop = S_far`

Source `the November 2 reference manuscript` 3888-3920, 5785.

`SopSubIsFarSeq` is read off `seqNearSplit_of` (`ReturnInst/Inverses/Seq.lean`): the near split
`B.SN = B.S - Sf` of the concrete base, with `B.S = Sop` and `B.SN = SNop` by `rfl`, and
`RepairStanding` supplying the actual level, the near operators and the numerical hypotheses.

The three analytic inputs `StressMapWeakSol`, `FreeWeakUniqueness` (the `hU` family) and
`NearOpsExistC` are not closed theorems of the project yet; they are taken as hypotheses in
`sopSubIsFarSeq_of`. `NearInst.stressPairAE` is closed and is used directly.

The unconditional `sopSubIsFarSeq` does not use `NearOpsExistC`: the actual near operators at the
large levels are the field `near` of `RepairStanding.pins` (`RegimePins`, `Estimates.lean`), and the
near split along the sequence is `seqNearSplitStanding` (`Sub/PartIII-b_C_rep_5_2_1/NearSplit.lean`,
with the closed `stressMapWeakSolC` (`HW.lean`) and `freeWeakUniquenessAll` (`HU.lean`)).
-/

set_option autoImplicit false

noncomputable section

open Filter Set MeasureTheory UnforcedLeray.Axi
open UnforcedLeray.Blueprint.Planar (PlanarData)

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- **`S_μ - S_N = S_far`** along the sequence, conditional on the three analytic inputs of the
concrete near theory (`StressMapWeakSol`, the free weak uniqueness family `hU`, and
`NearOpsExistC`). -/
theorem sopSubIsFarSeq_of
    (hW : NearInst.StressMapWeakSol)
    (hU : ∀ (c γ ν ε μ : ℝ), 0 < c → 0 < ν → 0 < ε → 2 * ε * c ≤ 1 → 0 < μ + 1 / 4 →
      FreeWeakUniqueness c γ ν ε μ)
    (hEx : NearInst.NearOpsExistC) (Pl : PlanarData) (σ₀ mZ dm dp : ℝ) :
    SopSubIsFarSeq Pl σ₀ mZ dm dp := by
  unfold SopSubIsFarSeq
  intro D _ _ _ hst
  have hS : SeqNearSplit D dm dp := seqNearSplit_of hW NearInst.stressPairAE hU hEx D hst.planar hst.dm_pos
    hst.omega_ne hst.sigma_pos hst.sigma_lt hst.mZ_gt hst.b_pos hst.b_lt hst.δ_pos
    hst.m0_pos hst.m0_lt.le hst.C0_pos
  filter_upwards [hS hst.actual, hst.near] with n hn hnear
  intro z hz
  obtain ⟨Sf, hSf, hsn⟩ := hn z hz (hnear z hz)
  refine ⟨Sf, hSf, ?_⟩
  have e1 : (concreteBase D.Pl D.K (D.level n) (D.mu n z) (hnear z hz)).S
      = Sop D.Pl D.K (D.level n) (D.mu n z) := rfl
  have e2 : (concreteBase D.Pl D.K (D.level n) (D.mu n z) (hnear z hz)).SN
      = SNop D.Pl D.K (D.level n) (D.mu n z) := rfl
  rw [e1, e2] at hsn
  rw [hsn, sub_sub_cancel]

/-- **`S_μ - S_N = S_far`** along the sequence (source 3888-3920, 5785): the near split
`seqNearSplitStanding`, read off the standing hypotheses of the repair section. -/
theorem sopSubIsFarSeq (Pl : PlanarData) (σ₀ mZ dm dp : ℝ) : SopSubIsFarSeq Pl σ₀ mZ dm dp := by
  intro D _ _ _ hst
  have hS : SeqNearSplit D dm dp := seqNearSplitStanding D hst
  filter_upwards [hS hst.actual, hst.near] with n hn hnear
  intro z hz
  obtain ⟨Sf, hSf, hsn⟩ := hn z hz (hnear z hz)
  refine ⟨Sf, hSf, ?_⟩
  have e1 : (concreteBase D.Pl D.K (D.level n) (D.mu n z) (hnear z hz)).S
      = Sop D.Pl D.K (D.level n) (D.mu n z) := rfl
  have e2 : (concreteBase D.Pl D.K (D.level n) (D.mu n z) (hnear z hz)).SN
      = SNop D.Pl D.K (D.level n) (D.mu n z) := rfl
  rw [e1, e2] at hsn
  rw [hsn, sub_sub_cancel]

end UnforcedLeray.Short.PartIIIb.Concrete
