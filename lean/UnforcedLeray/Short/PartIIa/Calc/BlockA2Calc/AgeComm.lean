import UnforcedLeray.Short.PartIIa.Calc.BlockA2Calc
import UnforcedLeray.Short.PartIIa.Sub.R02
import UnforcedLeray.Short.PartIIa.Tasks.R02.FluctuationProfile.ProfileCommute

/-!
# Part II-a, block `A₂`, task `PartII-a:R02/12/3`: commutators of `∂_s` with `K`, `∂_η`, `∂_q`

Source: `the November 2 reference manuscript`, lines 1267-1268 and 439-446.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.PartIIa.Jet.A2

open UnforcedLeray.B0184 UnforcedLeray.B0185 UnforcedLeray.B0188 UnforcedLeray.B0190

/-- **Commutators of `∂_s`** (task `PartII-a:R02/12/3`), from the pointwise profile commutators. -/
theorem ageComm_of (hC : UnforcedLeray.Short.PartIIa.ProfileCommutators) :
    UnforcedLeray.Short.PartIIa.Jet.A2.AgeComm := by
  intro F hF
  refine ⟨?_, ?_, ?_⟩
  · intro ν c hν hc tr htr x hx
    have hf2 : ContDiffAt ℝ 2 (F ν c tr) x :=
      ((hF ν c hν hc tr htr).contDiffAt
        (UnforcedLeray.Short.PartIIa.isOpen_late.mem_nhds hx)).of_le (by norm_num)
    have h := (hC (F ν c tr) x hf2).2.2
    show ageOperator (partialAge (F ν c tr)) x
      = partialAge (ageOperator (F ν c tr)) x - 2 * partialAge (F ν c tr) x
    linarith
  · intro ν c hν hc tr htr x hx
    have hf2 : ContDiffAt ℝ 2 (F ν c tr) x :=
      ((hF ν c hν hc tr htr).contDiffAt
        (UnforcedLeray.Short.PartIIa.isOpen_late.mem_nhds hx)).of_le (by norm_num)
    exact UnforcedLeray.Short.PartIIa.FluctuationProfile.partialEta_partialAge_comm_at hf2
  · intro ν c hν hc tr htr x hx
    have hf2 : ContDiffAt ℝ 2 (F ν c tr) x :=
      ((hF ν c hν hc tr htr).contDiffAt
        (UnforcedLeray.Short.PartIIa.isOpen_late.mem_nhds hx)).of_le (by norm_num)
    exact UnforcedLeray.Short.PartIIa.FluctuationProfile.profile_fderiv_comm_at hf2 esDir eqDir

end UnforcedLeray.Short.PartIIa.Jet.A2
