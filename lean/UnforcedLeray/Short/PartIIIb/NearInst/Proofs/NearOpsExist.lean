import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_near_5

/-!
# Proof of `nearOpsExistC_of` (target `NearOpsExistC`, `NearInst/Targets.lean`; source 3866-3914)

The assembly is the compiled conditional `nearOpsExistC_of_sub` (`Sub/PartIII-b_C_near_5.lean`),
which takes `MaskedNearExists` in the organizer's form (`∀ ρ_b` placed after `ν₀`, see
`NearInst/Targets.lean`).  This file is the one-line specialization.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.NearInst

/-- **`PartIII-b:C/near/5`** (source 3866-3914): the pinned near operators exist, from the five
lemma `Prop`s `FreeStressExists`, `MaskedNearExists`, `CoeffMultExists`, `FlatTrainMultBound`,
`SplitMultBound`. -/
theorem nearOpsExistC_of (hF : FreeStressExists) (hN : MaskedNearExists)
    (hC : CoeffMultExists) (hT : FlatTrainMultBound) (hS : SplitMultBound) :
    NearOpsExistC :=
  nearOpsExistC_of_sub hF hN hC hT hS

end UnforcedLeray.Short.PartIIIb.NearInst
