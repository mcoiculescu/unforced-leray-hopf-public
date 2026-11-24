import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_2_3.PtOrg

/-!
# `PartIII-b:C/rep/8/2/3/2/16`: the age jets of the Gaussian pressure `PcJetSup`

Source of record: `the November 2 reference manuscript` 4963-4968, 5484-5495.
For `ℓ, m`, take the joint bound `K` of `PcJointJet` at order `ℓ + m` (`C = K`, `k = 0`, `a = 1/2`).
The age jet is bounded by the joint derivative of the same order (`AgeJetLeJoint`), and `ν⁻¹^0 = 1`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.Cyl (Plane)

theorem pcJetSup_of (h1 : PcSmooth) (h2 : PcJointJet) (h3 : AgeJetLeJoint) : PcJetSup := by
  intro ℓ m
  obtain ⟨K, hK⟩ := h2 (ℓ + m)
  refine ⟨K, 0, 1 / 2, by norm_num, fun ν hν hνa s hs hsν z => ?_⟩
  have hF := h1 ν (cOf ν) hν (cOf_pos hν)
  have h3' := h3 (fun r w => UnforcedLeray.Train.pc ν (cOf ν) r w) hF ℓ m s hs z
  have hK' := hK ν hν hνa (s, z) hs hsν
  rw [pow_zero, mul_one]
  exact h3'.trans hK'

end UnforcedLeray.Short.PartIIIb.Concrete
