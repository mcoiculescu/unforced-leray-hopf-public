import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_8
import UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst.Proofs.FlatBmatCont
import UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst.Proofs.FlatTermDecay

/-!
# `PartIII-b:C/flatset/col/8`: `FlatForceDecay`

Source of record: `the November 2 reference manuscript`, lines 4594-4596, 4988
("the sums and their required derivatives converge by Gaussian decay"), 3426-3440 (the force of
the causal problem lies in `𝒯`).

Assembly: the continuity of `B` (`flatBmatCont`) and the decaying lattice-term bound
(`flatTermDecay`) give `FlatForceDecay` through the compiled reduction `flatForceDecay_of`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

theorem flatForceDecay : FlatForceDecay :=
  flatForceDecay_of flatBmatCont flatTermDecay

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
