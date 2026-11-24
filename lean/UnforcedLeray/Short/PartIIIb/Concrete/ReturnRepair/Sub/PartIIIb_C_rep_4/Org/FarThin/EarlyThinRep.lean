import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_4.Org.FarThin.EarlyThinRepOrg
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_4.Org.FarThin.ThinRepKernel.Kernel

/-!
# `PartIII-b:C/rep/4/1/org/5`: the early-source thin-to-repair entry

Source `the November 2 reference manuscript` 5303-5311, 5318-5319, 5323-5339.

`farEarlyThinRep`: `FarEarlyThinRep` (`Org/FarThinProps.lean`) from the ungained kernel leaf
`farThinRepKernel` (`Org/FarThin/ThinRepKernel/Kernel.lean`), via `farEarlyThinRep_of`
(`Org/FarThin/EarlyThinRepOrg.lean`).
-/

set_option autoImplicit false

noncomputable section

open UnforcedLeray.Blueprint.Planar (PlanarData)

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- **The early-source thin-to-repair entry** (source 5303-5311, 5318-5319, 5323-5339): the
`FarEarlyThinRep` bound from the ungained thin-to-repair far kernel. -/
theorem farEarlyThinRep (Pl : PlanarData) (σ₀ mZ dm dp : ℝ) : FarEarlyThinRep Pl σ₀ mZ dm dp :=
  farEarlyThinRep_of Pl σ₀ mZ dm dp (farThinRepKernel Pl σ₀ mZ dm dp)

end UnforcedLeray.Short.PartIIIb.Concrete
