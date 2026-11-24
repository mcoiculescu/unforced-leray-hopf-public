import UnforcedLeray.Statement
import UnforcedLeray.Short.Spine.Proofs.Final

/-! Checked library for the unconditional formalization of `UnforcedLeray.MainClaim`. -/

set_option autoImplicit false

namespace UnforcedLeray

theorem main_theorem : UnforcedLeray.MainClaim :=
  UnforcedLeray.Short.Spine.mainClaim

end UnforcedLeray
