import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_8
import UnforcedLeray.Short.PartIIb.Bridge.Tasks.LerayPairSol

/-!
# The Leray projection is invisible to solenoidal tests (source 1358-1359)

Task `PartIII-b:C/ward/12/3/1/2/8/3`.  Source of record
`the November 2 reference manuscript`.

For a solenoidal phase test `Φ`, `⟪Φ, 𝐏F⟫ = ⟪Φ, F⟫`: slice by slice, `𝐏` is the complex
Leray projection of `L^{q₀}(ℝ³)`, which is self-adjoint against `L^{q₀'}` and fixes the
divergence-free slice `Φ(t,·)`.  This is the already compiled theorem
`UnforcedLeray.Short.IIb.lerayPairSol` (`PartII-b/Bridge/Tasks/LerayPairSol.lean`) at
`q = q₀ = 11/4`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- **Solenoidal tests do not see the Leray projection** (source 1358-1359). -/
theorem gELerayPairSol_proof : GELerayPairSol := by
  intro P _ F Φ hΦ
  exact UnforcedLeray.Short.IIb.lerayPairSol UnforcedLeray.B0412.q0E
    UnforcedLeray.B0412.one_lt_q0E UnforcedLeray.B0412.q0E_ne_top P F Φ hΦ

end UnforcedLeray.Short.PartIIIb.Concrete
