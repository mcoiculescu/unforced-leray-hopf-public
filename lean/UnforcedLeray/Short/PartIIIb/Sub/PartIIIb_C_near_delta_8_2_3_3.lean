import UnforcedLeray.Short.PartIIIb.NearInst.Delta.Sub.PartIIIb_C_near_delta_8_2_3
import UnforcedLeray.Short.PartIIIb.NearInst.Body.Proofs.SolenoidalConj
import UnforcedLeray.Short.PartIIIb.NearInst.Body.Proofs.T0Conj

/-!
# Decomposition of `flatStressReal` (item `PartIII-b:C/near/delta/8/2/3/3`)

Source `the November 2 reference manuscript`,
1675-1679 (stress maps are real, by density of real smooth tensor tests), 1655-1656 (`T_0 = R_0 P_0`
real).  `T0flat` commutes with conjugation (`Body.t0flat_conj`, proved from `solenoidalConj`,
`t0Conj`), so it preserves `IsRealH`; the generic density argument is `GenericStressReal`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory UnforcedLeray.Axi Set

namespace UnforcedLeray.Short.PartIIIb.NearInst.Delta

open UnforcedLeray.Short.PartIIa

/-- **Generic reality of stress maps** (source 1675-1679): if `T : H → H` preserves real fields,
every stress map `S'` of `T` (`IsStressMap c ε T S'`) maps real tensors to real fields.  Proof:
approximate a real `F` in `H_T` by smooth tensor tests (`Masked.tensorTestDense`), replace each
`M_n` by its componentwise real part (still a test, `‖F - Re M_n‖ ≤ ‖F - M_n‖` since `F` is a.e.
real), `s div_ε (Re M_n)` is real (`Masked.smul_divEps_im`), `S'(Re M_n) = T(s div_ε Re M_n)` is
real, `IsRealH` is closed and `S'` is continuous.  Mirrors `PartIII-b:C/near/masked/8`. -/
def GenericStressReal : Prop :=
  ∀ (c ε : ℝ), 0 < c →
    ∀ T : UnforcedLeray.B0220.HSpace c UnforcedLeray.B0223.MeridC →L[ℂ]
        UnforcedLeray.B0220.HSpace c UnforcedLeray.B0223.MeridC,
      (∀ g, Masked.IsRealH c g → Masked.IsRealH c (T g)) →
      ∀ S' : HTSpace c →L[ℂ] UnforcedLeray.B0220.HSpace c UnforcedLeray.B0223.MeridC,
        IsStressMap c ε T S' → Masked.IsRealStress c S'

/-- `FlatStressReal` from the generic reality of stress maps. -/
theorem flatStressReal_of (hG : GenericStressReal) : FlatStressReal := by
  intro ν c hc _ μ hμ S' hS
  refine hG c 0 hc _ ?_ S' hS
  intro g hg
  rw [Body.isRealH_iff] at hg ⊢
  have hμ' : 0 < μ + 1 / 4 := by linarith
  rw [← Body.t0flat_conj Body.solenoidalConj Body.t0Conj hc ν hμ' g, hg]

end UnforcedLeray.Short.PartIIIb.NearInst.Delta
