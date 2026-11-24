import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_near_pins_3_4_2_3_2
import UnforcedLeray.Short.PartIIIb.NearInst.Link.Pins.Proofs.OuterGen.Transp.Deriv.OdScaledTest
import UnforcedLeray.Short.PartIIIb.NearInst.Link.Pins.Proofs.OuterGen.Transp.Deriv.OdRightDeriv0
import UnforcedLeray.Short.PartIIIb.NearInst.Link.Pins.Proofs.OuterGen.Transp.Deriv.OdTwoSided

/-!
# `OuterTransposeDeriv` (task `PartIII-b:C/near/pins/3/4/2/3/2/4/8`)

Assembly of the strong `t`-derivative of the transposed outer semigroup on a scaled test:
the scaled test `scaledFn p Φ` is a phase test (`odScaledTest`), its right derivative at `0`
is `outerGenT` (`odRightDeriv0`), and the two-sided derivative at `t > 0` follows from the
semigroup law, the norm bound and strong continuity (`odTwoSided`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology

namespace UnforcedLeray.Short.PartIIIb.NearInst

theorem outerTransposeDeriv : OuterTransposeDeriv := by
  intro p Φ hΦ Ψ Ψ' hΨ hΨ' t ht
  have : Fact (0 < p.period) := ⟨p.period_pos⟩
  have hψ : UnforcedLeray.PhaseSpace.IsPhaseTest p.period (scaledFn p Φ) := odScaledTest p Φ hΦ
  have hΨ0 : OuterRepFn p (scaledFn p Φ) Ψ := hΨ
  have hR := odRightDeriv0 p (scaledFn p Φ) hψ Ψ Ψ' hΨ0 hΨ'
  have hh : 0 ≤ p.ν * p.ε ^ 2 := mul_nonneg p.ν_pos.le (sq_nonneg _)
  exact odTwoSided p.period (p.ν * p.ε ^ 2) hh Ψ Ψ' hR t ht

end UnforcedLeray.Short.PartIIIb.NearInst
