import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_A
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_B
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_D

/-!
# `PartIII-b:C/rep/5/1/1/1/3`: `FreeWeakUniqueness` for all admissible parameters

Immediate from `freeWeakUniqueness_of` (source 2666-2700, 1580-1583) with the four sub-lemmas
`fwuSub` (`D2_1_A`), `fwuLiftYr` (`D2_1_B`), `fwuHomog` (`D2_1_C`), `fwuLiftInj` (`D2_1_D`).
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb

open UnforcedLeray.Short.PartIIIb.Concrete

theorem freeWeakUniquenessAll : ∀ (c γ ν ε μ : ℝ), 0 < c → 0 < ν → 0 < ε → 2 * ε * c ≤ 1 →
    0 < μ + 1 / 4 → FreeWeakUniqueness c γ ν ε μ := by
  intro c γ ν ε μ hc hν hε hP hμ
  exact freeWeakUniqueness_of hc hν hε hP hμ (fwuSub hc hν hε) (fwuLiftYr hc hν hε) fwuHomog
    (fwuLiftInj hc hν hε)

end UnforcedLeray.Short.PartIIIb
