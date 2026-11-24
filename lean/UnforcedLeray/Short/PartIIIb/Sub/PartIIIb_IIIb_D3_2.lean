import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D3_2.FlatUniform
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D3_2.G1
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D3_2.G2
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D3_2.G3
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D3_2.G4
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D3_2.G5
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D3_2.G6

/-!
# `PartIII-b:IIIb-D3/2`: Assembly of `FlatLimitKflatPart` (SP 4821–4916)

Assembles `FlatLimitKflatPart D G` from `flatLimitKflatPart_of_hyp`,
`FlatUnif.flatInputsHold_of`, the six group theorems `G1..G6`, and `flatScalarChain`.
-/

set_option autoImplicit false

namespace UnforcedLeray.Short.PartIIIb.Concrete

open Filter Set

theorem flatLimitKflatPart_of (D : SeqData) {dm dp : ℝ} (hst : D.RepairStanding dm dp)
    (hflat : ∀ᶠ n : ℕ in atTop, ∀ z ∈ Icc (-1 : ℝ) 1,
      NearInst.Kflat.IsFlatDuhamelColumn (D.flat n)
        (cOf_pos (retNu_pos D.Pl D.σ₀ n)) (D.train n) (D.mu n z) D.K.as D.K.χf)
    (G : ∀ n, AffSp D.K.as →L[ℝ] GrdG (cOf (retNu D.Pl D.σ₀ n))) :
    FlatLimitKflatPart D G :=
  flatLimitKflatPart_of_hyp D hst hflat G
    ⟨FlatUnif.flatInputsHold_of (flatGroupYoung D) (flatGroupGauss D)
      (flatGroupOld D) (flatGroupTested D), flatNewtonComparison D⟩
    flatScalarChain

end UnforcedLeray.Short.PartIIIb.Concrete
