import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_13_8_2_2_2
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_13_8_2_2_2.A
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_13_8_2_2_2.B
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_13_8_2_2_2.C

/-!
# `PartIII-b:C/ward/13/8/2/2/2/L2`: the unit annular Poincare inequality

Source `the November 2 reference manuscript`
117-118, 2641-2642. Assembles the decomposition `unitAnnularPoincare_of` with the chain lemma
`abstractChain` (file A), the cone Poincare inequalities `conePieces` (file B) and the cone geometry
`coneGeometry` (file C).
-/

set_option autoImplicit false

noncomputable section

theorem unitAnnularPoincare : UnforcedLeray.Short.PartIIIb.Concrete.AnnPoinSub.UnitAnnularPoincare :=
  UnforcedLeray.Short.PartIIIb.Concrete.AnnPoinSub.Chain.unitAnnularPoincare_of
    UnforcedLeray.Short.PartIIIb.Concrete.AnnPoinSub.Chain.abstractChain
    UnforcedLeray.Short.PartIIIb.Concrete.AnnPoinSub.Chain.conePieces
    UnforcedLeray.Short.PartIIIb.Concrete.AnnPoinSub.Chain.coneGeometry
