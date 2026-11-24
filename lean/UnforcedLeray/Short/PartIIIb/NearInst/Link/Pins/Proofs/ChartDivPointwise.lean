import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_near_pins_4_1
import UnforcedLeray.Short.PartIIIb.NearInst.Link.Pins.Proofs.ChartDivPointwise.PerReduceLeaf
import UnforcedLeray.Short.PartIIIb.NearInst.Link.Pins.Proofs.ChartDivPointwise.ChainLeaf
import UnforcedLeray.Short.PartIIIb.NearInst.Link.Pins.Proofs.ChartDivPointwise.CylDivLeaf
import UnforcedLeray.Short.PartIIIb.NearInst.Link.Pins.Proofs.ChartDivPointwise.CompSmoothLeaf
import UnforcedLeray.Short.PartIIIb.NearInst.Link.Pins.Proofs.ChartDivPointwise.DivEpsRealLeaf
import UnforcedLeray.Short.PartIIIb.NearInst.Link.Pins.Proofs.ChartDivPointwise.G0Periodic
import UnforcedLeray.Short.PartIIIb.NearInst.Link.Pins.Proofs.ChartDivPointwise.ScaleDeriv

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.NearInst

theorem chartDivPointwise : ChartDivPointwise :=
  chartDivPointwise_of perReduceLeaf chainLeaf cylDivLeaf compSmoothLeaf divEpsRealLeaf g0Periodic scaleDeriv

end UnforcedLeray.Short.PartIIIb.NearInst
