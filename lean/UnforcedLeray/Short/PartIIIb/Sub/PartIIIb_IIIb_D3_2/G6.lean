import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D3_2.G6Org
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D3_2.G6.ClassAmp
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D3_2.G6.Scalar
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D3_2.G6.Bclass
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D3_2.G6.Congr
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D3_2.G6.ActualSeq
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D3_2.G5.NearUnit

/-!
# `PartIII-b:IIIb-D3/2/G6`: Assembly of `FlatUnif.FlatScalarChain`

Assembles `FlatUnif.FlatScalarChain` from `FlatUnif.G6.flatScalarChain_of` and the six
leaf theorems.
-/

set_option autoImplicit false

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem flatScalarChain : FlatUnif.FlatScalarChain :=
  FlatUnif.G6.flatScalarChain_of
    FlatUnif.G6.classAmpWindow
    FlatUnif.G6.scalarWindow
    FlatUnif.G6.bmatBclass
    FlatUnif.G6.ellMuAtCongr
    FlatUnif.G6.actualSeqPinned
    FlatUnif.G5.flatNearUnit

end UnforcedLeray.Short.PartIIIb.Concrete
