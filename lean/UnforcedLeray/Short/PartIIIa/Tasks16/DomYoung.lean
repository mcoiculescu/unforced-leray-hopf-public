import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T16_2
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T16_2.KdLb
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T16_2.YoungDil
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T16_2.PhaseMink

set_option autoImplicit false

theorem sepDomYoung : UnforcedLeray.Short.IIIa.SepDomYoung :=
  UnforcedLeray.Short.IIIa.sepDomYoung_of UnforcedLeray.Short.IIIa.sepKdLb
    UnforcedLeray.Short.IIIa.sepYoungDil UnforcedLeray.Short.IIIa.sepPhaseMink
