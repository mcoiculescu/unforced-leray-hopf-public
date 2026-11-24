import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_9
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_9_3
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_9_3.S1
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_9_3.S3
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_9_3.S4

/-!
# `PartIII-b:C/ward/9/3`: the young `Y₂` bound of the stream transitions (assembly)

Source `the November 2 reference manuscript` 3687-3713, 4202-4216.

The three analytic inputs `WardYTransDomG`, `WardYTransMajChartG`, `WardYTransMeasG` are proved in
`Sub/PartIII-b_C_ward_9_3/S1.lean`, `S3.lean`, `S4.lean`; `wardYTransYoungL2_of` of
`Sub/PartIII-b_C_ward_9_3.lean` combines them into `WardYTransYoungL2`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- **Lemma 3** (source 3687-3713, 4202-4216): the young chart reading of `transField` is bounded
by `C‖g‖`, assembled from the domination, chart-majorant and measurability lemmas. -/
theorem wardYTransYoungL2_proved : WardYTransYoungL2 :=
  wardYTransYoungL2_of wardYTransDomG_proved wardYTransMajChartG_proved wardYTransMeasG_proved

end UnforcedLeray.Short.PartIIIb.Concrete
