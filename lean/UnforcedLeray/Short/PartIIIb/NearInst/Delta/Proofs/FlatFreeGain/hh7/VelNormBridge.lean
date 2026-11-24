import UnforcedLeray.Short.PartIIIb.NearInst.Delta.Proofs.FlatFreeGain.VelNormBridge

/-!
# Re-export of `FlatFreeGain/VelNormBridge.lean`

This module used to hold a verbatim copy of `FlatFreeGain/VelNormBridge.lean` (importing
`hh7/Props.lean` in place of `Sub/PartIII-b_C_near_delta_7.lean`, whose conditional
`flatFreeGainBound_of` clashes with the closed one in `FlatFreeGain.lean`).  The two copies could
not be imported together.  `FlatFreeGain/VelNormBridge.lean` now imports `hh7/Props.lean` itself, so this
file only re-exports it and every importer sees one set of declarations.
-/
