import UnforcedLeray.Short.PartIIb.Sub.PartIIb_F8
import UnforcedLeray.Short.PartIIb.Tasks.LocalSmoothing.ParabolicH2Duhamel
import UnforcedLeray.Short.PartIIb.Tasks.LocalSmoothing.FlatKFromH2

/-!
# Part II-b, task `PartII-b:F8` — Local $H^1 \to H^2$ smoothing and convective interaction bound
(SP 2296–2312)

Assembles `UnforcedLeray.Short.IIb.LocalSmoothing` from `TailSourceAndGlobalEnergy`,
`cylinderParabolicH2Duhamel_proof`, and `flatKInteractionFromH2_proof` via
`UnforcedLeray.Short.IIb.localSmoothing_of`.
-/

theorem localSmoothing_of
    (hGE : UnforcedLeray.Short.IIb.TailSourceAndGlobalEnergy) :
    UnforcedLeray.Short.IIb.LocalSmoothing :=
  UnforcedLeray.Short.IIb.localSmoothing_of
    UnforcedLeray.Short.IIb.cylinderParabolicH2Duhamel_proof
    UnforcedLeray.Short.IIb.flatKInteractionFromH2_proof
    hGE
