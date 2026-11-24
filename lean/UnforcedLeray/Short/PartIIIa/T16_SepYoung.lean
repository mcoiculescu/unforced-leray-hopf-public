import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T16
import UnforcedLeray.Short.PartIIIa.Tasks16.Dominated
import UnforcedLeray.Short.PartIIIa.Tasks16.DomYoung
import UnforcedLeray.Short.PartIIIa.Tasks16.DomPointwise
import UnforcedLeray.Short.PartIIIa.T15_SepKernelBounds

/-!
# Part III-a, task `PartIII-a:T16`: `sep:young` and its pointwise form (SP 3631-3647)

Target (`SeparatedKernels.lean`): `SepYoung` and `SepYoungPointwise`. The conditional theorems
`sepYoung_of` and `sepYoungPointwise_of` (`Sub/PartIII-a_T16.lean`) are applied to the proved
domination statements `sepWDominated` (`Tasks16/Dominated.lean`), `sepDomYoung`
(`Tasks16/DomYoung.lean`), `sepDomPointwise` (`Tasks16/DomPointwise.lean`) and the
unconditional kernel bounds `sepKernelBounds` (`T15_SepKernelBounds.lean`).
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.IIIa

theorem sepYoung : UnforcedLeray.Short.IIIa.SepYoung :=
  sepYoung_of sepWDominated sepKernelBounds sepDomYoung

theorem sepYoungPointwise : UnforcedLeray.Short.IIIa.SepYoungPointwise :=
  sepYoungPointwise_of sepWDominated sepKernelBounds sepDomPointwise

end UnforcedLeray.Short.IIIa

end
