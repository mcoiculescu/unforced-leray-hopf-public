import UnforcedLeray.Short.PartIIa.Sub.PartIIa_N05_1
import UnforcedLeray.Short.PartIIa.Sub.PartIIa_N05_1_1.Final

/-!


Target: `theorem bodyEpsLocalH1 : BodyEpsLocalH1`
(`the November 2 reference manuscript`,
lines 1789–1793).

Decomposed in `UnforcedLeray.Short.«PartII-a».Sub.«PartII-a_N05_1»` via `bodyEpsLocalH1_of`
into the chart-pullback and cutoff-localisation leaf obligation:
- `PhaseD2CutoffSQE` (`PartII-a:N05/1/1`)
-/

set_option autoImplicit false

namespace UnforcedLeray.Short.PartIIa

/-- Conditional assembly of `BodyEpsLocalH1` from the leaf obligation `PhaseD2CutoffSQE` in
`Sub/PartII-a_N05_1.lean`. -/
theorem bodyEpsLocalH1_of_leaf (hPull : PhaseD2CutoffSQE) : BodyEpsLocalH1 :=
  bodyEpsLocalH1_of hPull

theorem bodyEpsLocalH1 : UnforcedLeray.Short.PartIIa.BodyEpsLocalH1 :=
  bodyEpsLocalH1_of phaseD2CutoffSQE

end UnforcedLeray.Short.PartIIa
