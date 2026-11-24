import UnforcedLeray.Short.PartIIb.Sub.T07
import UnforcedLeray.Short.PartIIb.Tasks.NvCNorm.PhaseIntegral
import UnforcedLeray.Short.PartIIb.Tasks.NvCNorm.PeriodicRepresentative
import UnforcedLeray.Short.PartIIb.Tasks.NvCNorm.ChartNull

/-!
# Part II-b, task `PartII-b:T07`: the norm identity for the complex ring lift (unconditional)

Source of record: `the November 2 reference manuscript`, lines 1902-1906
("the lift `Mb = √s b` and the norm factor `(πR²)^{1/r}` cancel"), `‖N_v b‖_{Y_r} =
(πR²)^{1/r}‖b‖_{H_r}` for the complex lift `N_v b = N_v(Re b) + i N_v(Im b)`.


`hmeas : AEStronglyMeasurable b (hMeas c r)` is added next to `hper : QPeriodic c b`.

Proof: the conditional theorem `phaseLpNorm_NvC_of` (`Sub/T07.lean`) applied to the three
proved leaves `nvCPhaseIntegral` (T07/4), `periodicRepresentative` (T07/7) and
`chartNullPullback` (T07/8).
-/

set_option autoImplicit false

open Set MeasureTheory Filter Topology
open scoped ENNReal

namespace UnforcedLeray.Short.IIb

/-- **`PartII-b:T07`**: for `c, r, ε > 0` and a `c`-periodic, a.e.-strongly measurable profile
`b` of `H_r`, the `L^r` phase norm of the complex ring lift `N_v b` equals
`(π ε⁻² )^{1/r}` times `‖b‖_{H_r}`. -/
theorem phaseLpNorm_NvC {c r ε : ℝ} (hc : 0 < c) (hr : 0 < r) (hε : 0 < ε) (b : CProf)
    (hper : QPeriodic c b) (hmeas : AEStronglyMeasurable b (hMeas c r)) :
    phaseLpNorm (2 * ε * c) r (NvC ε⁻¹ b) =
      ENNReal.ofReal ((Real.pi * (ε⁻¹) ^ 2) ^ (1 / r)) * hNorm c r b :=
  phaseLpNorm_NvC_of nvCPhaseIntegral periodicRepresentative chartNullPullback hc hr hε b hper
    hmeas

end UnforcedLeray.Short.IIb
