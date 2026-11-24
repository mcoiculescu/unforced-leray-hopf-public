import UnforcedLeray.Short.PartIIIa.T18_FreeCausal.EnergyBound.WeightedEnergy.FlatWeakFromDensity.Limit

/-!
# Part III-a, task `PartIII-a:T18/3/1/2`: the tested equation extends to `H¹` test fields

Target: `FlatWeakFromDensity` (`Sub/T18_3_1.lean`), i.e. the density hypothesis `DivFreeCutoffDensity`
implies `FlatWeakAll`. Source of record: `the November 2 reference manuscript`,
lines 3541-3552 and 3427-3440.

The proof is the composition of the helper steps:

* `ErrorZero` (with `Spatial`, `Pointwise`, `ErrorInt`, `Basic`): the extended identity
  `spatial_extWeak` for every spatial flat test `φₖ`;
* `LimitLinear`, `LimitBound`, `LimitTendsto`: the linear form of the extended integrand, the
  pointwise `L²` bound on the time-space box, and the integrated defect bound;
* `Limit`: `extWeak_limit`, the limit `k → ∞` of the approximating tests, with the defect given
  by `DivFreeCutoffDensity`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology UnforcedLeray.Axi UnforcedLeray.Blueprint.Planar
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

/-- **`PartIII-a:T18/3/1/2`**: the density hypothesis `DivFreeCutoffDensity` implies that the tested
equation extends to all `H¹` divergence-free test fields (`FlatWeakAll`). -/
theorem flatWeakFromDensity : FlatWeakFromDensity := by
  intro hD c ν μ F b G hdat ψ hψ hψc hts φ hφ
  obtain ⟨φk, hk, hT⟩ := hD c hdat.pos_c φ hφ
  exact extWeak_limit hdat hψ hψc hts hφ hk hT

end UnforcedLeray.Short.IIIa
