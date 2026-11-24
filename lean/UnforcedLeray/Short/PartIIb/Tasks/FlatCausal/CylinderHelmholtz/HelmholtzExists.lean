import UnforcedLeray.Short.PartIIb.Sub.T12_1
import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.CylinderHelmholtz.HelmholtzUnique
import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.CylinderHelmholtz.PlanePeriodicLimit
import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.CylinderHelmholtz.CylOfPlaneProps
import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.CylinderHelmholtz.HelmholtzExists.Core

/-!
# Part II-b, task `PartII-b:T12/1/6` (`CylHelmholtzExists`): existence of the cylinder Helmholtz
decomposition with a `c`-uniform bound

Source of record: `the November 2 reference manuscript`, lines 1923-1926 and
1933-1935. The statement is the definition `CylHelmholtzExists` of `Sub/T12_1.lean`; the constant
is the one of `planePeriodicLimit`.

The proof is the `c`-uniform limit argument of `HelmholtzExists/Core.lean` (`cyl_exists_core`),
applied with the three leaves `cylHelmholtzUnique` (`HelmholtzUnique.lean`), `cylOfPlaneProps`
(`CylOfPlaneProps.lean`) and `planePeriodicLimit` (`PlanePeriodicLimit.lean`). The helper files in
`HelmholtzExists/` are: `Bounded` (periodic weights are bounded), `Pair` (the weighted pairing is
continuous in `L^r`), `Trunc` (the truncation `F_n` converges to `F` in `L^r`), `Diff`
(nice-case companion and the uniqueness step), `Weights` (test weights), `Core` (the limit).
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.IIb

theorem cylHelmholtzExists : UnforcedLeray.Short.IIb.CylHelmholtzExists := by
  intro r hr
  obtain ⟨C, hC, hPPL⟩ := planePeriodicLimit r hr
  refine ⟨C, hC, fun c hc F hF => ?_⟩
  exact cyl_exists_core cylHelmholtzUnique cylOfPlaneProps hr hC
    (fun c hc F hF hF2 => hPPL c hc F hF hF2) hc F hF

end UnforcedLeray.Short.IIb
