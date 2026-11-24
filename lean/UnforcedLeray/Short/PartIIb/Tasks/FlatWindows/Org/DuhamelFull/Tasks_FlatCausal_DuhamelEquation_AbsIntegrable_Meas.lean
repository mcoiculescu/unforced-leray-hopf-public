import UnforcedLeray.Short.PartIIb.Tasks.FlatWindows.Org.DuhamelFull.Defs
import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.DuhamelEquation.AbsIntegrable.Meas
import UnforcedLeray.Short.PartIIb.Tasks.FlatWindows.Org.DuhamelFull.Tasks_FlatCausal_DuhamelEquation_AbsIntegrable_Meas_Core
import UnforcedLeray.Short.PartIIb.Tasks.FlatWindows.Org.DuhamelFull.Tasks_FlatCausal_DuhamelEquation_AbsIntegrable_Reduction

/-!
# Part II-b, task `PartII-b:T12/7/7/1` (`dfe_deqAbsMeas`): measurability of the DeqAbs integrand

Source of record: `the November 2 reference manuscript`, lines 1923-1927.

Replace `G` by a strongly measurable, `c`-periodic-in-`q` representative `G'` agreeing with `G`
a.e. on `{s > 0}` (`exists_periodic_rep`), then the integrand of `G'` is measurable
(`dfe_deqam_integrand_measurable`) and equals that of `G` a.e. (`deqam_ae_eq`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

/-- **Leaf (measurability).** The `dfe_DeqAbsIntegrable` integrand is a.e. strongly measurable. -/
theorem dfe_deqAbsMeas : dfe_DeqAbsMeas := by
  intro r hr1 hr3 μ hμ ν c hν hc G hG Ψ hΨ
  obtain ⟨G', hG's, hGG'⟩ :=
    exists_periodic_rep (a := r / 2 - 5 / 2) hc hG.periodic hG.meas
  exact (dfe_deqam_integrand_measurable ν μ Ψ hΨ hG's).aestronglyMeasurable.congr
    (deqam_ae_eq ν μ Ψ hGG').symm

end UnforcedLeray.Short.IIb
