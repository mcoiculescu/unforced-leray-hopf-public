import UnforcedLeray.Short.PartIIIa.Defs

/-!
# Part III-a long assembly, L1: measurable representative with the same `xNorm`

Proves `UnforcedLeray.Short.IIIa.ae_representative_xNorm` (task PartIII-a:T21/long/1).
The representative is `hg.1.mk g` (`AEStronglyMeasurable.mk`); it agrees a.e. with `g` and the
`eLpNorm` is invariant under a.e. equality.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal

namespace UnforcedLeray.Short.IIIa

theorem ae_representative_xNorm (c m : ℝ) (g : ℝ × ℝ → ℂ) (hg : MemLp g 2 (UnforcedLeray.B0579.cellMeasure c m)) : ∃ h : ℝ × ℝ → ℂ, Measurable h ∧ g =ᵐ[UnforcedLeray.B0579.cellMeasure c m] h ∧ xNorm c m h = xNorm c m g := by
  refine ⟨hg.1.mk g, hg.1.stronglyMeasurable_mk.measurable, hg.1.ae_eq_mk, ?_⟩
  unfold xNorm
  exact (eLpNorm_congr_ae hg.1.ae_eq_mk).symm

end UnforcedLeray.Short.IIIa
