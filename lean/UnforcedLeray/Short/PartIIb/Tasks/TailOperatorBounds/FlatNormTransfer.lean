import UnforcedLeray.Short.PartIIb.Sub.PartIIb_G2_3
import UnforcedLeray.Short.PartIIb.Sub.ComparisonAndStrongDesign
import UnforcedLeray.Short.PartIIb.Tasks.BodyLift.Norm

/-!
# `PartII-b:G2/3/1`: norm transfer for the flat operator `K_0`

Source `the November 2 reference manuscript` lines 2436-2445.
Proves `IIb.FlatNormTransfer`: the indicator norm `hpIndNorm` is the real part of the `hNorm` of the
indicator of the periodic profile `toProf`, and `hNorm (toProf g) = ‖g‖ₑ` (`hNorm_toProf`).
-/

set_option autoImplicit false

open Set MeasureTheory Filter
open scoped ENNReal

theorem flatNormTransfer_proof : UnforcedLeray.Short.IIb.FlatNormTransfer := by
  intro c hc A _hA g
  constructor
  · unfold UnforcedLeray.Short.IIb.hpIndNorm UnforcedLeray.Short.IIb.hNorm
    have hae : A.indicator (UnforcedLeray.Short.IIb.toProf c g) =ᵐ[UnforcedLeray.Short.IIb.hMeas c UnforcedLeray.Short.IIb.bgp]
        A.indicator (fun x => UnforcedLeray.Short.IIb.liftM ((g : _ → UnforcedLeray.Axi.Merid) x)) := by
      filter_upwards [UnforcedLeray.Short.IIb.toProf_ae_eq hc g] with x hx
      by_cases hxA : x ∈ A
      · rw [Set.indicator_of_mem hxA, Set.indicator_of_mem hxA, hx]
      · rw [Set.indicator_of_notMem hxA, Set.indicator_of_notMem hxA]
    have hn : ∀ x, ‖A.indicator (fun x => UnforcedLeray.Short.IIb.liftM ((g : _ → UnforcedLeray.Axi.Merid) x)) x‖
        = ‖A.indicator (g : _ → UnforcedLeray.Axi.Merid) x‖ := by
      intro x
      by_cases hxA : x ∈ A
      · rw [Set.indicator_of_mem hxA, Set.indicator_of_mem hxA, UnforcedLeray.Short.IIb.liftM_norm]
      · rw [Set.indicator_of_notMem hxA, Set.indicator_of_notMem hxA, norm_zero, norm_zero]
    rw [eLpNorm_congr_ae hae, eLpNorm_congr_norm_ae (Filter.Eventually.of_forall hn)]
  · rw [UnforcedLeray.Short.IIb.hNorm_toProf hc g, ofReal_norm_eq_enorm]
