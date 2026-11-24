import UnforcedLeray.Short.PartIIb.Defs
import UnforcedLeray.Short.PartIIa.Sub.F03Rep
import UnforcedLeray.Units.B0411
import UnforcedLeray.Units.B0412

/-!


Source of record: `the November 2 reference manuscript`, lines 1341-1344
(`Y_r` norm is the phase-normalised `L^r` norm) and 1478-1480.

Let `p = q₀ = 11/4`. The normalisation `‖F‖ₑ^p = P⁻¹ ∫₀ᴾ ‖F(t)‖ₑ^p dt` (`B0411.enorm_rpow_Yq`)
and the slice identity `‖F(t)‖ₑ^p = ∫ ‖W'(t,y)‖ₑ^p dy` for a.e. `t` (from `IsRep.slice`,
`lintegral_enorm_rpow_Lp`) give `‖F‖ₑ^p = P⁻¹ ∫₀ᴾ ∫ ‖W'‖ₑ^p`. Taking the `1/p` power
gives `phaseLpNorm P bgp W' = ‖F‖ₑ`, and `toReal_enorm'` finishes.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

open UnforcedLeray.PhaseSpace UnforcedLeray.B0412

theorem yqOfFields_norm (P : ℝ) [Fact (0 < P)] (W' : ℝ × Space → CVec3) (F : Yq P q0E)
    (hF : UnforcedLeray.Short.PartIIa.Rep.IsRep F W') :
    ‖F‖ = (phaseLpNorm P bgp W').toReal := by
  have hp : q0E.toReal = bgp := by
    rw [B0412.q0E_toReal]
    norm_num [bgp]
  have hI : ∫⁻ t in Ioc (0:ℝ) P, ‖F (t : AddCircle P)‖ₑ ^ q0E.toReal
      = ∫⁻ t in Ioc (0:ℝ) P, ∫⁻ y : Space, ‖W' (t, y)‖ₑ ^ q0E.toReal := by
    refine lintegral_congr_ae ?_
    filter_upwards [ae_restrict_of_ae hF.slice] with t ht
    rw [← lintegral_enorm_rpow_Lp (F (t : AddCircle P)) q0E_ne_top]
    refine lintegral_congr_ae ?_
    filter_upwards [ht] with y hy
    rw [hy]
  have hmain : ‖F‖ₑ ^ q0E.toReal
      = ENNReal.ofReal P⁻¹ * ∫⁻ t in Ioc (0:ℝ) P, ∫⁻ y : Space, ‖W' (t, y)‖ₑ ^ q0E.toReal := by
    rw [B0411.enorm_rpow_Yq F q0E_ne_top, hI]
  have hne : q0E.toReal ≠ 0 := by
    rw [hp]
    norm_num [bgp]
  have key : phaseLpNorm P bgp W' = ‖F‖ₑ := by
    unfold phaseLpNorm
    rw [← hp, ← hmain, one_div]
    exact ENNReal.rpow_rpow_inv hne _
  rw [key, Lp.enorm_def, Lp.norm_def]

end UnforcedLeray.Short.IIb
