import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_4_2_4_2_1.FlatLerayDefs

/-!
# `CoefSmoothBand` (organize task `PartIII-b:C/flatset/col/7/1/1/2/4/2/4/2/1/1/9`)

Source of record `the November 2 reference manuscript`
lines 1713-1716 and 1738: the `q`-Fourier coefficients of the oscillating part `f - f̄` are smooth
and supported in one common `(s, η)`-band.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst.FlatLeray

open UnforcedLeray.B0220 UnforcedLeray.B0223 UnforcedLeray.Short.PartIIa

theorem coefSmoothBand : CoefSmoothBand := by
  intro c hc f hf
  have hO : IsMeridTest c (fOsc c f) := (fOsc_isMeridTest hc hf).2.1
  obtain ⟨s0, s1, L, hs0, hb⟩ := hO.band
  refine ⟨s0, s1, L, hs0, fun n => ?_⟩
  have hsm : ContDiff ℝ ∞ (nzCoeff c n (fOsc c f)) :=
    nztt_coeff_smooth intervalParamSmooth_proof c n (fOsc c f) hO.smooth
  -- the coefficient vanishes outside the common band
  have hz : ∀ x : ℝ × ℝ, ¬ (x.1 ∈ Icc s0 s1 ∧ |x.2| ≤ L) → nzCoeff c n (fOsc c f) x = 0 :=
    fun x hx => nztt_coeff_zero c n (fOsc c f) s0 s1 L hb x hx
  have bandOf : ∀ j : Fin 2, NzBandJ s0 s1 L (fun x => nzCoeff c n (fOsc c f) x j) := by
    intro j x hx
    by_contra hb'
    exact hx (by simp [hz x hb'])
  refine ⟨?_, ?_, bandOf 0, bandOf 1⟩
  · exact ((contDiff_piLp 2).1 hsm) 0
  · exact ((contDiff_piLp 2).1 hsm) 1

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst.FlatLeray
