import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T12_7_3_1

/-!
# Part II-b, leaf `DeqhsConvPeriodic` (SP 1923-1927): measurability and everywhere periodicity of `convAbs`

Source of record: `the November 2 reference manuscript`, lines 1923-1927.
For each fixed `z` the map `w ↦ z - w` is measure preserving, so a.e. identities in `u` transfer to a.e.
identities in `w`. This gives `convAbs θ g z = convAbs θ g₀ z` for every `z`, with `g₀` a strongly
measurable representative, and the periodicity of `g` a.e. transfers to the periodicity of `convAbs`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

theorem deqhsConvPeriodic : UnforcedLeray.Short.IIb.DeqhsConvPeriodic := by
  intro c r g hc hr hg θ hθ
  obtain ⟨hper, hgm, -⟩ := hg
  -- (1) a strongly measurable representative `g₀`
  obtain ⟨g₀, hg₀m, hg₀⟩ : ∃ g₀ : ℝ × ℝ → CMerid, StronglyMeasurable g₀ ∧
      ∀ᵐ z : ℝ × ℝ, g₀ z = g z :=
    ⟨hgm.mk g, hgm.stronglyMeasurable_mk, hgm.ae_eq_mk.symm⟩
  have hg₀meas : Measurable g₀ := hg₀m.measurable
  have hKc : Continuous (flatHeatKernel θ) := by
    unfold flatHeatKernel
    fun_prop
  -- (2) `convAbs θ g` agrees with `convAbs θ g₀` at every point
  have hrep : ∀ z : ℝ × ℝ, convAbs θ g z = convAbs θ g₀ z := by
    intro z
    unfold convAbs
    refine lintegral_congr_ae ?_
    have hq := quasiMeasurePreserving_sub_left_of_right_invariant (volume : Measure (ℝ × ℝ)) z
    filter_upwards [hq.ae hg₀] with w hw
    simp only [hw]
  -- (3) measurability of `convAbs θ g₀`
  have hmeasF : Measurable (fun p : (ℝ × ℝ) × (ℝ × ℝ) =>
      ENNReal.ofReal (flatHeatKernel θ p.2) * ‖g₀ (p.1 - p.2)‖ₑ) :=
    (ENNReal.measurable_ofReal.comp (hKc.measurable.comp measurable_snd)).mul
      ((hg₀meas.comp (measurable_fst.sub measurable_snd)).enorm)
  have hmeas0 : Measurable (convAbs θ g₀) := by
    unfold convAbs
    exact hmeasF.lintegral_prod_right'
  have hmeas : Measurable (convAbs θ g) := by
    have hfun : convAbs θ g = convAbs θ g₀ := funext hrep
    rw [hfun]
    exact hmeas0
  refine ⟨hmeas, fun z => ?_⟩
  -- (4) periodicity: pull the a.e. periodicity of `g` back along `w ↦ z - w`
  unfold convAbs
  refine lintegral_congr_ae ?_
  have hq := quasiMeasurePreserving_sub_left_of_right_invariant (volume : Measure (ℝ × ℝ)) z
  filter_upwards [hq.ae hper] with w hw
  have e : (z.1 + c, z.2) - w = ((z - w).1 + c, (z - w).2) := by
    ext <;> simp <;> ring
  rw [e, hw]

end UnforcedLeray.Short.IIb
