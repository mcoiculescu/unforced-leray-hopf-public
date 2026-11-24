import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T12_7_3_1

/-!
# Part II-b, leaf `DeqhsAbsMeas` (SP 1923-1927): a.e. strong measurability of the Fubini integrand

Source of record: `the November 2 reference manuscript`, lines 1923-1927.
The map `p ↦ p.1 - p.2` is quasi measure preserving for `volume.prod volume`, so a.e. equal
replacements of `g` by a strongly measurable representative `g₀` pull back to a.e. equal functions.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

theorem deqhsAbsMeas : UnforcedLeray.Short.IIb.DeqhsAbsMeas := by
  intro c r g hc hr hg θ hθ ψ hψ
  -- (1) a strongly measurable representative `g₀` of `g`
  obtain ⟨g₀, hg₀m, hg₀⟩ : ∃ g₀ : ℝ × ℝ → CMerid, StronglyMeasurable g₀ ∧
      ∀ᵐ z : ℝ × ℝ, g₀ z = g z :=
    ⟨hg.2.1.mk g, hg.2.1.stronglyMeasurable_mk, hg.2.1.ae_eq_mk.symm⟩
  have hg₀meas : Measurable g₀ := hg₀m.measurable
  -- (2) the difference map is quasi measure preserving on the product
  have hφ : Measure.QuasiMeasurePreserving (fun p : (ℝ × ℝ) × (ℝ × ℝ) => p.1 - p.2)
      (volume.prod volume) volume :=
    Measure.quasiMeasurePreserving_fst.comp
      (measurePreserving_sub_prod (volume : Measure (ℝ × ℝ)) volume).quasiMeasurePreserving
  have hφm : Measurable (fun p : (ℝ × ℝ) × (ℝ × ℝ) => p.1 - p.2) :=
    measurable_fst.sub measurable_snd
  have hae : ∀ᵐ p : (ℝ × ℝ) × (ℝ × ℝ) ∂(volume.prod volume),
      g₀ (p.1 - p.2) = g (p.1 - p.2) := hφ.ae_eq_comp hg₀
  -- (3) measurability of the model integrand
  have hKc : Continuous (flatHeatKernel θ) := by
    unfold flatHeatKernel
    fun_prop
  have hFm : Measurable (fun p : (ℝ × ℝ) × (ℝ × ℝ) =>
      flatHeatKernel θ p.2 * ‖g₀ (p.1 - p.2)‖ * |ψ p.1|) :=
    ((hKc.measurable.comp measurable_snd).mul ((hg₀meas.comp hφm).norm)).mul
      (hψ.comp continuous_fst).abs.measurable
  refine ⟨hFm.aestronglyMeasurable.congr ?_, fun i => ?_⟩
  · filter_upwards [hae] with p hp
    simp only [hp]
  · -- coordinate version
    have hcoord : Measurable (fun p : (ℝ × ℝ) × (ℝ × ℝ) =>
        (flatHeatKernel θ p.2 : ℂ) * g₀ (p.1 - p.2) i * (ψ p.1 : ℂ)) := by
      have hi : Measurable (fun x : CMerid => x i) :=
        ((continuous_apply i).comp (PiLp.continuous_ofLp 2 (fun _ : Fin 2 => ℂ))).measurable
      have h1 : Measurable (fun p : (ℝ × ℝ) × (ℝ × ℝ) => g₀ (p.1 - p.2) i) :=
        hi.comp (hg₀meas.comp hφm)
      have h2 : Measurable (fun p : (ℝ × ℝ) × (ℝ × ℝ) => (flatHeatKernel θ p.2 : ℂ)) :=
        Complex.measurable_ofReal.comp (hKc.measurable.comp measurable_snd)
      have h3 : Measurable (fun p : (ℝ × ℝ) × (ℝ × ℝ) => (ψ p.1 : ℂ)) :=
        Complex.measurable_ofReal.comp (hψ.measurable.comp measurable_fst)
      exact (h2.mul h1).mul h3
    refine hcoord.aestronglyMeasurable.congr ?_
    filter_upwards [hae] with p hp
    simp only [hp]

end UnforcedLeray.Short.IIb
