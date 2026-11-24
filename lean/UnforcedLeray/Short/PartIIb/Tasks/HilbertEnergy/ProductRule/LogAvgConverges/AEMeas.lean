import UnforcedLeray.Short.PartIIb.Sub.T15_2_10

/-!
# Part II-b, task `PartII-b:T15/2/10/2`: joint a.e.-measurability of the shear difference

Source: `the November 2 reference manuscript`, lines 1975-1979.
Proves `LogAcAEMeas` (`Sub/T15_2_10.lean`). The shear `(σ, x) ↦ (x.1 + σ, x.2)` from
`volume.prod (logMeas c)` to `logMeas c` is quasi-measure-preserving, by Tonelli and translation
invariance of `logMeas c` in the first coordinate.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal

namespace UnforcedLeray.Short.IIb

/-- The shear `(σ, x) ↦ (x.1 + σ, x.2)` is quasi-measure-preserving from
`volume.prod (logMeas c)` to `logMeas c`. -/
theorem logAcAEMeas_qmp (c : ℝ) :
    Measure.QuasiMeasurePreserving (fun p : ℝ × Coord => (p.2.1 + p.1, p.2.2))
      (volume.prod (logMeas c)) (logMeas c) := by
  refine ⟨?_, ?_⟩
  · exact (measurable_snd.fst.add measurable_fst).prodMk measurable_snd.snd
  · intro s hs0
    obtain ⟨t, hst, htm, ht0⟩ := exists_measurable_superset_of_null hs0
    apply measure_mono_null hst
    have hmeas : Measurable (fun p : ℝ × Coord => (p.2.1 + p.1, p.2.2)) :=
      (measurable_snd.fst.add measurable_fst).prodMk measurable_snd.snd
    rw [Measure.map_apply hmeas htm, Measure.prod_apply (hmeas htm)]
    have hfib : ∀ σ : ℝ, logMeas c (Prod.mk σ ⁻¹' ((fun p : ℝ × Coord => (p.2.1 + p.1, p.2.2)) ⁻¹' t))
        = 0 := by
      intro σ
      have hpre : Prod.mk σ ⁻¹' ((fun p : ℝ × Coord => (p.2.1 + p.1, p.2.2)) ⁻¹' t)
          = (fun x : Coord => (x.1 + σ, x.2)) ⁻¹' t := rfl
      rw [hpre]
      exact ((logTC_measurePreserving c σ).measure_preimage htm.nullMeasurableSet).trans ht0
    simp only [hfib, lintegral_zero]

/-- **Leaf `PartII-b:T15/2/10/2`** (joint measurability). -/
theorem logAcAEMeas : UnforcedLeray.Short.IIb.LogAcAEMeas := by
  intro c G hG
  have hQ := logAcAEMeas_qmp c
  have h1 : AEStronglyMeasurable (fun p : ℝ × Coord => G (p.2.1 + p.1, p.2.2))
      (volume.prod (logMeas c)) :=
    hG.comp_quasiMeasurePreserving hQ
  have h2 : AEStronglyMeasurable (fun p : ℝ × Coord => G p.2) (volume.prod (logMeas c)) :=
    hG.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_snd
  exact ((h1.sub h2).enorm).pow_const 2

end UnforcedLeray.Short.IIb
