import UnforcedLeray.Short.PartI.Sub.T07

/-!
# Part I, cylinder cells: transport between the library cell and the centred cell

Source of record: `the November 2 reference manuscript`, lines 355-374 (the cells of
the cylinder). The library cell `(0, c] × ℝ` of `Units/B0151` (`B0151.cellMeasure c`) and the centred
cell `[-c/2, c/2) × ℝ` of `Lib/Cylinder/Basic` (`Cyl.cellμ c`) carry the same integrals of
`c`-periodic functions (`CylCellBridge`), hence the same `L^p` norms and the same `MemLp` predicates
for measurable real-valued periodic functions.

Target: `cylCellBridge_proof : CylCellBridge`. Corollaries used by `T07`:
`eLpNorm_cellMeasure_eq` and `memLp_cellMeasure_iff`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal

namespace UnforcedLeray.Short.PartI

open UnforcedLeray

/-- The library cell `(0, c] × ℝ` and the half-open strip `[0, c) × ℝ` have the same measure: the
two intervals in the first factor differ by a Lebesgue-null set. -/
theorem cellMeasure_eq_restrict_Ico (c : ℝ) :
    B0151.cellMeasure c = volume.restrict (Ico 0 c ×ˢ (univ : Set ℝ)) := by
  have hset : Ioc 0 c =ᵐ[volume] Ico 0 c := Ioc_ae_eq_Icc.trans Ico_ae_eq_Icc.symm
  rw [B0151.cellMeasure_eq_prod, Measure.restrict_congr_set hset, Measure.volume_eq_prod,
    ← Measure.prod_restrict, Measure.restrict_univ]

/-- **Cell bridge** (source lines 355-374): integrals of nonnegative measurable `c`-periodic functions
over the library cell `(0, c]` and over the centred cell agree. -/
theorem cylCellBridge_proof : CylCellBridge := by
  intro c hc g _hg hper
  have h := Cyl.lintegral_strip_eq_cell hc hper 0
  rw [zero_add] at h
  rw [cellMeasure_eq_restrict_Ico c]
  exact h

/-- Measures of periodic measurable sets agree on the two cells. -/
theorem cellMeasure_apply_eq {c : ℝ} (hc : 0 < c) {S : Set Cyl.Plane} (hS : MeasurableSet S)
    (hSper : ∀ z : Cyl.Plane, (z.1 + c, z.2) ∈ S ↔ z ∈ S) :
    B0151.cellMeasure c S = Cyl.cellμ c S := by
  have hper : Cyl.IsPeriodic c (S.indicator (1 : Cyl.Plane → ℝ≥0∞)) := by
    intro z
    by_cases hz : z ∈ S
    · have hz' : (z.1 + c, z.2) ∈ S := (hSper z).2 hz
      simp [hz, hz']
    · have hz' : (z.1 + c, z.2) ∉ S := fun h => hz ((hSper z).1 h)
      simp [hz, hz']
  have hmeas : Measurable (S.indicator (1 : Cyl.Plane → ℝ≥0∞)) :=
    measurable_one.indicator hS
  have h := cylCellBridge_proof c hc (S.indicator (1 : Cyl.Plane → ℝ≥0∞)) hmeas hper
  rw [lintegral_indicator_one hS, lintegral_indicator_one hS] at h
  exact h

/-- **Essential supremum transfer**: for measurable real `c`-periodic `g`, the essential suprema of
`‖g‖ₑ` over the two cells agree. Each is `sInf {a | μ {x | a < ‖g x‖ₑ} = 0}`
(`essSup_eq_sInf`), and the sets `{x | a < ‖g x‖ₑ}` are measurable and periodic. -/
theorem eLpNormEssSup_cellMeasure_eq {c : ℝ} (hc : 0 < c) {g : Cyl.Plane → ℝ}
    (hg : Measurable g) (hper : Cyl.IsPeriodic c g) :
    eLpNormEssSup g (B0151.cellMeasure c) = eLpNormEssSup g (Cyl.cellμ c) := by
  unfold eLpNormEssSup
  rw [essSup_eq_sInf, essSup_eq_sInf]
  congr 1
  ext a
  simp only [Set.mem_ofPred_eq]
  have hnorm : Measurable (fun x : Cyl.Plane => ‖g x‖ₑ) := measurable_enorm.comp hg
  have hS : MeasurableSet {x : Cyl.Plane | a < ‖g x‖ₑ} :=
    measurableSet_lt measurable_const hnorm
  have hSper : ∀ z : Cyl.Plane, (z.1 + c, z.2) ∈ {x : Cyl.Plane | a < ‖g x‖ₑ} ↔
      z ∈ {x : Cyl.Plane | a < ‖g x‖ₑ} := by
    intro z
    simp only [Set.mem_ofPred_eq, hper z]
  rw [cellMeasure_apply_eq hc hS hSper]

/-- **eLpNorm transfer** (for `T07/1`, `T07/2`, `T07/7`): the `L^p` norm of a measurable real
`c`-periodic function is the same on the library cell and on the centred cell, for every exponent
`p ∈ [0, ∞]`. -/
theorem eLpNorm_cellMeasure_eq {c : ℝ} (hc : 0 < c) {g : Cyl.Plane → ℝ} (hg : Measurable g)
    (hper : Cyl.IsPeriodic c g) (p : ℝ≥0∞) :
    eLpNorm g p (B0151.cellMeasure c) = eLpNorm g p (Cyl.cellμ c) := by
  by_cases hp0 : p = 0
  · subst hp0
    rw [eLpNorm_exponent_zero, eLpNorm_exponent_zero]
  by_cases hpt : p = ⊤
  · subst hpt
    rw [eLpNorm_exponent_top, eLpNorm_exponent_top]
    exact eLpNormEssSup_cellMeasure_eq hc hg hper
  · rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hpt,
      eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hpt]
    congr 1
    have hmeas : Measurable (fun z : Cyl.Plane => ‖g z‖ₑ ^ p.toReal) :=
      (measurable_enorm.comp hg).pow_const _
    have hperE : Cyl.IsPeriodic c (fun z : Cyl.Plane => ‖g z‖ₑ ^ p.toReal) := by
      intro z
      simp only [hper z]
    exact cylCellBridge_proof c hc (fun z : Cyl.Plane => ‖g z‖ₑ ^ p.toReal) hmeas hperE

/-- **MemLp transfer**: membership in `L^p` of a measurable real `c`-periodic function is the same on
the library cell and on the centred cell. -/
theorem memLp_cellMeasure_iff {c : ℝ} (hc : 0 < c) {g : Cyl.Plane → ℝ} (hg : Measurable g)
    (hper : Cyl.IsPeriodic c g) (p : ℝ≥0∞) :
    MemLp g p (B0151.cellMeasure c) ↔ MemLp g p (Cyl.cellμ c) := by
  unfold MemLp
  rw [eLpNorm_cellMeasure_eq hc hg hper p]
  exact and_congr ⟨fun _ => hg.aestronglyMeasurable, fun _ => hg.aestronglyMeasurable⟩ Iff.rfl

end UnforcedLeray.Short.PartI
