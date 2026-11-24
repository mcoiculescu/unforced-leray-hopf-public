import UnforcedLeray.Units.B0151.Linf
import UnforcedLeray.Lib.Cylinder.Basic

/-!
# Periodic cylinder-cell bridge for the scalar B0151 estimates

The scalar B0151 embedding uses the unnormalized cell `(0,c] × ℝ`, while the train Sobolev
spaces use the centered cell `[-c/2,c/2) × ℝ`. Periodicity identifies their `L²` norms.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace UnforcedLeray.TrainB

open UnforcedLeray.GaussianVortex (Plane)

/-- Product Fubini for a set restricted in the first coordinate. -/
private theorem setLIntegral_prod_univ_bridge {α β : Type*} [MeasurableSpace α]
    [MeasurableSpace β] {μ : Measure α} {ν : Measure β} [SFinite μ] [SFinite ν]
    (s : Set α) {H : α × β → ℝ≥0∞} (hH : Measurable H) :
    ∫⁻ p in s ×ˢ (Set.univ : Set β), H p ∂(μ.prod ν) =
      ∫⁻ a in s, ∫⁻ b, H (a, b) ∂ν ∂μ := by
  rw [← Measure.prod_restrict, Measure.restrict_univ, lintegral_prod _ hH.aemeasurable]

/-- Split a product strip integral into its two one-dimensional integrals. -/
private theorem strip_integral_prod (c : ℝ) {g : Plane → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ z in Set.Ico 0 c ×ˢ (Set.univ : Set ℝ), g z ∂(volume : Measure Plane) =
      ∫⁻ q in Set.Ico 0 c, ∫⁻ η, g (q, η) := by
  rw [Measure.volume_eq_prod ℝ ℝ, setLIntegral_prod_univ_bridge _ hg]

/-- The centered cell product integral also splits into its two one-dimensional integrals. -/
private theorem centered_cell_integral_prod {c : ℝ} {g : Plane → ℝ≥0∞}
    (hg : Measurable g) :
    ∫⁻ z, g z ∂UnforcedLeray.Cyl.cellμ c =
      ∫⁻ q in Set.Ico (-c / 2) (c / 2), ∫⁻ η, g (q, η) := by
  rw [UnforcedLeray.Cyl.cellμ_eq_prod]
  exact lintegral_prod _ hg.aemeasurable

/-- The centered cell set integral also splits into its two one-dimensional integrals. -/
private theorem centered_set_integral_prod {c : ℝ} {g : Plane → ℝ≥0∞}
    (hg : Measurable g) :
    ∫⁻ z in UnforcedLeray.Cyl.cell c, g z =
      ∫⁻ q in Set.Ico (-c / 2) (c / 2), ∫⁻ η, g (q, η) := by
  rw [UnforcedLeray.Cyl.cell, Measure.volume_eq_prod ℝ ℝ,
    setLIntegral_prod_univ_bridge _ hg]

/-- B0151's `(0,c]` cell measure is the restriction to `[0,c) × ℝ`; the endpoint convention
changes only a null set. -/
theorem b0151_cellMeasure_eq_zeroStrip (c : ℝ) :
    UnforcedLeray.B0151.cellMeasure c =
      volume.restrict (Set.Ico 0 c ×ˢ (Set.univ : Set ℝ)) := by
  rw [UnforcedLeray.B0151.cellMeasure_eq_prod, Measure.volume_eq_prod,
    ← Measure.prod_restrict, Measure.restrict_univ]
  rw [Measure.restrict_congr_set (Ico_ae_eq_Ioc (μ := (volume : Measure ℝ))).symm]

/-- Any nonnegative periodic density has the same integral on the B0151 and centered train cells.
This is unnormalized Lebesgue measure on both sides. -/
theorem lintegral_b0151_cell_eq_cyl_cell {c : ℝ} (hc : 0 < c)
    {g : Plane → ℝ≥0∞} (hg : Measurable g)
    (hper : UnforcedLeray.Cyl.IsPeriodic c g) :
    ∫⁻ z, g z ∂UnforcedLeray.B0151.cellMeasure c =
      ∫⁻ z, g z ∂UnforcedLeray.Cyl.cellμ c := by
  have hB := UnforcedLeray.B0151.lintegral_cell c hg
  have hIoc : (∫⁻ q in Set.Ioc 0 c, ∫⁻ η, g (q, η)) =
      ∫⁻ q in Set.Ico 0 c, ∫⁻ η, g (q, η) := by
    exact setLIntegral_congr (Ico_ae_eq_Ioc (μ := (volume : Measure ℝ))).symm
  have hstrip := UnforcedLeray.Cyl.lintegral_strip_eq_cell hc hper 0
  have hstrip0 :
      (∫⁻ z in Set.Ico 0 c ×ˢ (Set.univ : Set ℝ), g z) =
        ∫⁻ z in UnforcedLeray.Cyl.cell c, g z := by
    simpa only [zero_add] using hstrip
  have hstrip' :
      (∫⁻ q in Set.Ico 0 c, ∫⁻ η, g (q, η)) =
        ∫⁻ q in Set.Ico (-c / 2) (c / 2), ∫⁻ η, g (q, η) := by
    rw [strip_integral_prod c hg, centered_set_integral_prod hg] at hstrip0
    exact hstrip0
  calc
    ∫⁻ z, g z ∂UnforcedLeray.B0151.cellMeasure c =
        ∫⁻ q in Set.Ioc 0 c, ∫⁻ η, g (q, η) := hB
    _ = ∫⁻ q in Set.Ico 0 c, ∫⁻ η, g (q, η) := hIoc
    _ = ∫⁻ q in Set.Ico (-c / 2) (c / 2), ∫⁻ η, g (q, η) := hstrip'
    _ = ∫⁻ z, g z ∂UnforcedLeray.Cyl.cellμ c := (centered_cell_integral_prod hg).symm

/-- The square of an `L²` norm is the integral of the squared ENNReal norm, for arbitrary
normed-valued fields. -/
private theorem lintegral_enorm_sq_eq_bridge {F : Type*} [NormedAddCommGroup F]
    [MeasurableSpace F] [BorelSpace F] [SecondCountableTopology F]
    {μ : Measure Plane} (f : Plane → F) :
    ∫⁻ z, ‖f z‖ₑ ^ 2 ∂μ = eLpNorm f 2 μ ^ 2 := by
  have h := eLpNorm_nnreal_pow_eq_lintegral (f := f) (μ := μ) (p := 2) (by norm_num)
  have e2 : ((2 : NNReal) : ℝ) = ((2 : ℕ) : ℝ) := by norm_num
  simp only [e2, ENNReal.rpow_natCast, ENNReal.coe_ofNat] at h
  exact h.symm

/-- The `L²` norm is identical on B0151's and the centered train cell for periodic fields,
including Euclidean vector fields. -/
theorem eLpNorm_sq_b0151_eq_cyl {F : Type*} [NormedAddCommGroup F]
    [MeasurableSpace F] [BorelSpace F] [SecondCountableTopology F]
    {c : ℝ} (hc : 0 < c) {f : Plane → F} (hfmeas : Measurable f)
    (hf : UnforcedLeray.Cyl.IsPeriodic c f) :
    eLpNorm f 2 (UnforcedLeray.B0151.cellMeasure c) =
      eLpNorm f 2 (UnforcedLeray.Cyl.cellμ c) := by
  have hper : UnforcedLeray.Cyl.IsPeriodic c (fun z => ‖f z‖ₑ ^ 2) := by
    intro z
    simp only [hf z]
  have hmeas : Measurable fun z => ‖f z‖ₑ ^ 2 := hfmeas.enorm.pow_const 2
  have hsq : (eLpNorm f 2 (UnforcedLeray.B0151.cellMeasure c)) ^ 2 =
      (eLpNorm f 2 (UnforcedLeray.Cyl.cellμ c)) ^ 2 := by
    rw [← lintegral_enorm_sq_eq_bridge, ← lintegral_enorm_sq_eq_bridge]
    exact lintegral_b0151_cell_eq_cyl_cell hc hmeas hper
  apply le_antisymm
  · exact (ENNReal.pow_le_pow_left_iff two_ne_zero).1 (le_of_eq hsq)
  · exact (ENNReal.pow_le_pow_left_iff two_ne_zero).1 (le_of_eq hsq.symm)

/-- Finite-L² membership transfers from the centered cell to B0151's unnormalized shifted cell. -/
theorem memLp_b0151_of_cell {F : Type*} [NormedAddCommGroup F]
    [MeasurableSpace F] [BorelSpace F] [SecondCountableTopology F]
    {c : ℝ} (hc : 0 < c) {f : Plane → F}
    (hfmeas : Measurable f) (hper : UnforcedLeray.Cyl.IsPeriodic c f)
    (hf : MemLp f 2 (UnforcedLeray.Cyl.cellμ c)) :
    MemLp f 2 (UnforcedLeray.B0151.cellMeasure c) := by
  refine ⟨hfmeas.aestronglyMeasurable, ?_⟩
  rw [eLpNorm_sq_b0151_eq_cyl hc hfmeas hper]
  exact lt_top_iff_ne_top.mpr hf.eLpNorm_ne_top

/-- Finite-L² membership transfers from B0151's shifted cell to the centered cell. -/
theorem memLp_cell_of_b0151 {F : Type*} [NormedAddCommGroup F]
    [MeasurableSpace F] [BorelSpace F] [SecondCountableTopology F]
    {c : ℝ} (hc : 0 < c) {f : Plane → F}
    (hfmeas : Measurable f) (hper : UnforcedLeray.Cyl.IsPeriodic c f)
    (hf : MemLp f 2 (UnforcedLeray.B0151.cellMeasure c)) :
    MemLp f 2 (UnforcedLeray.Cyl.cellμ c) := by
  refine ⟨hfmeas.aestronglyMeasurable, ?_⟩
  rw [← eLpNorm_sq_b0151_eq_cyl hc hfmeas hper]
  exact lt_top_iff_ne_top.mpr hf.eLpNorm_ne_top

end UnforcedLeray.TrainB

#print axioms UnforcedLeray.TrainB.lintegral_b0151_cell_eq_cyl_cell
#print axioms UnforcedLeray.TrainB.eLpNorm_sq_b0151_eq_cyl
