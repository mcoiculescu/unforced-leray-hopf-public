import UnforcedLeray.Units.B0284
import UnforcedLeray.Units.B0151.Cell
import UnforcedLeray.Lib.Cylinder.Basic
import UnforcedLeray.Lib.TrainB.CellBridge

/-!
# Normalized and centered cylinder `L²` cells

The Gaussian heat-divergence estimate uses B0284's normalized `(0,c]` cell, while the train
Sobolev space uses the unnormalized centered cell. This module records their exact periodic
`L²` conversion.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace UnforcedLeray.HeatCylinder

open UnforcedLeray.GaussianVortex (Plane)

/-- For periodic fields, squared `L²` norms on B0284's normalized cell are `1/c` times the
squared norms on the centered, unnormalized train cell. -/
theorem eLpNorm_sq_cellMeasure_eq_cyl {F : Type*} [NormedAddCommGroup F]
    [MeasurableSpace F] [BorelSpace F] [SecondCountableTopology F]
    {c : ℝ} (hc : 0 < c) {f : Plane → F} (hfmeas : Measurable f)
    (hfper : UnforcedLeray.B0284.IsQPeriodic c f) :
    (eLpNorm f 2 (UnforcedLeray.B0284.cellMeasure c)) ^ 2 =
      (ENNReal.ofReal c)⁻¹ * (eLpNorm f 2 (UnforcedLeray.Cyl.cellμ c)) ^ 2 := by
  have hfperCyl : UnforcedLeray.Cyl.IsPeriodic c f := by
    intro z
    simpa [UnforcedLeray.B0284.IsQPeriodic, UnforcedLeray.Cyl.IsPeriodic] using hfper z
  have hcoe : (Real.toNNReal c : ℝ≥0∞) = ENNReal.ofReal c :=
    ENNReal.ofNNReal_toNNReal c
  let cNN : NNReal := Real.toNNReal c
  have hcNN : cNN ≠ 0 := (Real.toNNReal_pos.mpr hc).ne'
  have hscale : ((cNN⁻¹ : NNReal) : ℝ≥0∞) = (ENNReal.ofReal c)⁻¹ := by
    rw [ENNReal.coe_inv hcNN, show (cNN : ℝ≥0∞) = ENNReal.ofReal c from hcoe]
  have hmeasure : UnforcedLeray.B0284.cellMeasure c =
      (ENNReal.ofReal c)⁻¹ • UnforcedLeray.B0151.cellMeasure c := by
    rw [UnforcedLeray.B0284.cellMeasure, UnforcedLeray.B0284.cell,
      UnforcedLeray.B0151.cellMeasure]
    change ((cNN⁻¹ : NNReal) • volume.restrict _) = _
    rw [← Measure.coe_nnreal_smul, hscale]
  have hsq {μ : Measure Plane} :
      (eLpNorm f 2 μ) ^ 2 = ∫⁻ z, ‖f z‖ₑ ^ 2 ∂μ := by
    have h := eLpNorm_nnreal_pow_eq_lintegral (f := f) (μ := μ) (p := 2) (by norm_num)
    have e2 : ((2 : NNReal) : ℝ) = ((2 : ℕ) : ℝ) := by norm_num
    simp only [e2, ENNReal.rpow_natCast, ENNReal.coe_ofNat] at h
    exact h
  have hperSq : UnforcedLeray.Cyl.IsPeriodic c (fun z => ‖f z‖ₑ ^ 2) := by
    intro z
    simp [hfperCyl z]
  have hgmeas : Measurable (fun z => ‖f z‖ₑ ^ 2) := hfmeas.enorm.pow_const 2
  have hcell := UnforcedLeray.TrainB.lintegral_b0151_cell_eq_cyl_cell hc hgmeas hperSq
  rw [hsq, hsq, hmeasure, MeasureTheory.lintegral_smul_measure]
  rw [show ((ENNReal.ofReal c)⁻¹ : ℝ≥0∞) •
      ∫⁻ z, ‖f z‖ₑ ^ 2 ∂UnforcedLeray.B0151.cellMeasure c =
      (ENNReal.ofReal c)⁻¹ *
      ∫⁻ z, ‖f z‖ₑ ^ 2 ∂UnforcedLeray.B0151.cellMeasure c by rfl]
  rw [hcell]

/-- The equivalent squared-norm identity in the direction from normalized to centered cell. -/
theorem eLpNorm_sq_cyl_eq_cellMeasure {F : Type*} [NormedAddCommGroup F]
    [MeasurableSpace F] [BorelSpace F] [SecondCountableTopology F]
    {c : ℝ} (hc : 0 < c) {f : Plane → F} (hfmeas : Measurable f)
    (hfper : UnforcedLeray.B0284.IsQPeriodic c f) :
    (eLpNorm f 2 (UnforcedLeray.Cyl.cellμ c)) ^ 2 =
      ENNReal.ofReal c * (eLpNorm f 2 (UnforcedLeray.B0284.cellMeasure c)) ^ 2 := by
  have hsq := eLpNorm_sq_cellMeasure_eq_cyl hc hfmeas hfper
  have hcpos : 0 < ENNReal.ofReal c := ENNReal.ofReal_pos.mpr hc
  have hc0 : ENNReal.ofReal c ≠ 0 := hcpos.ne'
  have hcTop : ENNReal.ofReal c ≠ ⊤ := ENNReal.ofReal_ne_top
  rw [hsq]
  exact (ENNReal.mul_inv_cancel_left hc0 hcTop).symm

/-- Finite `L²` membership of a measurable periodic field transfers from the centered,
unnormalized train cell to B0284's normalized `(0,c]` cell. The squared norm conversion above
shows the period normalization preserves finiteness. -/
theorem memLp_cellMeasure_of_memLp_cyl {F : Type*} [NormedAddCommGroup F]
    [MeasurableSpace F] [BorelSpace F] [SecondCountableTopology F]
    {c : ℝ} (hc : 0 < c) {f : Plane → F} (hfmeas : Measurable f)
    (hfper : UnforcedLeray.B0284.IsQPeriodic c f)
    (hf : MemLp f 2 (UnforcedLeray.Cyl.cellμ c)) :
    MemLp f 2 (UnforcedLeray.B0284.cellMeasure c) := by
  refine ⟨hfmeas.aestronglyMeasurable.mono_ac
    (UnforcedLeray.B0284.cellMeasure_ac c), ?_⟩
  have hsq := eLpNorm_sq_cellMeasure_eq_cyl hc hfmeas hfper
  have hsqTop : (eLpNorm f 2 (UnforcedLeray.B0284.cellMeasure c)) ^ 2 < ⊤ := by
    rw [hsq]
    exact ENNReal.mul_lt_top
      (ENNReal.inv_lt_top.mpr (ENNReal.ofReal_pos.mpr hc))
      (ENNReal.pow_lt_top hf.eLpNorm_ne_top.lt_top)
  exact ((ENNReal.pow_lt_top_iff).mp hsqTop).resolve_right (by norm_num)

/-- Finite `L²` membership transfers back from normalized B0284 measure to the centered train
cell. This is the reverse direction needed when inserting actual heat outputs into the train's
unweighted Sobolev graph. -/
theorem memLp_cyl_of_memLp_cellMeasure {F : Type*} [NormedAddCommGroup F]
    [MeasurableSpace F] [BorelSpace F] [SecondCountableTopology F]
    {c : ℝ} (hc : 0 < c) {f : Plane → F} (hfmeas : Measurable f)
    (hfper : UnforcedLeray.B0284.IsQPeriodic c f)
    (hf : MemLp f 2 (UnforcedLeray.B0284.cellMeasure c)) :
    MemLp f 2 (UnforcedLeray.Cyl.cellμ c) := by
  refine ⟨hfmeas.aestronglyMeasurable.mono_ac Measure.absolutelyContinuous_restrict, ?_⟩
  have hsq := eLpNorm_sq_cellMeasure_eq_cyl hc hfmeas hfper
  have hcpos : 0 < ENNReal.ofReal c := ENNReal.ofReal_pos.mpr hc
  have hc0 : ENNReal.ofReal c ≠ 0 := hcpos.ne'
  have hcTop : ENNReal.ofReal c ≠ ⊤ := ENNReal.ofReal_ne_top
  have hcenterSq : (eLpNorm f 2 (UnforcedLeray.Cyl.cellμ c)) ^ 2 =
      ENNReal.ofReal c * (eLpNorm f 2 (UnforcedLeray.B0284.cellMeasure c)) ^ 2 := by
    rw [hsq]
    exact (ENNReal.mul_inv_cancel_left hc0 hcTop).symm
  have hcenterSqTop : (eLpNorm f 2 (UnforcedLeray.Cyl.cellμ c)) ^ 2 < ⊤ := by
    rw [hcenterSq]
    exact ENNReal.mul_lt_top hcTop.lt_top (ENNReal.pow_lt_top hf.eLpNorm_ne_top.lt_top)
  exact ((ENNReal.pow_lt_top_iff).mp hcenterSqTop).resolve_right (by norm_num)

end UnforcedLeray.HeatCylinder

#print axioms UnforcedLeray.HeatCylinder.eLpNorm_sq_cellMeasure_eq_cyl
#print axioms UnforcedLeray.HeatCylinder.eLpNorm_sq_cyl_eq_cellMeasure
#print axioms UnforcedLeray.HeatCylinder.memLp_cellMeasure_of_memLp_cyl
#print axioms UnforcedLeray.HeatCylinder.memLp_cyl_of_memLp_cellMeasure
