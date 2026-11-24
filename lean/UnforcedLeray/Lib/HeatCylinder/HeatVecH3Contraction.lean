import UnforcedLeray.Lib.HeatCylinder.HeatVecH3Smooth

/-!
# Period-independent derivative contraction for smooth ordinary cylinder heat

Each derivative uses the actual Euclidean-vector Gaussian Young inequality on the normalized
cell. The squared cell-transfer identity has the same period factor for input and output, so it
cancels exactly.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace UnforcedLeray.HeatCylinder

open UnforcedLeray.GaussianVortex (Plane)
open UnforcedLeray.Train (Vec)

private theorem isQPeriodic_iterD_vec {c : ℝ} {T : Plane → Vec}
    (hT : UnforcedLeray.Sob.IsCylSmooth c T) (vs : List Plane) :
    UnforcedLeray.B0284.IsQPeriodic c (UnforcedLeray.Sob.iterD vs T) := by
  intro z
  have hcoord : (z.1 + c, z.2) = z + (c, 0) := by ext <;> simp
  rw [hcoord]
  exact (hT.iterD vs).periodic z

/-- Centered-cell L² contraction for every ordered derivative field of actual vector heat. -/
theorem eLpNorm_heatVecH3Field_le {c θ : ℝ} (hc : 0 < c) (hθ : 0 < θ)
    {T : Plane → Vec} (hT : UnforcedLeray.Sob.IsCylSmooth c T)
    (α : UnforcedLeray.Sob.Idx 2 3) :
    eLpNorm (heatVecH3Field (c := c) (θ := θ) T α) 2 (UnforcedLeray.Cyl.cellμ c) ≤
      eLpNorm (UnforcedLeray.Sob.iterD
        ((UnforcedLeray.Sob.cylinder c).word α) T) 2 (UnforcedLeray.Cyl.cellμ c) := by
  let vs := (UnforcedLeray.Sob.cylinder c).word α
  let Tα := UnforcedLeray.Sob.iterD vs T
  have hTα : UnforcedLeray.Sob.IsCylSmooth c Tα := hT.iterD vs
  have hper : UnforcedLeray.B0284.IsQPeriodic c Tα := isQPeriodic_iterD_vec hT vs
  have hmeas : Measurable Tα := hTα.smooth.continuous.measurable
  have hmem : MemLp Tα 2 (UnforcedLeray.B0284.cellMeasure c) :=
    memLp_iterD_vec_cylSmooth_normalized hc hT vs
  have hcontract := eLpNorm_heatVecConvolution_le hc hθ hper
    hmeas.aestronglyMeasurable (by norm_num : (1 : ℝ≥0∞) ≤ 2) ENNReal.ofNat_ne_top
  have houtmeas : Measurable (heatVecConvolution θ Tα) := by
    exact (differentiable_heatVecConvolution_of_cylSmooth hc hθ hTα).continuous.measurable
  have houtper : UnforcedLeray.B0284.IsQPeriodic c (heatVecConvolution θ Tα) :=
    heatVecConvolution_periodic hc hθ hTα
  have houtSq := UnforcedLeray.HeatCylinder.eLpNorm_sq_cyl_eq_cellMeasure hc houtmeas houtper
  have hinSq := UnforcedLeray.HeatCylinder.eLpNorm_sq_cyl_eq_cellMeasure hc hmeas hper
  have hsquared :
      (eLpNorm (heatVecH3Field (c := c) (θ := θ) T α) 2
        (UnforcedLeray.Cyl.cellμ c)) ^ 2 ≤
      (eLpNorm Tα 2 (UnforcedLeray.Cyl.cellμ c)) ^ 2 := by
    change (eLpNorm (heatVecConvolution θ Tα) 2
        (UnforcedLeray.Cyl.cellμ c)) ^ 2 ≤ _
    rw [houtSq, hinSq]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left' hcontract 2)
      (by positivity)
  exact (ENNReal.pow_le_pow_left_iff (by norm_num : 2 ≠ 0)).1 hsquared

end UnforcedLeray.HeatCylinder

#print axioms UnforcedLeray.HeatCylinder.eLpNorm_heatVecH3Field_le
