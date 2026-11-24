import UnforcedLeray.Statement
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Function.LpSeminorm.SMul
import Mathlib.Tactic

/-!
# Actual spatial dilation on Euclidean R³

The spatial change of variables needed for `paper/main.tex`,
`eq:viscosity-one-transport`. These are measure, norm and support theorems
for actual fields, not assumptions about a transport operator. The
Navier--Stokes derivative and weak-equation transport is a separate step.
-/

noncomputable section
set_option maxHeartbeats 800000
open Set MeasureTheory
open scoped ENNReal NNReal
namespace UnforcedLeray.SpatialScaling

/-- Amplitude and spatial dilation, with time unchanged. -/
def spatialScale (a b : ℝ) (f : SpatialField) : SpatialField :=
  fun x => a • f (b • x)

/-- The Haar Jacobian, with the actual Euclidean dimension three. -/
theorem map_dilation {b : ℝ} (hb : b ≠ 0) :
    Measure.map (fun x : Space => b • x) volume =
      ENNReal.ofReal |(b ^ 3)⁻¹| • volume := by
  simpa [Space, finrank_euclideanSpace] using
    Measure.map_addHaar_smul (volume : Measure Space) hb

theorem dilation_measurableEmbedding {b : ℝ} (hb : b ≠ 0) :
    MeasurableEmbedding (fun x : Space => b • x) :=
  (Homeomorph.smulOfNeZero b hb).measurableEmbedding

/-- Dilation preserves actual Lp membership for every exponent. -/
theorem memLp_comp_dilation {f : SpatialField} {p : ℝ≥0∞}
    (hf : MemLp f p volume) {b : ℝ} (hb : b ≠ 0) :
    MemLp (fun x : Space => f (b • x)) p volume := by
  apply (dilation_measurableEmbedding hb).memLp_map_measure_iff.mp
  rw [map_dilation hb]
  exact hf.smul_measure ENNReal.ofReal_ne_top

theorem memLp_spatialScale {f : SpatialField} {p : ℝ≥0∞}
    (hf : MemLp f p volume) (a : ℝ) {b : ℝ} (hb : b ≠ 0) :
    MemLp (spatialScale a b f) p volume :=
  (memLp_comp_dilation hf hb).const_smul a

/-- Null-set equivalence is respected by the nonsingular change of variables. -/
theorem ae_eq_comp_dilation {f g : SpatialField} (h : f =ᵐ[volume] g)
    {b : ℝ} (hb : b ≠ 0) :
    (fun x : Space => f (b • x)) =ᵐ[volume] (fun x => g (b • x)) := by
  apply ((dilation_measurableEmbedding hb).ae_map_iff
    (μ := (volume : Measure Space)) (p := fun x => f x = g x)).mp
  rw [map_dilation hb]
  exact Measure.ae_smul_measure h _

theorem ae_eq_spatialScale {f g : SpatialField} (h : f =ᵐ[volume] g)
    (a : ℝ) {b : ℝ} (hb : b ≠ 0) :
    spatialScale a b f =ᵐ[volume] spatialScale a b g := by
  filter_upwards [ae_eq_comp_dilation h hb] with x hx
  exact congrArg (fun v : Space => a • v) hx

@[simp] theorem spatialScale_zero (a b : ℝ) : spatialScale a b (0 : SpatialField) = 0 := by
  ext x
  simp [spatialScale]

theorem spatialScale_inverse (a b : ℝ) (ha : a ≠ 0) (hb : b ≠ 0)
    (f : SpatialField) : spatialScale a⁻¹ b⁻¹ (spatialScale a b f) = f := by
  ext x
  simp only [spatialScale, smul_inv_smul₀ hb, inv_smul_smul₀ ha]

/-- Invertible spatial scaling cannot hide a nonzero field on a null set. -/
theorem ae_eq_spatialScale_iff (a b : ℝ) (ha : a ≠ 0) (hb : b ≠ 0)
    (f g : SpatialField) :
    spatialScale a b f =ᵐ[volume] spatialScale a b g ↔ f =ᵐ[volume] g := by
  constructor
  · intro h
    have hi := ae_eq_spatialScale h a⁻¹ (inv_ne_zero hb)
    simpa only [spatialScale_inverse a b ha hb] using hi
  · intro h
    exact ae_eq_spatialScale h a hb

theorem nonzero_ae_spatialScale_iff (a b : ℝ) (ha : a ≠ 0) (hb : b ≠ 0)
    (f : SpatialField) :
    ¬ spatialScale a b f =ᵐ[volume] 0 ↔ ¬ f =ᵐ[volume] 0 := by
  simpa only [spatialScale_zero] using
    not_congr (ae_eq_spatialScale_iff a b ha hb f 0)

/-- Compact support is preserved by a nonsingular spatial dilation. -/
theorem hasCompactSupport_spatialScale {f : SpatialField} (hf : HasCompactSupport f)
    (a : ℝ) {b : ℝ} (hb : b ≠ 0) : HasCompactSupport (spatialScale a b f) := by
  have hc : HasCompactSupport (fun x : Space => f (b • x)) :=
    hf.comp_homeomorph (Homeomorph.smulOfNeZero b hb)
  change HasCompactSupport ((fun _ : Space => a) • (fun x : Space => f (b • x)))
  exact hc.smul_left

/-- Exact squared-integral scaling. The L² hypothesis ensures this is an
identity of finite integrals, rather than a use of their totalized defaults. -/
theorem integral_norm_sq_spatialScale (f : SpatialField) (_hf : MemLp f 2 volume)
    (a : ℝ) {b : ℝ} (hb : 0 < b) :
    (∫ x : Space, ‖spatialScale a b f x‖ ^ 2) =
      a ^ 2 * (b ^ 3)⁻¹ * (∫ x : Space, ‖f x‖ ^ 2) := by
  simp_rw [spatialScale, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
  rw [integral_const_mul]
  rw [Measure.integral_comp_smul_of_nonneg (volume : Measure Space)
    (fun x : Space => ‖f x‖ ^ 2) b (hR := hb.le)]
  simp [Space, finrank_euclideanSpace, smul_eq_mul, mul_assoc]

/-- Exact extended L² seminorm change of variables, prior to taking real values. -/
theorem eLpNorm_spatialScale (f : SpatialField) (a : ℝ) {b : ℝ} (hb : b ≠ 0) :
    eLpNorm (spatialScale a b f) 2 volume =
      ‖a‖ₑ * ((ENNReal.ofReal |(b ^ 3)⁻¹|) ^ (1 / 2 : ℝ) * eLpNorm f 2 volume) := by
  change eLpNorm (a • (f ∘ (fun x : Space => b • x))) 2 volume = _
  rw [eLpNorm_const_smul, ← (dilation_measurableEmbedding hb).eLpNorm_map_measure,
    map_dilation hb, eLpNorm_smul_measure_of_ne_top (by norm_num)]
  norm_num [ENNReal.smul_def]

/-- Square-root Jacobian written in the manuscript's real-power notation. -/
theorem jacobian_half_power {b : ℝ} (hb : 0 < b) :
    |(b ^ 3)⁻¹| ^ (1 / 2 : ℝ) = b ^ (-3 / 2 : ℝ) := by
  have hp : |(b ^ 3)⁻¹| = b ^ (-3 : ℝ) := by
    norm_num [Real.rpow_neg hb.le,
      abs_of_nonneg (inv_nonneg.mpr (pow_nonneg hb.le 3))]
  rw [hp, ← Real.rpow_mul hb.le]
  norm_num

/-- Actual L² norm transport by a positive spatial dilation in three dimensions. -/
theorem l2Norm_spatialScale (f : SpatialField) (_hf : MemLp f 2 volume)
    (a : ℝ) {b : ℝ} (hb : 0 < b) :
    l2Norm (spatialScale a b f) = |a| * b ^ (-3 / 2 : ℝ) * l2Norm f := by
  unfold l2Norm
  rw [eLpNorm_spatialScale f a hb.ne', ENNReal.toReal_mul, ENNReal.toReal_mul,
    ← ENNReal.toReal_rpow, toReal_enorm, Real.norm_eq_abs,
    ENNReal.toReal_ofReal (abs_nonneg _), jacobian_half_power hb]
  ring

/-- Both the original and scaled energy integrals are finite for genuine L² fields. -/
theorem integrable_norm_sq_spatialScale {f : SpatialField} (hf : MemLp f 2 volume)
    (a : ℝ) {b : ℝ} (hb : b ≠ 0) :
    Integrable (fun x => ‖spatialScale a b f x‖ ^ 2) volume :=
  (memLp_spatialScale hf a hb).integrable_norm_pow (by norm_num)

/-- The manuscript's viscosity-one velocity/datum transform. -/
def viscosityScale (h : ℝ) (f : SpatialField) : SpatialField :=
  spatialScale (h ^ (-1 / 2 : ℝ)) (Real.sqrt h) f

/-- The exact `h^(-5/4)` factor in the finite-energy separation estimate. -/
theorem l2Norm_viscosityScale (f : SpatialField) (hf : MemLp f 2 volume)
    {h : ℝ} (hh : 0 < h) :
    l2Norm (viscosityScale h f) = h ^ (-5 / 4 : ℝ) * l2Norm f := by
  rw [viscosityScale, l2Norm_spatialScale f hf _ (Real.sqrt_pos.mpr hh),
    abs_of_pos (Real.rpow_pos_of_pos hh _), Real.sqrt_eq_rpow,
    ← Real.rpow_mul hh.le, ← Real.rpow_add hh]
  norm_num

/-- The actual squared L² norm acquires the manuscript's `h^(-5/2)` factor. -/
theorem l2Norm_viscosityScale_sq (f : SpatialField) (hf : MemLp f 2 volume)
    {h : ℝ} (hh : 0 < h) :
    l2Norm (viscosityScale h f) ^ 2 = h ^ (-5 / 2 : ℝ) * l2Norm f ^ 2 := by
  rw [l2Norm_viscosityScale f hf hh, mul_pow]
  have hp : (h ^ (-5 / 4 : ℝ)) ^ (2 : ℕ) = h ^ (-5 / 2 : ℝ) := by
    rw [← Real.rpow_natCast _ 2, ← Real.rpow_mul hh.le]
    norm_num
  rw [hp]

theorem memLp_viscosityScale {f : SpatialField} {p : ℝ≥0∞}
    (hf : MemLp f p volume) {h : ℝ} (hh : 0 < h) :
    MemLp (viscosityScale h f) p volume :=
  memLp_spatialScale hf _ (Real.sqrt_pos.mpr hh).ne'

theorem hasCompactSupport_viscosityScale {f : SpatialField} (hf : HasCompactSupport f)
    {h : ℝ} (hh : 0 < h) : HasCompactSupport (viscosityScale h f) :=
  hasCompactSupport_spatialScale hf _ (Real.sqrt_pos.mpr hh).ne'

theorem nonzero_ae_viscosityScale_iff (f : SpatialField) {h : ℝ} (hh : 0 < h) :
    ¬ viscosityScale h f =ᵐ[volume] 0 ↔ ¬ f =ᵐ[volume] 0 :=
  nonzero_ae_spatialScale_iff _ _ (Real.rpow_pos_of_pos hh _).ne'
    (Real.sqrt_pos.mpr hh).ne' f

end UnforcedLeray.SpatialScaling
