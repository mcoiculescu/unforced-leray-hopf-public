import UnforcedLeray.Analysis.ViscosityTransport.Defs
import UnforcedLeray.Analysis.DerivativeScaling

/-!
# Actual normalized fields and initial data

The velocity, gradient and second derivative fields below are the concrete
viscosity-one dilation. Their raw Lp, distributional derivative, divergence,
initial-value and strong-trace properties follow from change of variables.
No solution existence or normalized PDE property is presumed.
-/

noncomputable section
open Set MeasureTheory Filter
open scoped ENNReal Topology
open UnforcedLeray.SpatialScaling UnforcedLeray.DerivativeScaling
namespace UnforcedLeray.ViscosityTransport

/-- The manuscript's velocity normalization, without changing time. -/
def normalizedVelocity (h : ℝ) (u : Velocity) : Velocity :=
  scaleVelocity (h ^ (-1 / 2 : ℝ)) (Real.sqrt h) u

/-- The amplitude of the first derivative becomes one. -/
def normalizedGradient (h : ℝ) (G : FirstDerivatives) : FirstDerivatives :=
  fun t i => spatialScale 1 (Real.sqrt h) (G t i)

/-- The second derivative has the additional factor `sqrt h`. -/
def normalizedSecond (h : ℝ) (H : SecondDerivatives) : SecondDerivatives :=
  fun t i j => spatialScale (Real.sqrt h) (Real.sqrt h) (H t i j)

@[simp] theorem normalizedVelocity_apply (h : ℝ) (u : Velocity) (t : ℝ) :
    normalizedVelocity h u t = viscosityScale h (u t) := rfl

/-- Initial data retain the full compact, solenoidal, nonzero finite-energy class. -/
theorem isInitialDatum_viscosityScale {f : SpatialField} (hf : IsInitialDatum f)
    {h : ℝ} (hh : 0 < h) : IsInitialDatum (viscosityScale h f) := by
  constructor
  · exact memLp_viscosityScale hf.memLp hh
  · exact hasCompactSupport_viscosityScale hf.compact hh
  · exact isSolenoidal_viscosityScale hf.solenoidal hh
  · rw [l2Norm_viscosityScale f hf.memLp hh]
    exact mul_pos (Real.rpow_pos_of_pos hh _) hf.nonzero

/-- Spatial scaling distributes over the actual pointwise field difference. -/
theorem spatialScale_sub (a b : ℝ) (f g : SpatialField) :
    spatialScale a b (f - g) = spatialScale a b f - spatialScale a b g := by
  funext x
  exact smul_sub a (f (b • x)) (g (b • x))

theorem viscosityScale_sub (h : ℝ) (f g : SpatialField) :
    viscosityScale h (f - g) = viscosityScale h f - viscosityScale h g :=
  spatialScale_sub _ _ f g

/-- Exact transport of the physical L² distance between two fields. -/
theorem l2Norm_viscosityScale_sub (f g : SpatialField)
    (hf : MemLp f 2 volume) (hg : MemLp g 2 volume) {h : ℝ} (hh : 0 < h) :
    l2Norm (viscosityScale h f - viscosityScale h g) =
      h ^ (-5 / 4 : ℝ) * l2Norm (f - g) := by
  rw [← viscosityScale_sub]
  exact l2Norm_viscosityScale (f - g) (hf.sub hg) hh

/-- Any Lp time slice retains its membership under normalization. -/
theorem memLp_normalizedVelocity {u : Velocity} {t : ℝ} {p : ℝ≥0∞}
    (hu : MemLp (u t) p volume) {h : ℝ} (hh : 0 < h) :
    MemLp (normalizedVelocity h u t) p volume :=
  memLp_viscosityScale hu hh

theorem memLp_normalizedGradient {G : FirstDerivatives} {t : ℝ} {i : Fin 3}
    {p : ℝ≥0∞} (hG : MemLp (G t i) p volume) {h : ℝ} (hh : 0 < h) :
    MemLp (normalizedGradient h G t i) p volume :=
  memLp_spatialScale hG _ (Real.sqrt_pos.mpr hh).ne'

theorem memLp_normalizedSecond {H : SecondDerivatives} {t : ℝ} {i j : Fin 3}
    {p : ℝ≥0∞} (hH : MemLp (H t i j) p volume) {h : ℝ} (hh : 0 < h) :
    MemLp (normalizedSecond h H t i j) p volume :=
  memLp_spatialScale hH _ (Real.sqrt_pos.mpr hh).ne'

/-- The normalized gradient is the actual weak derivative of the normalized velocity. -/
theorem weak_gradient_normalized {u : Velocity} {G : FirstDerivatives}
    {t : ℝ} {i : Fin 3} (hG : HasWeakSpatialDerivative i (u t) (G t i))
    {h : ℝ} (hh : 0 < h) :
    HasWeakSpatialDerivative i (normalizedVelocity h u t) (normalizedGradient h G t i) :=
  weak_derivative_viscosityScale hG hh

/-- The normalized second fields differentiate the normalized gradient. -/
theorem weak_second_normalized {G : FirstDerivatives} {H : SecondDerivatives}
    {t : ℝ} {i j : Fin 3} (hH : HasWeakSpatialDerivative j (G t i) (H t i j))
    {h : ℝ} (hh : 0 < h) :
    HasWeakSpatialDerivative j (normalizedGradient h G t i) (normalizedSecond h H t i j) := by
  simpa only [normalizedGradient, normalizedSecond, one_mul] using
    hasWeakSpatialDerivative_spatialScale hH 1 (Real.sqrt_pos.mpr hh).ne'

theorem solenoidal_normalizedVelocity {u : Velocity} {t : ℝ}
    (hu : IsSolenoidal (u t)) {h : ℝ} (hh : 0 < h) :
    IsSolenoidal (normalizedVelocity h u t) :=
  isSolenoidal_viscosityScale hu hh

/-- The initial-value equality is preserved as an equality of L² representatives. -/
theorem initial_value_normalized {u : Velocity} {u₀ : SpatialField}
    (hu : u 0 =ᵐ[volume] u₀) {h : ℝ} (hh : 0 < h) :
    normalizedVelocity h u 0 =ᵐ[volume] viscosityScale h u₀ :=
  ae_eq_spatialScale hu _ (Real.sqrt_pos.mpr hh).ne'

/-- Strong L² convergence is transported by the exact norm scaling factor. -/
theorem tendsto_l2Norm_viscosityScale_sub {ι : Type*} {l : Filter ι}
    {u : ι → SpatialField} {u₀ : SpatialField}
    (hu : ∀ᶠ t in l, MemLp (u t) 2 volume) (h₀ : MemLp u₀ 2 volume)
    (hlim : Tendsto (fun t => l2Norm (u t - u₀)) l (𝓝 0))
    {h : ℝ} (hh : 0 < h) :
    Tendsto (fun t => l2Norm (viscosityScale h (u t) - viscosityScale h u₀)) l (𝓝 0) := by
  have hmul := hlim.const_mul (h ^ (-5 / 4 : ℝ))
  simp only [mul_zero] at hmul
  apply hmul.congr'
  filter_upwards [hu] with t ht
  exact (l2Norm_viscosityScale_sub (u t) u₀ ht h₀ hh).symm

/-- The exact strong initial trace condition from the main statement transports. -/
theorem strong_initial_trace_normalized {T : ℝ} {u : Velocity} {u₀ : SpatialField}
    (hu : ∀ t ∈ Icc (0 : ℝ) T, MemLp (u t) 2 volume) (h₀ : MemLp u₀ 2 volume)
    (hlim : Tendsto (fun t => l2Norm (u t - u₀))
      (𝓝[Icc (0 : ℝ) T] 0) (𝓝 0)) {h : ℝ} (hh : 0 < h) :
    Tendsto (fun t => l2Norm (normalizedVelocity h u t - viscosityScale h u₀))
      (𝓝[Icc (0 : ℝ) T] 0) (𝓝 0) := by
  apply tendsto_l2Norm_viscosityScale_sub _ h₀ hlim hh
  filter_upwards [self_mem_nhdsWithin] with t ht
  exact hu t ht

end UnforcedLeray.ViscosityTransport
