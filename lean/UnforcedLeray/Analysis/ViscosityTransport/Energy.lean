import UnforcedLeray.Analysis.ViscosityTransport.Fields

/-!
# Exact energy and dissipation factors under viscosity normalization

Squared velocity norms scale by h^(-5/2), and the actual sum of squared
weak-gradient norms scales by h^(-3/2). Thus an energy equality with viscosity
h yields exactly the viscosity-one equality, with the same time interval.
-/

noncomputable section
open Set MeasureTheory
open UnforcedLeray.SpatialScaling
namespace UnforcedLeray.ViscosityTransport

theorem sqrt_dilation_norm_factor_sq {h : ℝ} (hh : 0 < h) :
    ((Real.sqrt h) ^ (-3 / 2 : ℝ)) ^ (2 : ℕ) = h ^ (-3 / 2 : ℝ) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hh.le,
    ← Real.rpow_natCast _ 2, ← Real.rpow_mul hh.le]
  norm_num

/-- The concrete normalized gradient has the actual h^(-3/2) dissipation factor. -/
theorem dissipation_normalizedGradient (G : FirstDerivatives) (t : ℝ)
    (hG : ∀ i, MemLp (G t i) 2 volume) {h : ℝ} (hh : 0 < h) :
    dissipation (normalizedGradient h G) t = h ^ (-3 / 2 : ℝ) * dissipation G t := by
  have hi (i : Fin 3) : l2Norm (normalizedGradient h G t i) ^ 2 =
      h ^ (-3 / 2 : ℝ) * l2Norm (G t i) ^ 2 := by
    change l2Norm (spatialScale 1 (Real.sqrt h) (G t i)) ^ 2 = _
    rw [l2Norm_spatialScale _ (hG i) _ (Real.sqrt_pos.mpr hh), abs_one,
      one_mul, mul_pow, sqrt_dilation_norm_factor_sq hh]
  simp only [dissipation, hi, Finset.mul_sum]

/-- Exact integral of normalized dissipation on an arbitrary measurable time set. -/
theorem integral_dissipation_normalizedGradient (G : FirstDerivatives)
    {s : Set ℝ} (hs : MeasurableSet s) (hG : ∀ t ∈ s, ∀ i, MemLp (G t i) 2 volume)
    {h : ℝ} (hh : 0 < h) :
    (∫ t in s, dissipation (normalizedGradient h G) t) =
      h ^ (-3 / 2 : ℝ) * (∫ t in s, dissipation G t) := by
  calc
    _ = ∫ t in s, h ^ (-3 / 2 : ℝ) * dissipation G t :=
      setIntegral_congr_fun hs (fun t ht => dissipation_normalizedGradient G t (hG t ht) hh)
    _ = _ := integral_const_mul _ _

theorem integrable_dissipation_normalizedGradient (G : FirstDerivatives)
    {s : Set ℝ} (hs : MeasurableSet s) (hG : ∀ t ∈ s, ∀ i, MemLp (G t i) 2 volume)
    (hD : IntegrableOn (dissipation G) s) {h : ℝ} (hh : 0 < h) :
    IntegrableOn (dissipation (normalizedGradient h G)) s := by
  apply IntegrableOn.congr_fun (hD.const_mul (h ^ (-3 / 2 : ℝ))) ?_ hs
  intro t ht
  exact (dissipation_normalizedGradient G t (hG t ht) hh).symm

/-- Integrability of the actual H1 norm is preserved, using both supplied
finite-energy and finite-dissipation integrals. -/
theorem integrable_H1_normalized (u : Velocity) (G : FirstDerivatives)
    {s : Set ℝ} (hs : MeasurableSet s) (hu : ∀ t ∈ s, MemLp (u t) 2 volume)
    (hG : ∀ t ∈ s, ∀ i, MemLp (G t i) 2 volume)
    (hH1 : IntegrableOn (fun t => l2Norm (u t) ^ 2 + dissipation G t) s)
    (hD : IntegrableOn (dissipation G) s) {h : ℝ} (hh : 0 < h) :
    IntegrableOn (fun t => l2Norm (normalizedVelocity h u t) ^ 2 +
      dissipation (normalizedGradient h G) t) s := by
  have hu2 : IntegrableOn (fun t => l2Norm (u t) ^ 2) s := by
    have he : (fun t => l2Norm (u t) ^ 2 + dissipation G t) - dissipation G =
        (fun t => l2Norm (u t) ^ 2) := by
      funext t
      exact add_sub_cancel_right _ _
    rw [← he]
    exact hH1.sub hD
  have hi := (hu2.const_mul (h ^ (-5 / 2 : ℝ))).add
    (hD.const_mul (h ^ (-3 / 2 : ℝ)))
  apply IntegrableOn.congr_fun hi ?_ hs
  intro t ht
  change h ^ (-5 / 2 : ℝ) * l2Norm (u t) ^ 2 +
      h ^ (-3 / 2 : ℝ) * dissipation G t =
      l2Norm (viscosityScale h (u t)) ^ 2 + dissipation (normalizedGradient h G) t
  rw [l2Norm_viscosityScale_sq _ (hu t ht) hh,
    dissipation_normalizedGradient G t (hG t ht) hh]

theorem energy_dissipation_factor {h : ℝ} (hh : 0 < h) :
    h ^ (-5 / 2 : ℝ) * h = h ^ (-3 / 2 : ℝ) := by
  calc
    _ = h ^ (-5 / 2 : ℝ) * h ^ (1 : ℝ) := by rw [Real.rpow_one]
    _ = h ^ ((-5 / 2 : ℝ) + 1) := (Real.rpow_add hh _ _).symm
    _ = _ := by norm_num

/-- An actual viscosity-h energy identity becomes the viscosity-one identity. -/
theorem energy_equality_normalized (u : Velocity) (G : FirstDerivatives)
    (t₀ t₁ : ℝ) (hu₀ : MemLp (u t₀) 2 volume) (hu₁ : MemLp (u t₁) 2 volume)
    (hG : ∀ t ∈ Ioo t₀ t₁, ∀ i, MemLp (G t i) 2 volume)
    {h : ℝ} (hh : 0 < h)
    (he : (1 / 2 : ℝ) * l2Norm (u t₁) ^ 2 +
      h * (∫ t in Ioo t₀ t₁, dissipation G t) = (1 / 2 : ℝ) * l2Norm (u t₀) ^ 2) :
    (1 / 2 : ℝ) * l2Norm (normalizedVelocity h u t₁) ^ 2 +
      (∫ t in Ioo t₀ t₁, dissipation (normalizedGradient h G) t) =
      (1 / 2 : ℝ) * l2Norm (normalizedVelocity h u t₀) ^ 2 := by
  change (1 / 2 : ℝ) * l2Norm (viscosityScale h (u t₁)) ^ 2 + _ =
    (1 / 2 : ℝ) * l2Norm (viscosityScale h (u t₀)) ^ 2
  rw [l2Norm_viscosityScale_sq _ hu₁ hh, l2Norm_viscosityScale_sq _ hu₀ hh,
    integral_dissipation_normalizedGradient G measurableSet_Ioo hG hh,
    ← energy_dissipation_factor hh]
  linear_combination (h ^ (-5 / 2 : ℝ)) * he

end UnforcedLeray.ViscosityTransport
