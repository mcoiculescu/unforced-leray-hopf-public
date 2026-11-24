import UnforcedLeray.Consequences
import UnforcedLeray.Separation
import UnforcedLeray.Analysis.ViscosityTransport.Solution

/-!
# Reduction of Theorem A to a positive-viscosity construction

`paper/main.tex` proves Theorem A by constructing two solutions with viscosity
`h > 0` and applying `eq:viscosity-one-transport`. This module proves that last
step for the full target: every clause of `MainClaim`, including the integrated
separation and the symmetry clause, follows from the positive-viscosity
construction with the manuscript's unnormalized constant `c`, transported to
`c* = h^(-5/4) c`. Nothing here constructs the positive-viscosity solutions.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter
open scoped ENNReal Topology
open UnforcedLeray.SpatialScaling UnforcedLeray.ViscosityTransport

namespace UnforcedLeray

/-- The squared L² distance of two target solutions is integrable in time. It is
continuous on the closed interval, by L² continuity of both solutions. -/
theorem integrableOn_sq_l2_dist {T : ℝ} {u₀ : SpatialField} {u₁ u₂ : Velocity}
    {p₁ p₂ : Pressure} {G₁ G₂ : FirstDerivatives} {H₁ H₂ : SecondDerivatives}
    (h₁ : IsTheoremASolution T u₀ u₁ p₁ G₁ H₁) (h₂ : IsTheoremASolution T u₀ u₂ p₂ G₂ H₂) :
    IntegrableOn (fun t => l2Norm (u₂ t - u₁ t) ^ 2) (Ioo (0 : ℝ) T) := by
  have hcont : ContinuousOn (fun t => ‖toL2 (u₂ t) - toL2 (u₁ t)‖ ^ 2) (Icc (0 : ℝ) T) :=
    ((h₂.continuousL2.sub h₁.continuousL2).norm).pow 2
  have hI : IntegrableOn (fun t => ‖toL2 (u₂ t) - toL2 (u₁ t)‖ ^ 2) (Icc (0 : ℝ) T) :=
    hcont.integrableOn_Icc
  refine (hI.mono_set Ioo_subset_Icc_self).congr_fun (fun t ht => ?_) measurableSet_Ioo
  have hm₁ := h₁.memL2 t (Ioo_subset_Icc_self ht)
  have hm₂ := h₂.memL2 t (Ioo_subset_Icc_self ht)
  simp only
  rw [← toL2_sub hm₂ hm₁, norm_toL2 (hm₂.sub hm₁)]

/-- Spatial dilation commutes with every linear isometry, so it preserves the
manuscript's symmetry class. -/
theorem isAxisymmetricNoSwirl_viscosityScale {f : SpatialField}
    (hf : IsAxisymmetricNoSwirl f) {h : ℝ} (hh : 0 < h) :
    IsAxisymmetricNoSwirl (viscosityScale h f) := by
  intro g hg
  have hb : Real.sqrt h ≠ 0 := (Real.sqrt_pos.mpr hh).ne'
  have hs := ae_eq_spatialScale (hf g hg) (h ^ (-1 / 2 : ℝ)) hb
  refine Filter.EventuallyEq.trans (Filter.Eventually.of_forall fun x => ?_) hs
  simp only [viscosityScale, spatialScale, LinearIsometryEquiv.map_smul]

/-- Theorem A at one positive viscosity, with the unnormalized separation constant.
This is the conclusion of the manuscript's localization theorem applied to the
background and mode of `prop:unstable-background`. -/
def ViscosityMainClaim : Prop :=
  ∃ (h T : ℝ) (u₀ : SpatialField) (u₁ u₂ : Velocity) (p₁ p₂ : Pressure)
      (G₁ G₂ : FirstDerivatives) (H₁ H₂ : SecondDerivatives) (c σ : ℝ),
    0 < h ∧ 0 < T ∧ IsInitialDatum u₀ ∧
    IsTheoremASolutionViscosity h T u₀ u₁ p₁ G₁ H₁ ∧
    IsTheoremASolutionViscosity h T u₀ u₂ p₂ G₂ H₂ ∧
    0 < c ∧ 0 < σ ∧ σ < 1 / 4 ∧
    (∀ t ∈ Ioc (0 : ℝ) T,
      c * Real.rpow t (σ + 1 / 4) ≤ l2Norm (u₂ t - u₁ t)) ∧
    IsAxisymmetricNoSwirl u₀ ∧
    (∀ t ∈ Icc (0 : ℝ) T, IsAxisymmetricNoSwirl (u₁ t)) ∧
    (∀ t ∈ Icc (0 : ℝ) T, IsAxisymmetricNoSwirl (u₂ t))

/-- The final step of the manuscript's proof of Theorem A. -/
theorem mainClaim_of_viscosityMainClaim (hV : ViscosityMainClaim) : MainClaim := by
  obtain ⟨h, T, u₀, u₁, u₂, p₁, p₂, G₁, G₂, H₁, H₂, c, σ, hh, hT, hd, s₁, s₂,
    hc, hσ, hσ', hsep, hsym₀, hsym₁, hsym₂⟩ := hV
  have n₁ := normalize_solution hh hT.le s₁
  have n₂ := normalize_solution hh hT.le s₂
  have hc' : 0 < h ^ (-5 / 4 : ℝ) * c := mul_pos (Real.rpow_pos_of_pos hh _) hc
  have hsep' : ∀ t ∈ Ioc (0 : ℝ) T, h ^ (-5 / 4 : ℝ) * c * Real.rpow t (σ + 1 / 4) ≤
      l2Norm (normalizedVelocity h u₂ t - normalizedVelocity h u₁ t) := by
    intro t ht
    have hm₁ := s₁.memL2 t (Ioc_subset_Icc_self ht)
    have hm₂ := s₂.memL2 t (Ioc_subset_Icc_self ht)
    simp only [normalizedVelocity_apply]
    rw [l2Norm_viscosityScale_sub (u₂ t) (u₁ t) hm₂ hm₁ hh, mul_assoc]
    exact mul_le_mul_of_nonneg_left (hsep t ht) (Real.rpow_pos_of_pos hh _).le
  have hint := integrableOn_sq_l2_dist n₁ n₂
  obtain ⟨hbound, hpos⟩ := integrated_l2_separation hT hc' hσ hint hsep'
  exact ⟨T, viscosityScale h u₀, normalizedVelocity h u₁, normalizedVelocity h u₂, _, _,
    _, _, _, _, h ^ (-5 / 4 : ℝ) * c, σ, hT, isInitialDatum_viscosityScale hd hh,
    n₁, n₂, hc', hσ, hσ', hsep', hint, hbound, hpos,
    isAxisymmetricNoSwirl_viscosityScale hsym₀ hh,
    fun t ht => isAxisymmetricNoSwirl_viscosityScale (hsym₁ t ht) hh,
    fun t ht => isAxisymmetricNoSwirl_viscosityScale (hsym₂ t ht) hh⟩

end UnforcedLeray
