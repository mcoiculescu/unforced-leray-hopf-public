import UnforcedLeray.Short.PartIIIa.Sub.T21_c1_a_3_of

/-!
# Part III-a, `PartIII-a:T21/c1/a/3/2`: polar coordinates on the plane

Source: `the November 2 reference manuscript`, lines 2891-2897.
Proves `SeedPolarPlane` (defined in `T21_c1_a_3_of.lean`).

Argument. Transport the planar integral to `ℂ` (`Complex.volume_preserving_equiv_real_prod`),
apply Fubini in polar coordinates (`Planar.NUE.Polar.integral_eq_integral_Ioi_intervalIntegral`,
from `Lib/PlanarSectors/NUE/PolarFubini.lean`), and use `angPhase (-n) (r e^{iθ}) = e^{-inθ}`
for `r > 0`. The integrability of the integrand on `ℂ` comes from compact support of `f`
and the bound on `G` (hypothesis on `(0,1]`, continuity on `[1,R]`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.IIIa.SeedPolarPlaneAux

lemma circleMap_zero_eq (r θ : ℝ) :
    circleMap 0 r θ = (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I) := by
  simp [circleMap]

lemma norm_circle_pos (r θ : ℝ) (hr : 0 < r) :
    ‖(r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)‖ = r := by
  rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
    Real.norm_of_nonneg hr.le]

lemma angPhase_circle (n : ℤ) (r θ : ℝ) (hr : 0 < r) :
    UnforcedLeray.Planar.NUE.Ang.angPhase (-n) ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) =
      Complex.exp (-((n : ℂ) * (θ : ℂ) * Complex.I)) := by
  have hrC : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  unfold UnforcedLeray.Planar.NUE.Ang.angPhase
  rw [norm_circle_pos r θ hr]
  rw [mul_div_cancel_left₀ _ hrC, ← Complex.exp_int_mul]
  congr 1
  push_cast
  ring

lemma integrable_polar_integrand (n : ℤ) (G : ℝ → ℂ) (hGc : ContinuousOn G (Ioi 0))
    (hGb : ∃ C : ℝ, ∀ r : ℝ, 0 < r → r ≤ 1 → ‖G r‖ ≤ C)
    (f : ℂ → ℂ) (hf : ContDiff ℝ ∞ f) (hfs : HasCompactSupport f) :
    Integrable (fun z : ℂ => G ‖z‖ * UnforcedLeray.Planar.NUE.Ang.angPhase (-n) z * f z) := by
  obtain ⟨R0, hR0⟩ := hfs.isCompact.isBounded.subset_closedBall (0 : ℂ)
  obtain ⟨C1, hC1⟩ := hGb
  obtain ⟨C2, hC2⟩ := (isCompact_Icc : IsCompact (Icc (1 : ℝ) (max R0 1))).exists_bound_of_continuousOn
    (hGc.mono (fun x hx => lt_of_lt_of_le one_pos hx.1))
  obtain ⟨Bf, hBf⟩ := ((isCompact_closedBall (0 : ℂ) (max R0 1))).exists_bound_of_continuousOn
    hf.continuous.continuousOn
  have hsupp : ∀ z : ℂ, max R0 1 < ‖z‖ → f z = 0 := by
    intro z hz
    by_contra hne
    have hzt : z ∈ tsupport f := subset_tsupport f (Function.mem_support.2 hne)
    have h3 := hR0 hzt
    rw [Metric.mem_closedBall, dist_zero_right] at h3
    linarith [le_max_left R0 1]
  have hCG0 : 0 ≤ (|C1| + |C2|) := by positivity
  -- pointwise bound on the punctured closed ball
  have hGbd : ∀ z : ℂ, z ≠ 0 → ‖z‖ ≤ max R0 1 → ‖G ‖z‖‖ ≤ (|C1| + |C2|) := by
    intro z hz hzR
    have hzpos : 0 < ‖z‖ := norm_pos_iff.2 hz
    by_cases h1 : ‖z‖ ≤ 1
    · have hG1 : ‖G ‖z‖‖ ≤ C1 := hC1 ‖z‖ hzpos h1
      have hc1 : C1 ≤ |C1| := le_abs_self C1
      have hc2 : 0 ≤ |C2| := abs_nonneg C2
      linarith
    · push_neg at h1
      have hmem : ‖z‖ ∈ Icc (1 : ℝ) (max R0 1) := ⟨h1.le, hzR⟩
      have hG2 : ‖G ‖z‖‖ ≤ C2 := hC2 ‖z‖ hmem
      have hc1 : 0 ≤ |C1| := abs_nonneg C1
      have hc2 : C2 ≤ |C2| := le_abs_self C2
      linarith
  -- continuity of the integrand off the origin
  have hden : ∀ z ∈ ({0}ᶜ : Set ℂ), ((‖z‖ : ℝ) : ℂ) ≠ 0 := fun z hz =>
    Complex.ofReal_ne_zero.2 (norm_ne_zero_iff.2 hz)
  have hq : ContinuousOn (fun z : ℂ => z / ((‖z‖ : ℝ) : ℂ)) ({0}ᶜ : Set ℂ) :=
    ContinuousOn.div continuousOn_id
      (Complex.continuous_ofReal.comp continuous_norm).continuousOn hden
  have hAP : ContinuousOn (fun z : ℂ => UnforcedLeray.Planar.NUE.Ang.angPhase (-n) z)
      ({0}ᶜ : Set ℂ) := by
    unfold UnforcedLeray.Planar.NUE.Ang.angPhase
    exact hq.zpow₀ (-n) (fun z hz => Or.inl (div_ne_zero hz (hden z hz)))
  have hGn : ContinuousOn (fun z : ℂ => G ‖z‖) ({0}ᶜ : Set ℂ) :=
    hGc.comp continuous_norm.continuousOn (fun z hz => norm_pos_iff.2 hz)
  have hFc : ContinuousOn (fun z : ℂ => G ‖z‖ * UnforcedLeray.Planar.NUE.Ang.angPhase (-n) z * f z)
      ({0}ᶜ : Set ℂ) :=
    (hGn.mul hAP).mul hf.continuous.continuousOn
  have hae : ∀ᵐ z ∂(volume : Measure ℂ), z ∈ ({0}ᶜ : Set ℂ) :=
    compl_mem_ae_iff.2 (measure_singleton 0)
  have hmeas : AEStronglyMeasurable (fun z : ℂ => G ‖z‖ * UnforcedLeray.Planar.NUE.Ang.angPhase (-n) z * f z)
      (volume : Measure ℂ) := by
    have hcm : AEStronglyMeasurable (fun z : ℂ => G ‖z‖ * UnforcedLeray.Planar.NUE.Ang.angPhase (-n) z * f z)
        ((volume : Measure ℂ).restrict ({0}ᶜ : Set ℂ)) :=
      hFc.aestronglyMeasurable (isOpen_compl_singleton.measurableSet)
    rwa [Measure.restrict_eq_self_of_ae_mem hae] at hcm
  -- integrable majorant: a constant on the closed ball
  have hgint : Integrable ((Metric.closedBall (0 : ℂ) (max R0 1)).indicator
      (fun _ : ℂ => (|C1| + |C2|) * |Bf|)) (volume : Measure ℂ) := by
    rw [integrable_indicator_iff measurableSet_closedBall]
    exact integrableOn_const (measure_closedBall_lt_top (μ := (volume : Measure ℂ))).ne
  refine hgint.mono' hmeas ?_
  filter_upwards [hae] with z hz
  have hz0 : z ≠ 0 := hz
  by_cases hzR : ‖z‖ ≤ max R0 1
  · have hmem : z ∈ Metric.closedBall (0 : ℂ) (max R0 1) := by
      rw [Metric.mem_closedBall, dist_zero_right]; exact hzR
    rw [indicator_of_mem hmem]
    have hA : ‖UnforcedLeray.Planar.NUE.Ang.angPhase (-n) z‖ ≤ 1 := by
      unfold UnforcedLeray.Planar.NUE.Ang.angPhase
      rw [norm_zpow, norm_div, Complex.norm_real, Real.norm_of_nonneg (norm_nonneg z),
        div_self (norm_ne_zero_iff.2 hz0)]
      simp
    have hfb : ‖f z‖ ≤ |Bf| := le_trans (hBf z (Metric.mem_closedBall.2 (by
        rw [dist_zero_right]; exact hzR))) (le_abs_self Bf)
    calc ‖G ‖z‖ * UnforcedLeray.Planar.NUE.Ang.angPhase (-n) z * f z‖
        = ‖G ‖z‖‖ * ‖UnforcedLeray.Planar.NUE.Ang.angPhase (-n) z‖ * ‖f z‖ := by
          rw [norm_mul, norm_mul]
      _ ≤ (|C1| + |C2|) * 1 * |Bf| :=
          mul_le_mul (mul_le_mul (hGbd z hz0 hzR) hA (norm_nonneg _) hCG0) hfb (norm_nonneg _)
            (by positivity)
      _ = (|C1| + |C2|) * |Bf| := by ring
  · push_neg at hzR
    rw [hsupp z hzR]
    simp only [mul_zero, norm_zero]
    apply indicator_nonneg
    intro x _
    positivity

end UnforcedLeray.Short.IIIa.SeedPolarPlaneAux

open UnforcedLeray.Short.IIIa.SeedPolarPlaneAux in
theorem seedPolarPlane_proof : UnforcedLeray.Short.IIIa.SeedPolarPlane := by
  unfold UnforcedLeray.Short.IIIa.SeedPolarPlane
  intro n G hGc hGb f hf hfs
  have hint := integrable_polar_integrand n G hGc hGb f hf hfs
  have h1 : ∫ y : ℝ × ℝ, G ‖UnforcedLeray.Short.IIIa.planeToC y‖ * UnforcedLeray.Planar.NUE.Ang.angPhase (-n) (UnforcedLeray.Short.IIIa.planeToC y) *
        f (UnforcedLeray.Short.IIIa.planeToC y) =
      ∫ z : ℂ, G ‖z‖ * UnforcedLeray.Planar.NUE.Ang.angPhase (-n) z * f z :=
    (Complex.volume_preserving_equiv_real_prod.symm).integral_comp
      Complex.measurableEquivRealProd.symm.measurableEmbedding
      (fun z : ℂ => G ‖z‖ * UnforcedLeray.Planar.NUE.Ang.angPhase (-n) z * f z)
  have h2 : ∀ r ∈ Ioi (0 : ℝ),
      r • ∫ θ in (0 : ℝ)..2 * Real.pi,
        G ‖circleMap 0 r θ‖ * UnforcedLeray.Planar.NUE.Ang.angPhase (-n) (circleMap 0 r θ) *
          f (circleMap 0 r θ) =
      (2 * Real.pi : ℂ) *
        (G r * UnforcedLeray.Planar.NUE.Polar.angularSector f n r * (r : ℂ)) := by
    intro r hr
    have hr0 : 0 < r := hr
    have hpt : ∀ θ : ℝ,
        G ‖circleMap 0 r θ‖ * UnforcedLeray.Planar.NUE.Ang.angPhase (-n) (circleMap 0 r θ) *
          f (circleMap 0 r θ) =
        G r * (f ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) *
          Complex.exp (-((n : ℂ) * (θ : ℂ) * Complex.I))) := by
      intro θ
      rw [circleMap_zero_eq, norm_circle_pos r θ hr0, angPhase_circle n r θ hr0]
      ring
    have hA : (2 * Real.pi : ℂ) * UnforcedLeray.Planar.NUE.Polar.angularSector f n r =
        ∫ θ in (0 : ℝ)..2 * Real.pi,
          f ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) *
            Complex.exp (-((n : ℂ) * (θ : ℂ) * Complex.I)) := by
      unfold UnforcedLeray.Planar.NUE.Polar.angularSector
      have hne : (2 * Real.pi : ℂ) ≠ 0 :=
        mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.2 Real.pi_ne_zero)
      rw [← mul_assoc, mul_inv_cancel₀ hne, one_mul]
    simp only [hpt]
    rw [intervalIntegral.integral_const_mul, ← hA, Complex.real_smul]
    ring
  rw [h1, UnforcedLeray.Planar.NUE.Polar.integral_eq_integral_Ioi_intervalIntegral
    (integrable_polar_integrand n G hGc hGb f hf hfs)]
  rw [setIntegral_congr_fun measurableSet_Ioi h2, integral_const_mul]
