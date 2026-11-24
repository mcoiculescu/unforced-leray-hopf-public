import UnforcedLeray.Short.PartI.Tasks.EulerSectorBridge.SecProfAE.OnSmoothSums.StreamQ

/-!
# Part I, task `PartI:S11/1/1/3`: sector `0` has zero perturbation

Target: `secPertZero : SecPertZero` (`Sub/PartI_S11_1_1.lean`, lines 841-889). For a smooth
profile `φ` with compact support in `(0,∞)`, the radial function `q(y) = φ(|y|)` satisfies
`B0009.perturbation q y = 0` for almost every `y`.

Method. `perturbation q y = (Kq)₁ y · k(|y|) y₁ + (Kq)₂ y · k(|y|) y₂`, so it suffices that
`(Kq)₁ y · y₁ + (Kq)₂ y · y₂ = 0`. With `biotSavart_apply` and the identity
`K₁(w) y₁ + K₂(w) y₂ = H(y,z)` (`H(y,z) = (y₁ z₂ - y₂ z₁)/(2π|y-z|²)`, `w = y - z`) this is
`∫ H(y,z) q(z) dz = 0`. The reflection `σ z = (y/ȳ) z̄` fixes the line `ℝ y`, preserves `|z|`,
`|y-z|` and Lebesgue measure, and satisfies `H(y,σz) = -H(y,z)`. Hence the integral vanishes.
Integrability of the convolution integrands comes from `convolutionExistsAt_kernel`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Real
open scoped ContDiff ComplexConjugate

namespace UnforcedLeray.Short.PartI

open UnforcedLeray UnforcedLeray.Planar.NUE

namespace SecPertZeroAux

/-- The radial sector profile: `Ang.ofProfile 0 φ z = φ ‖z‖`. -/
theorem ofProfile_zero_apply (φ : ℝ → ℂ) (z : ℂ) : Ang.ofProfile 0 φ z = φ ‖z‖ := by
  simp [Ang.ofProfile, Ang.angPhase]

/-- The real Biot-Savart weight `H(y,z) = (y₁ z₂ - y₂ z₁)/(2π|y-z|²)`. -/
def Hk (y z : ℂ) : ℝ := (y.re * z.im - y.im * z.re) / (2 * Real.pi * ‖y - z‖ ^ 2)

theorem kernel_combo (y z : ℂ) :
    B0009.kernel 0 (y - z) * (y.re : ℂ) + B0009.kernel 1 (y - z) * (y.im : ℂ) =
      ((Hk y z : ℝ) : ℂ) := by
  unfold Hk B0009.kernel B0009.perpComp
  simp only [Complex.sub_im, Complex.sub_re]
  push_cast
  ring

/-- Reflection identity for the weight, from `conj y * s = y * conj z` and `|y - s| = |y - z|`. -/
theorem Hk_of_conj (y z s : ℂ) (hs : conj y * s = y * conj z) (hn : ‖y - s‖ = ‖y - z‖) :
    Hk y s = -Hk y z := by
  have h := congrArg Complex.im hs
  simp only [Complex.mul_im, Complex.conj_re, Complex.conj_im] at h
  unfold Hk
  rw [hn, ← neg_div]
  congr 1
  linear_combination h

/-- The reflection `z ↦ (y/ȳ) z̄` across the line `ℝ y`. -/
theorem exists_reflection (y : ℂ) (hy : y ≠ 0) :
    ∃ σ : ℂ ≃ₗᵢ[ℝ] ℂ, MeasurePreserving σ volume volume ∧
      (∀ z, conj y * σ z = y * conj z) ∧ (∀ z, ‖y - σ z‖ = ‖y - z‖) ∧
      (∀ z, ‖σ z‖ = ‖z‖) := by
  have hcy : conj y ≠ 0 := by simpa using hy
  obtain ⟨a, ha_def⟩ : ∃ a : ℂ, a = y / conj y := ⟨_, rfl⟩
  have hay : a * conj y = y := by rw [ha_def, div_mul_cancel₀ y hcy]
  have ha1 : ‖a‖ = 1 := by
    rw [ha_def, norm_div, Complex.norm_conj, div_self (norm_ne_zero_iff.2 hy)]
  let w : Metric.sphere (0 : ℂ) 1 := ⟨a, mem_sphere_zero_iff_norm.2 ha1⟩
  let u : Circle := w
  have hσ : ∀ z, (Complex.conjLIE.trans (rotation u)) z = a * conj z := by
    intro z
    rw [LinearIsometryEquiv.trans_apply, Complex.conjLIE_apply, rotation_apply]
  refine ⟨Complex.conjLIE.trans (rotation u), (Complex.conjLIE.trans (rotation u)).measurePreserving, ?_, ?_, ?_⟩
  · intro z
    rw [hσ z]
    linear_combination (conj z) * hay
  · intro z
    rw [hσ z, show y - a * conj z = a * conj (y - z) by rw [map_sub, mul_sub, hay]]
    rw [norm_mul, ha1, one_mul, Complex.norm_conj]
  · intro z
    rw [hσ z, norm_mul, ha1, one_mul, Complex.norm_conj]

/-- The reflected integral of the weighted radial profile vanishes. -/
theorem integral_reflect_zero (y : ℂ) (hy : y ≠ 0) (φ : ℝ → ℂ) :
    ∫ z, ((Hk y z : ℝ) : ℂ) * Ang.ofProfile 0 φ z = 0 := by
  obtain ⟨σ, hMP, hconj, hnorm, hnz⟩ := exists_reflection y hy
  have hG : ∀ z, ((Hk y (σ z) : ℝ) : ℂ) * Ang.ofProfile 0 φ (σ z) =
      -(((Hk y z : ℝ) : ℂ) * Ang.ofProfile 0 φ z) := by
    intro z
    rw [Hk_of_conj y z (σ z) (hconj z) (hnorm z), ofProfile_zero_apply, ofProfile_zero_apply,
      hnz z]
    push_cast
    ring
  have h1 := hMP.integral_comp σ.toHomeomorph.measurableEmbedding
    (fun z => ((Hk y z : ℝ) : ℂ) * Ang.ofProfile 0 φ z)
  simp only [hG, integral_neg] at h1
  linear_combination (-1 / 2 : ℂ) * h1

end SecPertZeroAux

open SecPertZeroAux

/-- **Target `PartI:S11/1/1/3`**: `SecPertZero` (see `Sub/PartI_S11_1_1.lean`, lines 841-889). -/
theorem secPertZero : UnforcedLeray.Short.PartI.SecPertZero := by
  unfold SecPertZero
  intro φ hφ
  unfold SmoothCptFun at hφ
  obtain ⟨hs, hc, hts⟩ := hφ
  have hcl : IsClosed (tsupport φ) := isClosed_tsupport φ
  have hq : ContDiff ℝ ∞ (Ang.ofProfile 0 φ) :=
    SecStreamQAux.ofProfile_contDiff hs hcl hts 0
  obtain ⟨R, hR⟩ := SecStreamQAux.ofProfile_tsupport_sub hc 0
  have hcs : HasCompactSupport (Ang.ofProfile 0 φ) :=
    HasCompactSupport.intro (isCompact_closedBall (0 : ℂ) R) (fun z hz =>
      Classical.byContradiction fun h => hz (hR (subset_tsupport _ (Function.mem_support.2 h))))
  have hint : Integrable (Ang.ofProfile 0 φ) volume :=
    hq.continuous.integrable_of_hasCompactSupport hcs
  have ce0 := B0009.convolutionExistsAt_kernel hint 0
  have ce1 := B0009.convolutionExistsAt_kernel hint 1
  filter_upwards [ce0, ce1] with y h0 h1
  by_cases hy : y = 0
  · subst hy
    simp [B0009.perturbation, B0009.gradE0_eq]
  · have hI0 : Integrable (fun z => B0009.kernel 0 (y - z) * Ang.ofProfile 0 φ z) volume := by
      unfold ConvolutionExistsAt at h0
      simpa [ContinuousLinearMap.mul_apply', mul_comm] using h0
    have hI1 : Integrable (fun z => B0009.kernel 1 (y - z) * Ang.ofProfile 0 φ z) volume := by
      unfold ConvolutionExistsAt at h1
      simpa [ContinuousLinearMap.mul_apply', mul_comm] using h1
    have hsum : (∫ z, B0009.kernel 0 (y - z) * Ang.ofProfile 0 φ z) * (y.re : ℂ) +
        (∫ z, B0009.kernel 1 (y - z) * Ang.ofProfile 0 φ z) * (y.im : ℂ) = 0 := by
      rw [← integral_mul_const, ← integral_mul_const,
        ← integral_add (hI0.mul_const _) (hI1.mul_const _)]
      refine Eq.trans ?_ (integral_reflect_zero y hy φ)
      congr 1
      funext z
      linear_combination (Ang.ofProfile 0 φ z) * kernel_combo y z
    simp only [B0009.perturbation, B0009.gradE0_eq]
    rw [B0009.biotSavart_apply, B0009.biotSavart_apply]
    push_cast
    linear_combination ((GaussianVortex.radialK ‖y‖ : ℂ)) * hsum

end UnforcedLeray.Short.PartI
