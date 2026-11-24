import UnforcedLeray.Short.PartI.StatementsSeed
import UnforcedLeray.Short.PartI.Tasks.SeedUniqueness
import UnforcedLeray.Short.PartI.Tasks.MemHjMGaussian
import UnforcedLeray.Short.PartI.Tasks.BiotSavartPerpGrad

/-!
# Part I, task `PartI:S05` (conditional): regularity and decay of the growing mode

Source of record: `the November 2 reference manuscript`, lines 593-601, 758-808.
The only missing fact is the planar Laplacian identity for the streamfunction of a Gaussian growing
mode (`GaussianModeLaplacian`); everything else is assembled from `S02`, `S03`, `S04`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.PartI

open UnforcedLeray

/-- **`ΔΨ = q` for a Gaussian growing mode** (source lines 788-803): the streamfunction
`Ψ = φ e^{2iϑ}` has planar Laplacian `∂₁²Ψ + ∂₂²Ψ = q = h e^{2iϑ}`, since `Δ₂ φ = h`
(`G.φ_rayleigh`, `G.h_mul`) and `Δ (ofProfile 2 φ) = ofProfile 2 (Δ₂ φ)` away from the origin
(removable at the origin by smoothness of `Ψ`, `q`). -/
def GaussianModeLaplacian : Prop :=
  ∀ G : Planar.GaussianGrowingMode, ∀ y : ℂ,
    iteratedFDeriv ℝ 2 G.Ψ y ![1, 1] + iteratedFDeriv ℝ 2 G.Ψ y ![Complex.I, Complex.I] = G.q y

theorem seedModeRegularity_of (hL : GaussianModeLaplacian) : SeedModeRegularity := by
  intro lam h hh ℓ hs
  obtain ⟨G, μ, hμ, hlam, hq⟩ := isSeedXG_gaussianGrowingMode hs
  have hQ : seedPlanar (μ • G.h) = μ • G.q := by
    funext y
    simp [Planar.NUE.Ang.ofProfile, G.q_eq, mul_assoc]
  have hae : (μ • G.h) =ᵐ[volume.restrict (Ioi (0 : ℝ))] h := by
    have hc := Lp.coeFn_smul μ ((G.h_memLp_XG).toLp G.h)
    rw [← hq] at hc
    have h1 : h =ᵐ[B0010.xGMeasure] μ • G.h := by
      filter_upwards [hh.coeFn_toLp, (G.h_memLp_XG).coeFn_toLp,
        hc] with r a b c
      rw [← a, c]
      simp [b]
    exact (B0012.restrict_ac.ae_eq h1).symm
  have hsm : ContDiff ℝ ∞ (μ • G.q) := G.q_smooth.const_smul μ
  have hbd : ∀ k : ℕ, ∃ C : ℝ, ∃ N : ℕ, ∀ y : ℂ,
      ‖iteratedFDeriv ℝ k (μ • G.q) y‖ ≤ C * (1 + ‖y‖) ^ N * Real.exp (-(‖y‖ ^ 2) / 4) := by
    intro k
    obtain ⟨C, N, hCN⟩ := G.q_bound k
    refine ⟨‖μ‖ * C, N, fun y => ?_⟩
    rw [iteratedFDeriv_const_smul_apply ((G.q_smooth.of_le (by exact_mod_cast le_top : ((k : ℕ) : WithTop ℕ∞) ≤ ∞)).contDiffAt), norm_smul]
    calc ‖μ‖ * ‖iteratedFDeriv ℝ k G.q y‖ ≤ ‖μ‖ * (C * (1 + ‖y‖) ^ N * Real.exp (-(‖y‖ ^ 2) / 4)) :=
          mul_le_mul_of_nonneg_left (hCN y) (norm_nonneg _)
      _ = _ := by ring
  have hint : Integrable (μ • G.q) volume := G.q_integrable.smul μ
  have hlap : ∀ y, iteratedFDeriv ℝ 2 (μ • G.Ψ) y ![1, 1] +
      iteratedFDeriv ℝ 2 (μ • G.Ψ) y ![Complex.I, Complex.I] = (μ • G.q) y := by
    intro y
    rw [iteratedFDeriv_const_smul_apply ((G.Ψ_smooth.of_le (by first | exact WithTop.coe_le_coe.2 le_top | simp | exact_mod_cast le_top : ((2 : ℕ) : WithTop ℕ∞) ≤ ∞)).contDiffAt)]
    simp only [Pi.smul_apply, smul_eq_mul, ContinuousMultilinearMap.smul_apply]
    rw [← mul_add, hL G y]
  obtain ⟨K, hK0, hK⟩ := G.velocity_bound
  have hdec : Filter.Tendsto (fderiv ℝ (μ • G.Ψ)) (Filter.cocompact ℂ) (nhds 0) := by
    have hfd : fderiv ℝ (μ • G.Ψ) = fun y => μ • fderiv ℝ G.Ψ y := by
      funext y
      exact fderiv_const_smul (G.Ψ_smooth.differentiable (by simp) y) μ
    rw [hfd]
    have h0 : Filter.Tendsto (fun y : ℂ => ‖μ‖ * (K / (1 + ‖y‖) ^ 3)) (Filter.cocompact ℂ) (nhds 0) := by
      have ht : Filter.Tendsto (fun y : ℂ => (1 + ‖y‖)) (Filter.cocompact ℂ) Filter.atTop :=
        Filter.tendsto_atTop_add_const_left _ _ tendsto_norm_cocompact_atTop
      have h3 : Filter.Tendsto (fun y : ℂ => (1 + ‖y‖) ^ 3) (Filter.cocompact ℂ) Filter.atTop :=
        (tendsto_pow_atTop (by norm_num)).comp ht
      have := (tendsto_const_nhds (x := ‖μ‖ * K)).div_atTop h3
      simpa [mul_div_assoc] using this
    refine squeeze_zero_norm (fun y => ?_) h0
    rw [norm_smul]
    exact mul_le_mul_of_nonneg_left (hK y) (norm_nonneg _)
  have hbs := biotSavart_eq_perpGrad hsm hbd (by show ∫ y, μ • G.q y = 0; rw [integral_smul, G.integral_q, smul_zero])
    (G.Ψ_smooth.const_smul μ) hlap hdec
  have hvel : ∀ v : ℂ, MemLp (fun y => fderiv ℝ (μ • G.Ψ) y v) 2 volume := by
    intro v
    have hfd : ∀ y, fderiv ℝ (μ • G.Ψ) y = μ • fderiv ℝ G.Ψ y := fun y =>
      fderiv_const_smul (G.Ψ_smooth.differentiable (by simp) y) μ
    refine MemLp.of_le_mul (c := ‖μ‖ * ‖v‖) G.velocity_memLp ?_ (Filter.Eventually.of_forall fun y => ?_)
    · have hc : Continuous fun y => fderiv ℝ (μ • G.Ψ) y v :=
        ((G.Ψ_smooth.const_smul μ).continuous_fderiv (by simp)).clm_apply continuous_const
      exact hc.aestronglyMeasurable
    · rw [hfd y]
      calc ‖(μ • fderiv ℝ G.Ψ y) v‖ = ‖μ‖ * ‖fderiv ℝ G.Ψ y v‖ := by simp [norm_smul]
        _ ≤ ‖μ‖ * (‖fderiv ℝ G.Ψ y‖ * ‖v‖) :=
          mul_le_mul_of_nonneg_left (ContinuousLinearMap.le_opNorm _ _) (norm_nonneg _)
        _ = ‖μ‖ * ‖v‖ * ‖fderiv ℝ G.Ψ y‖ := by ring
  have hquad : ∫ r in Ioi (0 : ℝ), (r : ℂ) ^ 3 * (μ • G.h) r =
      μ * ∫ r in Ioi (0 : ℝ), (r : ℂ) ^ 3 * G.h r := by
    rw [← integral_const_mul]
    congr 1; funext r; simp only [Pi.smul_apply, smul_eq_mul]; ring
  have hquad_int : IntegrableOn (fun r : ℝ => (r : ℂ) ^ 3 * (μ • G.h) r) (Ioi 0) volume := by
    have : IntegrableOn (fun r : ℝ => (r : ℂ) ^ 3 * G.h r) (Ioi 0) volume :=
      Integrable.of_integral_ne_zero G.quadrupole_ne_zero
    have e : (fun r : ℝ => (r : ℂ) ^ 3 * (μ • G.h) r) = fun r : ℝ => μ * ((r : ℂ) ^ 3 * G.h r) := by
      funext r; simp only [Pi.smul_apply, smul_eq_mul]; ring
    rw [e]; exact this.const_mul μ
  refine ⟨?_, ?_, μ • G.h, hae, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have := G.freq_gt; rw [hlam]; simpa [Planar.GaussianGrowingMode.eigenvalue] using this
  · have := G.freq_lt; rw [hlam]; simpa [Planar.GaussianGrowingMode.eigenvalue] using this
  · rw [hQ]; exact hsm
  · rw [hQ]; exact hbd
  · rw [hQ]; exact hint
  · rw [hQ]; show ∫ y, μ • G.q y = 0
    rw [integral_smul, G.integral_q, smul_zero]
  · intro j M; rw [hQ]; exact memHjM_of_gaussian_bounds hsm hbd j M
  · rw [hQ]
    refine Fin.forall_fin_two.2 ⟨?_, ?_⟩
    · have e : B0009.biotSavart (μ • G.q) 0 = fun y => -(fderiv ℝ (μ • G.Ψ) y Complex.I) :=
        funext fun y => (hbs y).1
      rw [e]; exact (hvel _).neg
    · have e : B0009.biotSavart (μ • G.q) 1 = fun y => fderiv ℝ (μ • G.Ψ) y 1 :=
        funext fun y => (hbs y).2
      rw [e]; exact hvel _
  · exact hquad_int
  · unfold Blueprint.Planar.quadrupole
    rw [hquad]
    exact mul_ne_zero hμ G.quadrupole_ne_zero

end UnforcedLeray.Short.PartI

end
