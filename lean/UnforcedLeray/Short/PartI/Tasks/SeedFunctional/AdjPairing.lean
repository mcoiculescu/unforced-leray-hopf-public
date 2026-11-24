import UnforcedLeray.Short.PartI.Sub.PartI_S09
import UnforcedLeray.Short.PartI.Tasks.AdjointEigenvectorExplicit

/-!
# Part I, leaf `PartI:S09/1`: the adjoint pairing `⟪gd, f⟫ = ∫₀^∞ h f / k r dr`

Source: `the November 2 reference manuscript` lines 890-912 and 603-607.
Proof: `gd = seedAdjEig q lam` (from `AdjointEigenvectorExplicit`). Pointwise on `r > 0`,
`conj(gd r) · xGDensity r = q r · r / radialK r` (from the eigen equation), and the pairing
reduces to the `dr`-integral by `B0094.integral_xGMeasure`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Real
open scoped ENNReal NNReal ComplexConjugate ContDiff Topology

open UnforcedLeray
open UnforcedLeray.GaussianVortex (radialOmega radialK radialOmega_pos)
open UnforcedLeray.Short.PartI

namespace UnforcedLeray.Short.PartI.SeedAdjPairingAux

/-- `strainK` vanishes only at `±√8` (copied from `Compose.lean` to keep this file upstream). -/
theorem aeStrainK_ne_zero : ∀ᵐ r : ℝ ∂volume, Blueprint.Planar.strainK r ≠ 0 := by
  have hsub : {r : ℝ | Blueprint.Planar.strainK r = 0} ⊆ {Real.sqrt 8, -Real.sqrt 8} := by
    intro r hr
    simp only [Blueprint.Planar.strainK, mul_eq_zero] at hr
    rcases hr with h | h
    · have h8 : r ^ 2 = 8 := by linarith
      have : r = Real.sqrt 8 ∨ r = -Real.sqrt 8 := by
        have hs : Real.sqrt 8 ^ 2 = 8 := Real.sq_sqrt (by norm_num)
        have : (r - Real.sqrt 8) * (r + Real.sqrt 8) = 0 := by nlinarith
        rcases mul_eq_zero.1 this with h1 | h1
        · left; linarith
        · right; linarith
      simpa using this
    · exact absurd h (Real.exp_pos _).ne'
  rw [ae_iff]
  have hfin : ({Real.sqrt 8, -Real.sqrt 8} : Set ℝ).Finite := Set.toFinite _
  have hnull : volume ({Real.sqrt 8, -Real.sqrt 8} : Set ℝ) = 0 := hfin.measure_zero volume
  refine measure_mono_null ?_ hnull
  intro r hr
  have h0 : Blueprint.Planar.strainK r = 0 := by simpa using hr
  exact hsub h0

theorem strainK_eq_radialK (r : ℝ) : Blueprint.Planar.strainK r = radialK r := by
  simp only [Blueprint.Planar.strainK, GaussianVortex.radialK, GaussianVortex.radialOmega, neg_div]

theorem aeRadialK_ne_zero : ∀ᵐ r : ℝ ∂volume, radialK r ≠ 0 := by
  filter_upwards [aeStrainK_ne_zero] with r hr
  rw [← strainK_eq_radialK]
  exact hr

/-- Algebra: `p⁻¹ r (p φ / D) = q r / K` once `D q = K φ`. -/
theorem alg_div_pointwise (p φ D K q r : ℂ) (hp : p ≠ 0) (hD : D ≠ 0) (hK : K ≠ 0)
    (hA : D * q = K * φ) : p⁻¹ * r * (p * φ / D) = q * r / K := by
  have e1 : p⁻¹ * r * (p * φ / D) = r * φ / D := by
    field_simp
  rw [e1, div_eq_div_iff hD hK]
  linear_combination (-r) * hA

theorem conj_den (r : ℝ) (lam : ℂ) :
    starRingEnd ℂ ((radialOmega r : ℂ) - starRingEnd ℂ (Complex.I * lam / 2)) =
      (radialOmega r : ℂ) - Complex.I * lam / 2 := by
  rw [map_sub, Complex.conj_ofReal, Complex.conj_conj]

/-- Pointwise density identity: `xGDensity r · conj(gd r) = q r · r / k r` for `r > 0`. -/
theorem density_conj_gd {lam : ℂ} (hre : 0 < lam.re) (q : B0010.XG) (r : ℝ) (hr : 0 < r)
    (hk : radialK r ≠ 0)
    (hA : ((radialOmega r : ℂ) - Complex.I * lam / 2) * q r =
      (radialK r : ℂ) * Planar.greenN 2 (⇑q) r) :
    ((B0010.xGDensity r : ℝ) : ℂ) * starRingEnd ℂ (seedAdjEig q lam r) =
      (q r) * (r : ℂ) / (radialK r : ℂ) := by
  have hΩ : (0 : ℝ) < radialOmega r := radialOmega_pos r
  have hD := adjEig_den_ne hre (radialOmega r)
  have hk' : (radialK r : ℂ) ≠ 0 := by exact_mod_cast hk
  have hp : (((4 * π)⁻¹ * radialOmega r : ℝ) : ℂ) ≠ 0 := by
    have : (0 : ℝ) < (4 * π)⁻¹ * radialOmega r := mul_pos (by positivity) hΩ
    exact Complex.ofReal_ne_zero.2 this.ne'
  have key := alg_div_pointwise _ (Planar.greenN 2 (⇑q) r) _ _ (q r) (r : ℂ) hp hD hk'
    (by linear_combination hA)
  rw [B0010.coe_xGDensity hr]
  unfold seedAdjEig B0010.radialGaussianWeight
  rw [map_div₀, map_mul, Complex.conj_ofReal, Complex.conj_conj, conj_den]
  simp only [Complex.ofReal_mul, Complex.ofReal_inv] at key ⊢
  exact key

/-- The a.e. (on `(0,∞)`, Lebesgue) form of the density identity. -/
theorem ae_density_conj_gd {lam : ℂ} (hre : 0 < lam.re) (q : B0010.XG)
    (hq : Planar.L0 q = lam • q) :
    ∀ᵐ r ∂(volume.restrict (Ioi (0 : ℝ))),
      ((B0010.xGDensity r : ℝ) : ℂ) * starRingEnd ℂ (seedAdjEig q lam r) =
        (q r) * (r : ℂ) / (radialK r : ℂ) := by
  have hall : ∀ᵐ r ∂B0010.xGMeasure,
      radialK r ≠ 0 ∧ ((radialOmega r : ℂ) - Complex.I * lam / 2) * q r =
        (radialK r : ℂ) * Planar.greenN 2 (⇑q) r := by
    have hK : ∀ᵐ r ∂B0010.xGMeasure, radialK r ≠ 0 :=
      B0012.xG_ac.ae_le (ae_restrict_of_ae aeRadialK_ne_zero)
    filter_upwards [hK, adjEig_pointwise hq] with r h1 h2
    exact ⟨h1, h2⟩
  filter_upwards [B0012.restrict_ac.ae_le hall, ae_restrict_mem measurableSet_Ioi] with r hr hpos
  exact density_conj_gd hre q r hpos hr.1 hr.2

end UnforcedLeray.Short.PartI.SeedAdjPairingAux

open UnforcedLeray.Short.PartI.SeedAdjPairingAux

theorem seedAdjPairing_proof : UnforcedLeray.Short.PartI.SeedAdjPairing := by
  intro lam h hh ℓ hI
  have hre : 0 < lam.re := hI.re_pos
  set q : B0010.XG := hh.toLp h with hqdef
  refine ⟨(seedAdjEig_memLp hre q).toLp (seedAdjEig q lam), seedAdjEig_adjoint hre hI.eigen,
    seedAdjEig_ne_zero hre hI.ne_zero hI.eigen, ?_⟩
  intro f
  set gd : B0010.XG := (seedAdjEig_memLp hre q).toLp (seedAdjEig q lam) with hgd
  have hq : (⇑q : ℝ → ℂ) =ᵐ[volume.restrict (Ioi (0 : ℝ))] h :=
    B0012.restrict_ac.ae_le hh.coeFn_toLp
  have hgd_ae : (⇑gd : ℝ → ℂ) =ᵐ[volume.restrict (Ioi (0 : ℝ))] seedAdjEig q lam :=
    B0012.restrict_ac.ae_le (seedAdjEig_memLp hre q).coeFn_toLp
  have hP : ∀ᵐ r ∂(volume.restrict (Ioi (0 : ℝ))),
      ((B0010.xGDensity r : ℝ) : ℂ) * starRingEnd ℂ ((gd : ℝ → ℂ) r) =
        h r * (r : ℂ) / (Blueprint.Planar.strainK r : ℂ) := by
    filter_upwards [ae_density_conj_gd hre q hI.eigen, hq, hgd_ae] with r h1 h2 h3
    rw [h3, strainK_eq_radialK, h1, h2]
  have hint : Integrable (fun r : ℝ => (f : ℝ → ℂ) r * starRingEnd ℂ ((gd : ℝ → ℂ) r))
      B0010.xGMeasure := by
    refine (L2.integrable_inner gd f).congr (ae_of_all _ fun r => ?_)
    simp only [RCLike.inner_apply]
  have hint2 : Integrable (fun r : ℝ => (B0010.xGDensity r) •
      ((f : ℝ → ℂ) r * starRingEnd ℂ ((gd : ℝ → ℂ) r))) (volume.restrict (Ioi (0 : ℝ))) :=
    (integrable_withDensity_iff_integrable_smul B0010.measurable_xGDensity).1 hint
  have hint3 : IntegrableOn
      (fun r : ℝ => h r * (f : ℝ → ℂ) r / (Blueprint.Planar.strainK r : ℂ) * (r : ℂ))
      (Ioi 0) volume := by
    refine hint2.congr ?_
    filter_upwards [hP] with r hr
    simp only [NNReal.smul_def, Complex.real_smul]
    linear_combination ((f : ℝ → ℂ) r) * hr
  refine ⟨hint3, ?_⟩
  rw [← B0010.pairing_eq_inner]
  unfold B0010.pairing
  rw [B0094.integral_xGMeasure]
  refine integral_congr_ae ?_
  filter_upwards [hP] with r hr
  beta_reduce
  linear_combination ((f : ℝ → ℂ) r) * hr
