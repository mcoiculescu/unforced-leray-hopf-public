import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.CylinderHelmholtz.PlaneHelmholtz.RieszFamily.Defs
import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.CylinderHelmholtz.PlaneHelmholtz.RieszFamily.PdTest
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.Calculus.Deriv.Pi

/-!
# Leaf `PartII-b:T12/1/1/2/5`: the planar flux identity `∫ ∇N · ∇φ = -φ(0)`

Source of record: `the November 2 reference manuscript`, line 1670 (`P_0`, the
ordinary planar cylinder projection) and lines 1923-1926 (`P_0` in the causal formula); classical
Calderón-Zygmund theory (Grafakos, *Classical Fourier Analysis*, Cor. 5.2.8).

Polar coordinates `y = r (cos θ, sin θ)`: the integrand `∇N · ∇φ` at `y` equals
`(2π)⁻¹ r⁻¹ ∂_r [φ(y)]`, so the Jacobian `r` cancels `r⁻¹`.  The radial integral is
`∫_0^∞ ∂_r φ dr = -φ(0)` (compact support), and the angular integral over `(-π, π)` gives
`2π · (2π)⁻¹ = 1`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set
open scoped ContDiff ENNReal NNReal Topology

namespace UnforcedLeray.Short.IIb.PlaneRiesz

/-- The planar point with coordinates `a, b`. -/
abbrev ngpPt (a b : ℝ) : Pl := ![a, b]

theorem ngp_apply0 (a b : ℝ) : ngpPt a b 0 = a := by simp [ngpPt]

theorem ngp_apply1 (a b : ℝ) : ngpPt a b 1 = b := by simp [ngpPt]

theorem ngp_zero (θ : ℝ) : ngpPt (0 * Real.cos θ) (0 * Real.sin θ) = 0 := by
  funext i
  fin_cases i <;> simp [ngpPt]

/-- The radial-direction vector derivative: `D(r, θ) = ∂_{(cos θ, sin θ)} φ` at `r(cos θ, sin θ)`. -/
def ngpD (φ : Pl → ℝ) (r θ : ℝ) : ℝ :=
  fderiv ℝ φ (ngpPt (r * Real.cos θ) (r * Real.sin θ)) (ngpPt (Real.cos θ) (Real.sin θ))

/-- The integrand of `NewtonGradKernelPolar`: `∇N · ∇φ`. -/
def ngpG (φ : Pl → ℝ) (y : Pl) : ℝ :=
  newtonGradKernel 0 y * pd 0 φ y + newtonGradKernel 1 y * pd 1 φ y

/-- The polar-coordinate integrand `(2π)⁻¹ ∂_{(cos θ, sin θ)} φ`, as a function of `(r, θ)`. -/
def ngpF (φ : Pl → ℝ) (p : ℝ × ℝ) : ℝ :=
  (2 * Real.pi)⁻¹ * ngpD φ p.1 p.2

/-- Change of variables from the plane to `ℝ × ℝ`. -/
theorem ngp_integral_plane (G : Pl → ℝ) :
    ∫ x, G x = ∫ p : ℝ × ℝ, G (ngpPt p.1 p.2) := by
  have h := (MeasurePreserving.symm _ (volume_preserving_finTwoArrow ℝ)).integral_comp' G
  exact h.symm

/-- Outside a radius `M` (uniform in the angle), the ray `r ↦ (r cos θ, r sin θ)` leaves
the support of a compactly supported `φ`. -/
theorem ngp_ray_out {φ : Pl → ℝ} (hc : HasCompactSupport φ) :
    ∃ M : ℝ, ∀ (θ r : ℝ), M < |r| → ngpPt (r * Real.cos θ) (r * Real.sin θ) ∉ tsupport φ := by
  obtain ⟨R, hR⟩ := hc.isCompact.isBounded.subset_closedBall 0
  refine ⟨2 * |R| + 1, fun θ r hr hmem => ?_⟩
  have h1 := hR hmem
  rw [Metric.mem_closedBall, dist_zero_right] at h1
  have h0 : |r * Real.cos θ| ≤ R := by
    have h := norm_le_pi_norm (ngpPt (r * Real.cos θ) (r * Real.sin θ)) 0
    rw [ngp_apply0, Real.norm_eq_abs] at h
    linarith
  have h2 : |r * Real.sin θ| ≤ R := by
    have h := norm_le_pi_norm (ngpPt (r * Real.cos θ) (r * Real.sin θ)) 1
    rw [ngp_apply1, Real.norm_eq_abs] at h
    linarith
  have a1 : (r * Real.cos θ) ^ 2 ≤ R ^ 2 := by
    have := pow_le_pow_left₀ (abs_nonneg _) h0 2
    rwa [sq_abs] at this
  have a2 : (r * Real.sin θ) ^ 2 ≤ R ^ 2 := by
    have := pow_le_pow_left₀ (abs_nonneg _) h2 2
    rwa [sq_abs] at this
  have e := Real.sin_sq_add_cos_sq θ
  have hsum : r ^ 2 = (r * Real.cos θ) ^ 2 + (r * Real.sin θ) ^ 2 := by
    linear_combination (-(r ^ 2)) * e
  have hsq : r ^ 2 ≤ 2 * R ^ 2 := by linarith
  have hpos : 0 ≤ 2 * |R| + 1 := by positivity
  have hr2 : (2 * |R| + 1) ^ 2 < r ^ 2 := by
    nlinarith [sq_abs r, abs_nonneg r]
  nlinarith [sq_abs R, abs_nonneg R]

theorem ngpD_zero {φ : Pl → ℝ} {M : ℝ}
    (hM : ∀ (θ r : ℝ), M < |r| → ngpPt (r * Real.cos θ) (r * Real.sin θ) ∉ tsupport φ)
    (θ r : ℝ) (hr : M < |r|) : ngpD φ r θ = 0 := by
  have hx := hM θ r hr
  have h0 : fderiv ℝ φ (ngpPt (r * Real.cos θ) (r * Real.sin θ)) = 0 := by
    by_contra h
    exact hx (support_fderiv_subset (𝕜 := ℝ) (Function.mem_support.2 h))
  unfold ngpD
  rw [h0]
  simp

theorem ngpD_radial {φ : Pl → ℝ} (hφ : ContDiff ℝ ∞ φ) (θ r : ℝ) :
    HasDerivAt (fun s : ℝ => φ (ngpPt (s * Real.cos θ) (s * Real.sin θ))) (ngpD φ r θ) r := by
  have hline : HasDerivAt (fun s : ℝ => ngpPt (s * Real.cos θ) (s * Real.sin θ))
      (ngpPt (Real.cos θ) (Real.sin θ)) r := by
    rw [hasDerivAt_pi]
    intro i
    fin_cases i
    · simpa [ngpPt] using (hasDerivAt_id' r).mul_const (Real.cos θ)
    · simpa [ngpPt] using (hasDerivAt_id' r).mul_const (Real.sin θ)
  exact (hφ.differentiable (by simp) (ngpPt (r * Real.cos θ) (r * Real.sin θ))).hasFDerivAt.comp_hasDerivAt
    r hline

theorem ngp_cont_ray_r (θ : ℝ) :
    Continuous (fun s : ℝ => ngpPt (s * Real.cos θ) (s * Real.sin θ)) := by
  refine continuous_pi fun i => ?_
  fin_cases i <;> simp [ngpPt] <;> fun_prop

theorem ngp_cont_ray : Continuous (fun p : ℝ × ℝ => ngpPt (p.1 * Real.cos p.2) (p.1 * Real.sin p.2)) := by
  refine continuous_pi fun i => ?_
  fin_cases i <;> simp [ngpPt] <;> fun_prop

theorem ngpD_cont {φ : Pl → ℝ} (hφ : ContDiff ℝ ∞ φ) :
    Continuous (fun p : ℝ × ℝ => ngpD φ p.1 p.2) := by
  have hv : Continuous (fun p : ℝ × ℝ => ngpPt (Real.cos p.2) (Real.sin p.2)) := by
    refine continuous_pi fun i => ?_
    fin_cases i <;> simp [ngpPt] <;> fun_prop
  have hfd : Continuous (fderiv ℝ φ) := hφ.continuous_fderiv (by simp)
  exact (((hfd.comp ngp_cont_ray)).clm_apply hv)

/-- The pointwise polar identity: `r · ∇N·∇φ(r(cos θ, sin θ)) = (2π)⁻¹ ∂_{(cos θ, sin θ)} φ`. -/
theorem ngp_pointwise (φ : Pl → ℝ) {r : ℝ} (hr : 0 < r) (θ : ℝ) :
    r * ngpG φ (ngpPt (r * Real.cos θ) (r * Real.sin θ)) = (2 * Real.pi)⁻¹ * ngpD φ r θ := by
  have hden : (r * Real.cos θ) ^ 2 + (r * Real.sin θ) ^ 2 = r ^ 2 := by
    linear_combination r ^ 2 * (Real.sin_sq_add_cos_sq θ)
  have hsplit : ngpPt (Real.cos θ) (Real.sin θ) =
      Real.cos θ • (Pi.single 0 1 : Pl) + Real.sin θ • (Pi.single 1 1 : Pl) := by
    funext i
    fin_cases i <;> simp [ngpPt]
  have hr0 : r ≠ 0 := hr.ne'
  unfold ngpG ngpD pd
  rw [hsplit, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
  simp only [newtonGradKernel, ngp_apply0, ngp_apply1]
  rw [hden]
  field_simp

/-- Radial integral: `∫_{(0,∞)} ∂_r φ(r(cos θ, sin θ)) dr = -φ(0)`. -/
theorem ngp_radial_integral {φ : Pl → ℝ} (hφ : IsTest φ) (θ : ℝ) :
    ∫ r in Ioi (0 : ℝ), ngpD φ r θ = -φ 0 := by
  obtain ⟨hs, hc⟩ := hφ
  obtain ⟨M, hM⟩ := ngp_ray_out hc
  have hΦc : Continuous (fun s : ℝ => φ (ngpPt (s * Real.cos θ) (s * Real.sin θ))) :=
    hs.continuous.comp (ngp_cont_ray_r θ)
  have hDc : Continuous (fun r : ℝ => ngpD φ r θ) :=
    (ngpD_cont hs).comp (continuous_id.prodMk continuous_const)
  have hDcs : HasCompactSupport (fun r : ℝ => ngpD φ r θ) := by
    refine HasCompactSupport.intro (isCompact_Icc (a := -M) (b := M)) fun r hr => ?_
    have hr' : M < |r| := by
      by_contra h
      apply hr
      exact abs_le.1 (not_lt.1 h)
    exact ngpD_zero hM θ r hr'
  have hT : Tendsto (fun s : ℝ => φ (ngpPt (s * Real.cos θ) (s * Real.sin θ))) atTop (𝓝 0) := by
    refine (tendsto_const_nhds (x := (0 : ℝ))).congr' ?_
    refine Filter.eventually_atTop.2 ⟨M + 1, fun r hr => ?_⟩
    have hr' : M < |r| := lt_of_lt_of_le (by linarith) (le_abs_self r)
    have hx := hM θ r hr'
    exact (image_eq_zero_of_notMem_tsupport hx).symm
  have key : ∫ r in Ioi (0 : ℝ), ngpD φ r θ = 0 - φ (ngpPt (0 * Real.cos θ) (0 * Real.sin θ)) :=
    integral_Ioi_of_hasDerivAt_of_tendsto
    (f := fun s : ℝ => φ (ngpPt (s * Real.cos θ) (s * Real.sin θ)))
    (f' := fun r => ngpD φ r θ) hΦc.continuousWithinAt
    (fun x _ => ngpD_radial hs θ x) (Continuous.integrable_of_hasCompactSupport hDc hDcs).integrableOn
    hT
  rw [key, ngp_zero θ]
  simp

/-- Integrability of the polar integrand on the rectangle `(0,∞) × (-π, π)`. -/
theorem ngpF_integrableOn {φ : Pl → ℝ} (hφ : IsTest φ) {M : ℝ}
    (hM : ∀ (θ r : ℝ), M < |r| → ngpPt (r * Real.cos θ) (r * Real.sin θ) ∉ tsupport φ) :
    IntegrableOn (ngpF φ) (Ioi (0 : ℝ) ×ˢ Ioo (-Real.pi) Real.pi) := by
  have hfc : Continuous (ngpF φ) := continuous_const.mul (ngpD_cont hφ.1)
  have hK1 : IntegrableOn (ngpF φ) (Icc (0 : ℝ) M ×ˢ Icc (-Real.pi) Real.pi) :=
    ContinuousOn.integrableOn_compact ((isCompact_Icc).prod isCompact_Icc) hfc.continuousOn
  refine IntegrableOn.of_forall_sdiff_eq_zero hK1 (measurableSet_Ioi.prod measurableSet_Ioo) ?_
  intro x hx
  have hxT : x ∈ Ioi (0 : ℝ) ×ˢ Ioo (-Real.pi) Real.pi := hx.1
  have hxK : x ∉ Icc (0 : ℝ) M ×ˢ Icc (-Real.pi) Real.pi := hx.2
  have hx1 : M < |x.1| := by
    by_contra h
    apply hxK
    have h' := abs_le.1 (not_lt.1 h)
    exact ⟨⟨(show (0 : ℝ) < x.1 from hxT.1).le, h'.2⟩,
      ⟨(show -Real.pi < x.2 from hxT.2.1).le, (show x.2 < Real.pi from hxT.2.2).le⟩⟩
  show (2 * Real.pi)⁻¹ * ngpD φ x.1 x.2 = 0
  rw [ngpD_zero hM x.2 x.1 hx1, mul_zero]

/-- **Leaf `PartII-b:T12/1/1/2/5`.**  `∫ ∇N · ∇φ = -φ(0)` for a planar test `φ`. -/
theorem newtonGradKernelPolar : NewtonGradKernelPolar := by
  intro φ hφ
  obtain ⟨M, hM⟩ := ngp_ray_out hφ.2
  have hint := ngpF_integrableOn hφ hM
  have hfub : ∫ p in Ioi (0 : ℝ) ×ˢ Ioo (-Real.pi) Real.pi, ngpF φ p =
      ∫ θ in Ioo (-Real.pi) Real.pi, ∫ r in Ioi (0 : ℝ), ngpF φ (r, θ) := by
    refine (setIntegral_prod (ngpF φ) hint).trans ?_
    exact integral_integral_swap (by rw [Measure.prod_restrict]; exact hint)
  have hin : ∀ θ : ℝ, ∫ r in Ioi (0 : ℝ), ngpF φ (r, θ) = (2 * Real.pi)⁻¹ * (-φ 0) := by
    intro θ
    have h := ngp_radial_integral hφ θ
    simp only [ngpF]
    rw [integral_const_mul, h]
  have hpol : ∫ p : ℝ × ℝ, ngpG φ (ngpPt p.1 p.2) =
      ∫ p in polarCoord.target, p.1 * ngpG φ (ngpPt (p.1 * Real.cos p.2) (p.1 * Real.sin p.2)) := by
    have := integral_comp_polarCoord_symm (fun p : ℝ × ℝ => ngpG φ (ngpPt p.1 p.2))
    simp only [smul_eq_mul] at this
    exact this.symm
  show ∫ y, ngpG φ y = -φ 0
  calc ∫ y, ngpG φ y = ∫ p : ℝ × ℝ, ngpG φ (ngpPt p.1 p.2) := ngp_integral_plane _
    _ = ∫ p in polarCoord.target, p.1 * ngpG φ (ngpPt (p.1 * Real.cos p.2) (p.1 * Real.sin p.2)) :=
        hpol
    _ = ∫ p in Ioi (0 : ℝ) ×ˢ Ioo (-Real.pi) Real.pi, ngpF φ p :=
        setIntegral_congr_fun (measurableSet_Ioi.prod measurableSet_Ioo)
          (fun p hp => ngp_pointwise φ hp.1 p.2)
    _ = ∫ θ in Ioo (-Real.pi) Real.pi, ∫ r in Ioi (0 : ℝ), ngpF φ (r, θ) := hfub
    _ = ∫ θ in Ioo (-Real.pi) Real.pi, (2 * Real.pi)⁻¹ * (-φ 0) :=
        setIntegral_congr_fun measurableSet_Ioo (fun θ _ => hin θ)
    _ = -φ 0 := by
        rw [setIntegral_const, Real.volume_real_Ioo_of_le (by linarith [Real.pi_pos]), smul_eq_mul]
        have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
        field_simp
        try ring

end UnforcedLeray.Short.IIb.PlaneRiesz
