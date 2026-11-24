import UnforcedLeray.Short.PartI.StatementsSeed
import UnforcedLeray.Units.B0090
import UnforcedLeray.Lib.PlanarSectors.Green
import UnforcedLeray.Lib.PlanarSectors.XG

/-!
# Part I, task `PartI:S07`: the explicit adjoint eigenvector

Source of record: `the November 2 reference manuscript`, lines 890-912
(`h_X = G conj(phi)/(Omega - conj c) e^{2i theta}`, `L_0^* h_X = conj(lam) h_X`, `c = i lam / 2`).

Proof outline (with `g = f` the profile of the seed `q`, `phi = greenN 2 g`, `V = x - 2`,
`k = V Omega`, `G = (4 pi)^{-1} Omega`, `D = Omega - conj c`):
* the eigen equation `L_0 q = lam q` gives `(Omega - c) g = k phi` a.e.;
* conjugating, `D conj(g) = k conj(phi)`, so `V gd = (4 pi)^{-1} conj(g)` a.e.;
* `R` has a real kernel, so `R(V gd) = (4 pi)^{-1} conj(phi)` for `r > 0`;
* the adjoint formula `L_0^* h = 2 i Omega (h - R(V h))` then gives `L_0^* gd = conj(lam) gd`;
* `|D| >= Re(lam)/2 > 0` and `|phi| <= K` give `gd` in `X_G`; `gd = 0` forces `g = 0`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Real
open scoped ENNReal NNReal ComplexConjugate ContDiff Topology

namespace UnforcedLeray.Short.PartI

open UnforcedLeray.GaussianVortex (radialOmega radialK radialOmega_pos)

/-- `Im (Ω - conj(iλ/2)) = Re λ / 2`. -/
theorem adjEig_im_den_conj (lam : ℂ) (w : ℝ) :
    ((w : ℂ) - starRingEnd ℂ (Complex.I * lam / 2)).im = lam.re / 2 := by
  simp only [Complex.sub_im, Complex.conj_im, Complex.ofReal_im, Complex.div_ofNat_im,
    Complex.mul_im, Complex.I_re, Complex.I_im]
  ring

/-- `Im (Ω - iλ/2) = -Re λ / 2`. -/
theorem adjEig_im_den (lam : ℂ) (w : ℝ) :
    ((w : ℂ) - Complex.I * lam / 2).im = -(lam.re / 2) := by
  simp [Complex.div_ofNat_im]

theorem adjEig_den_conj_ne {lam : ℂ} (hre : 0 < lam.re) (w : ℝ) :
    (w : ℂ) - starRingEnd ℂ (Complex.I * lam / 2) ≠ 0 := by
  intro h0
  have h1 := adjEig_im_den_conj lam w
  rw [h0, Complex.zero_im] at h1
  linarith

theorem adjEig_den_ne {lam : ℂ} (hre : 0 < lam.re) (w : ℝ) :
    (w : ℂ) - Complex.I * lam / 2 ≠ 0 := by
  intro h0
  have h1 := adjEig_im_den lam w
  rw [h0, Complex.zero_im] at h1
  linarith

theorem adjEig_two_I_conj (lam : ℂ) :
    2 * Complex.I * starRingEnd ℂ (Complex.I * lam / 2) = starRingEnd ℂ lam := by
  simp only [map_div₀, map_mul, Complex.conj_I, map_ofNat]
  linear_combination (-(starRingEnd ℂ lam)) * Complex.I_sq

/-- `greenN 2` depends only on the class of the profile on `(0, ∞)`. -/
theorem adjEig_greenN_congr {g₁ g₂ : ℝ → ℂ}
    (hg : g₁ =ᵐ[volume.restrict (Ioi (0 : ℝ))] g₂) (r : ℝ) :
    Planar.greenN 2 g₁ r = Planar.greenN 2 g₂ r := by
  unfold Planar.greenN
  congr 1
  refine integral_congr_ae ?_
  filter_upwards [hg] with ρ hρ
  rw [hρ]

/-- Pointwise eigen equation: `(Ω - iλ/2) f = k greenN 2 f` a.e. (from `L_0 f = λ f`). -/
theorem adjEig_pointwise {lam : ℂ} {f : B0010.XG} (he : Planar.L0 f = lam • f) :
    ∀ᵐ r ∂B0010.xGMeasure,
      ((radialOmega r : ℂ) - Complex.I * lam / 2) * f r =
        (radialK r : ℂ) * Planar.greenN 2 (⇑f) r := by
  filter_upwards [Planar.coeFn_L0 f, Lp.coeFn_smul lam f] with r h1 h2
  rw [he] at h1
  simp only [Pi.smul_apply, smul_eq_mul] at h2
  rw [h2] at h1
  have key : 2 * Complex.I * (((radialOmega r : ℂ) - Complex.I * lam / 2) * f r -
      (radialK r : ℂ) * Planar.greenN 2 (⇑f) r) = 0 := by
    linear_combination h1 + (-(lam * f r)) * Complex.I_sq
  have h3 := (mul_eq_zero.1 key).resolve_left (mul_ne_zero two_ne_zero Complex.I_ne_zero)
  exact sub_eq_zero.1 h3

/-- Conjugate eigen equation: `(Ω - conj(iλ/2)) conj f = k conj(greenN 2 f)` a.e. -/
theorem adjEig_conj {lam : ℂ} {f : B0010.XG} (he : Planar.L0 f = lam • f) :
    ∀ᵐ r ∂B0010.xGMeasure,
      ((radialOmega r : ℂ) - starRingEnd ℂ (Complex.I * lam / 2)) * starRingEnd ℂ (f r) =
        (radialK r : ℂ) * starRingEnd ℂ (Planar.greenN 2 (⇑f) r) := by
  filter_upwards [adjEig_pointwise he] with r hr
  have := congrArg (starRingEnd ℂ) hr
  simpa only [map_mul, map_sub, Complex.conj_ofReal] using this

/-- The explicit adjoint eigenvector (source lines 890-912), in the form of the statement
(`(4π)⁻¹ Ω conj(greenN 2 f) / (Ω - conj(iλ/2))`). -/
def seedAdjEig (f : B0010.XG) (lam : ℂ) : ℝ → ℂ := fun r =>
  (((4 * π)⁻¹ * radialOmega r : ℝ) : ℂ) * starRingEnd ℂ (Planar.greenN 2 (⇑f) r) /
    ((radialOmega r : ℂ) - starRingEnd ℂ (Complex.I * lam / 2))

/-- `V gd = (4π)⁻¹ conj f` a.e. -/
theorem seedAdjEig_mul_V {lam : ℂ} (hre : 0 < lam.re) {f : B0010.XG}
    (he : Planar.L0 f = lam • f) :
    ∀ᵐ r ∂B0010.xGMeasure,
      (B0090.V r : ℂ) * seedAdjEig f lam r = (((4 * π)⁻¹ : ℝ) : ℂ) * starRingEnd ℂ (f r) := by
  filter_upwards [adjEig_conj he] with r hr
  have hD := adjEig_den_conj_ne hre (radialOmega r)
  rw [B0090.radialK_eq_V_mul_omega] at hr
  simp only [seedAdjEig]
  rw [mul_div_assoc', div_eq_iff hD]
  push_cast at hr ⊢
  linear_combination (-((4 * (π : ℂ))⁻¹)) * hr

/-- The Green operator applied to `V gd`, for `r > 0`. -/
theorem seedAdjEig_R {lam : ℂ} (hre : 0 < lam.re) {f : B0010.XG}
    (he : Planar.L0 f = lam • f) {r : ℝ} (hr : 0 < r) :
    B0011.R (fun s => (B0090.V s : ℂ) * seedAdjEig f lam s) r =
      (((4 * π)⁻¹ : ℝ) : ℂ) * starRingEnd ℂ (Planar.greenN 2 (⇑f) r) := by
  have hae : (fun s => (B0090.V s : ℂ) * seedAdjEig f lam s) =ᵐ[volume.restrict (Ioi (0 : ℝ))]
      (fun s => (((4 * π)⁻¹ : ℝ) : ℂ) * starRingEnd ℂ (f s)) :=
    B0012.restrict_ac.ae_le (seedAdjEig_mul_V hre he)
  rw [B0012.R_congr hae hr, B0012.R_const_mul, B0090.R_conj (B0012.wprof_coe f) hr,
    Planar.greenN_two_eq_R (B0012.wprof_coe f) hr]

/-- Pointwise norm bound for the explicit eigenvector. -/
theorem adjEig_norm_le {lam : ℂ} (hre : 0 < lam.re) (w K : ℝ) (hw : 0 ≤ w) (hK : 0 ≤ K)
    (G : ℂ) (hG : ‖G‖ ≤ K) :
    ‖(((4 * π)⁻¹ * w : ℝ) : ℂ) * starRingEnd ℂ G /
        ((w : ℂ) - starRingEnd ℂ (Complex.I * lam / 2))‖ ≤
      2 * K / lam.re * ((4 * π)⁻¹ * w) := by
  have ha : 0 ≤ (4 * π)⁻¹ * w := mul_nonneg (by positivity) hw
  have hD : lam.re / 2 ≤ ‖(w : ℂ) - starRingEnd ℂ (Complex.I * lam / 2)‖ := by
    have h1 := Complex.abs_im_le_norm ((w : ℂ) - starRingEnd ℂ (Complex.I * lam / 2))
    rw [adjEig_im_den_conj] at h1
    exact le_trans (le_abs_self _) h1
  have hDpos : 0 < ‖(w : ℂ) - starRingEnd ℂ (Complex.I * lam / 2)‖ :=
    lt_of_lt_of_le (half_pos hre) hD
  rw [norm_div, norm_mul, Complex.norm_real, Real.norm_of_nonneg ha, Complex.norm_conj]
  rw [div_le_iff₀ hDpos]
  have hc : 0 ≤ 2 * K / lam.re := div_nonneg (by linarith) hre.le
  have h1 : 2 * K / lam.re * (lam.re / 2) = K := by
    field_simp
  have h2 : K ≤ 2 * K / lam.re * ‖(w : ℂ) - starRingEnd ℂ (Complex.I * lam / 2)‖ := by
    calc K = 2 * K / lam.re * (lam.re / 2) := h1.symm
      _ ≤ 2 * K / lam.re * ‖(w : ℂ) - starRingEnd ℂ (Complex.I * lam / 2)‖ :=
        mul_le_mul_of_nonneg_left hD hc
  calc (4 * π)⁻¹ * w * ‖G‖ ≤ (4 * π)⁻¹ * w * K := mul_le_mul_of_nonneg_left hG ha
    _ ≤ (4 * π)⁻¹ * w * (2 * K / lam.re * ‖(w : ℂ) - starRingEnd ℂ (Complex.I * lam / 2)‖) :=
        mul_le_mul_of_nonneg_left h2 ha
    _ = 2 * K / lam.re * ((4 * π)⁻¹ * w) *
        ‖(w : ℂ) - starRingEnd ℂ (Complex.I * lam / 2)‖ := by ring

/-- `gd` lies in `X_G`. -/
theorem seedAdjEig_memLp {lam : ℂ} (hre : 0 < lam.re) (f : B0010.XG) :
    MemLp (seedAdjEig f lam) 2 B0010.xGMeasure := by
  have hmeasG : AEStronglyMeasurable (fun r => Planar.greenN 2 (⇑f) r) B0010.xGMeasure := by
    refine (B0012.aesm_R f).congr ?_
    filter_upwards [B0012.ae_xG_pos] with r hr
    exact (Planar.greenN_two_eq_R (B0012.wprof_coe f) hr).symm
  have hcont1 : Continuous (fun r : ℝ => (((4 * π)⁻¹ * radialOmega r : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.comp (continuous_const.mul B0012.continuous_radialOmega)
  have hcont2 : Continuous (fun r : ℝ => (radialOmega r : ℂ) - starRingEnd ℂ (Complex.I * lam / 2)) :=
    (Complex.continuous_ofReal.comp B0012.continuous_radialOmega).sub continuous_const
  have hcont3 : Continuous (fun r : ℝ =>
      ((radialOmega r : ℂ) - starRingEnd ℂ (Complex.I * lam / 2))⁻¹) :=
    hcont2.inv₀ (fun r => adjEig_den_conj_ne hre (radialOmega r))
  have hmeas : AEStronglyMeasurable (seedAdjEig f lam) B0010.xGMeasure := by
    have hprod : AEStronglyMeasurable (fun r : ℝ =>
        (((4 * π)⁻¹ * radialOmega r : ℝ) : ℂ) * starRingEnd ℂ (Planar.greenN 2 (⇑f) r) *
          ((radialOmega r : ℂ) - starRingEnd ℂ (Complex.I * lam / 2))⁻¹) B0010.xGMeasure :=
      ((hcont1.aestronglyMeasurable).mul
        (Complex.continuous_conj.comp_aestronglyMeasurable hmeasG)).mul hcont3.aestronglyMeasurable
    refine hprod.congr (ae_of_all _ fun r => ?_)
    simp only [seedAdjEig, div_eq_mul_inv]
  have hK : ∀ r : ℝ, 0 < r → ‖Planar.greenN 2 (⇑f) r‖ ≤ 1 / 4 * ‖B0012.gaussLp‖ * ‖f‖ := by
    intro r hr
    rw [Planar.greenN_two_eq_R (B0012.wprof_coe f) hr]
    exact B0012.norm_R_coe_le f hr
  have hK0 : 0 ≤ 1 / 4 * ‖B0012.gaussLp‖ * ‖f‖ := by positivity
  refine ((B0012.memLp_gauss.const_smul ((2 * (1 / 4 * ‖B0012.gaussLp‖ * ‖f‖) / lam.re : ℝ) : ℂ))).of_le
    hmeas ?_
  filter_upwards [B0012.ae_xG_pos] with r hr
  have hb := adjEig_norm_le hre (radialOmega r) (1 / 4 * ‖B0012.gaussLp‖ * ‖f‖)
    (radialOmega_pos r).le hK0 (Planar.greenN 2 (⇑f) r) (hK r hr)
  have hC0 : 0 ≤ 2 * (1 / 4 * ‖B0012.gaussLp‖ * ‖f‖) / lam.re :=
    div_nonneg (by linarith [hK0]) hre.le
  have hrg : 0 ≤ B0010.radialGaussianWeight r := mul_nonneg (by positivity) (radialOmega_pos r).le
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hC0, Complex.norm_real,
    Real.norm_of_nonneg hrg]
  exact hb

/-- The adjoint identity `L_0^* gd = conj(lam) gd`. -/
theorem seedAdjEig_adjoint {lam : ℂ} (hre : 0 < lam.re) {f : B0010.XG}
    (he : Planar.L0 f = lam • f) :
    ContinuousLinearMap.adjoint Planar.L0 ((seedAdjEig_memLp hre f).toLp (seedAdjEig f lam)) =
      (starRingEnd ℂ) lam • (seedAdjEig_memLp hre f).toLp (seedAdjEig f lam) := by
  have e1 : (Planar.L0 : B0010.XG →L[ℂ] B0010.XG) = B0012.L0 := rfl
  rw [e1, B0090.adjoint_L0_toLp (seedAdjEig_memLp hre f)]
  refine Lp.ext ?_
  filter_upwards [(B0090.memLp_L0AdjFun (seedAdjEig_memLp hre f)).coeFn_toLp,
    Lp.coeFn_smul (starRingEnd ℂ lam) ((seedAdjEig_memLp hre f).toLp (seedAdjEig f lam)),
    (seedAdjEig_memLp hre f).coeFn_toLp, B0012.ae_xG_pos] with r h1 h2 h3 hpos
  rw [h1, h2, Pi.smul_apply, smul_eq_mul, h3, B0090.L0AdjFun, seedAdjEig_R hre he hpos]
  simp only [seedAdjEig]
  have hD := adjEig_den_conj_ne hre (radialOmega r)
  rw [← adjEig_two_I_conj lam]
  push_cast
  field_simp
  ring

/-- The eigenvector is nonzero when `f ≠ 0`. -/
theorem seedAdjEig_ne_zero {lam : ℂ} (hre : 0 < lam.re) {f : B0010.XG} (hf : f ≠ 0)
    (he : Planar.L0 f = lam • f) :
    (seedAdjEig_memLp hre f).toLp (seedAdjEig f lam) ≠ 0 := by
  intro hz
  have h0 : ⇑((seedAdjEig_memLp hre f).toLp (seedAdjEig f lam)) =ᵐ[B0010.xGMeasure] (0 : ℝ → ℂ) := by
    rw [hz]
    exact Lp.coeFn_zero _ _ _
  have hg0 : seedAdjEig f lam =ᵐ[B0010.xGMeasure] 0 :=
    (seedAdjEig_memLp hre f).coeFn_toLp.symm.trans h0
  have hf0 : (⇑f) =ᵐ[B0010.xGMeasure] 0 := by
    filter_upwards [hg0, B0012.ae_xG_pos, adjEig_pointwise he] with r hgr hpos hA
    have hD := adjEig_den_conj_ne hre (radialOmega r)
    have hpos' : (0 : ℝ) < (4 * π)⁻¹ * radialOmega r :=
      mul_pos (by positivity) (radialOmega_pos r)
    have hc : (((4 * π)⁻¹ * radialOmega r : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hpos'.ne'
    simp only [seedAdjEig, Pi.zero_apply] at hgr
    have hG' : starRingEnd ℂ (Planar.greenN 2 (⇑f) r) = 0 := by
      rcases div_eq_zero_iff.1 hgr with h | h
      · exact (mul_eq_zero.1 h).resolve_left hc
      · exact absurd h hD
    have hG : Planar.greenN 2 (⇑f) r = 0 := by
      simpa using congrArg (starRingEnd ℂ) hG'
    rw [hG, mul_zero] at hA
    exact (mul_eq_zero.1 hA).resolve_left (adjEig_den_ne hre (radialOmega r))
  exact hf (Lp.ext (hf0.trans (Lp.coeFn_zero _ _ _).symm))

/-- **Explicit adjoint eigenvector** (source lines 890-912). -/
theorem adjoint_L0_explicit_eigenvector {lam : ℂ} {h : ℝ → ℂ} {hh : MemLp h 2 B0010.xGMeasure} {l}
    (hI : IsSeedXG lam (hh.toLp h) l) (hs : ContDiffOn ℝ ∞ h (Set.Ioi 0)) :
    ∃ (gd : ℝ → ℂ) (hg : MemLp gd 2 B0010.xGMeasure),
      (∀ r, 0 < r → gd r = (((4 * π)⁻¹ * Blueprint.Planar.vortexOmega r : ℝ) : ℂ) *
        (starRingEnd ℂ) (Planar.greenN 2 h r) /
          (((Blueprint.Planar.vortexOmega r : ℝ) : ℂ) - (starRingEnd ℂ) (Complex.I * lam / 2))) ∧
      ContinuousLinearMap.adjoint Planar.L0 (hg.toLp gd) = (starRingEnd ℂ) lam • hg.toLp gd ∧
      hg.toLp gd ≠ 0 := by
  have hre : 0 < lam.re := hI.re_pos
  have hfh : (⇑(hh.toLp h) : ℝ → ℂ) =ᵐ[volume.restrict (Ioi (0 : ℝ))] h :=
    B0012.restrict_ac.ae_le hh.coeFn_toLp
  refine ⟨seedAdjEig (hh.toLp h) lam, seedAdjEig_memLp hre _, ?_,
    seedAdjEig_adjoint hre hI.eigen, seedAdjEig_ne_zero hre hI.ne_zero hI.eigen⟩
  intro r _hr
  have hv : Blueprint.Planar.vortexOmega r = radialOmega r := by
    unfold Blueprint.Planar.vortexOmega GaussianVortex.radialOmega
    congr 1
    ring
  simp only [seedAdjEig]
  rw [adjEig_greenN_congr hfh r, hv]

end UnforcedLeray.Short.PartI
