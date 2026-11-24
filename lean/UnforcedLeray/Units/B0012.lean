import UnforcedLeray.Units.B0010
import UnforcedLeray.Units.B0011

/-!
# B0012: the angular-two bounded generator `L₀` on `X_G` (`eq:st18-t00006`)

Blueprint unit B0012, label `eq:st18-t00006`, `paper/main.tex` lines 678--682 (dependencies
B0010 = `eq:st18-t00005`, the space `X_G`, and B0011 = `eq:st18-t00007`, the Green inverse `R`).

The manuscript says (lines 678--682): "The angular-two generator is bounded:
`L₀f = -2iΩf + 2ikRf`, `R = Δ₂⁻¹`", on the Gaussian space `X_G` of `eq:st18-t00005`, where
`Ω(r) = e^{-r²/4}` (`eq:st18-t00001`, line 639) and `k(r) = E₀'(r)/r = (x-2)e^{-x}`, `x = r²/4`
(`eq:st18-t00002`, line 647), and `R` is the Green formula `eq:st18-t00007` (lines 685--688).

**Formalization.**
* `X_G` is B0010's `XG = L²((0,∞), G(r)⁻¹ r dr; ℂ)` of radial profiles `f₂`; the angular factor
  `e^{2iϑ}` is common to `f` and `L₀f` (B0010 `angularTwoField`), so `L₀` acts on profiles.
* `L0Fun f r = -2iΩ(r) f(r) + 2ik(r) (Rf)(r)` is the manuscript formula on a profile, with
  `Ω = GaussianVortex.radialOmega`, `k = GaussianVortex.radialK` (library, unit B0007; note
  `radialK_eq_deriv_div`: `k = E₀'/r`), and `R = B0011.R` verbatim.
* `L0 : XG →L[ℂ] XG` is a continuous (= bounded) complex-linear operator, and `coeFn_L0` says
  that it is given a.e. by the formula: `L0 f = L0Fun f` a.e. Since `R f r` is defined by
  integrals over `(0,∞)`, it depends only on the class of `f` (`R_congr`); for `f ∈ X_G` both
  integrals converge absolutely (B0011 `WProf.integrable_R_parts`), so no junk value enters.
* The claim "`L₀` is bounded" is `L0_bounded` (operator form) and `L0Fun_bounded`,
  `L0Fun_integral_bound` (formula form: the formula maps every profile of `X_G` to a profile of
  `X_G`, with `∫₀^∞ |L₀f|² G⁻¹ r dr ≤ C² ∫₀^∞ |f|² G⁻¹ r dr`). `isDelta2Sol_R_coe` records that the
  `R` used here is the Green inverse `R = Δ₂⁻¹` of B0011.

**Proof route.** The blueprint (proof outline, tex lines 1415ff, `eq:st18-t00062`) uses
`|Rf(r)| ≤ C‖f‖ min(r, r⁻²)`. We only need the cruder uniform bound
`|Rf(r)| ≤ ¼ ‖G‖_{X_G} ‖f‖_{X_G}` (`norm_R_coe_le`): by B0011 `R_eq_kernel`,
`Rf(r) = -¼ ∫₀^∞ (min(r,s)/max(r,s))² s f(s) ds = -¼ ⟨f, h_r⟩_{X_G}` with
`h_r(s) = (min(r,s)/max(r,s))² G(s)`, `|h_r| ≤ G`, and Cauchy–Schwarz. Then
`|k Rf| ≤ ¼‖G‖‖f‖ |k|` and `k ∈ X_G` (`|k|²G⁻¹r` is a polynomial times a Gaussian) give
`‖kRf‖ ≤ ¼‖G‖‖k‖‖f‖`; multiplication by `Ω ∈ (0,1]` has norm at most `1`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal NNReal ComplexConjugate

namespace UnforcedLeray.B0012

open B0010 B0011 GaussianVortex

/-! ## Measure-theoretic preliminaries on `X_G` -/

/-- `G(r)⁻¹ r dr` on `(0, ∞)` is absolutely continuous with respect to `dr` on `(0, ∞)`. -/
theorem xG_ac : xGMeasure ≪ volume.restrict (Ioi (0 : ℝ)) :=
  withDensity_absolutelyContinuous _ _

/-- `dr` on `(0, ∞)` is absolutely continuous with respect to `G(r)⁻¹ r dr` (the density is
positive on `(0, ∞)`), so `X_G`-classes determine profiles a.e. on `(0, ∞)`. -/
theorem restrict_ac : volume.restrict (Ioi (0 : ℝ)) ≪ xGMeasure := by
  refine withDensity_absolutelyContinuous' measurable_xGDensity.coe_nnreal_ennreal.aemeasurable ?_
  refine ae_restrict_of_forall_mem measurableSet_Ioi fun r hr => ?_
  have hr' : (0 : ℝ) < r := hr
  refine ENNReal.coe_ne_zero.2 fun h => ?_
  have h2 := coe_xGDensity hr'
  rw [h, NNReal.coe_zero] at h2
  exact (mul_pos (inv_pos.2 (radialGaussianWeight_pos r)) hr').ne h2

theorem ae_xG_pos : ∀ᵐ r ∂xGMeasure, (0 : ℝ) < r :=
  xG_ac.ae_le (ae_restrict_mem measurableSet_Ioi)

/-- An element of `X_G` is measurable on `(0, ∞)` for Lebesgue measure. -/
theorem aesm_coe (f : XG) : AEStronglyMeasurable (⇑f) (volume.restrict (Ioi (0 : ℝ))) :=
  (Lp.aestronglyMeasurable f).mono_ac restrict_ac

/-- Every element of `X_G` (B0010) satisfies B0011's defining condition `MemXG`. -/
theorem memXG_coe (f : XG) : MemXG ⇑f := by
  refine ⟨aesm_coe f, ?_⟩
  have h := (memLp_iff_integrableOn (aesm_coe f)).1 (Lp.memLp f)
  refine h.congr (ae_of_all _ fun r => ?_)
  simp only [gaussG, radialGaussianWeight]
  ring

theorem wprof_coe (f : XG) : WProf ⇑f := (memXG_coe f).wprof

/-! ## Algebraic properties of the Green formula `R` (B0011, `eq:st18-t00007`) -/

/-- `R f r` (`r > 0`) only depends on the values of `f` a.e. on `(0, ∞)`. -/
theorem R_congr {f g : ℝ → ℂ} (h : f =ᵐ[volume.restrict (Ioi (0 : ℝ))] g) {r : ℝ}
    (hr : 0 < r) : R f r = R g r := by
  have h' : ∀ᵐ s ∂(volume : Measure ℝ), s ∈ Ioi (0 : ℝ) → f s = g s :=
    (ae_restrict_iff' measurableSet_Ioi).1 h
  have e1 : ∫ s in (0 : ℝ)..r, (s : ℂ) ^ 3 * f s = ∫ s in (0 : ℝ)..r, (s : ℂ) ^ 3 * g s := by
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards [h'] with s hs hmem
    rw [uIoc_of_le hr.le] at hmem
    rw [hs hmem.1]
  have e2 : ∫ s in Ioi r, (s : ℂ)⁻¹ * f s = ∫ s in Ioi r, (s : ℂ)⁻¹ * g s := by
    refine setIntegral_congr_ae measurableSet_Ioi ?_
    filter_upwards [h'] with s hs hmem
    rw [hs (lt_trans hr hmem)]
  simp only [R]
  rw [e1, e2]

/-- `R` is additive on profiles with `r f(r) ∈ L¹(0,∞)` (B0011 `WProf`), at every `r > 0`. -/
theorem R_add {f g : ℝ → ℂ} (hf : WProf f) (hg : WProf g) {r : ℝ} (hr : 0 < r) :
    R (fun s => f s + g s) r = R f r + R g r := by
  obtain ⟨hf1, hf2⟩ := hf.integrable_R_parts hr
  obtain ⟨hg1, hg2⟩ := hg.integrable_R_parts hr
  have e1 : ∫ s in (0 : ℝ)..r, (s : ℂ) ^ 3 * (f s + g s) =
      (∫ s in (0 : ℝ)..r, (s : ℂ) ^ 3 * f s) + ∫ s in (0 : ℝ)..r, (s : ℂ) ^ 3 * g s := by
    rw [← intervalIntegral.integral_add hf1 hg1]
    simp only [mul_add]
  have e2 : ∫ s in Ioi r, (s : ℂ)⁻¹ * (f s + g s) =
      (∫ s in Ioi r, (s : ℂ)⁻¹ * f s) + ∫ s in Ioi r, (s : ℂ)⁻¹ * g s := by
    rw [← integral_add hf2 hg2]
    simp only [mul_add]
  simp only [R]
  rw [e1, e2]
  ring

/-- `R` is complex-homogeneous (no hypothesis needed). -/
theorem R_const_mul (c : ℂ) (f : ℝ → ℂ) (r : ℝ) : R (fun s => c * f s) r = c * R f r := by
  have e1 : ∫ s in (0 : ℝ)..r, (s : ℂ) ^ 3 * (c * f s) =
      c * ∫ s in (0 : ℝ)..r, (s : ℂ) ^ 3 * f s := by
    rw [← intervalIntegral.integral_const_mul]
    congr 1
    ext s
    ring
  have e2 : ∫ s in Ioi r, (s : ℂ)⁻¹ * (c * f s) = c * ∫ s in Ioi r, (s : ℂ)⁻¹ * f s := by
    rw [← integral_const_mul]
    congr 1
    ext s
    ring
  simp only [R]
  rw [e1, e2]
  ring

/-- For `f ∈ X_G`, `R f` is continuous on `(0, ∞)` (it is differentiable there, B0011). -/
theorem continuousOn_R (f : XG) : ContinuousOn (R ⇑f) (Ioi 0) := by
  obtain ⟨ψ', hd, -, -⟩ := (wprof_coe f).isDelta2Sol_R
  exact fun r hr => (hd r hr).continuousAt.continuousWithinAt

theorem aesm_R (f : XG) : AEStronglyMeasurable (R ⇑f) xGMeasure :=
  ((continuousOn_R f).aestronglyMeasurable measurableSet_Ioi).mono_ac xG_ac

/-- The `R` of `L₀` is the Green inverse `R = Δ₂⁻¹` of B0011 (tex line 680): for `f ∈ X_G`,
`R f` solves `Δ₂(Rf) = f` on `(0, ∞)` (integrated form, B0011 `IsDelta2Sol`). -/
theorem isDelta2Sol_R_coe (f : XG) : IsDelta2Sol ⇑f (R ⇑f) :=
  isDelta2Sol_R (memXG_coe f)

/-! ## Two fixed elements of `X_G`: the Gaussian `G` and the coefficient `k` -/

theorem continuous_radialGaussianWeight : Continuous radialGaussianWeight := by
  unfold radialGaussianWeight radialOmega
  fun_prop

theorem continuous_radialK : Continuous radialK := radialK_smooth.continuous

theorem integrableOn_pow_three_mul_gaussG :
    IntegrableOn (fun ρ : ℝ => ρ ^ 3 * gaussG ρ) (Ioi 0) := by
  have h := integrableOn_rpow_mul_gaussG (s := 3) (by norm_num)
  refine h.congr_fun (fun ρ _ => ?_) measurableSet_Ioi
  simp only
  rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]

/-- The Gaussian `G(r) = (4π)⁻¹e^{-r²/4}` lies in `X_G`: `∫₀^∞ G² G⁻¹ r dr = ∫₀^∞ G r dr < ∞`. -/
theorem memLp_gauss : MemLp (fun r => (radialGaussianWeight r : ℂ)) 2 xGMeasure := by
  have hm : AEStronglyMeasurable (fun r => (radialGaussianWeight r : ℂ))
      (volume.restrict (Ioi (0 : ℝ))) :=
    (Complex.continuous_ofReal.comp continuous_radialGaussianWeight).aestronglyMeasurable
  refine (memLp_iff_integrableOn hm).2 ?_
  refine integrableOn_mul_gaussG.congr_fun (fun r _ => ?_) measurableSet_Ioi
  have hG := radialGaussianWeight_pos r
  simp only [Complex.norm_real, Real.norm_eq_abs, sq_abs]
  show r * radialGaussianWeight r = _
  field_simp

/-- The Gaussian as an element of `X_G`. -/
def gaussLp : XG := memLp_gauss.toLp _

theorem coeFn_gaussLp : ⇑gaussLp =ᵐ[xGMeasure] fun r => (radialGaussianWeight r : ℂ) :=
  memLp_gauss.coeFn_toLp

/-- The coefficient `k(r) = (r²/4 - 2)e^{-r²/4}` (tex line 647) lies in `X_G`:
`|k|² G⁻¹ r = 16π² (r⁵/16 - r³ + 4r) G` is integrable. -/
theorem memLp_k : MemLp (fun r => (radialK r : ℂ)) 2 xGMeasure := by
  have hm : AEStronglyMeasurable (fun r => (radialK r : ℂ)) (volume.restrict (Ioi (0 : ℝ))) :=
    (Complex.continuous_ofReal.comp continuous_radialK).aestronglyMeasurable
  refine (memLp_iff_integrableOn hm).2 ?_
  have h : IntegrableOn (fun ρ : ℝ => (4 * Real.pi) ^ 2 *
      (1 / 16 * (ρ ^ 5 * gaussG ρ) - ρ ^ 3 * gaussG ρ + 4 * (ρ * gaussG ρ))) (Ioi 0) :=
    (((integrableOn_pow_five_mul_gaussG.const_mul (1 / 16)).sub
      integrableOn_pow_three_mul_gaussG).add (integrableOn_mul_gaussG.const_mul 4)).const_mul _
  refine h.congr_fun (fun r _ => ?_) measurableSet_Ioi
  have hΩ := radialOmega_pos r
  have hπ := Real.pi_pos
  simp only [Complex.norm_real, Real.norm_eq_abs, sq_abs]
  unfold radialK radialGaussianWeight gaussG
  field_simp
  ring

/-- The coefficient `k` as an element of `X_G`. -/
def kLp : XG := memLp_k.toLp _

theorem coeFn_kLp : ⇑kLp =ᵐ[xGMeasure] fun r => (radialK r : ℂ) :=
  memLp_k.coeFn_toLp

/-! ## The uniform bound `|Rf(r)| ≤ ¼ ‖G‖ ‖f‖` -/

/-- The representer `h_r(s) = (min(r,s)/max(r,s))² G(s)` of `f ↦ ∫₀^∞ ker(r,s) f(s) ds`. -/
def rep (r s : ℝ) : ℂ := (((min r s / max r s) ^ 2 * radialGaussianWeight s : ℝ) : ℂ)

theorem norm_rep_le {r s : ℝ} (hr : 0 < r) (hs : 0 < s) :
    ‖rep r s‖ ≤ ‖(radialGaussianWeight s : ℂ)‖ := by
  have hG := radialGaussianWeight_pos s
  have hmax : 0 < max r s := lt_max_of_lt_left hr
  have h0 : 0 ≤ min r s / max r s := div_nonneg (le_min hr.le hs.le) hmax.le
  have h1 : min r s / max r s ≤ 1 := div_le_one_of_le₀ min_le_max hmax.le
  have h2 : (min r s / max r s) ^ 2 ≤ 1 := pow_le_one₀ h0 h1
  rw [rep, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (by positivity), abs_of_pos hG]
  calc (min r s / max r s) ^ 2 * radialGaussianWeight s ≤ 1 * radialGaussianWeight s := by
        gcongr
    _ = radialGaussianWeight s := one_mul _

theorem memLp_rep {r : ℝ} (hr : 0 < r) : MemLp (rep r) 2 xGMeasure := by
  have hc : Continuous (rep r) := by
    unfold rep
    refine Complex.continuous_ofReal.comp ?_
    refine (((continuous_const.min continuous_id).div (continuous_const.max continuous_id)
      fun s => (lt_max_of_lt_left hr).ne').pow 2).mul continuous_radialGaussianWeight
  refine memLp_gauss.of_le hc.aestronglyMeasurable ?_
  filter_upwards [ae_xG_pos] with s hs
  exact norm_rep_le hr hs

/-- `∫₀^∞ ker(r,s) f(s) ds = ⟨f, h_r⟩_{X_G}` (B0010 `pairing`). -/
theorem Psi_eq_pairing (f : XG) {r : ℝ} (hr : 0 < r) :
    Psi 2 (⇑f) r = pairing f ((memLp_rep hr).toLp (rep r)) := by
  have h1 : pairing f ((memLp_rep hr).toLp (rep r)) = ∫ s, rep r s * f s ∂xGMeasure := by
    unfold pairing
    apply integral_congr_ae
    filter_upwards [(memLp_rep hr).coeFn_toLp] with s hs
    rw [hs, rep, Complex.conj_ofReal, mul_comm]
  have h2 : ∫ s, rep r s * f s ∂xGMeasure =
      ∫ s in Ioi 0, xGDensity s • (rep r s * f s) :=
    integral_withDensity_eq_integral_smul measurable_xGDensity _
  rw [h1, h2, Psi]
  refine setIntegral_congr_fun measurableSet_Ioi (fun s hs => ?_)
  have hs' : (0 : ℝ) < s := hs
  have hG := (radialGaussianWeight_pos s).ne'
  have e : (min r s / max r s) ^ 2 * s =
      (radialGaussianWeight s)⁻¹ * s * ((min r s / max r s) ^ 2 * radialGaussianWeight s) := by
    field_simp
  simp only [NNReal.smul_def, coe_xGDensity hs', Complex.real_smul, rep]
  rw [show B0011.ker 2 r s = (radialGaussianWeight s)⁻¹ * s *
      ((min r s / max r s) ^ 2 * radialGaussianWeight s) from e, Complex.ofReal_mul]
  ring

/-- **Uniform Green bound.** For `f ∈ X_G` and `r > 0`, `|Rf(r)| ≤ ¼ ‖G‖_{X_G} ‖f‖_{X_G}`
(a weak form of `eq:st18-t00062`, tex lines 1417--1420, sufficient for boundedness of `L₀`). -/
theorem norm_R_coe_le (f : XG) {r : ℝ} (hr : 0 < r) :
    ‖R (⇑f) r‖ ≤ 1 / 4 * ‖gaussLp‖ * ‖f‖ := by
  rw [R_eq_Psi (wprof_coe f) hr, Psi_eq_pairing f hr, pairing_eq_inner, norm_mul]
  have h1 : ‖(memLp_rep hr).toLp (rep r)‖ ≤ ‖gaussLp‖ := by
    apply Lp.norm_le_norm_of_ae_le
    filter_upwards [(memLp_rep hr).coeFn_toLp, coeFn_gaussLp, ae_xG_pos]
      with s h1 h2 hs
    rw [h1, h2]
    exact norm_rep_le hr hs
  have h2 := norm_inner_le_norm (𝕜 := ℂ) ((memLp_rep hr).toLp (rep r)) f
  have hn : ‖-(1 / 4 : ℂ)‖ = 1 / 4 := by norm_num
  rw [hn]
  calc 1 / 4 * ‖inner ℂ ((memLp_rep hr).toLp (rep r)) f‖
      ≤ 1 / 4 * (‖(memLp_rep hr).toLp (rep r)‖ * ‖f‖) := by gcongr
    _ ≤ 1 / 4 * (‖gaussLp‖ * ‖f‖) := by gcongr
    _ = 1 / 4 * ‖gaussLp‖ * ‖f‖ := by ring

/-! ## The interaction `f ↦ k R f` -/

theorem memLp_kR (f : XG) : MemLp (fun r => (radialK r : ℂ) * R (⇑f) r) 2 xGMeasure := by
  refine (memLp_k.const_smul (((1 / 4 * ‖gaussLp‖ * ‖f‖ : ℝ)) : ℂ)).of_le
    ((Complex.continuous_ofReal.comp continuous_radialK).aestronglyMeasurable.mul (aesm_R f)) ?_
  filter_upwards [ae_xG_pos] with r hr
  have hC : 0 ≤ 1 / 4 * ‖gaussLp‖ * ‖f‖ := by positivity
  rw [Pi.smul_apply, smul_eq_mul, norm_mul, norm_mul, mul_comm (‖_‖) (‖(radialK r : ℂ)‖),
    Complex.norm_real (1 / 4 * ‖gaussLp‖ * ‖f‖), Real.norm_of_nonneg hC]
  exact mul_le_mul_of_nonneg_left (norm_R_coe_le f hr) (norm_nonneg _)

/-- The interaction `f ↦ k R f` as a linear map of `X_G`. -/
def kRLin : XG →ₗ[ℂ] XG where
  toFun f := (memLp_kR f).toLp _
  map_add' f g := by
    rw [← MemLp.toLp_add]
    apply MemLp.toLp_congr
    have hfg : ⇑(f + g) =ᵐ[volume.restrict (Ioi (0 : ℝ))] fun s => f s + g s :=
      restrict_ac.ae_le (Lp.coeFn_add f g)
    filter_upwards [ae_xG_pos] with r hr
    simp only [Pi.add_apply]
    rw [R_congr hfg hr, R_add (wprof_coe f) (wprof_coe g) hr]
    ring
  map_smul' c f := by
    rw [RingHom.id_apply, ← MemLp.toLp_const_smul]
    apply MemLp.toLp_congr
    have hcf : ⇑(c • f) =ᵐ[volume.restrict (Ioi (0 : ℝ))] fun s => c * f s :=
      restrict_ac.ae_le (Lp.coeFn_smul c f)
    filter_upwards [ae_xG_pos] with r hr
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [R_congr hcf hr, R_const_mul]
    ring

theorem norm_kRLin_le (f : XG) : ‖kRLin f‖ ≤ 1 / 4 * ‖gaussLp‖ * ‖kLp‖ * ‖f‖ := by
  set c : ℂ := ((1 / 4 * ‖gaussLp‖ * ‖f‖ : ℝ) : ℂ) with hc
  have hC : 0 ≤ 1 / 4 * ‖gaussLp‖ * ‖f‖ := by positivity
  have h : ‖kRLin f‖ ≤ ‖c • kLp‖ := by
    apply Lp.norm_le_norm_of_ae_le
    filter_upwards [(memLp_kR f).coeFn_toLp, Lp.coeFn_smul c kLp, coeFn_kLp,
      ae_xG_pos] with r h1 h2 h3 hr
    show ‖((memLp_kR f).toLp _ : XG) r‖ ≤ _
    rw [h1, h2, Pi.smul_apply, h3, smul_eq_mul, norm_mul, norm_mul, mul_comm (‖_‖) (‖(radialK r : ℂ)‖),
      hc, Complex.norm_real (1 / 4 * ‖gaussLp‖ * ‖f‖), Real.norm_of_nonneg hC]
    exact mul_le_mul_of_nonneg_left (norm_R_coe_le f hr) (norm_nonneg _)
  rw [norm_smul, hc, Complex.norm_real, Real.norm_of_nonneg hC] at h
  calc ‖kRLin f‖ ≤ 1 / 4 * ‖gaussLp‖ * ‖f‖ * ‖kLp‖ := h
    _ = 1 / 4 * ‖gaussLp‖ * ‖kLp‖ * ‖f‖ := by ring

/-- The interaction `f ↦ k R f` (tex line 680) as a bounded operator on `X_G`. -/
def kROp : XG →L[ℂ] XG :=
  kRLin.mkContinuous (1 / 4 * ‖gaussLp‖ * ‖kLp‖) norm_kRLin_le

theorem kROp_apply (f : XG) : kROp f = (memLp_kR f).toLp _ := rfl

theorem coeFn_kROp (f : XG) :
    ⇑(kROp f) =ᵐ[xGMeasure] fun r => (radialK r : ℂ) * R (⇑f) r :=
  (memLp_kR f).coeFn_toLp

theorem norm_kROp_le (f : XG) : ‖kROp f‖ ≤ 1 / 4 * ‖gaussLp‖ * ‖kLp‖ * ‖f‖ :=
  norm_kRLin_le f

/-! ## Multiplication by `Ω` -/

theorem continuous_radialOmega : Continuous radialOmega := radialOmega_smooth.continuous

theorem radialOmega_le_one (r : ℝ) : radialOmega r ≤ 1 := by
  unfold radialOmega
  exact Real.exp_le_one_iff.2 (neg_nonpos.2 (by positivity))

theorem norm_omega_mul_le (r : ℝ) (z : ℂ) : ‖(radialOmega r : ℂ) * z‖ ≤ ‖z‖ := by
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (radialOmega_pos r).le]
  calc radialOmega r * ‖z‖ ≤ 1 * ‖z‖ := by gcongr; exact radialOmega_le_one r
    _ = ‖z‖ := one_mul _

theorem memLp_omegaMul (f : XG) : MemLp (fun r => (radialOmega r : ℂ) * f r) 2 xGMeasure :=
  (Lp.memLp f).of_le ((Complex.continuous_ofReal.comp continuous_radialOmega).aestronglyMeasurable.mul
    (Lp.aestronglyMeasurable f)) (ae_of_all _ fun r => norm_omega_mul_le r (f r))

/-- Multiplication by `Ω` as a linear map of `X_G`. -/
def omegaLin : XG →ₗ[ℂ] XG where
  toFun f := (memLp_omegaMul f).toLp _
  map_add' f g := by
    rw [← MemLp.toLp_add]
    apply MemLp.toLp_congr
    filter_upwards [Lp.coeFn_add f g] with r h
    simp only [Pi.add_apply]
    rw [h, Pi.add_apply, mul_add]
  map_smul' c f := by
    rw [RingHom.id_apply, ← MemLp.toLp_const_smul]
    apply MemLp.toLp_congr
    filter_upwards [Lp.coeFn_smul c f] with r h
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [h, Pi.smul_apply, smul_eq_mul]
    ring

theorem norm_omegaLin_le (f : XG) : ‖omegaLin f‖ ≤ 1 * ‖f‖ := by
  rw [one_mul]
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [(memLp_omegaMul f).coeFn_toLp] with r h
  show ‖((memLp_omegaMul f).toLp _ : XG) r‖ ≤ _
  rw [h]
  exact norm_omega_mul_le r (f r)

/-- Multiplication by `Ω(r) = e^{-r²/4}` (tex line 639) as a bounded operator on `X_G`. -/
def omegaOp : XG →L[ℂ] XG := omegaLin.mkContinuous 1 norm_omegaLin_le

theorem coeFn_omegaOp (f : XG) :
    ⇑(omegaOp f) =ᵐ[xGMeasure] fun r => (radialOmega r : ℂ) * f r :=
  (memLp_omegaMul f).coeFn_toLp

theorem norm_omegaOp_le (f : XG) : ‖omegaOp f‖ ≤ ‖f‖ := by
  have h := norm_omegaLin_le f
  rwa [one_mul] at h

/-! ## The generator `L₀` -/

/-- The manuscript formula `eq:st18-t00006` (tex line 680) on a radial profile `f`:
`L₀f(r) = -2iΩ(r) f(r) + 2ik(r) (Rf)(r)`, with `R` the Green formula `eq:st18-t00007`. -/
def L0Fun (f : ℝ → ℂ) (r : ℝ) : ℂ :=
  -2 * Complex.I * (radialOmega r : ℂ) * f r + 2 * Complex.I * (radialK r : ℂ) * R f r

/-- **`eq:st18-t00006`** (tex lines 678--682): the angular-two generator
`L₀ = -2iΩ + 2ikR` as a bounded complex-linear operator on `X_G`. -/
def L0 : XG →L[ℂ] XG := (-2 * Complex.I) • omegaOp + (2 * Complex.I) • kROp

/-- `L0` is given by the manuscript formula: `L₀f = -2iΩf + 2ikRf` a.e. (tex line 680). -/
theorem coeFn_L0 (f : XG) : ⇑(L0 f) =ᵐ[xGMeasure] L0Fun ⇑f := by
  have e : L0 f = (-2 * Complex.I) • omegaOp f + (2 * Complex.I) • kROp f := rfl
  rw [e]
  filter_upwards [Lp.coeFn_add ((-2 * Complex.I) • omegaOp f) ((2 * Complex.I) • kROp f),
    Lp.coeFn_smul (-2 * Complex.I) (omegaOp f), Lp.coeFn_smul (2 * Complex.I) (kROp f),
    coeFn_omegaOp f, coeFn_kROp f] with r h1 h2 h3 h4 h5
  rw [h1, Pi.add_apply, h2, h3, Pi.smul_apply, Pi.smul_apply, h4, h5, L0Fun, smul_eq_mul,
    smul_eq_mul]
  ring

/-- The formula `L0Fun` only depends on the `X_G`-class of the profile. -/
theorem L0Fun_congr {f g : ℝ → ℂ} (h : f =ᵐ[xGMeasure] g) : L0Fun f =ᵐ[xGMeasure] L0Fun g := by
  have h' : f =ᵐ[volume.restrict (Ioi (0 : ℝ))] g := restrict_ac.ae_le h
  filter_upwards [h, ae_xG_pos] with r h1 hr
  rw [L0Fun, L0Fun, h1, R_congr h' hr]

/-- The formula maps `X_G` into `X_G`: for every profile `f₂` of `X_G`, `L₀f₂ ∈ X_G`. -/
theorem memLp_L0Fun {f₂ : ℝ → ℂ} (hf : MemLp f₂ 2 xGMeasure) : MemLp (L0Fun f₂) 2 xGMeasure :=
  (Lp.memLp (L0 (hf.toLp f₂))).ae_eq ((coeFn_L0 _).trans (L0Fun_congr hf.coeFn_toLp))

/-- On a profile `f₂ ∈ X_G`, `L0` is the class of `L0Fun f₂`. -/
theorem L0_toLp {f₂ : ℝ → ℂ} (hf : MemLp f₂ 2 xGMeasure) :
    L0 (hf.toLp f₂) = (memLp_L0Fun hf).toLp (L0Fun f₂) :=
  Lp.ext ((coeFn_L0 _).trans ((L0Fun_congr hf.coeFn_toLp).trans
    (memLp_L0Fun hf).coeFn_toLp.symm))

/-- The explicit bound `‖L₀f‖ ≤ (2 + ½ ‖G‖ ‖k‖) ‖f‖`. -/
theorem norm_L0_le (f : XG) : ‖L0 f‖ ≤ (2 + 1 / 2 * ‖gaussLp‖ * ‖kLp‖) * ‖f‖ := by
  have e : L0 f = (-2 * Complex.I) • omegaOp f + (2 * Complex.I) • kROp f := rfl
  have n1 : ‖(-2 * Complex.I)‖ = 2 := by
    rw [norm_mul, norm_neg, Complex.norm_I]; norm_num
  have n2 : ‖(2 * Complex.I)‖ = 2 := by
    rw [norm_mul, Complex.norm_I]; norm_num
  rw [e]
  refine (norm_add_le _ _).trans ?_
  rw [norm_smul, norm_smul, n1, n2]
  have h1 := norm_omegaOp_le f
  have h2 := norm_kROp_le f
  nlinarith

/-- **`eq:st18-t00006`: `L₀` is bounded on `X_G`** (tex line 678, "The angular-two generator is
bounded"). -/
theorem L0_bounded : ∃ C : ℝ, 0 ≤ C ∧ ∀ f : XG, ‖L0 f‖ ≤ C * ‖f‖ :=
  ⟨2 + 1 / 2 * ‖gaussLp‖ * ‖kLp‖, by positivity, norm_L0_le⟩

/-- **`eq:st18-t00006`, formula form** (tex lines 678--680): there is `C` such that for every
profile `f₂ ∈ X_G`, the manuscript formula `L₀f₂ = -2iΩf₂ + 2ikRf₂` lies in `X_G` and
`‖L₀f₂‖_{X_G} ≤ C ‖f₂‖_{X_G}`. -/
theorem L0Fun_bounded : ∃ C : ℝ, 0 ≤ C ∧ ∀ f₂ : ℝ → ℂ, ∀ hf : MemLp f₂ 2 xGMeasure,
    ∃ hL : MemLp (L0Fun f₂) 2 xGMeasure, ‖hL.toLp (L0Fun f₂)‖ ≤ C * ‖hf.toLp f₂‖ := by
  refine ⟨2 + 1 / 2 * ‖gaussLp‖ * ‖kLp‖, by positivity, fun f₂ hf => ⟨memLp_L0Fun hf, ?_⟩⟩
  rw [← L0_toLp hf]
  exact norm_L0_le _

/-- **`eq:st18-t00006`, integral form** (tex lines 674--680): there is `C` such that every
measurable profile `f₂` on `(0, ∞)` with `∫₀^∞ |f₂|² G⁻¹ r dr < ∞` satisfies
`∫₀^∞ |L₀f₂|² G⁻¹ r dr ≤ C ∫₀^∞ |f₂|² G⁻¹ r dr` (and the left integrand is integrable). -/
theorem L0Fun_integral_bound : ∃ C : ℝ, 0 ≤ C ∧ ∀ f₂ : ℝ → ℂ,
    AEStronglyMeasurable f₂ (volume.restrict (Ioi 0)) →
    IntegrableOn (fun r => ‖f₂ r‖ ^ 2 * ((radialGaussianWeight r)⁻¹ * r)) (Ioi 0) →
      IntegrableOn (fun r => ‖L0Fun f₂ r‖ ^ 2 * ((radialGaussianWeight r)⁻¹ * r)) (Ioi 0) ∧
      ∫ r in Ioi 0, ‖L0Fun f₂ r‖ ^ 2 * ((radialGaussianWeight r)⁻¹ * r) ≤
        C * ∫ r in Ioi 0, ‖f₂ r‖ ^ 2 * ((radialGaussianWeight r)⁻¹ * r) := by
  obtain ⟨C, hC, hb⟩ := L0Fun_bounded
  refine ⟨C ^ 2, by positivity, fun f₂ hm hi => ?_⟩
  have hf : MemLp f₂ 2 xGMeasure := (memLp_iff_integrableOn hm).2 hi
  obtain ⟨hL, hle⟩ := hb f₂ hf
  have hmL : AEStronglyMeasurable (L0Fun f₂) (volume.restrict (Ioi (0 : ℝ))) :=
    hL.1.mono_ac restrict_ac
  refine ⟨(memLp_iff_integrableOn hmL).1 hL, ?_⟩
  rw [← norm_sq_toLp hL, ← norm_sq_toLp hf]
  have h0 := norm_nonneg (hL.toLp (L0Fun f₂))
  calc ‖hL.toLp (L0Fun f₂)‖ ^ 2 ≤ (C * ‖hf.toLp f₂‖) ^ 2 := by gcongr
    _ = C ^ 2 * ‖hf.toLp f₂‖ ^ 2 := by ring

end UnforcedLeray.B0012
