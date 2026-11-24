import UnforcedLeray.Lib.PlanarSectorsB.Coupling

/-!
# Sector generators `Lsec n` on `L²_M` and the decay of the couplings (INF12 target P6, part 2)


§5, Level P, target **P6**; decision D7 (bounded generators sector by sector) and bypass B1.

Manuscript (`paper/main.tex`): on the sector `f = w(r)e^{inϑ}` the generator
`𝓛f = -Ω∂_ϑf - (Kf)·∇E₀` (lines 662–670, `eq:st18-t00004`, unit `B0009`) is
`𝓛_n w = -inΩ w + i n k Δ_{|n|}⁻¹ w`. The transport part `-inΩ` is skew-adjoint (it generates
the multiplication group `e^{-inΩt}`, the sector form of the transport group `T(t)`,
`eq:st18-t00050`/`t00051`, lines 1228–1237, unit `B0062`), and the coupling is bounded uniformly
in `n` and compact (lines 1206–1222, units `B0059`–`B0061`, at `j = 0`).

Main declarations (namespace `UnforcedLeray.Planar`):
* `crepSq`, `norm_couplingSec_le_sqrt`: `‖couplingSec hM n‖ ≤ ½ (∫ |k|² ‖crep_{|n|,r}‖² dμ(r))^{1/2}`;
* `tendsto_norm_couplingSec`: `‖couplingSec hM n‖ → 0` as `n → ∞` (dominated convergence twice:
  `(min(r,s)/max(r,s))^{2n} → 0` for `s ≠ r`);
* `omegaP`, `inner_omegaP`, `adjoint_omegaP`; `transportSec M n = -(i n) Ω`,
  `adjoint_transportSec` (skew-adjoint);
* `Lsec hM n = transportSec M n + couplingSec hM n`, `coeFn_Lsec`, `Lsec_zero`;
* `lsecBound hM` and `norm_exp_Lsec_le`: `‖exp(t Lsec n)‖ ≤ e^{t B_M}` for all `n` and `t ≥ 0`
  (via `Infra.norm_exp_skew_add_le`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Real
open scoped ENNReal InnerProductSpace ComplexConjugate

namespace UnforcedLeray.Planar

open UnforcedLeray.GaussianVortex (radialOmega radialK radialOmega_pos)

/-! ### The Hilbert–Schmidt-type bound and the decay in `n` -/

/-- `crepSq M n r = ∫ ‖crep_{n,r}‖² dμ`, the squared norm of the representer (for `r > 0`). -/
def crepSq (M : ℝ) (n : ℕ) (r : ℝ) : ℝ := ∫ s, ‖crep M n r s‖ ^ 2 ∂profileMeasure M

theorem measurable_crep_sq (M : ℝ) (n : ℕ) :
    Measurable fun z : ℝ × ℝ => ‖crep M n z.1 z.2‖ ^ 2 := by
  have h1 := measurable_minmax_pow n
  have h2 : Measurable fun z : ℝ × ℝ => ((wrep M z.2 : ℝ) : ℂ) :=
    (Complex.continuous_ofReal.comp (continuous_wrep M)).measurable.comp measurable_snd
  have h3 : Measurable fun z : ℝ × ℝ => crep M n z.1 z.2 := by
    have : (fun z : ℝ × ℝ => crep M n z.1 z.2) =
        fun z => (((min z.1 z.2 / max z.1 z.2) ^ n : ℝ) : ℂ) * ((wrep M z.2 : ℝ) : ℂ) := by
      funext z
      simp [crep]
    rw [this]
    exact h1.mul h2
  exact h3.norm.pow_const 2

instance sFinite_profileMeasure (M : ℝ) : SFinite (profileMeasure M) := by
  unfold profileMeasure
  infer_instance

theorem stronglyMeasurable_crepSq (M : ℝ) (n : ℕ) : StronglyMeasurable (crepSq M n) :=
  StronglyMeasurable.integral_prod_right' (f := fun z : ℝ × ℝ => ‖crep M n z.1 z.2‖ ^ 2)
    (measurable_crep_sq M n).stronglyMeasurable

theorem norm_crepLp_sq {M : ℝ} (hM : 1 < M) (n : ℕ) {r : ℝ} (hr : 0 < r) :
    ‖crepLp hM n hr‖ ^ 2 = crepSq M n r := by
  rw [norm_sq_Lp_eq_integral, crepSq]
  refine integral_congr_ae ?_
  filter_upwards [(memLp_crep hM n hr).coeFn_toLp] with s hs
  rw [crepLp, hs]

theorem crepSq_nonneg (M : ℝ) (n : ℕ) (r : ℝ) : 0 ≤ crepSq M n r :=
  integral_nonneg fun _ => by positivity

theorem crepSq_le {M : ℝ} (hM : 1 < M) (n : ℕ) {r : ℝ} (hr : 0 < r) :
    crepSq M n r ≤ ‖wrepLp hM‖ ^ 2 := by
  rw [← norm_crepLp_sq hM n hr]
  exact pow_le_pow_left₀ (norm_nonneg _) (norm_crepLp_le hM n hr) 2

/-- For `r > 0`, `crepSq M n r → 0` as `n → ∞`. -/
theorem tendsto_crepSq {M : ℝ} (hM : 1 < M) {r : ℝ} (hr : 0 < r) :
    Tendsto (fun n : ℕ => crepSq M n r) atTop (𝓝 0) := by
  have hw2 : Integrable (fun s => ‖(wrep M s : ℂ)‖ ^ 2) (profileMeasure M) :=
    (memLp_two_iff_integrable_sq_norm (memLp_wrep hM).1).1 (memLp_wrep hM)
  have hne : ∀ᵐ s ∂profileMeasure M, s ≠ r := by
    have h : ∀ᵐ s ∂(volume : Measure ℝ), s ≠ r := B0011.ae_ne_point r
    exact (profileMeasure_ac M).ae_le (ae_restrict_of_ae h)
  have h := tendsto_integral_of_dominated_convergence (μ := profileMeasure M)
    (F := fun n s => ‖crep M n r s‖ ^ 2) (f := fun _ => (0 : ℝ))
    (fun s => ‖(wrep M s : ℂ)‖ ^ 2) ?_ hw2 ?_ ?_
  · simpa [crepSq] using h
  · intro n
    exact ((continuous_crep M n hr).norm.pow 2).aestronglyMeasurable
  · intro n
    filter_upwards [ae_profile_pos M] with s hs
    rw [Real.norm_of_nonneg (by positivity)]
    exact pow_le_pow_left₀ (norm_nonneg _) (norm_crep_le hr hs) 2
  · filter_upwards [ae_profile_pos M, hne] with s hs hsr
    have hq0 : 0 ≤ min r s / max r s := minmax_nonneg hr hs
    have hq1 : min r s / max r s < 1 := by
      have hmax : 0 < max r s := lt_max_of_lt_left hr
      rw [div_lt_one hmax]
      rcases lt_or_gt_of_ne hsr with h | h
      · rw [min_eq_right h.le, max_eq_left h.le]; exact h
      · rw [min_eq_left h.le, max_eq_right h.le]; exact h
    have hp := tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1
    have hp2 := (hp.mul_const (wrep M s)).pow 2
    rw [zero_mul, zero_pow two_ne_zero] at hp2
    refine hp2.congr fun n => ?_
    rw [crep, Complex.norm_real, Real.norm_eq_abs, sq_abs]

/-- The bound `|i n k(r) greenN |n| w r|² ≤ ¼ ‖w‖² |k(r)|² crepSq` (`n ≠ 0`, `r > 0`). -/
theorem norm_cpl_sq_le {M : ℝ} (hM : 1 < M) {n : ℕ} (hn : n ≠ 0) {r : ℝ} (hr : 0 < r)
    (w : ProfL2 M) :
    ‖cplCoeff n r * greenN n w r‖ ^ 2 ≤ 1 / 4 * ‖w‖ ^ 2 * (radialK r ^ 2 * crepSq M n r) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hg : ‖greenN n w r‖ ≤ (2 * n : ℝ)⁻¹ * (‖crepLp hM n hr‖ * ‖w‖) := by
    rw [greenN_eq_inner hM n hr w, norm_mul, norm_neg, Complex.norm_real,
      Real.norm_of_nonneg (by positivity)]
    gcongr
    exact norm_inner_le_norm _ _
  have hc : ‖cplCoeff n r‖ = n * |radialK r| := by
    rw [norm_cplCoeff]
    push_cast
    rw [abs_of_pos hn']
  rw [norm_mul, hc, ← norm_crepLp_sq hM n hr]
  calc (n * |radialK r| * ‖greenN n w r‖) ^ 2
      ≤ (n * |radialK r| * ((2 * n : ℝ)⁻¹ * (‖crepLp hM n hr‖ * ‖w‖))) ^ 2 := by
        gcongr
    _ = 1 / 4 * ‖w‖ ^ 2 * (radialK r ^ 2 * ‖crepLp hM n hr‖ ^ 2) := by
        rw [← sq_abs (radialK r)]
        field_simp
        ring

theorem integrable_k_sq_mul_crepSq {M : ℝ} (hM : 1 < M) (n : ℕ) :
    Integrable (fun r => radialK r ^ 2 * crepSq M n r) (profileMeasure M) := by
  have hk2 : Integrable (fun r => ‖(radialK r : ℂ)‖ ^ 2) (profileMeasure M) :=
    (memLp_two_iff_integrable_sq_norm (memLp_radialK_profile M).1).1 (memLp_radialK_profile M)
  refine (hk2.mul_const (‖wrepLp hM‖ ^ 2)).mono' ?_ ?_
  · exact ((B0012.continuous_radialK.pow 2).aestronglyMeasurable).mul
      (stronglyMeasurable_crepSq M n).aestronglyMeasurable
  · filter_upwards [ae_profile_pos M] with r hr
    rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) (crepSq_nonneg M n r)), Complex.norm_real,
      Real.norm_eq_abs, sq_abs]
    exact mul_le_mul_of_nonneg_left (crepSq_le hM n hr) (sq_nonneg _)

/-- **Hilbert–Schmidt-type bound**: `‖couplingSec hM n‖ ≤ ½ (∫ k² crepSq_{|n|} dμ)^{1/2}`. -/
theorem norm_couplingSec_le_sqrt {M : ℝ} (hM : 1 < M) {n : ℕ} (hn : n ≠ 0) :
    ‖couplingSec hM (n : ℤ)‖ ≤
      1 / 2 * Real.sqrt (∫ r, radialK r ^ 2 * crepSq M n r ∂profileMeasure M) := by
  set β : ℝ := ∫ r, radialK r ^ 2 * crepSq M n r ∂profileMeasure M with hβ
  have hβ0 : 0 ≤ β := integral_nonneg fun r => mul_nonneg (sq_nonneg _) (crepSq_nonneg M n r)
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun w => ?_
  have hsq : ‖couplingSec hM (n : ℤ) w‖ ^ 2 ≤ (1 / 2 * Real.sqrt β * ‖w‖) ^ 2 := by
    rw [norm_sq_Lp_eq_integral]
    have e : ∫ r, ‖(couplingSec hM (n : ℤ) w : ℝ → ℂ) r‖ ^ 2 ∂profileMeasure M =
        ∫ r, ‖cplCoeff n r * greenN n w r‖ ^ 2 ∂profileMeasure M := by
      refine integral_congr_ae ?_
      filter_upwards [coeFn_couplingSec hM n w] with r hr
      rw [hr, cplCoeff, Int.natAbs_natCast]
    rw [e]
    calc ∫ r, ‖cplCoeff n r * greenN n w r‖ ^ 2 ∂profileMeasure M
        ≤ ∫ r, 1 / 4 * ‖w‖ ^ 2 * (radialK r ^ 2 * crepSq M n r) ∂profileMeasure M := by
          refine integral_mono_of_nonneg (Eventually.of_forall fun r => by positivity)
            ((integrable_k_sq_mul_crepSq hM n).const_mul _) ?_
          filter_upwards [ae_profile_pos M] with r hr
          exact norm_cpl_sq_le hM hn hr w
      _ = 1 / 4 * ‖w‖ ^ 2 * β := by rw [integral_const_mul]
      _ = (1 / 2 * Real.sqrt β * ‖w‖) ^ 2 := by
          rw [mul_pow, mul_pow, Real.sq_sqrt hβ0]
          ring
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 hsq

/-- **P6, decay in the sector** (`tendsto_norm_couplingSec`): `‖couplingSec hM n‖ → 0` as
`n → ∞`. This is the input that makes the large sectors a small perturbation of the transport
(scoping note §5, P6 and G-5). -/
theorem tendsto_norm_couplingSec {M : ℝ} (hM : 1 < M) :
    Tendsto (fun n : ℕ => ‖couplingSec hM (n : ℤ)‖) atTop (𝓝 0) := by
  have hk2 : Integrable (fun r => ‖(radialK r : ℂ)‖ ^ 2 * ‖wrepLp hM‖ ^ 2) (profileMeasure M) :=
    ((memLp_two_iff_integrable_sq_norm (memLp_radialK_profile M).1).1
      (memLp_radialK_profile M)).mul_const _
  have hβ : Tendsto (fun n : ℕ => ∫ r, radialK r ^ 2 * crepSq M n r ∂profileMeasure M) atTop
      (𝓝 0) := by
    have h := tendsto_integral_of_dominated_convergence (μ := profileMeasure M)
      (F := fun (n : ℕ) r => radialK r ^ 2 * crepSq M n r) (f := fun _ => (0 : ℝ))
      (fun r => ‖(radialK r : ℂ)‖ ^ 2 * ‖wrepLp hM‖ ^ 2) ?_ hk2 ?_ ?_
    · simpa using h
    · intro n
      exact (integrable_k_sq_mul_crepSq hM n).1
    · intro n
      filter_upwards [ae_profile_pos M] with r hr
      rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) (crepSq_nonneg M n r)),
        Complex.norm_real, Real.norm_eq_abs, sq_abs]
      exact mul_le_mul_of_nonneg_left (crepSq_le hM n hr) (sq_nonneg _)
    · filter_upwards [ae_profile_pos M] with r hr
      have := (tendsto_crepSq hM hr).const_mul (radialK r ^ 2)
      rwa [mul_zero] at this
  have hs : Tendsto (fun n : ℕ =>
      1 / 2 * Real.sqrt (∫ r, radialK r ^ 2 * crepSq M n r ∂profileMeasure M)) atTop (𝓝 0) := by
    have := ((Real.continuous_sqrt.tendsto 0).comp hβ).const_mul (1 / 2)
    simpa [Function.comp_def] using this
  refine squeeze_zero' (Eventually.of_forall fun n => norm_nonneg _) ?_ hs
  filter_upwards [eventually_ne_atTop 0] with n hn
  exact norm_couplingSec_le_sqrt hM hn

/-! ### The transport part and the sector generator -/

theorem aesm_omega (M : ℝ) :
    AEStronglyMeasurable (fun r => (radialOmega r : ℂ)) (profileMeasure M) :=
  (Complex.continuous_ofReal.comp B0012.continuous_radialOmega).aestronglyMeasurable

theorem ae_norm_omega_le (M : ℝ) : ∀ᵐ r ∂profileMeasure M, ‖(radialOmega r : ℂ)‖ ≤ 1 :=
  Eventually.of_forall fun r => by
    rw [Complex.norm_real, Real.norm_of_nonneg (radialOmega_pos r).le]
    exact B0012.radialOmega_le_one r

/-- Multiplication by the angular velocity `Ω(r) = e^{-r²/4}` (`eq:st18-t00001`, tex line 639)
on `ProfL2 M`. -/
def omegaP (M : ℝ) : ProfL2 M →L[ℂ] ProfL2 M :=
  Infra.Mult.mulOp (fun r => (radialOmega r : ℂ)) (aesm_omega M) (ae_norm_omega_le M)

theorem coeFn_omegaP (M : ℝ) (w : ProfL2 M) :
    ⇑(omegaP M w) =ᵐ[profileMeasure M] fun r => (radialOmega r : ℂ) * w r :=
  Infra.Mult.coeFn_mulOp (aesm_omega M) (ae_norm_omega_le M) w

theorem inner_omegaP (M : ℝ) (f g : ProfL2 M) : ⟪omegaP M f, g⟫_ℂ = ⟪f, omegaP M g⟫_ℂ := by
  rw [L2.inner_def, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [coeFn_omegaP M f, coeFn_omegaP M g] with r h1 h2
  rw [h1, h2, RCLike.inner_apply', RCLike.inner_apply', map_mul, Complex.conj_ofReal]
  ring

theorem adjoint_omegaP (M : ℝ) : ContinuousLinearMap.adjoint (omegaP M) = omegaP M :=
  ((ContinuousLinearMap.eq_adjoint_iff (omegaP M) (omegaP M)).2 (inner_omegaP M)).symm

/-- The sector transport `w ↦ -inΩ w` (`-Ω∂_ϑ` on `w(r)e^{inϑ}`, tex line 667). -/
def transportSec (M : ℝ) (n : ℤ) : ProfL2 M →L[ℂ] ProfL2 M :=
  (-(Complex.I * (n : ℂ))) • omegaP M

/-- The sector transport is skew-adjoint (`Ω` is real). -/
theorem adjoint_transportSec (M : ℝ) (n : ℤ) :
    ContinuousLinearMap.adjoint (transportSec M n) = -transportSec M n := by
  refine ((ContinuousLinearMap.eq_adjoint_iff (-transportSec M n) (transportSec M n)).2
    fun f g => ?_).symm
  have e1 : (-transportSec M n) f = -((-(Complex.I * (n : ℂ))) • omegaP M f) := rfl
  have e2 : transportSec M n g = (-(Complex.I * (n : ℂ))) • omegaP M g := rfl
  rw [e1, e2, inner_neg_left, inner_smul_left, inner_smul_right, inner_omegaP]
  simp only [map_neg, map_mul, Complex.conj_I, map_intCast]
  ring

/-- **P6.** The sector generator `𝓛_n = -inΩ + i n k Δ_{|n|}⁻¹` on `ProfL2 M`
(`eq:st18-t00004`, tex lines 662–670, on the sector `w(r)e^{inϑ}`). -/
def Lsec {M : ℝ} (hM : 1 < M) (n : ℤ) : ProfL2 M →L[ℂ] ProfL2 M :=
  transportSec M n + couplingSec hM n

theorem coeFn_Lsec {M : ℝ} (hM : 1 < M) (n : ℤ) (w : ProfL2 M) :
    ⇑(Lsec hM n w) =ᵐ[profileMeasure M] fun r =>
      -(Complex.I * n) * (radialOmega r : ℂ) * w r +
        Complex.I * n * (radialK r : ℂ) * greenN n.natAbs w r := by
  have e : Lsec hM n w = (-(Complex.I * (n : ℂ))) • omegaP M w + couplingSec hM n w := rfl
  rw [e]
  filter_upwards [Lp.coeFn_add ((-(Complex.I * (n : ℂ))) • omegaP M w) (couplingSec hM n w),
    Lp.coeFn_smul (-(Complex.I * (n : ℂ))) (omegaP M w), coeFn_omegaP M w,
    coeFn_couplingSec hM n w] with r h1 h2 h3 h4
  rw [h1, Pi.add_apply, h2, Pi.smul_apply, h3, h4, smul_eq_mul]
  ring

/-- Sector `0` is stationary: `𝓛₀ = 0` (tex line 1356, unit `B0078`(i)). -/
theorem Lsec_zero {M : ℝ} (hM : 1 < M) : Lsec hM 0 = 0 := by
  rw [Lsec, couplingSec_zero, add_zero, transportSec]
  simp

/-- The growth constant `B_M = ½ ‖wrep‖ ‖k‖`, uniform in the sector. -/
def lsecBound {M : ℝ} (hM : 1 < M) : ℝ := cplConst hM * ‖kProf M‖

theorem lsecBound_nonneg {M : ℝ} (hM : 1 < M) : 0 ≤ lsecBound hM :=
  mul_nonneg (cplConst_nonneg hM) (norm_nonneg _)

/-- **Uniform growth bound of the sector semigroups**: `‖exp(t 𝓛_n)‖ ≤ e^{t B_M}` for every
sector `n` and `t ≥ 0` (skew-adjoint transport plus a coupling of norm `≤ B_M`). -/
theorem norm_exp_Lsec_le {M : ℝ} (hM : 1 < M) (n : ℤ) {t : ℝ} (ht : 0 ≤ t) :
    ‖NormedSpace.exp ((t : ℂ) • Lsec hM n)‖ ≤ Real.exp (t * lsecBound hM) := by
  refine (Infra.norm_exp_skew_add_le (adjoint_transportSec M n) ht).trans ?_
  exact Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left (norm_couplingSec_le hM n) ht)

end UnforcedLeray.Planar
