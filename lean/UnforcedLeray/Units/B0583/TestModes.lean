import UnforcedLeray.Units.B0581
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Topology.UniformSpace.Uniformizable

/-!
# B0583 helper: horizontal modes of cylinder test fields

Blueprint unit **B0583** (`prepared:p1.4`), `paper/main.tex` lines 9425–9433: "The gradient is
bounded by the Fourier multiplier of order zero." To identify the order-zero multipliers with
the distributional gradient on the cylinder (`B0579.HasWeakCellDeriv`), we compute the
horizontal modes (`B0581.modes`) of the test fields `φ(x) e_j` (`φ` a cylinder test function,
`B0579.IsCylTest`, `e_j` a unit vector of `ℂ²`):

* `modes_testLp`: the `k`-th mode of `φ e_j` is the Schwartz function
  `η ↦ √c c⁻¹ (∫_{-c/2}^{c/2} e^{-2πikq/c} φ(q, η) dq) e_j` (`tSchwartz`);
* `modes_testLp_pd0`: `∂_q` acts on the `k`-th mode as multiplication by `iκ_k`,
  `κ_k = 2πk/c` (integration by parts over one period, using periodicity);
* `fourier_modes_testLp_pd1`: `∂_η` acts on the `η`-Fourier transform of the `k`-th mode as
  multiplication by `2πiξ` (Mathlib's normalization `𝓕 f(ξ) = ∫ e^{-2πixξ} f(x) dx`).

The smoothness of parametric interval integrals (`paramInt_hasDerivAt`, `paramInt_contDiff`) is
copied and adapted from the reference formalization
`NonUniqueEuler/lean/NonUniqueEuler/H/Infra/AngularFourier/NormEquiv/ProfileDeriv/ParamInt.lean`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Complex Topology FourierTransform
open scoped ENNReal NNReal InnerProductSpace Real ComplexConjugate ContDiff

namespace UnforcedLeray.B0583

open B0581

/-! ### Parametric interval integrals (adapted from the reference formalization) -/

/-- The partial derivative in the first variable, `∂_r F (r, θ) = DF(r, θ)(1, 0)`. -/
def d1 (F : ℝ × ℝ → ℂ) (p : ℝ × ℝ) : ℂ :=
  fderiv ℝ F p (1, 0)

theorem contDiff_d1 {F : ℝ × ℝ → ℂ} (hF : ContDiff ℝ ∞ F) : ContDiff ℝ ∞ (d1 F) :=
  (hF.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const

theorem hasDerivAt_d1 {F : ℝ × ℝ → ℂ} (hF : Differentiable ℝ F) (r θ : ℝ) :
    HasDerivAt (fun s => F (s, θ)) (d1 F (r, θ)) r := by
  have h1 : HasDerivAt (fun s : ℝ => (s, θ)) ((1 : ℝ), (0 : ℝ)) r :=
    (hasDerivAt_id r).prodMk (hasDerivAt_const r θ)
  have h2 := (hF (r, θ)).hasFDerivAt.comp_hasDerivAt r h1
  simpa [d1, Function.comp_def] using h2

/-- Derivative under the integral sign for a `C¹` integrand. -/
theorem paramInt_hasDerivAt {F : ℝ × ℝ → ℂ} (hF : ContDiff ℝ 1 F) (a b r : ℝ) :
    HasDerivAt (fun s => ∫ θ in a..b, F (s, θ)) (∫ θ in a..b, d1 F (r, θ)) r := by
  have hFd : Differentiable ℝ F := hF.differentiable one_ne_zero
  have hd1c : Continuous (d1 F) :=
    ((hF.continuous_fderiv one_ne_zero).clm_apply continuous_const)
  have hK : IsCompact (Icc (r - 1) (r + 1) ×ˢ uIcc a b) := isCompact_Icc.prod isCompact_uIcc
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn hd1c.continuousOn
  have hs : Icc (r - 1) (r + 1) ∈ 𝓝 r := Icc_mem_nhds (by linarith) (by linarith)
  have hFc : Continuous F := hF.continuous
  refine (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun s θ => F (s, θ)) (F' := fun s θ => d1 F (s, θ)) (bound := fun _ => M) hs
    (Eventually.of_forall fun s => ?_) ?_ ?_ ?_ intervalIntegrable_const ?_).2
  · exact (hFc.comp (Continuous.prodMk_right s)).aestronglyMeasurable
  · exact (hFc.comp (Continuous.prodMk_right r)).intervalIntegrable a b
  · exact (hd1c.comp (Continuous.prodMk_right r)).aestronglyMeasurable
  · refine Eventually.of_forall fun t ht x hx => hM (x, t) ⟨hx, ?_⟩
    exact uIoc_subset_uIcc ht
  · exact Eventually.of_forall fun t _ x _ => hasDerivAt_d1 hFd x t

theorem paramInt_deriv {F : ℝ × ℝ → ℂ} (hF : ContDiff ℝ 1 F) (a b : ℝ) :
    deriv (fun s => ∫ θ in a..b, F (s, θ)) = fun r => ∫ θ in a..b, d1 F (r, θ) := by
  funext r
  exact (paramInt_hasDerivAt hF a b r).deriv

/-- `r ↦ ∫_a^b F(r, θ) dθ` is `C^∞` for `F` smooth. -/
theorem paramInt_contDiff {F : ℝ × ℝ → ℂ} (hF : ContDiff ℝ ∞ F) (a b : ℝ) :
    ContDiff ℝ ∞ (fun s => ∫ θ in a..b, F (s, θ)) := by
  rw [contDiff_infty]
  intro n
  induction n generalizing F with
  | zero =>
    rw [Nat.cast_zero, contDiff_zero]
    have h1 : ContDiff ℝ 1 F := hF.of_le (by simp)
    exact continuous_iff_continuousAt.2 fun r =>
      (paramInt_hasDerivAt h1 a b r).continuousAt
  | succ n ih =>
    have h1 : ContDiff ℝ 1 F := hF.of_le (by simp)
    rw [Nat.cast_add, Nat.cast_one, contDiff_succ_iff_deriv]
    refine ⟨fun r => (paramInt_hasDerivAt h1 a b r).differentiableAt, by simp, ?_⟩
    rw [paramInt_deriv h1 a b]
    exact ih (contDiff_d1 hF)

/-! ### Partial derivatives of plane functions along coordinate lines -/

theorem hasDerivAt_pd0 {φ : B0579.Plane → ℝ} (hφ : Differentiable ℝ φ) (q η : ℝ) :
    HasDerivAt (fun s => φ (s, η)) (B0579.pd 0 φ (q, η)) q := by
  have h1 : HasDerivAt (fun s : ℝ => (s, η)) ((1 : ℝ), (0 : ℝ)) q :=
    (hasDerivAt_id q).prodMk (hasDerivAt_const q η)
  have h2 := (hφ (q, η)).hasFDerivAt.comp_hasDerivAt q h1
  simpa [B0579.pd, B0579.dir, Function.comp_def] using h2

theorem hasDerivAt_pd1 {φ : B0579.Plane → ℝ} (hφ : Differentiable ℝ φ) (q η : ℝ) :
    HasDerivAt (fun s => φ (q, s)) (B0579.pd 1 φ (q, η)) η := by
  have h1 : HasDerivAt (fun s : ℝ => (q, s)) ((0 : ℝ), (1 : ℝ)) η :=
    (hasDerivAt_const η q).prodMk (hasDerivAt_id η)
  have h2 := (hφ (q, η)).hasFDerivAt.comp_hasDerivAt η h1
  simpa [B0579.pd, B0579.dir, Function.comp_def] using h2

/-! ### The conjugate horizontal mode -/

theorem conj_eMode (c : ℝ) (k : ℤ) (q : ℝ) :
    conj (eMode c k q) = Complex.exp (-(I * (kappa c k : ℂ) * (q : ℂ))) := by
  unfold eMode kappa
  rw [← Complex.exp_conj]
  congr 1
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I]
  push_cast
  ring

theorem contDiff_conj_eMode (c : ℝ) (k : ℤ) : ContDiff ℝ ∞ (fun q : ℝ => conj (eMode c k q)) := by
  simp_rw [conj_eMode]
  have h : ContDiff ℝ ∞ (fun q : ℝ => -(I * (kappa c k : ℂ) * (q : ℂ))) :=
    (contDiff_const.mul (Complex.ofRealCLM.contDiff)).neg
  exact Complex.contDiff_exp.comp h

theorem hasDerivAt_conj_eMode (c : ℝ) (k : ℤ) (q : ℝ) :
    HasDerivAt (fun q => conj (eMode c k q)) (-(I * (kappa c k : ℂ)) * conj (eMode c k q)) q := by
  simp_rw [conj_eMode]
  have h1 : HasDerivAt (fun q : ℝ => -(I * (kappa c k : ℂ) * (q : ℂ))) (-(I * (kappa c k : ℂ)))
      q := by
    have h0 : HasDerivAt (fun q : ℝ => I * (kappa c k : ℂ) * (q : ℂ)) (I * (kappa c k : ℂ)) q := by
      simpa using ((hasDerivAt_id q).ofReal_comp).const_mul (I * (kappa c k : ℂ))
    exact h0.neg
  have := h1.cexp
  convert this using 1
  ring

theorem eMode_add_period {c : ℝ} (hc : c ≠ 0) (k : ℤ) (q : ℝ) :
    eMode c k (q + c) = eMode c k q := by
  unfold eMode
  have hc' : (c : ℂ) ≠ 0 := by exact_mod_cast hc
  have : (((2 * π * k * (q + c) / c : ℝ) : ℂ) * I) =
      ((2 * π * k * q / c : ℝ) : ℂ) * I + (k : ℂ) * (2 * π * I) := by
    push_cast
    field_simp
  rw [this, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

/-! ### Scalar horizontal coefficients of a test function -/

theorem setIntegral_qInt {c : ℝ} (hc : 0 ≤ c) (f : ℝ → ℂ) :
    ∫ q in qInt c, f q = ∫ q in (-(c / 2))..(c / 2), f q := by
  rw [intervalIntegral.integral_of_le (by linarith), qInt, integral_Ico_eq_integral_Ioo,
    integral_Ioc_eq_integral_Ioo]

/-- `sc c k φ η = ∫_{-c/2}^{c/2} e^{-2πikq/c} φ(q, η) dq` (so `φ_k = c⁻¹ sc c k φ`). -/
def sc (c : ℝ) (k : ℤ) (φ : B0579.Plane → ℝ) (η : ℝ) : ℂ :=
  ∫ q in qInt c, conj (eMode c k q) * (φ (q, η) : ℂ)

/-- The integrand of `sc` with the parameter `η` first. -/
def gInt (c : ℝ) (k : ℤ) (φ : B0579.Plane → ℝ) (p : ℝ × ℝ) : ℂ :=
  conj (eMode c k p.2) * (φ (p.2, p.1) : ℂ)

theorem sc_eq_paramInt {c : ℝ} (hc : 0 ≤ c) (k : ℤ) (φ : B0579.Plane → ℝ) :
    sc c k φ = fun η => ∫ q in (-(c / 2))..(c / 2), gInt c k φ (η, q) := by
  funext η
  rw [sc, setIntegral_qInt hc]
  rfl

theorem contDiff_gInt (c : ℝ) (k : ℤ) {φ : B0579.Plane → ℝ} (hφ : ContDiff ℝ ∞ φ) :
    ContDiff ℝ ∞ (gInt c k φ) := by
  have h1 : ContDiff ℝ ∞ (fun p : ℝ × ℝ => conj (eMode c k p.2)) :=
    (contDiff_conj_eMode c k).comp contDiff_snd
  have h2 : ContDiff ℝ ∞ (fun p : ℝ × ℝ => (φ (p.2, p.1) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (hφ.comp (contDiff_snd.prodMk contDiff_fst))
  exact h1.mul h2

theorem d1_gInt (c : ℝ) (k : ℤ) {φ : B0579.Plane → ℝ} (hφ : ContDiff ℝ ∞ φ) (p : ℝ × ℝ) :
    d1 (gInt c k φ) p = gInt c k (B0579.pd 1 φ) p := by
  have hd : Differentiable ℝ φ := hφ.differentiable (by simp)
  have h1 := hasDerivAt_d1 ((contDiff_gInt c k hφ).differentiable (by simp)) p.1 p.2
  have h2 : HasDerivAt (fun s => gInt c k φ (s, p.2)) (gInt c k (B0579.pd 1 φ) p) p.1 := by
    have := ((hasDerivAt_pd1 hd p.2 p.1).ofReal_comp).const_mul (conj (eMode c k p.2))
    simpa [gInt] using this
  exact h1.unique h2

theorem hasDerivAt_sc {c : ℝ} (hc : 0 ≤ c) (k : ℤ) {φ : B0579.Plane → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (η : ℝ) :
    HasDerivAt (sc c k φ) (sc c k (B0579.pd 1 φ) η) η := by
  rw [sc_eq_paramInt hc, sc_eq_paramInt hc]
  have := paramInt_hasDerivAt ((contDiff_gInt c k hφ).of_le (by simp)) (-(c / 2)) (c / 2) η
  simp_rw [d1_gInt c k hφ] at this
  exact this

theorem contDiff_sc {c : ℝ} (hc : 0 ≤ c) (k : ℤ) {φ : B0579.Plane → ℝ}
    (hφ : ContDiff ℝ ∞ φ) : ContDiff ℝ ∞ (sc c k φ) := by
  rw [sc_eq_paramInt hc]
  exact paramInt_contDiff (contDiff_gInt c k hφ) _ _

theorem sc_eq_zero {c : ℝ} (k : ℤ) {φ : B0579.Plane → ℝ} {R : ℝ}
    (hR : ∀ x : B0579.Plane, R < |x.2| → φ x = 0) {η : ℝ} (hη : R < |η|) : sc c k φ η = 0 := by
  have : ∀ q : ℝ, conj (eMode c k q) * (φ (q, η) : ℂ) = 0 := fun q => by
    rw [hR (q, η) hη]; simp
  simp [sc, this]

theorem hasCompactSupport_sc {c : ℝ} (k : ℤ) {φ : B0579.Plane → ℝ} (hφ : B0579.IsCylTest c φ) :
    HasCompactSupport (sc c k φ) := by
  obtain ⟨R, hR⟩ := hφ.band
  refine HasCompactSupport.intro (isCompact_Icc (a := -R) (b := R)) fun η hη => ?_
  refine sc_eq_zero k hR ?_
  by_contra h
  push Not at h
  exact hη ⟨by linarith [neg_abs_le η], by linarith [le_abs_self η]⟩

/-- **`∂_q` on the horizontal coefficients**: `∫ e^{-iκq} ∂_q φ dq = iκ ∫ e^{-iκq} φ dq`
(integration by parts over one period; the boundary terms cancel by `c`-periodicity). -/
theorem sc_pd0 {c : ℝ} (hc : 0 < c) (k : ℤ) {φ : B0579.Plane → ℝ} (hφ : B0579.IsCylTest c φ)
    (η : ℝ) : sc c k (B0579.pd 0 φ) η = (I * (kappa c k : ℂ)) * sc c k φ η := by
  have hd : Differentiable ℝ φ := hφ.differentiable
  have hcont : Continuous (B0579.pd 0 φ) := (hφ.pd 0).continuous
  simp only [sc]
  rw [setIntegral_qInt hc.le, setIntegral_qInt hc.le]
  have hu : ∀ x ∈ uIcc (-(c / 2)) (c / 2), HasDerivAt (fun q => conj (eMode c k q))
      (-(I * (kappa c k : ℂ)) * conj (eMode c k x)) x := fun x _ => hasDerivAt_conj_eMode c k x
  have hv : ∀ x ∈ uIcc (-(c / 2)) (c / 2), HasDerivAt (fun q => (φ (q, η) : ℂ))
      ((B0579.pd 0 φ (x, η) : ℝ) : ℂ) x := fun x _ => (hasDerivAt_pd0 hd x η).ofReal_comp
  have hu' : IntervalIntegrable (fun x => -(I * (kappa c k : ℂ)) * conj (eMode c k x)) volume
      (-(c / 2)) (c / 2) :=
    (continuous_const.mul (contDiff_conj_eMode c k).continuous).intervalIntegrable _ _
  have hv' : IntervalIntegrable (fun x => ((B0579.pd 0 φ (x, η) : ℝ) : ℂ)) volume
      (-(c / 2)) (c / 2) :=
    (continuous_ofReal.comp (hcont.comp (Continuous.prodMk_left η))).intervalIntegrable _ _
  rw [intervalIntegral.integral_mul_deriv_eq_deriv_mul hu hv hu' hv']
  have hper : φ (c / 2, η) = φ (-(c / 2), η) := by
    have := hφ.periodic (-(c / 2), η)
    simp only at this
    rwa [show -(c / 2) + c = c / 2 by ring] at this
  have hper' : conj (eMode c k (c / 2)) = conj (eMode c k (-(c / 2))) := by
    have := eMode_add_period hc.ne' k (-(c / 2))
    rw [← this]
    congr 2
    ring
  rw [hper, hper', sub_self, zero_sub]
  rw [← intervalIntegral.integral_neg]
  rw [← intervalIntegral.integral_const_mul]
  congr 1
  funext x
  ring

/-! ### Test fields `φ e_j` and their modes -/

/-- The test field `φ(x) e_j` with values in `ℂ²`. -/
def testField (φ : B0579.Plane → ℝ) (j : Fin 2) (x : B0579.Plane) : Vel :=
  ((φ x : ℝ) : ℂ) • EuclideanSpace.single j (1 : ℂ)

theorem norm_testField (φ : B0579.Plane → ℝ) (j : Fin 2) (x : B0579.Plane) :
    ‖testField φ j x‖ = |φ x| := by
  simp [testField, norm_smul]

theorem continuous_testField {φ : B0579.Plane → ℝ} (hφ : Continuous φ) (j : Fin 2) :
    Continuous (testField φ j) :=
  (continuous_ofReal.comp hφ).smul continuous_const

theorem memLp_cellVol_of_isCylTest {c : ℝ} {φ : B0579.Plane → ℝ} (hφ : B0579.IsCylTest c φ) :
    MemLp φ 2 (cellVol c) :=
  (hφ.memLp 0).mono_measure (cellVol_le_cellMeasure c le_rfl)

theorem memLp_testField {c : ℝ} {φ : B0579.Plane → ℝ} (hφ : B0579.IsCylTest c φ) (j : Fin 2) :
    MemLp (testField φ j) 2 (cellVol c) :=
  (memLp_cellVol_of_isCylTest hφ).of_le (continuous_testField hφ.continuous j).aestronglyMeasurable
    (Eventually.of_forall fun x => by rw [norm_testField, Real.norm_eq_abs])

/-- The test field `φ e_j` as an element of `L²(cell; ℂ²)`. -/
def testLp (c : ℝ) {φ : B0579.Plane → ℝ} (hφ : B0579.IsCylTest c φ) (j : Fin 2) :
    Lp Vel 2 (cellVol c) :=
  (memLp_testField hφ j).toLp _

theorem coeFn_testLp (c : ℝ) {φ : B0579.Plane → ℝ} (hφ : B0579.IsCylTest c φ) (j : Fin 2) :
    testLp c hφ j =ᵐ[cellVol c] testField φ j :=
  MemLp.coeFn_toLp _

/-- Pairing with a test field extracts the `j`-th component: `⟪φ e_j, u⟫ = ∫ φ u_j`. -/
theorem inner_testLp (c : ℝ) {φ : B0579.Plane → ℝ} (hφ : B0579.IsCylTest c φ) (j : Fin 2)
    (u : Lp Vel 2 (cellVol c)) :
    ⟪testLp c hφ j, u⟫_ℂ = ∫ x, ((φ x : ℝ) : ℂ) * (u x : Vel) j ∂cellVol c := by
  rw [L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [coeFn_testLp c hφ j] with x hx
  rw [hx, testField, inner_smul_left, EuclideanSpace.inner_single_left, Complex.conj_ofReal,
    map_one, one_mul]

theorem integrable_testLp_mul (c : ℝ) {φ : B0579.Plane → ℝ} (hφ : B0579.IsCylTest c φ)
    (j : Fin 2) (u : Lp Vel 2 (cellVol c)) :
    Integrable (fun x => ((φ x : ℝ) : ℂ) * (u x : Vel) j) (cellVol c) := by
  refine (L2.integrable_inner (𝕜 := ℂ) (testLp c hφ j) u).congr ?_
  filter_upwards [coeFn_testLp c hφ j] with x hx
  rw [hx, testField, inner_smul_left, EuclideanSpace.inner_single_left, Complex.conj_ofReal,
    map_one, one_mul]

theorem modeCoeff_testField (c : ℝ) (k : ℤ) (φ : B0579.Plane → ℝ) (j : Fin 2) (η : ℝ) :
    modeCoeff c k (testField φ j) η =
      (((c⁻¹ : ℝ) : ℂ) * sc c k φ η) • EuclideanSpace.single j (1 : ℂ) := by
  rw [modeCoeff, sc, mul_smul, ← integral_smul_const]
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun q => ?_)
  simp only [testField, smul_smul]

/-- Coefficients only see the a.e. class on the cell, slice by slice. -/
theorem ae_modeCoeff_congr (c : ℝ) (k : ℤ) {f g : B0579.Plane → Vel}
    (hfg : f =ᵐ[cellVol c] g) : ∀ᵐ η ∂(volume : Measure ℝ), modeCoeff c k f η = modeCoeff c k g η := by
  rw [EventuallyEq, ae_cellVol] at hfg
  have h1 := (Measure.measurePreserving_swap (μ := (volume : Measure ℝ)) (ν := μq c)
    ).quasiMeasurePreserving.ae_eq_comp hfg
  have h2 := Measure.ae_ae_of_ae_prod h1
  filter_upwards [h2] with η hη
  rw [modeCoeff, modeCoeff]
  congr 1
  refine integral_congr_ae ?_
  filter_upwards [hη] with q hq
  simp only [Function.comp_apply, Prod.swap_prod_mk] at hq
  rw [hq]

/-- The function `η ↦ √c c⁻¹ sc c k φ η e_j`, the `k`-th mode of `φ e_j`. -/
def tFun (c : ℝ) (k : ℤ) (φ : B0579.Plane → ℝ) (j : Fin 2) (η : ℝ) : Vel :=
  ((Real.sqrt c : ℂ) * (((c⁻¹ : ℝ) : ℂ) * sc c k φ η)) • EuclideanSpace.single j (1 : ℂ)

theorem contDiff_tFun {c : ℝ} (hc : 0 ≤ c) (k : ℤ) {φ : B0579.Plane → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (j : Fin 2) : ContDiff ℝ ∞ (tFun c k φ j) :=
  (contDiff_const.mul (contDiff_const.mul (contDiff_sc hc k hφ))).smul contDiff_const

theorem hasCompactSupport_tFun {c : ℝ} (k : ℤ) {φ : B0579.Plane → ℝ}
    (hφ : B0579.IsCylTest c φ) (j : Fin 2) : HasCompactSupport (tFun c k φ j) := by
  have h : HasCompactSupport (fun η => (Real.sqrt c : ℂ) * (((c⁻¹ : ℝ) : ℂ) * sc c k φ η)) :=
    ((hasCompactSupport_sc k hφ).mul_left).mul_left
  exact h.smul_right

/-- The `k`-th mode of `φ e_j` as a Schwartz function. -/
def tSchwartz (c : ℝ) [hc : Fact (0 < c)] (k : ℤ) {φ : B0579.Plane → ℝ}
    (hφ : B0579.IsCylTest c φ) (j : Fin 2) : SchwartzMap ℝ Vel :=
  (hasCompactSupport_tFun k hφ j).toSchwartzMap (contDiff_tFun hc.out.le k hφ.smooth j)

theorem tSchwartz_apply (c : ℝ) [Fact (0 < c)] (k : ℤ) {φ : B0579.Plane → ℝ}
    (hφ : B0579.IsCylTest c φ) (j : Fin 2) (η : ℝ) : tSchwartz c k hφ j η = tFun c k φ j η :=
  rfl

/-- **The modes of a test field**: `(modes (φ e_j))_k = √c c⁻¹ sc c k φ · e_j`. -/
theorem modes_testLp (c : ℝ) [hc : Fact (0 < c)] (k : ℤ) {φ : B0579.Plane → ℝ}
    (hφ : B0579.IsCylTest c φ) (j : Fin 2) :
    (modes c (testLp c hφ j) : ModeSeq Vel) k = (tSchwartz c k hφ j).toLp 2 := by
  refine Lp.ext ?_
  filter_upwards [modes_apply_ae c k (testLp c hφ j),
    ae_modeCoeff_congr c k (coeFn_testLp c hφ j), (tSchwartz c k hφ j).coeFn_toLp 2]
    with η h1 h2 h3
  rw [h1, h3, h2, tSchwartz_apply, tFun, modeCoeff_testField, smul_smul]

/-- **`∂_q` on modes**: `(modes (∂_q φ e_j))_k = iκ_k (modes (φ e_j))_k`. -/
theorem modes_testLp_pd0 (c : ℝ) [hc : Fact (0 < c)] (k : ℤ) {φ : B0579.Plane → ℝ}
    (hφ : B0579.IsCylTest c φ) (j : Fin 2) :
    (modes c (testLp c (hφ.pd 0) j) : ModeSeq Vel) k =
      (I * (kappa c k : ℂ)) • (modes c (testLp c hφ j) : ModeSeq Vel) k := by
  rw [modes_testLp, modes_testLp]
  refine Lp.ext ?_
  filter_upwards [(tSchwartz c k (hφ.pd 0) j).coeFn_toLp 2, (tSchwartz c k hφ j).coeFn_toLp 2,
    Lp.coeFn_smul (I * (kappa c k : ℂ)) ((tSchwartz c k hφ j).toLp 2)] with η h1 h2 h3
  rw [h3, Pi.smul_apply, h2, h1, tSchwartz_apply, tSchwartz_apply, tFun, tFun,
    sc_pd0 hc.out k hφ, smul_smul]
  congr 1
  ring

theorem hasDerivAt_tFun {c : ℝ} (hc : 0 ≤ c) (k : ℤ) {φ : B0579.Plane → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (j : Fin 2) (η : ℝ) :
    HasDerivAt (tFun c k φ j) (tFun c k (B0579.pd 1 φ) j η) η := by
  have h := ((hasDerivAt_sc hc k hφ η).const_mul (((c⁻¹ : ℝ) : ℂ))).const_mul
    ((Real.sqrt c : ℂ))
  exact h.smul_const (EuclideanSpace.single j (1 : ℂ))

/-- **`∂_η` on modes, Fourier side**: `𝓕 (modes (∂_η φ e_j))_k (ξ) = 2πiξ 𝓕 (modes (φ e_j))_k (ξ)`
for a.e. `ξ`. -/
theorem fourier_modes_testLp_pd1 (c : ℝ) [hc : Fact (0 < c)] (k : ℤ) {φ : B0579.Plane → ℝ}
    (hφ : B0579.IsCylTest c φ) (j : Fin 2) :
    ((𝓕 ((modes c (testLp c (hφ.pd 1) j) : ModeSeq Vel) k) : Lp Vel 2 (volume : Measure ℝ)) :
        ℝ → Vel) =ᵐ[volume]
      fun ξ => ((2 * π * ξ : ℝ) * I : ℂ) •
        ((𝓕 ((modes c (testLp c hφ j) : ModeSeq Vel) k) : Lp Vel 2 (volume : Measure ℝ)) :
          ℝ → Vel) ξ := by
  rw [modes_testLp, modes_testLp, SchwartzMap.toLp_fourier_eq, SchwartzMap.toLp_fourier_eq]
  have hderiv : deriv (tSchwartz c k hφ j : ℝ → Vel) = (tSchwartz c k (hφ.pd 1) j : ℝ → Vel) := by
    funext η
    exact (hasDerivAt_tFun hc.out.le k hφ.smooth j η).deriv
  have hF : 𝓕 (tSchwartz c k (hφ.pd 1) j : ℝ → Vel) =
      fun ξ : ℝ => (2 * π * I * ξ) • 𝓕 (tSchwartz c k hφ j : ℝ → Vel) ξ := by
    rw [← hderiv]
    exact Real.fourier_deriv (tSchwartz c k hφ j).integrable
      (tSchwartz c k hφ j).differentiable (by rw [hderiv]; exact (tSchwartz c k (hφ.pd 1) j).integrable)
  filter_upwards [(𝓕 (tSchwartz c k (hφ.pd 1) j)).coeFn_toLp 2,
    (𝓕 (tSchwartz c k hφ j)).coeFn_toLp 2] with ξ h1 h2
  rw [h1, h2, SchwartzMap.fourier_coe, SchwartzMap.fourier_coe, hF]
  beta_reduce
  congr 1
  push_cast
  ring

end UnforcedLeray.B0583
