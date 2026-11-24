import UnforcedLeray.Units.B0062.Bounds
import UnforcedLeray.Analysis.GaussianVortex.PlanarDefs
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.MeasureTheory.Measure.WithDensity

/-!
# B0062 helper: the transport flow `y ↦ e^{-iΩ(|y|)t} y`

Helper file of blueprint unit **B0062** (`paper/main.tex` lines 1228–1237, label
`eq:st18-t00051`). The explicit group `T(t)f(r,ϑ) = f(r, ϑ - Ω(r)t)` (`eq:st18-t00050`,
`paper/main.tex:1229`) is composition with the flow map
`flow t y = e^{-iΩ(|y|)t} y`, `Ω(r) = e^{-r²/4}` (`eq:st18-t00001`, `paper/main.tex:639`).

* `flow_polar`: in polar coordinates the flow is `(r, ϑ) ↦ (r, ϑ - Ω(r)t)`.
* `flow_flow`, `flow_zero`: the group law.
* `norm_flow`: the flow preserves `|y|`, hence every radial weight.
* `measurePreserving_flow`, `measurePreserving_flow_withDensity`: it preserves area and every
  radially weighted measure (polar coordinates and shift invariance of `∫_{-π}^{π}` of a
  periodic function; adapted from `measurePreserving_rot_radial` in
  `NonUniqueEuler/lean/NonUniqueEuler/H/Sec4/SemigroupConstruct/TransportY.lean`).
* `fderiv_flow_apply`: `DΦ_t(y)v = e^{-iΩt}(v - i t (Dν(y)v - Ω v))`, `ν(y) = Ω(|y|) y`.
* `polyBd_fderiv_flow`, `norm_iteratedFDeriv_flow_le`: the Cartesian derivatives of the flow of
  order `n ≥ 1` are bounded by `C_n (1+|t|)^n` (`paper/main.tex:1231`).
-/

set_option autoImplicit false

noncomputable section

open scoped ContDiff ENNReal Real
open Set MeasureTheory

namespace UnforcedLeray.B0062

/-! ### The profile `Ω` -/

/-- `Ω(r) = e^{-r²/4}` (`eq:st18-t00001`, `paper/main.tex:639`). -/
def Omega (r : ℝ) : ℝ := Real.exp (-(r ^ 2 / 4))

/-- `y ↦ Ω(|y|)` on the plane `ℂ = ℝ²`. -/
def omegaR (y : ℂ) : ℝ := Omega ‖y‖

/-- Bridge to the library's Gaussian profile (B0006): `Ω(|y|) = planarGaussian (y₁, y₂)`. -/
theorem omegaR_eq_planarGaussian (y : ℂ) :
    omegaR y = GaussianVortex.planarGaussian (y.re, y.im) := by
  simp only [omegaR, Omega, GaussianVortex.planarGaussian, GaussianVortex.radiusSq]
  rw [Complex.sq_norm, Complex.normSq_apply]
  ring_nf

theorem omegaR_eq_gauss (y : ℂ) : omegaR y = gauss y.re * gauss y.im := by
  simp only [omegaR, Omega, gauss]
  rw [← Real.exp_add, Complex.sq_norm, Complex.normSq_apply]
  ring_nf

theorem cbInf_omegaR : CbInf omegaR := by
  have h := (cbInf_gauss.comp_clm Complex.reCLM).mul (cbInf_gauss.comp_clm Complex.imCLM)
  have e : omegaR = fun y => (gauss ∘ Complex.reCLM) y * (gauss ∘ Complex.imCLM) y := by
    funext y
    simp [omegaR_eq_gauss]
  rw [e]
  exact h

/-- `ν(y) = Ω(|y|) y`. -/
def nu (y : ℂ) : ℂ := (omegaR y : ℂ) * y

theorem cbInf_nu : CbInf nu := by
  have h1 := ((cbInf_id_mul_gauss.comp_clm Complex.reCLM).mul
    (cbInf_gauss.comp_clm Complex.imCLM)).clm_comp Complex.ofRealCLM
  have h2 := (((cbInf_gauss.comp_clm Complex.reCLM).mul
    (cbInf_id_mul_gauss.comp_clm Complex.imCLM)).clm_comp Complex.ofRealCLM).mul
    (CbInf.const (E := ℂ) Complex.I)
  have h := h1.add h2
  have e : nu = fun y => Complex.ofRealCLM (((fun s => s * gauss s) ∘ Complex.reCLM) y *
      (gauss ∘ Complex.imCLM) y) + Complex.ofRealCLM ((gauss ∘ Complex.reCLM) y *
      ((fun s => s * gauss s) ∘ Complex.imCLM) y) * Complex.I := by
    funext y
    apply Complex.ext <;> simp [nu, omegaR_eq_gauss] <;> ring
  rw [e]
  exact h

/-! ### The phase and the flow -/

/-- The phase `e^{-iΩ(|y|)t}`. -/
def phase (t : ℝ) (y : ℂ) : ℂ := gexp (-(Omega ‖y‖ * t))

/-- The flow map of `D_E = Ω∂_ϑ`: `flow t y = e^{-iΩ(|y|)t} y`, the point with polar coordinates
`(r, ϑ - Ω(r)t)` (`eq:st18-t00050`). -/
def flow (t : ℝ) (y : ℂ) : ℂ := phase t y * y

theorem norm_phase (t : ℝ) (y : ℂ) : ‖phase t y‖ = 1 := norm_gexp _

/-- The flow preserves `|y|` (`paper/main.tex:1231`, "preserves every radial weight"). -/
theorem norm_flow (t : ℝ) (y : ℂ) : ‖flow t y‖ = ‖y‖ := by
  rw [flow, norm_mul, norm_phase, one_mul]

theorem gexp_add (a b : ℝ) : gexp (a + b) = gexp a * gexp b := by
  simp only [gexp, Complex.ofReal_add, add_mul, Complex.exp_add]

theorem gexp_zero : gexp 0 = 1 := by simp [gexp]

/-- Group law of the flow: `Φ_s ∘ Φ_t = Φ_{s+t}`. -/
theorem flow_flow (s t : ℝ) (y : ℂ) : flow s (flow t y) = flow (s + t) y := by
  have h : phase s (flow t y) = phase s y := by rw [phase, phase, norm_flow]
  rw [flow, h, flow, flow, phase, phase, phase, ← mul_assoc, ← gexp_add]
  congr 2
  ring

theorem flow_zero (y : ℂ) : flow 0 y = y := by
  simp [flow, phase, gexp_zero]

theorem flow_neg_flow (t : ℝ) (y : ℂ) : flow (-t) (flow t y) = y := by
  rw [flow_flow, neg_add_cancel, flow_zero]

theorem flow_flow_neg (t : ℝ) (y : ℂ) : flow t (flow (-t) y) = y := by
  rw [flow_flow, add_neg_cancel, flow_zero]

/-- **The explicit group in polar coordinates** (`eq:st18-t00050`): the point `(r, ϑ)` goes to
`(r, ϑ - Ω(r)t)`, so `T(t)f(r,ϑ) = f(r, ϑ - Ω(r)t)`. -/
theorem flow_polar (t : ℝ) {r : ℝ} (hr : 0 ≤ r) (θ : ℝ) :
    flow t ((r : ℂ) * gexp θ) = (r : ℂ) * gexp (θ - Omega r * t) := by
  have hn : ‖(r : ℂ) * gexp θ‖ = r := by
    rw [norm_mul, norm_gexp, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr]
  rw [flow, phase, hn, sub_eq_add_neg, gexp_add]
  ring

/-! ### Smoothness and the derivative of the flow -/

theorem phase_eq (t : ℝ) (y : ℂ) : phase t y = gexp (t * (-omegaR y)) := by
  rw [phase, omegaR]
  congr 1
  ring

theorem cbInf_neg_omegaR : CbInf fun y => -omegaR y := by
  have := cbInf_omegaR.clm_comp (-ContinuousLinearMap.id ℝ ℝ)
  simpa using this

/-- The phases are `PolyBd 0`: `‖D^n e^{-iΩt}‖ ≤ C_n (1+|t|)^n`. -/
theorem polyBd_phase : PolyBd 0 phase := by
  have h := polyBd_gexp cbInf_neg_omegaR
  have e : phase = fun t y => gexp (t * (-omegaR y)) := by
    funext t y
    exact phase_eq t y
  rw [e]
  exact h

theorem contDiff_phase (t : ℝ) : ContDiff ℝ ∞ (phase t) := polyBd_phase.1 t

theorem contDiff_flow (t : ℝ) : ContDiff ℝ ∞ (flow t) :=
  (contDiff_phase t).mul contDiff_id

theorem hasFDerivAt_omegaR (y : ℂ) : HasFDerivAt omegaR (fderiv ℝ omegaR y) y :=
  ((cbInf_omegaR.1.differentiable (by simp)) y).hasFDerivAt

/-- `DΦ_t(y)v = e^{-iΩ(|y|)t} (v - i t (Dν(y)v - Ω(|y|)v))`, `ν(y) = Ω(|y|)y`. -/
theorem fderiv_flow_apply (t : ℝ) (y v : ℂ) :
    fderiv ℝ (flow t) y v =
      phase t y * (v - Complex.I * t * (fderiv ℝ nu y v - omegaR y * v)) := by
  have hω := hasFDerivAt_omegaR y
  have hin : HasFDerivAt (fun y => -(omegaR y * t)) (-(t • fderiv ℝ omegaR y)) y :=
    (hω.mul_const t).neg
  have hph : HasFDerivAt (phase t)
      ((ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ)
        (Complex.I * gexp (-(omegaR y * t)))).comp (-(t • fderiv ℝ omegaR y))) y :=
    (hasDerivAt_gexp _).hasFDerivAt.comp y hin
  have hfl : HasFDerivAt (flow t) (phase t y • ContinuousLinearMap.id ℝ ℂ +
      y • ((ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ)
        (Complex.I * gexp (-(omegaR y * t)))).comp (-(t • fderiv ℝ omegaR y)))) y :=
    hph.mul (hasFDerivAt_id y)
  have hnu : HasFDerivAt nu ((omegaR y : ℂ) • ContinuousLinearMap.id ℝ ℂ +
      y • (Complex.ofRealCLM.comp (fderiv ℝ omegaR y))) y :=
    (Complex.ofRealCLM.hasFDerivAt.comp y hω).mul (hasFDerivAt_id y)
  have hp : gexp (-(omegaR y * t)) = phase t y := rfl
  rw [hfl.fderiv, hnu.fderiv, hp]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.id_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.one_apply,
    ContinuousLinearMap.neg_apply, Complex.ofRealCLM_apply, smul_eq_mul, Complex.real_smul,
    Complex.ofReal_neg, Complex.ofReal_mul]
  ring

/-- The directional derivatives of the flow are `PolyBd 1`. -/
theorem polyBd_fderiv_flow (v : ℂ) : PolyBd 1 (fun t y => fderiv ℝ (flow t) y v) := by
  have hg : CbInf fun y => -(Complex.I * (fderiv ℝ nu y v - (omegaR y : ℂ) * v)) := by
    have h1 := cbInf_nu.dirDeriv v
    have h2 := (cbInf_omegaR.clm_comp Complex.ofRealCLM).mul (CbInf.const (E := ℂ) v)
    have h3 := ((h1.add (h2.clm_comp (-ContinuousLinearMap.id ℝ ℂ))).mul
      (CbInf.const (E := ℂ) Complex.I)).clm_comp (-ContinuousLinearMap.id ℝ ℂ)
    convert h3 using 1
    funext y
    simp only [Complex.ofRealCLM_apply, ContinuousLinearMap.neg_apply,
      ContinuousLinearMap.id_apply]
    ring
  have hB : PolyBd 1 (fun t y => v + t • -(Complex.I * (fderiv ℝ nu y v - (omegaR y : ℂ) * v))) :=
    ((PolyBd.of_cbInf (CbInf.const (E := ℂ) v)).mono (Nat.zero_le 1)).add
      (PolyBd.of_cbInf hg).smul_t
  have h := polyBd_phase.mul hB
  have e : (fun t y => fderiv ℝ (flow t) y v) =
      fun t y => phase t y * (v + t • -(Complex.I * (fderiv ℝ nu y v - (omegaR y : ℂ) * v))) := by
    funext t y
    rw [fderiv_flow_apply, Complex.real_smul]
    ring
  rw [e]
  simpa using h

/-- A real-linear map on `ℂ` is determined by its values at `1` and `i`. -/
theorem clm_apply_eq (L : ℂ →L[ℝ] ℂ) (h : ℂ) : L h = h.re • L 1 + h.im • L Complex.I := by
  have e : h = h.re • (1 : ℂ) + h.im • Complex.I := by
    simp [Complex.real_smul, Complex.re_add_im]
  conv_lhs => rw [e]
  rw [map_add, map_smul, map_smul]

/-- **Polynomial growth of the Cartesian derivatives of the flow** (`paper/main.tex:1231`):
for `n ≥ 1`, `‖D^n Φ_t(y)‖ ≤ C_n (1+|t|)^n` for all `t ∈ ℝ` and `y ∈ ℝ²`. -/
theorem norm_iteratedFDeriv_flow_le (n : ℕ) (hn : 1 ≤ n) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t y, ‖iteratedFDeriv ℝ n (flow t) y‖ ≤ C * (1 + |t|) ^ n := by
  let L1 : ℂ →L[ℝ] ℂ →L[ℝ] ℂ := ContinuousLinearMap.smulRightL ℝ ℂ ℂ Complex.reCLM
  let L2 : ℂ →L[ℝ] ℂ →L[ℝ] ℂ := ContinuousLinearMap.smulRightL ℝ ℂ ℂ Complex.imCLM
  have h := ((polyBd_fderiv_flow 1).clm_comp L1).add ((polyBd_fderiv_flow Complex.I).clm_comp L2)
  have e : (fun t y => L1 (fderiv ℝ (flow t) y 1) + L2 (fderiv ℝ (flow t) y Complex.I)) =
      fun t y => fderiv ℝ (flow t) y := by
    funext t y
    ext h
    simp only [L1, L2, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.smulRightL_apply_apply, ContinuousLinearMap.smulRight_apply,
      Complex.reCLM_apply, Complex.imCLM_apply]
    rw [clm_apply_eq (fderiv ℝ (flow t) y) h]
  rw [e] at h
  obtain ⟨K, hK, hb⟩ := h.2 (n - 1)
  refine ⟨K, hK, fun t y => ?_⟩
  have := hb t y
  rw [norm_iteratedFDeriv_fderiv, Nat.sub_add_cancel hn] at this
  rwa [show 1 + (n - 1) = n by omega] at this

/-! ### Area and radial weights are preserved -/

theorem gexp_periodic : Function.Periodic gexp (2 * π) := by
  intro θ
  simp only [gexp, Complex.ofReal_add, add_mul, Complex.ofReal_mul, Complex.ofReal_ofNat]
  exact Complex.exp_periodic _

theorem polarCoord_symm_eq (p : ℝ × ℝ) : Complex.polarCoord.symm p = (p.1 : ℂ) * gexp p.2 := by
  rw [Complex.polarCoord_symm_apply, gexp, Complex.exp_mul_I, ← Complex.ofReal_cos,
    ← Complex.ofReal_sin]

theorem measurable_polarCoord_symm : Measurable (Complex.polarCoord.symm : ℝ × ℝ → ℂ) := by
  have e : (Complex.polarCoord.symm : ℝ × ℝ → ℂ) = fun p => (p.1 : ℂ) * gexp p.2 :=
    funext polarCoord_symm_eq
  rw [e]
  exact ((Complex.continuous_ofReal.comp continuous_fst).mul
    (contDiff_gexp.continuous.comp continuous_snd)).measurable

/-- Shift invariance of `∫_{-π}^{π}` for `2π`-periodic functions (adapted from
`lintegral_Ioc_shift_of_periodic`, reference `TransportY.lean`). -/
theorem lintegral_Ioo_shift {g : ℝ → ℝ≥0∞} (hg : Function.Periodic g (2 * π)) (c : ℝ) :
    ∫⁻ θ in Ioo (-π) π, g (θ + c) = ∫⁻ θ in Ioo (-π) π, g θ := by
  have hI : ∀ f : ℝ → ℝ≥0∞,
      ∫⁻ θ in Ioo (-π) π, f θ = ∫⁻ θ in Ioc (-π) (-π + 2 * π), f θ := by
    intro f
    rw [show -π + 2 * π = π by ring]
    exact setLIntegral_congr Ioo_ae_eq_Ioc
  rw [hI, hI]
  have : Fact (0 < 2 * π) := ⟨Real.two_pi_pos⟩
  have hA : MeasurableEmbedding fun x : ℝ => x + c :=
    (Homeomorph.addRight c).isClosedEmbedding.measurableEmbedding
  have h1 : ∫⁻ θ in Ioc (-π) (-π + 2 * π), g (θ + c) =
      ∫⁻ θ in Ioc (-π + c) (-π + c + 2 * π), g θ := by
    have := (measurePreserving_add_right volume c).setLIntegral_comp_preimage_emb hA g
      (Ioc (-π + c) (-π + c + 2 * π))
    rw [preimage_add_const_Ioc, show -π + c - c = -π by ring,
      show -π + c + 2 * π - c = -π + 2 * π by ring] at this
    exact this
  have h2 := AddCircle.lintegral_preimage (2 * π) (-π + c) hg.lift
  have h3 := AddCircle.lintegral_preimage (2 * π) (-π) hg.lift
  simp only [Function.Periodic.lift_coe] at h2 h3
  rw [h1, h2, h3]

theorem lintegral_polar {f : ℂ → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ x, f x = ∫⁻ r in Ioi (0 : ℝ), ∫⁻ θ in Ioo (-π) π,
      ENNReal.ofReal r • f (Complex.polarCoord.symm (r, θ)) := by
  rw [← Complex.lintegral_comp_polarCoord_symm, polarCoord_target,
    Measure.volume_eq_prod, ← Measure.prod_restrict, lintegral_prod]
  exact ((ENNReal.measurable_ofReal.comp measurable_fst).smul
    (hf.comp measurable_polarCoord_symm)).aemeasurable

/-- Rotation by an angle depending only on `|x|` leaves Lebesgue integrals invariant. -/
theorem lintegral_comp_rotRadial {φ : ℝ → ℝ} (hφ : Measurable φ) {g : ℂ → ℝ≥0∞}
    (hg : Measurable g) : ∫⁻ x, g (gexp (φ ‖x‖) * x) = ∫⁻ x, g x := by
  have hR : Measurable fun x : ℂ => gexp (φ ‖x‖) * x :=
    (contDiff_gexp.continuous.measurable.comp (hφ.comp measurable_norm)).mul measurable_id
  rw [lintegral_polar (f := fun x => g (gexp (φ ‖x‖) * x)) (hg.comp hR), lintegral_polar hg]
  refine setLIntegral_congr_fun measurableSet_Ioi fun r hr => ?_
  have hr0 : 0 ≤ r := le_of_lt hr
  set G : ℝ → ℝ≥0∞ := fun θ => ENNReal.ofReal r • g ((r : ℂ) * gexp θ) with hG
  have hGp : Function.Periodic G (2 * π) := fun θ => by simp only [hG, gexp_periodic θ]
  have hrot : ∀ θ : ℝ, gexp (φ ‖Complex.polarCoord.symm (r, θ)‖) * Complex.polarCoord.symm (r, θ)
      = (r : ℂ) * gexp (θ + φ r) := by
    intro θ
    rw [polarCoord_symm_eq, norm_mul, norm_gexp, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hr0, gexp_add]
    ring
  calc ∫⁻ θ in Ioo (-π) π, ENNReal.ofReal r •
        g (gexp (φ ‖Complex.polarCoord.symm (r, θ)‖) * Complex.polarCoord.symm (r, θ))
      = ∫⁻ θ in Ioo (-π) π, G (θ + φ r) := lintegral_congr fun θ => by simp only [hG, hrot]
    _ = ∫⁻ θ in Ioo (-π) π, G θ := lintegral_Ioo_shift hGp (φ r)
    _ = ∫⁻ θ in Ioo (-π) π, ENNReal.ofReal r • g (Complex.polarCoord.symm (r, θ)) :=
        lintegral_congr fun θ => by simp only [hG, polarCoord_symm_eq]

/-- A measurable map leaving all `μ`-integrals of nonnegative measurable functions invariant
preserves `μ`. -/
theorem measurePreserving_of_lintegral {μ : Measure ℂ} {R : ℂ → ℂ} (hm : Measurable R)
    (h : ∀ g : ℂ → ℝ≥0∞, Measurable g → ∫⁻ x, g (R x) ∂μ = ∫⁻ x, g x ∂μ) :
    MeasurePreserving R μ μ := by
  refine ⟨hm, Measure.ext fun A hA => ?_⟩
  rw [Measure.map_apply hm hA]
  calc μ (R ⁻¹' A) = ∫⁻ x, (R ⁻¹' A).indicator 1 x ∂μ := (lintegral_indicator_one (hm hA)).symm
    _ = ∫⁻ x, A.indicator 1 (R x) ∂μ := lintegral_congr fun x => by
        by_cases hx : R x ∈ A <;> simp [hx]
    _ = ∫⁻ x, A.indicator 1 x ∂μ := h _ (measurable_one.indicator hA)
    _ = μ A := lintegral_indicator_one hA

theorem flow_eq_rot (t : ℝ) (y : ℂ) : flow t y = gexp ((fun r => -(Omega r * t)) ‖y‖) * y := rfl

theorem measurable_Omega : Measurable Omega :=
  (Real.continuous_exp.comp ((continuous_pow 2).div_const 4).neg).measurable

theorem measurable_flow (t : ℝ) : Measurable (flow t) := (contDiff_flow t).continuous.measurable

theorem lintegral_comp_flow (t : ℝ) {g : ℂ → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ x, g (flow t x) = ∫⁻ x, g x := by
  simp only [flow_eq_rot]
  exact lintegral_comp_rotRadial ((measurable_Omega.mul_const t).neg) hg

/-- **The flow preserves area** (`paper/main.tex:1231`). -/
theorem measurePreserving_flow (t : ℝ) : MeasurePreserving (flow t) volume volume :=
  measurePreserving_of_lintegral (measurable_flow t) fun _ hg => lintegral_comp_flow t hg

/-- **The flow preserves every radial weight** (`paper/main.tex:1231`): for every measurable
radial density `ρ(|y|)`, it preserves `ρ(|y|) dy`. -/
theorem measurePreserving_flow_withDensity (t : ℝ) {ρ : ℝ → ℝ≥0∞} (hρ : Measurable ρ) :
    MeasurePreserving (flow t) (volume.withDensity fun y => ρ ‖y‖)
      (volume.withDensity fun y => ρ ‖y‖) := by
  have hρ' : Measurable fun y : ℂ => ρ ‖y‖ := hρ.comp measurable_norm
  refine measurePreserving_of_lintegral (measurable_flow t) fun g hg => ?_
  have hgc : Measurable fun x => g (flow t x) := hg.comp (measurable_flow t)
  have e1 : ∫⁻ x, g (flow t x) ∂(volume.withDensity fun y => ρ ‖y‖) =
      ∫⁻ x, ρ ‖x‖ * g (flow t x) := lintegral_withDensity_eq_lintegral_mul volume hρ' hgc
  have e2 : ∫⁻ x, g x ∂(volume.withDensity fun y => ρ ‖y‖) = ∫⁻ x, ρ ‖x‖ * g x :=
    lintegral_withDensity_eq_lintegral_mul volume hρ' hg
  rw [e1, e2]
  have e3 : ∀ x, ρ ‖x‖ * g (flow t x) = (fun z => ρ ‖z‖ * g z) (flow t x) := fun x => by
    simp only [norm_flow]
  rw [lintegral_congr e3]
  exact lintegral_comp_flow t (hρ'.mul hg)

end UnforcedLeray.B0062
