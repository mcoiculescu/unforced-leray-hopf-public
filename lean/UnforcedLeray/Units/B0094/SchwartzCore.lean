import UnforcedLeray.Units.B0094.GaussSchwartz

/-!
# B0094 helper: the oscillator on angular-two Schwartz functions

Blueprint unit B0094 (`eq:st18-t00068`, `paper/main.tex` lines 1503--1505: "Take the tensor
product of the one-dimensional Hermite realizations ... Its selfadjoint closure has Schwartz
core"). After the conjugation `U_G f = f / √G` of B0093 (`eq:st18-t00067`), `D` becomes the
oscillator `Δ - |y|²/16 + 3/2` acting on Schwartz functions `φ` of angular weight two.

* `rot θ`, `IsAngularTwo φ`: `φ(R_θ y) = e^{2iθ} φ(y)` (angular weight two);
* `oscS φ`: the oscillator `Δ - |y|²/16 + 3/2` as a map `𝓢(ℝ², ℂ) → 𝓢(ℝ², ℂ)`
  (`coe_oscS : ⇑(oscS φ) = B0093.oscillator ⇑φ`); it preserves angular weight two
  (`IsAngularTwo.oscS`, the Laplacian commutes with rotations);
* `pairS_oscS`: the oscillator is symmetric on Schwartz functions (integration by parts);
* `schProf φ r = √G(r) φ(r, 0)`: the `X_G` profile of `U_G⁻¹ φ`
  (`angularTwoField_schProf : angularTwoField (schProf φ) = B0093.conjGInv φ`);
* `inner_prof_lag_schProf`: the weak form `⟪D (prof p), U_G⁻¹ φ⟫ = ⟪prof p, U_G⁻¹ (osc φ)⟫` on the
  core vectors, which `B0094.lean` turns into `U_G⁻¹ φ ∈ 𝒟(D)` with `D U_G⁻¹ φ = U_G⁻¹ osc φ`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open Polynomial MeasureTheory Set
open LineDeriv
open scoped SchwartzMap InnerProductSpace ComplexConjugate Real

namespace UnforcedLeray.B0094

open UnforcedLeray.B0010 UnforcedLeray.GaussianVortex

/-! ## Rotations and angular weight two -/

/-- The rotation `R_θ y = (y₁ cos θ - y₂ sin θ, y₁ sin θ + y₂ cos θ)` as a linear map. -/
def rotL (θ : ℝ) : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) :=
  (Real.cos θ • ContinuousLinearMap.fst ℝ ℝ ℝ - Real.sin θ • ContinuousLinearMap.snd ℝ ℝ ℝ).prod
    (Real.sin θ • ContinuousLinearMap.fst ℝ ℝ ℝ + Real.cos θ • ContinuousLinearMap.snd ℝ ℝ ℝ)

theorem rotL_apply (θ : ℝ) (z : ℝ × ℝ) :
    rotL θ z = (Real.cos θ * z.1 - Real.sin θ * z.2, Real.sin θ * z.1 + Real.cos θ * z.2) := by
  simp [rotL]

theorem rotL_neg_rotL (θ : ℝ) (z : ℝ × ℝ) : rotL (-θ) (rotL θ z) = z := by
  rw [rotL_apply, rotL_apply, Real.cos_neg, Real.sin_neg]
  refine Prod.ext ?_ ?_
  · simp only
    linear_combination z.1 * Real.sin_sq_add_cos_sq θ
  · simp only
    linear_combination z.2 * Real.sin_sq_add_cos_sq θ

/-- The rotation `R_θ` of the plane. -/
def rot (θ : ℝ) : (ℝ × ℝ) ≃L[ℝ] (ℝ × ℝ) :=
  ContinuousLinearEquiv.equivOfInverse (rotL θ) (rotL (-θ)) (rotL_neg_rotL θ)
    (fun z => by simpa using rotL_neg_rotL (-θ) z)

theorem rot_apply (θ : ℝ) (z : ℝ × ℝ) :
    rot θ z = (Real.cos θ * z.1 - Real.sin θ * z.2, Real.sin θ * z.1 + Real.cos θ * z.2) :=
  rotL_apply θ z

/-- **Angular weight two**: `φ(R_θ y) = e^{2iθ} φ(y)` for all `θ` and `y`, i.e. `φ` has the
form `f₂(r) e^{2iϑ}` (tex lines 674, 1507--1508). -/
def IsAngularTwo (φ : ℝ × ℝ → ℂ) : Prop :=
  ∀ (θ : ℝ) (z : ℝ × ℝ), φ (rot θ z) = Complex.exp (2 * Complex.I * θ) * φ z

theorem IsAngularTwo.polar {φ : ℝ × ℝ → ℂ} (h : IsAngularTwo φ) (r θ : ℝ) :
    φ (r * Real.cos θ, r * Real.sin θ) = Complex.exp (2 * Complex.I * θ) * φ (r, 0) := by
  have h1 : ((r * Real.cos θ, r * Real.sin θ) : ℝ × ℝ) = rot θ (r, 0) := by
    rw [rot_apply]
    refine Prod.ext ?_ ?_ <;> simp only <;> ring
  rw [h1, h θ]

theorem sz_rot (θ : ℝ) (z : ℝ × ℝ) : sz (rot θ z) = sz z := by
  rw [rot_apply]
  simp only [sz]
  linear_combination (z.1 ^ 2 + z.2 ^ 2) * Real.sin_sq_add_cos_sq θ

theorem wz_rot (θ : ℝ) (z : ℝ × ℝ) :
    wz (rot θ z) = Complex.exp (θ * Complex.I) * wz z := by
  rw [Complex.exp_mul_I, rot_apply]
  simp only [wz]
  push_cast
  linear_combination (-(Complex.sin θ * z.2)) * Complex.I_sq

theorem exp_two_mul_I (θ : ℝ) :
    Complex.exp (2 * Complex.I * θ) = Complex.exp (θ * Complex.I) ^ 2 := by
  rw [sq, ← Complex.exp_add]
  congr 1
  ring

/-! ## The oscillator on Schwartz functions -/

/-- The unit vector `e₁`. -/
def e1 : ℝ × ℝ := (1, 0)

/-- The unit vector `e₂`. -/
def e2 : ℝ × ℝ := (0, 1)

/-- The Laplacian `∂₁² + ∂₂²` on `𝓢(ℝ², ℂ)`. -/
def lapS (φ : 𝓢(ℝ × ℝ, ℂ)) : 𝓢(ℝ × ℝ, ℂ) := ∂_{e1} (∂_{e1} φ) + ∂_{e2} (∂_{e2} φ)

/-- The potential `|y|²/16`. -/
def radS (z : ℝ × ℝ) : ℝ := sz z / 16

theorem hasTemperateGrowth_radS : Function.HasTemperateGrowth radS := by
  have : radS = (fun _ : ℝ × ℝ => (1 / 16 : ℝ)) * sz := by
    funext z
    simp only [radS, Pi.mul_apply]
    ring
  rw [this]
  exact (Function.HasTemperateGrowth.const _).mul hasTemperateGrowth_sz

/-- **The oscillator** `Δ - |y|²/16 + 3/2` (right side of `eq:st18-t00067`) on `𝓢(ℝ², ℂ)`. -/
def oscS (φ : 𝓢(ℝ × ℝ, ℂ)) : 𝓢(ℝ × ℝ, ℂ) :=
  lapS φ - SchwartzMap.smulLeftCLM ℂ radS φ + (3 / 2 : ℝ) • φ

theorem dx_coe (φ : 𝓢(ℝ × ℝ, ℂ)) : B0093.dx ⇑φ = ⇑(∂_{e1} φ : 𝓢(ℝ × ℝ, ℂ)) := by
  funext z
  rw [B0093.dx_eq_fderiv φ.differentiableAt, SchwartzMap.lineDerivOp_apply_eq_fderiv]
  rfl

theorem dy_coe (φ : 𝓢(ℝ × ℝ, ℂ)) : B0093.dy ⇑φ = ⇑(∂_{e2} φ : 𝓢(ℝ × ℝ, ℂ)) := by
  funext z
  rw [B0093.dy_eq_fderiv φ.differentiableAt, SchwartzMap.lineDerivOp_apply_eq_fderiv]
  rfl

theorem coe_lapS (φ : 𝓢(ℝ × ℝ, ℂ)) : ⇑(lapS φ) = B0093.laplacian ⇑φ := by
  funext z
  simp only [B0093.laplacian, dx_coe, dy_coe, lapS, add_apply]

theorem oscS_apply (φ : 𝓢(ℝ × ℝ, ℂ)) (z : ℝ × ℝ) :
    oscS φ z = lapS φ z - (radS z : ℂ) * φ z + (3 / 2 : ℂ) * φ z := by
  simp only [oscS, add_apply, sub_apply, smul_apply,
    SchwartzMap.smulLeftCLM_apply_apply hasTemperateGrowth_radS, Complex.real_smul]
  push_cast
  ring

/-- `oscS` is B0093's `oscillator = Δ - |y|²/16 + 3/2`. -/
theorem coe_oscS (φ : 𝓢(ℝ × ℝ, ℂ)) : ⇑(oscS φ) = B0093.oscillator ⇑φ := by
  funext z
  rw [oscS_apply, B0093.oscillator, ← coe_lapS]
  simp only [Complex.real_smul, radS, sz, radiusSq]
  push_cast
  ring

theorem oscS_smul (c : ℂ) (φ : 𝓢(ℝ × ℝ, ℂ)) : oscS (c • φ) = c • oscS φ := by
  ext z
  simp only [smul_apply, oscS_apply, lapS, lineDerivOp_smul, add_apply,
    smul_eq_mul]
  ring

/-! ## The oscillator commutes with rotations -/

/-- `φ ∘ R_θ`. -/
abbrev rotS (θ : ℝ) (φ : 𝓢(ℝ × ℝ, ℂ)) : 𝓢(ℝ × ℝ, ℂ) :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (rot θ) φ

theorem rotS_apply (θ : ℝ) (φ : 𝓢(ℝ × ℝ, ℂ)) (z : ℝ × ℝ) : rotS θ φ z = φ (rot θ z) := rfl

theorem lineDeriv_rotS (θ : ℝ) (φ : 𝓢(ℝ × ℝ, ℂ)) (v : ℝ × ℝ) :
    ∂_{v} (rotS θ φ) = rotS θ (∂_{rot θ v} φ) :=
  SchwartzMap.lineDerivOp_compCLMOfContinuousLinearEquiv ℂ v (rot θ) φ

theorem rot_e1 (θ : ℝ) : rot θ e1 = Real.cos θ • e1 + Real.sin θ • e2 := by
  rw [rot_apply]
  refine Prod.ext ?_ ?_ <;> simp [e1, e2]

theorem rot_e2 (θ : ℝ) : rot θ e2 = (-Real.sin θ) • e1 + Real.cos θ • e2 := by
  rw [rot_apply]
  refine Prod.ext ?_ ?_ <;> simp [e1, e2]

/-- The Laplacian is rotation invariant (the cross terms cancel; no symmetry of mixed partials
is needed). -/
theorem lapS_rot_dir (θ : ℝ) (φ : 𝓢(ℝ × ℝ, ℂ)) :
    ∂_{rot θ e1} (∂_{rot θ e1} φ) + ∂_{rot θ e2} (∂_{rot θ e2} φ) = lapS φ := by
  rw [rot_e1, rot_e2]
  simp only [lineDerivOp_left_add, lineDerivOp_left_smul, lineDerivOp_add, lineDerivOp_smul]
  ext w
  simp only [lapS, add_apply, smul_apply, Complex.real_smul]
  have hcs : ((Real.sin θ : ℝ) : ℂ) ^ 2 + ((Real.cos θ : ℝ) : ℂ) ^ 2 = 1 := by
    rw [← Complex.ofReal_pow, ← Complex.ofReal_pow, ← Complex.ofReal_add, Real.sin_sq_add_cos_sq,
      Complex.ofReal_one]
  push_cast at hcs ⊢
  linear_combination ((∂_{e1} (∂_{e1} φ)) w + (∂_{e2} (∂_{e2} φ)) w) * hcs

theorem lapS_rotS (θ : ℝ) (φ : 𝓢(ℝ × ℝ, ℂ)) : lapS (rotS θ φ) = rotS θ (lapS φ) := by
  have h : lapS (rotS θ φ) =
      rotS θ (∂_{rot θ e1} (∂_{rot θ e1} φ) + ∂_{rot θ e2} (∂_{rot θ e2} φ)) := by
    ext z
    simp only [lapS, lineDeriv_rotS, add_apply, rotS_apply]
  rw [h, lapS_rot_dir]

theorem radS_rot (θ : ℝ) (z : ℝ × ℝ) : radS (rot θ z) = radS z := by
  simp only [radS, sz_rot]

theorem oscS_rotS (θ : ℝ) (φ : 𝓢(ℝ × ℝ, ℂ)) : oscS (rotS θ φ) = rotS θ (oscS φ) := by
  ext z
  rw [oscS_apply, lapS_rotS]
  simp only [rotS_apply, oscS_apply, radS_rot]

/-- **The oscillator preserves angular weight two** (tex lines 1507--1508). -/
theorem IsAngularTwo.oscS {φ : 𝓢(ℝ × ℝ, ℂ)} (h : IsAngularTwo φ) : IsAngularTwo (oscS φ) := by
  intro θ z
  have hrot : rotS θ φ = Complex.exp (2 * Complex.I * θ) • φ := by
    ext w
    rw [rotS_apply, h θ w, smul_apply, smul_eq_mul]
  have := congrArg (fun ψ : 𝓢(ℝ × ℝ, ℂ) => ψ z) (oscS_rotS θ φ)
  simp only [hrot, oscS_smul, rotS_apply, smul_apply, smul_eq_mul] at this
  exact this.symm

/-! ## Symmetry of the oscillator on Schwartz functions -/

/-- The real-bilinear pairing `(u, v) ↦ conj u * v`. -/
def Lc : ℂ →L[ℝ] ℂ →L[ℝ] ℂ :=
  (ContinuousLinearMap.mul ℝ ℂ).comp (Complex.conjCLE : ℂ →L[ℝ] ℂ)

theorem Lc_apply (u v : ℂ) : Lc u v = conj u * v := by
  simp [Lc]

/-- The planar `L²` pairing `∫ conj(Ψ) φ` of two Schwartz functions. -/
def pairS (Ψ φ : 𝓢(ℝ × ℝ, ℂ)) : ℂ := ∫ z, conj (Ψ z) * φ z

theorem integrable_conj_mul (Ψ φ : 𝓢(ℝ × ℝ, ℂ)) : Integrable (fun z => conj (Ψ z) * φ z) := by
  have := (SchwartzMap.pairing Lc Ψ φ).integrable (μ := volume)
  have h : ⇑(SchwartzMap.pairing Lc Ψ φ) = fun z => conj (Ψ z) * φ z := by
    funext z
    rw [SchwartzMap.pairing_apply_apply, Lc_apply]
  rwa [h] at this

theorem pairS_add_right (Ψ φ χ : 𝓢(ℝ × ℝ, ℂ)) : pairS Ψ (φ + χ) = pairS Ψ φ + pairS Ψ χ := by
  simp only [pairS, add_apply, mul_add]
  exact integral_add (integrable_conj_mul _ _) (integrable_conj_mul _ _)

theorem pairS_sub_right (Ψ φ χ : 𝓢(ℝ × ℝ, ℂ)) : pairS Ψ (φ - χ) = pairS Ψ φ - pairS Ψ χ := by
  simp only [pairS, sub_apply, mul_sub]
  exact integral_sub (integrable_conj_mul _ _) (integrable_conj_mul _ _)

theorem pairS_smul_right (Ψ φ : 𝓢(ℝ × ℝ, ℂ)) (c : ℝ) : pairS Ψ (c • φ) = c • pairS Ψ φ := by
  simp only [pairS, smul_apply]
  rw [← integral_smul]
  congr 1
  funext z
  rw [mul_smul_comm]

theorem pairS_add_left (Ψ Ψ' φ : 𝓢(ℝ × ℝ, ℂ)) : pairS (Ψ + Ψ') φ = pairS Ψ φ + pairS Ψ' φ := by
  simp only [pairS, add_apply, map_add, add_mul]
  exact integral_add (integrable_conj_mul _ _) (integrable_conj_mul _ _)

theorem pairS_sub_left (Ψ Ψ' φ : 𝓢(ℝ × ℝ, ℂ)) : pairS (Ψ - Ψ') φ = pairS Ψ φ - pairS Ψ' φ := by
  simp only [pairS, sub_apply, map_sub, sub_mul]
  exact integral_sub (integrable_conj_mul _ _) (integrable_conj_mul _ _)

theorem pairS_smul_left (Ψ φ : 𝓢(ℝ × ℝ, ℂ)) (c : ℝ) : pairS (c • Ψ) φ = c • pairS Ψ φ := by
  simp only [pairS, smul_apply]
  rw [← integral_smul]
  congr 1
  funext z
  rw [Complex.real_smul, Complex.real_smul, map_mul, Complex.conj_ofReal]
  ring

/-- Two integrations by parts in the direction `v`. -/
theorem pairS_lineDeriv2 (Ψ φ : 𝓢(ℝ × ℝ, ℂ)) (v : ℝ × ℝ) :
    pairS Ψ (∂_{v} (∂_{v} φ)) = pairS (∂_{v} (∂_{v} Ψ)) φ := by
  have h1 := SchwartzMap.integral_bilinear_lineDerivOp_right_eq_neg_left (μ := volume)
    Ψ (∂_{v} φ) Lc v
  have h2 := SchwartzMap.integral_bilinear_lineDerivOp_right_eq_neg_left (μ := volume)
    (∂_{v} Ψ) φ Lc v
  simp only [Lc_apply] at h1 h2
  rw [pairS, pairS, h1, h2, neg_neg]

theorem pairS_radS (Ψ φ : 𝓢(ℝ × ℝ, ℂ)) :
    pairS Ψ (SchwartzMap.smulLeftCLM ℂ radS φ) = pairS (SchwartzMap.smulLeftCLM ℂ radS Ψ) φ := by
  simp only [pairS, SchwartzMap.smulLeftCLM_apply_apply hasTemperateGrowth_radS,
    Complex.real_smul, map_mul, Complex.conj_ofReal]
  congr 1
  funext z
  ring

/-- **Symmetry of the oscillator** on Schwartz functions:
`∫ conj(Ψ) (osc φ) = ∫ conj(osc Ψ) φ`. -/
theorem pairS_oscS (Ψ φ : 𝓢(ℝ × ℝ, ℂ)) : pairS Ψ (oscS φ) = pairS (oscS Ψ) φ := by
  simp only [oscS, lapS, pairS_add_right, pairS_sub_right, pairS_smul_right, pairS_add_left,
    pairS_sub_left, pairS_smul_left, pairS_lineDeriv2, pairS_radS]

/-! ## The `X_G` profile of `U_G⁻¹ φ` -/

/-- The profile `r ↦ √G(r) φ(r, 0)` of `U_G⁻¹ φ = √G φ` (for `φ` of angular weight two,
`U_G⁻¹ φ = (√G(r) φ(r,0)) e^{2iϑ}`, `angularTwoField_schProf`). -/
def schProf (φ : ℝ × ℝ → ℂ) (r : ℝ) : ℂ := (Real.sqrt (radialGaussianWeight r) : ℂ) * φ (r, 0)

theorem continuous_schProf (φ : 𝓢(ℝ × ℝ, ℂ)) : Continuous (schProf φ) := by
  unfold schProf radialGaussianWeight GaussianVortex.radialOmega
  have := φ.continuous
  fun_prop

theorem sqrt_radialGaussianWeight (r : ℝ) :
    Real.sqrt (radialGaussianWeight r) = B0093.sqrtConst * Real.exp (-(r ^ 2 / 8)) := by
  have h := B0093.sqrt_gaussianWeight (r, 0)
  have hw : B0093.gaussianWeight (r, 0) = radialGaussianWeight r := by
    unfold B0093.gaussianWeight radialGaussianWeight planarGaussian GaussianVortex.radialOmega
      radiusSq
    simp
  rw [hw] at h
  rw [h, B0093.halfGaussian]
  simp [radiusSq]

/-- The restriction of a Schwartz function to the line `y₂ = 0`. -/
def lineS (φ : 𝓢(ℝ × ℝ, ℂ)) : 𝓢(ℝ, ℂ) :=
  SchwartzMap.compCLM ℂ (g := fun r : ℝ => ((r, 0) : ℝ × ℝ))
    (by
      have := (ContinuousLinearMap.inl ℝ ℝ ℝ).hasTemperateGrowth
      exact this)
    ⟨1, 1, fun r => by simp [Prod.norm_def]⟩ φ

theorem lineS_apply (φ : 𝓢(ℝ × ℝ, ℂ)) (r : ℝ) : lineS φ r = φ (r, 0) := rfl

/-- `U_G⁻¹ φ` lies in `X_G` for every Schwartz function `φ`. -/
theorem memLp_schProf (φ : 𝓢(ℝ × ℝ, ℂ)) : MemLp (schProf φ) 2 xGMeasure := by
  have hm : AEStronglyMeasurable (schProf φ) (volume.restrict (Ioi 0)) :=
    (continuous_schProf φ).aestronglyMeasurable
  rw [memLp_iff_integrableOn hm]
  set C : ℝ := SchwartzMap.seminorm ℝ 0 0 φ
  have hC : ∀ z, ‖φ z‖ ≤ C := fun z => SchwartzMap.norm_le_seminorm ℝ φ z
  have hint : Integrable (fun r : ℝ => C * (‖r‖ ^ 1 * ‖lineS φ r‖)) :=
    ((lineS φ).integrable_pow_mul volume 1).const_mul C
  refine Integrable.mono' hint.integrableOn ?_ ?_
  · have : Continuous fun r => ‖schProf φ r‖ ^ 2 * ((radialGaussianWeight r)⁻¹ * r) := by
      have h1 := continuous_schProf φ
      unfold radialGaussianWeight GaussianVortex.radialOmega
      fun_prop (disch := intros; positivity)
    exact this.aestronglyMeasurable
  · refine ae_restrict_of_forall_mem measurableSet_Ioi fun r hr => ?_
    have hr' : (0 : ℝ) < r := hr
    have hG := radialGaussianWeight_pos r
    have hsq : ‖schProf φ r‖ ^ 2 * ((radialGaussianWeight r)⁻¹ * r) = ‖φ (r, 0)‖ ^ 2 * r := by
      rw [schProf, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (Real.sqrt_nonneg _), mul_pow, Real.sq_sqrt hG.le]
      field_simp
    rw [hsq, Real.norm_eq_abs, abs_of_nonneg (by positivity), lineS_apply, pow_one,
      Real.norm_eq_abs, abs_of_pos hr']
    have h0 := hC (r, 0)
    have hn := norm_nonneg (φ (r, 0))
    nlinarith [mul_le_mul_of_nonneg_right h0 (mul_nonneg hn hr'.le)]

/-- For `φ` of angular weight two, the planar realization of the profile `schProf φ` is
`U_G⁻¹ φ = √G φ`. -/
theorem angularTwoField_schProf {φ : ℝ × ℝ → ℂ} (h : IsAngularTwo φ) :
    angularTwoField (schProf φ) = B0093.conjGInv φ := by
  funext z
  simp only [angularTwoField, schProf, B0093.conjGInv, polarCoord_apply, Complex.real_smul]
  set ζ := Complex.equivRealProd.symm z with hζ
  have hnorm : Real.sqrt (z.1 ^ 2 + z.2 ^ 2) = ‖ζ‖ := by
    rw [hζ, Complex.equivRealProd_symm_apply, Complex.norm_def, Complex.normSq_apply]
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, mul_zero,
      Complex.ofReal_im, Complex.I_im, mul_one, sub_self, add_zero, Complex.add_im,
      Complex.mul_im, zero_add]
    ring_nf
  have hre : ζ.re = z.1 := by simp [hζ]
  have him : ζ.im = z.2 := by simp [hζ]
  have hz : ((‖ζ‖ * Real.cos (Complex.arg ζ), ‖ζ‖ * Real.sin (Complex.arg ζ)) : ℝ × ℝ) = z := by
    rw [Complex.norm_mul_cos_arg, Complex.norm_mul_sin_arg, hre, him]
  have hw : B0093.gaussianWeight z = radialGaussianWeight (Real.sqrt (z.1 ^ 2 + z.2 ^ 2)) :=
    gaussianWeight_eq_radial z
  rw [hw, hnorm]
  have hp := h.polar ‖ζ‖ (Complex.arg ζ)
  rw [hz] at hp
  rw [hp]
  ring

/-- The profile of `U_G⁻¹ (coreS p)` is the core profile `r² p(r²) e^{-r²/4}`. -/
theorem schProf_coreS (p : ℂ[X]) : schProf (coreS p) = profFun p := by
  funext r
  rw [schProf, coreS_apply, sqrt_radialGaussianWeight]
  simp only [profFun, gauss, wz, sz]
  have hc : (B0093.sqrtConst : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 B0093.sqrtConst_pos.ne'
  have he : Real.exp (-(r ^ 2 / 4)) =
      Real.exp (-(r ^ 2 / 8)) * Real.exp (-((r ^ 2 + 0 ^ 2) / 8)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [he]
  push_cast
  field_simp
  ring

/-- The core functions have angular weight two. -/
theorem isAngularTwo_coreS (p : ℂ[X]) : IsAngularTwo (coreS p) := by
  intro θ z
  rw [coreS_apply, coreS_apply, wz_rot]
  have hs := sz_rot θ z
  have hs' : (rot θ z).1 ^ 2 + (rot θ z).2 ^ 2 = z.1 ^ 2 + z.2 ^ 2 := hs
  rw [hs, hs', exp_two_mul_I]
  ring

/-- `coreS (lag p) = osc (coreS p)`: B0093 conjugates `D` to the oscillator, and `D` maps the core
function of `p` to that of `lag p` (`Planar.lean`). -/
theorem coreS_lag (p : ℂ[X]) : coreS (lag p) = oscS (coreS p) := by
  ext z
  rw [coe_coreS, coe_oscS, ← gaussianOperator_angularTwoField_profFun, ← conjGInv_coreS,
    B0093.conjG_gaussianOperator_conjGInv_schwartz]

/-- The `X_G` pairing of a core vector with `U_G⁻¹ φ` is the planar `L²` pairing of
`U_G (core function)` with `φ`, divided by `2π`. -/
theorem inner_prof_toLp_schProf (a : ℂ[X]) {φ : 𝓢(ℝ × ℝ, ℂ)} (h : IsAngularTwo φ) :
    ⟪prof a, (memLp_schProf φ).toLp _⟫_ℂ = (2 * π : ℂ)⁻¹ * pairS (coreS a) φ := by
  rw [← pairing_eq_inner]
  have hprof : prof a = (memLp_profFun a).toLp _ := rfl
  rw [hprof, pairing_toLp_eq_planar, angularTwoField_schProf h, ← conjGInv_coreS, pairS]
  congr 1
  congr 1
  funext z
  simp only [B0093.conjGInv, Complex.real_smul, map_mul, Complex.conj_ofReal]
  have hG : B0010.gaussianWeight z = B0093.gaussianWeight z := rfl
  have hpos := B0093.gaussianWeight_pos z
  have hsq : ((Real.sqrt (B0093.gaussianWeight z) : ℝ) : ℂ) *
      ((Real.sqrt (B0093.gaussianWeight z) : ℝ) : ℂ) * (((B0093.gaussianWeight z)⁻¹ : ℝ) : ℂ) =
      1 := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt hpos.le, ← Complex.ofReal_mul,
      mul_inv_cancel₀ hpos.ne', Complex.ofReal_one]
  rw [hG]
  linear_combination (conj ((coreS a) z) * φ z) * hsq

/-- **Weak form of `D (U_G⁻¹ φ) = U_G⁻¹ (osc φ)`** on the core: for every polynomial `p`,
`⟪prof (lag p), U_G⁻¹ φ⟫ = ⟪prof p, U_G⁻¹ (osc φ)⟫`. -/
theorem inner_prof_lag_schProf (p : ℂ[X]) {φ : 𝓢(ℝ × ℝ, ℂ)} (h : IsAngularTwo φ) :
    ⟪prof (lag p), (memLp_schProf φ).toLp _⟫_ℂ =
      ⟪prof p, (memLp_schProf (oscS φ)).toLp _⟫_ℂ := by
  rw [inner_prof_toLp_schProf _ h, inner_prof_toLp_schProf _ h.oscS, coreS_lag, pairS_oscS]

end UnforcedLeray.B0094
