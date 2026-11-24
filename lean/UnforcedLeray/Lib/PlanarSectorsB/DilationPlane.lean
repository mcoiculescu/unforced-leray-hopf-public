import UnforcedLeray.Lib.PlanarSectorsB.Dilation

/-!
# The frozen heat dilation on `L²_M` and `𝒳_{0,M}`, and `dilation_conj` (INF12 target P7: B0102)


§5, Level P, target **P7** (`dilation_conj`: `𝓛_a = a⁻²J_a𝓛J_a⁻¹`, `‖J_a‖ ≤ a^{(M-3)/2}`) and
bypass B1 ("the frozen dilation is a uniformly bounded conjugation on `L²_M`").

Manuscript (`paper/main.tex`, lines 1569–1580, `eq:st18-t00074`, blueprint unit `B0102`):
`J_af(y) = a⁻²f(y/√a)`; "scaling Biot–Savart gives the exact identity `𝓛_a = a⁻²J_a𝓛J_a⁻¹`";
"for `a ∈ [1,A]`, `J_a` and its inverse are uniformly bounded on each `H^j_M` by a change of
variables"; "hence the complementary bounds hold uniformly, with time `t/a²`" (here `j = 0`,
decision D7).

By decision D7 the evolution `e^{t𝓛}` is the sector sum `eulerGroupW` (`EulerGroup.lean`), and
the frozen evolution `e^{t𝓛_a}` is the sector sum of the exponentials of the frozen sector
generators `LsecDil` (`Dilation.lean`, defined by the formula of `-V_a·∇ - (K·)·∇E_a`). The
whole-plane identity is therefore stated for the evolutions: `e^{t𝓛_a} = J_a e^{(t/a²)𝓛} J_a⁻¹`,
together with the sector generator identity `dilation_conj_sec`.

Main declarations (namespace `UnforcedLeray.Planar`):
* `dilWFun a F y = a⁻²F(y/√a)` and `dilW hM ha : L2w M →L[ℂ] L2w M` (`coeFn_dilW`),
  `norm_sq_dilW_le`, `norm_dilW_le` (`‖J_a‖ ≤ √(a⁻³max(1,a)^M)`), `norm_dilW_le_of_one_le`
  (`‖J_a‖ ≤ a^{(M-3)/2}`, `a ≥ 1`), `norm_dilW_inv_le_of_one_le` (`‖J_a⁻¹‖ ≤ a^{3/2}`);
* `massCLM_dilW` (`∫J_af = a⁻¹∫f`), `dilW_mem_X0`;
* `sectorProjW_dilW` (`P_nJ_a = J_aP_n`), `dilW_secEmb`, `secProf_dilW` (`(J_af)_n = J_a f_n`),
  `dilW_comp_inv`, `dilW_inv_comp` (`J_a⁻¹ = J_{a⁻¹}`);
* `eulerGroupDil hM ha t = ⊕ₙ exp(t𝓛_{a,n})` and **`dilation_conj`**:
  `eulerGroupDil hM ha t = J_a ∘ eulerGroupW hM (t/a²) ∘ J_a⁻¹`;
* on `𝒳_{0,M}`: `dilX0`, `eulerSemigroupDil` and `dilation_conj_X0`, with the uniform bounds
  `norm_dilX0_conj_le` (`‖J_aSJ_a⁻¹‖ ≤ A^{M/2}‖S‖` for `a ∈ [1,A]`, the transfer of
  complementary bounds) and `norm_eulerSemigroupDil_le_uniform`;
* `LsecDil_eigen`: an eigenvector `𝓛ₙw = zw` gives `𝓛_{a,n}(J_aw) = a⁻²z J_aw` (the unstable
  rates `a⁻²Re λ`, line 1580).

Not built here: `𝒫_a = J_a𝒫J_a⁻¹` and the norm continuity of `a ↦ 𝒫_a` (the projection `𝒫` of
target G-4 is not yet defined).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Real
open scoped ENNReal InnerProductSpace ComplexConjugate

namespace UnforcedLeray.Planar

open UnforcedLeray.Planar.NUE

/-! ### The dilation of planar functions -/

/-- The frozen heat dilation `J_aF(y) = a⁻²F(y/√a)` (`paper/main.tex` line 1571, unit `B0102`),
written with the real scalar action `y/√a = (√a)⁻¹ • y`. -/
def dilWFun (a : ℝ) (F : ℂ → ℂ) (y : ℂ) : ℂ := (((a ^ 2)⁻¹ : ℝ) : ℂ) * F ((√a)⁻¹ • y)

theorem qmp_smul_wMeasure {M c : ℝ} (hc : c ≠ 0) :
    Measure.QuasiMeasurePreserving (fun y : ℂ => c • y) (wMeasure M) (wMeasure M) :=
  (Measure.quasiMeasurePreserving_smul (μ := volume) hc).mono (wMeasure_ac M) (volume_ac M)

theorem sqrt_inv_ne_zero {a : ℝ} (ha : 0 < a) : (√a)⁻¹ ≠ 0 :=
  inv_ne_zero (Real.sqrt_pos.2 ha).ne'

theorem dilWFun_congr {M a : ℝ} (ha : 0 < a) {F G : ℂ → ℂ} (h : F =ᵐ[wMeasure M] G) :
    dilWFun a F =ᵐ[wMeasure M] dilWFun a G := by
  filter_upwards [(qmp_smul_wMeasure (M := M) (sqrt_inv_ne_zero ha)).ae_eq_comp h] with y hy
  simp only [Function.comp_apply] at hy
  simp only [dilWFun, hy]

theorem norm_sq_dilWFun (a : ℝ) (F : ℂ → ℂ) (y : ℂ) :
    ‖dilWFun a F y‖ ^ 2 = (a ^ 4)⁻¹ * ‖F ((√a)⁻¹ • y)‖ ^ 2 := by
  rw [dilWFun, norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]
  congr 1
  rw [inv_pow, ← pow_mul]

theorem density_smul_dilWFun {M a : ℝ} (ha : 0 < a) (F : ℂ → ℂ) (z : ℂ) :
    (B0008.density M (√a • z) : ℝ) * ‖dilWFun a F (√a • z)‖ ^ 2 =
      (a ^ 4)⁻¹ * ((1 + a * ‖z‖ ^ 2) ^ M * ‖F z‖ ^ 2) := by
  have hs : 0 < √a := Real.sqrt_pos.2 ha
  rw [B0008.coe_density, norm_sq_dilWFun, smul_smul, inv_mul_cancel₀ hs.ne', one_smul,
    norm_smul, Real.norm_of_nonneg hs.le, mul_pow, Real.sq_sqrt ha.le]
  ring

theorem integrable_density_sq {M : ℝ} {F : ℂ → ℂ} (hF : MemLp F 2 (wMeasure M)) :
    Integrable (fun y => (B0008.density M y : ℝ) * ‖F y‖ ^ 2) volume := by
  have h : Integrable (fun x => ‖F x‖ ^ 2)
      (volume.withDensity fun y => (B0008.density M y : ℝ≥0∞)) :=
    (memLp_two_iff_integrable_sq_norm hF.1).1 hF
  rw [integrable_withDensity_iff_integrable_smul (B0008.measurable_density M)] at h
  simpa only [NNReal.smul_def, smul_eq_mul] using h

theorem norm_sq_L2w_eq {M : ℝ} (F : L2w M) :
    ‖F‖ ^ 2 = ∫ y, (B0008.density M y : ℝ) * ‖F y‖ ^ 2 := by
  rw [norm_sq_Lp_eq_integral]
  show ∫ x, ‖F x‖ ^ 2 ∂(volume.withDensity fun y => (B0008.density M y : ℝ≥0∞)) = _
  rw [integral_withDensity_eq_integral_smul (B0008.measurable_density M)]
  simp only [NNReal.smul_def, smul_eq_mul]

theorem memLp_dilWFun {M : ℝ} (hM : 1 < M) {a : ℝ} (ha : 0 < a) {F : ℂ → ℂ}
    (hF : MemLp F 2 (wMeasure M)) : MemLp (dilWFun a F) 2 (wMeasure M) := by
  have hs : 0 < √a := Real.sqrt_pos.2 ha
  have hm : AEStronglyMeasurable (dilWFun a F) (wMeasure M) :=
    aestronglyMeasurable_const.mul
      (hF.1.comp_quasiMeasurePreserving (qmp_smul_wMeasure (sqrt_inv_ne_zero ha)))
  rw [memLp_two_iff_integrable_sq_norm hm]
  show Integrable (fun x => ‖dilWFun a F x‖ ^ 2)
    (volume.withDensity fun y => (B0008.density M y : ℝ≥0∞))
  rw [integrable_withDensity_iff_integrable_smul (B0008.measurable_density M)]
  refine (integrable_comp_smul_iff volume
    (fun y => B0008.density M y • ‖dilWFun a F y‖ ^ 2) hs.ne').1 ?_
  show Integrable (fun z : ℂ => B0008.density M (√a • z) • ‖dilWFun a F (√a • z)‖ ^ 2) volume
  simp only [NNReal.smul_def, smul_eq_mul, density_smul_dilWFun ha F]
  refine Integrable.const_mul ?_ _
  have hF2 := integrable_density_sq hF
  have hFv : AEStronglyMeasurable F volume := hF.1.mono_ac (volume_ac M)
  refine (hF2.const_mul (max 1 a ^ M)).mono' ?_ ?_
  · refine (Continuous.aestronglyMeasurable ?_).mul (hFv.norm.pow 2)
    exact Continuous.rpow_const (by fun_prop) fun z => Or.inl (by positivity)
  · refine Eventually.of_forall fun z => ?_
    have hb := one_add_mul_sq_rpow_le (M := M) (by linarith) ha.le ‖z‖
    rw [Real.norm_of_nonneg (by positivity), B0008.coe_density]
    calc (1 + a * ‖z‖ ^ 2) ^ M * ‖F z‖ ^ 2
        ≤ (max 1 a ^ M * (1 + ‖z‖ ^ 2) ^ M) * ‖F z‖ ^ 2 := by gcongr
      _ = max 1 a ^ M * ((1 + ‖z‖ ^ 2) ^ M * ‖F z‖ ^ 2) := by ring

/-- The dilation as a linear map of `L²_M`. -/
def dilWLin {M : ℝ} (hM : 1 < M) {a : ℝ} (ha : 0 < a) : L2w M →ₗ[ℂ] L2w M where
  toFun f := (memLp_dilWFun hM ha (Lp.memLp f)).toLp _
  map_add' f g := by
    rw [← MemLp.toLp_add]
    apply MemLp.toLp_congr
    filter_upwards [dilWFun_congr ha (Lp.coeFn_add f g)] with y hy
    rw [hy]
    simp only [dilWFun, Pi.add_apply]
    ring
  map_smul' c f := by
    rw [RingHom.id_apply, ← MemLp.toLp_const_smul]
    apply MemLp.toLp_congr
    filter_upwards [dilWFun_congr ha (Lp.coeFn_smul c f)] with y hy
    rw [hy]
    simp only [dilWFun, Pi.smul_apply, smul_eq_mul]
    ring

/-- **Change of variables** `y = √a z` (Mathlib `integral_comp_smul`, `finrank ℝ ℂ = 2`). -/
theorem integral_density_dilWFun {M a : ℝ} (ha : 0 < a) (F : ℂ → ℂ) :
    ∫ y, (B0008.density M y : ℝ) * ‖dilWFun a F y‖ ^ 2 =
      (a ^ 3)⁻¹ * ∫ z, (1 + a * ‖z‖ ^ 2) ^ M * ‖F z‖ ^ 2 := by
  have hs : 0 < √a := Real.sqrt_pos.2 ha
  have h := Measure.integral_comp_smul volume
    (fun y => (B0008.density M y : ℝ) * ‖dilWFun a F y‖ ^ 2) √a
  rw [Complex.finrank_real_complex, Real.sq_sqrt ha.le, abs_of_pos (inv_pos.2 ha),
    smul_eq_mul] at h
  simp only [density_smul_dilWFun ha F] at h
  rw [integral_const_mul] at h
  set I := ∫ z : ℂ, (1 + a * ‖z‖ ^ 2) ^ M * ‖F z‖ ^ 2
  set J := ∫ y : ℂ, (B0008.density M y : ℝ) * ‖dilWFun a F y‖ ^ 2
  have hJ : J = a * ((a ^ 4)⁻¹ * I) := by
    rw [h, ← mul_assoc, mul_inv_cancel₀ ha.ne', one_mul]
  rw [hJ]
  field_simp

theorem norm_sq_dilWLin_le {M : ℝ} (hM : 1 < M) {a : ℝ} (ha : 0 < a) (f : L2w M) :
    ‖dilWLin hM ha f‖ ^ 2 ≤ (a ^ 3)⁻¹ * max 1 a ^ M * ‖f‖ ^ 2 := by
  have h1 : ‖dilWLin hM ha f‖ ^ 2 =
      (a ^ 3)⁻¹ * ∫ z, (1 + a * ‖z‖ ^ 2) ^ M * ‖f z‖ ^ 2 := by
    rw [norm_sq_L2w_eq, ← integral_density_dilWFun ha]
    refine integral_congr_ae ?_
    filter_upwards [(volume_ac M).ae_le (memLp_dilWFun hM ha (Lp.memLp f)).coeFn_toLp] with y hy
    show _ * ‖((memLp_dilWFun hM ha (Lp.memLp f)).toLp _ : L2w M) y‖ ^ 2 = _
    rw [hy]
  have h2 : ∫ z, (1 + a * ‖z‖ ^ 2) ^ M * ‖f z‖ ^ 2 ≤
      max 1 a ^ M * ∫ y, (B0008.density M y : ℝ) * ‖f y‖ ^ 2 := by
    rw [← integral_const_mul]
    refine integral_mono_of_nonneg (Eventually.of_forall fun z => by positivity)
      ((integrable_density_sq (Lp.memLp f)).const_mul _) (Eventually.of_forall fun z => ?_)
    have hb := one_add_mul_sq_rpow_le (M := M) (by linarith) ha.le ‖z‖
    simp only
    rw [B0008.coe_density]
    calc (1 + a * ‖z‖ ^ 2) ^ M * ‖f z‖ ^ 2
        ≤ (max 1 a ^ M * (1 + ‖z‖ ^ 2) ^ M) * ‖f z‖ ^ 2 := by gcongr
      _ = max 1 a ^ M * ((1 + ‖z‖ ^ 2) ^ M * ‖f z‖ ^ 2) := by ring
  rw [h1, norm_sq_L2w_eq]
  have ha3 : 0 ≤ (a ^ 3)⁻¹ := by positivity
  calc (a ^ 3)⁻¹ * ∫ z, (1 + a * ‖z‖ ^ 2) ^ M * ‖f z‖ ^ 2
      ≤ (a ^ 3)⁻¹ * (max 1 a ^ M * ∫ y, (B0008.density M y : ℝ) * ‖f y‖ ^ 2) := by gcongr
    _ = (a ^ 3)⁻¹ * max 1 a ^ M * ∫ y, (B0008.density M y : ℝ) * ‖f y‖ ^ 2 := by ring

theorem norm_dilWLin_le {M : ℝ} (hM : 1 < M) {a : ℝ} (ha : 0 < a) (f : L2w M) :
    ‖dilWLin hM ha f‖ ≤ dilConst M a * ‖f‖ := by
  have hK : 0 ≤ (a ^ 3)⁻¹ * max 1 a ^ M := by
    have : (0 : ℝ) ≤ max 1 a := zero_le_one.trans (le_max_left _ _)
    positivity
  rw [← Real.sqrt_sq (norm_nonneg (dilWLin hM ha f)), dilConst,
    ← Real.sqrt_sq (norm_nonneg f), ← Real.sqrt_mul hK]
  exact Real.sqrt_le_sqrt (norm_sq_dilWLin_le hM ha f)

/-- **The frozen heat dilation on `L²_M`**, `J_af(y) = a⁻²f(y/√a)` (`paper/main.tex` line 1571,
unit `B0102`). -/
def dilW {M : ℝ} (hM : 1 < M) {a : ℝ} (ha : 0 < a) : L2w M →L[ℂ] L2w M :=
  (dilWLin hM ha).mkContinuous (dilConst M a) (norm_dilWLin_le hM ha)

theorem coeFn_dilW {M : ℝ} (hM : 1 < M) {a : ℝ} (ha : 0 < a) (f : L2w M) :
    ⇑(dilW hM ha f) =ᵐ[wMeasure M] fun y => (((a ^ 2)⁻¹ : ℝ) : ℂ) * f ((√a)⁻¹ • y) :=
  (memLp_dilWFun hM ha (Lp.memLp f)).coeFn_toLp

theorem norm_sq_dilW_le {M : ℝ} (hM : 1 < M) {a : ℝ} (ha : 0 < a) (f : L2w M) :
    ‖dilW hM ha f‖ ^ 2 ≤ (a ^ 3)⁻¹ * max 1 a ^ M * ‖f‖ ^ 2 :=
  norm_sq_dilWLin_le hM ha f

theorem norm_dilW_le {M : ℝ} (hM : 1 < M) {a : ℝ} (ha : 0 < a) :
    ‖dilW hM ha‖ ≤ dilConst M a :=
  LinearMap.mkContinuous_norm_le _ (dilConst_nonneg M a) _

/-- **`‖J_a‖ ≤ a^{(M-3)/2}` on `L²_M` for `a ≥ 1`** (`paper/main.tex` line 1580; scoping note
§4, B1: `‖J_af‖² ≤ a^{M-3}‖f‖²`). -/
theorem norm_dilW_le_of_one_le {M : ℝ} (hM : 1 < M) {a : ℝ} (ha : 1 ≤ a) :
    ‖dilW (M := M) hM (zero_lt_one.trans_le ha)‖ ≤ a ^ ((M - 3) / 2) :=
  (norm_dilW_le hM _).trans (le_of_eq (dilConst_of_one_le ha))

/-- **`‖J_a⁻¹‖ ≤ a^{3/2}` on `L²_M` for `a ≥ 1`**. -/
theorem norm_dilW_inv_le_of_one_le {M : ℝ} (hM : 1 < M) {a : ℝ} (ha : 1 ≤ a) :
    ‖dilW (M := M) hM (inv_pos.2 (zero_lt_one.trans_le ha))‖ ≤ a ^ (3 / 2 : ℝ) :=
  (norm_dilW_le hM _).trans (le_of_eq (dilConst_inv_of_one_le ha))

/-! ### Mass -/

/-- `∫ J_af = a⁻¹ ∫ f`. -/
theorem massCLM_dilW {M : ℝ} (hM : 1 < M) {a : ℝ} (ha : 0 < a) (f : L2w M) :
    massCLM hM (dilW hM ha f) = ((a⁻¹ : ℝ) : ℂ) * massCLM hM f := by
  rw [massCLM_apply, massCLM_apply]
  rw [integral_congr_ae ((volume_ac M).ae_le (coeFn_dilW hM ha f)), integral_const_mul,
    Measure.integral_comp_smul volume (fun y => f y) (√a)⁻¹, Complex.finrank_real_complex, inv_pow,
    Real.sq_sqrt ha.le, inv_inv, abs_of_pos ha, Complex.real_smul]
  have ha0 : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
  push_cast
  field_simp

theorem dilW_mem_X0 {M : ℝ} (hM : 1 < M) {a : ℝ} (ha : 0 < a) (f : L2w M) (hf : f ∈ X0 hM) :
    dilW hM ha f ∈ X0 hM := by
  have hf' : massCLM hM f = 0 := hf
  show massCLM hM (dilW hM ha f) = 0
  rw [massCLM_dilW, hf', mul_zero]

/-! ### Dilation commutes with the angular decomposition -/

theorem rot_smul (φ c : ℝ) (y : ℂ) : rot φ (c • y) = c • rot φ y := by
  simp only [rot, Complex.real_smul]
  ring

/-- Pointwise: `P_n(J_aF)(y) = a⁻²(P_nF)(y/√a)` for any function `F`. -/
theorem sectorProj_dilWFun (n : ℤ) (a : ℝ) (F : ℂ → ℂ) (y : ℂ) :
    Ang.sectorProj n (dilWFun a F) y = dilWFun a (Ang.sectorProj n F) y := by
  unfold Ang.sectorProj dilWFun
  have e : (fun φ : ℝ => Complex.exp (-((n : ℂ) * φ * Complex.I)) *
      ((((a ^ 2)⁻¹ : ℝ) : ℂ) * F ((√a)⁻¹ • rot φ y))) = fun φ : ℝ =>
      (((a ^ 2)⁻¹ : ℝ) : ℂ) *
        (Complex.exp (-((n : ℂ) * φ * Complex.I)) * F (rot φ ((√a)⁻¹ • y))) := by
    funext φ
    rw [rot_smul]
    ring
  rw [e, intervalIntegral.integral_const_mul]
  ring

/-- **`P_nJ_a = J_aP_n`** on `L²_M` (the dilation is radial). -/
theorem sectorProjW_dilW {M : ℝ} (hM : 1 < M) {a : ℝ} (ha : 0 < a) (n : ℤ) (f : L2w M) :
    sectorProjW M n (dilW hM ha f) = dilW hM ha (sectorProjW M n f) := by
  apply Lp.ext
  have h1 := coeFn_sectorProjW M n (dilW hM ha f)
  have h2 : Ang.sectorProj n ⇑(dilW hM ha f) =ᵐ[wMeasure M] Ang.sectorProj n (dilWFun a f) :=
    (wMeasure_ac M).ae_le (Ang.sectorProj_congr_ae n ((volume_ac M).ae_le (coeFn_dilW hM ha f)))
  have h3 := dilWFun_congr ha (coeFn_sectorProjW M n f)
  have h4 := coeFn_dilW hM ha (sectorProjW M n f)
  filter_upwards [h1, h2, h3, h4] with y hy1 hy2 hy3 hy4
  rw [hy1, hy2, sectorProj_dilWFun, hy4]
  exact hy3.symm

theorem angPhase_smul {c : ℝ} (hc : 0 < c) (n : ℤ) (y : ℂ) :
    Ang.angPhase n (c • y) = Ang.angPhase n y := by
  unfold Ang.angPhase
  congr 1
  rw [norm_smul, Real.norm_of_nonneg hc.le, Complex.real_smul]
  push_cast
  have hc' : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  rw [mul_div_mul_left _ _ hc']

/-- `J_a(w(r)e^{inϑ}) = (J_aw)(r)e^{inϑ}`. -/
theorem dilW_secEmb {M : ℝ} (hM : 1 < M) {a : ℝ} (ha : 0 < a) (n : ℤ) (h : ProfL2 M) :
    dilW hM ha (secEmb M n h) = secEmb M n (dilP hM ha h) := by
  have hs : 0 < √a := Real.sqrt_pos.2 ha
  apply Lp.ext
  have h1 := coeFn_dilW hM ha (secEmb M n h)
  have h2 := dilWFun_congr ha (coeFn_secEmb M n h)
  have h3 := coeFn_secEmb M n (dilP hM ha h)
  have h4 := ofProfile_congr_ae' M n (coeFn_dilP hM ha h)
  filter_upwards [h1, h2, h3, h4] with y hy1 hy2 hy3 hy4
  rw [hy1, hy3, hy4]
  have hy2' := hy2
  simp only [dilWFun] at hy2'
  rw [hy2']
  simp only [Ang.ofProfile, dilFun]
  rw [angPhase_smul (inv_pos.2 hs), norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hs.le),
    inv_mul_eq_div]
  ring

/-- **`(J_af)_n = J_a f_n`**: the sector profiles of `J_af` are the dilated profiles. -/
theorem secProf_dilW {M : ℝ} (hM : 1 < M) {a : ℝ} (ha : 0 < a) (n : ℤ) (f : L2w M) :
    secProf M n (dilW hM ha f) = dilP hM ha (secProf M n f) := by
  apply (secEmb M n).injective
  rw [secEmb_secProf, ← dilW_secEmb, secEmb_secProf, sectorProjW_dilW]

/-- `J_aJ_{a⁻¹} = 1` on `L²_M`. -/
theorem dilW_comp_inv {M : ℝ} (hM : 1 < M) {a : ℝ} (ha : 0 < a) :
    dilW hM ha ∘L dilW (M := M) hM (inv_pos.2 ha) = 1 := by
  ext1 f
  apply eq_of_secProf
  intro n
  rw [ContinuousLinearMap.comp_apply, secProf_dilW, secProf_dilW, ← ContinuousLinearMap.comp_apply,
    ← ContinuousLinearMap.mul_def, dilP_mul_inv]
  rfl

/-- `J_{a⁻¹}J_a = 1` on `L²_M`. -/
theorem dilW_inv_comp {M : ℝ} (hM : 1 < M) {a : ℝ} (ha : 0 < a) :
    dilW (M := M) hM (inv_pos.2 ha) ∘L dilW hM ha = 1 := by
  ext1 f
  apply eq_of_secProf
  intro n
  rw [ContinuousLinearMap.comp_apply, secProf_dilW, secProf_dilW, ← ContinuousLinearMap.comp_apply,
    ← ContinuousLinearMap.mul_def, dilP_inv_mul]
  rfl

/-! ### The frozen evolution and the conjugacy -/

/-- **The frozen evolution** `e^{t𝓛_a} = ⊕ₙ exp(t𝓛_{a,n})` on `L²_M` (decision D7, with the
frozen sector generators `LsecDil` of `paper/main.tex` line 1572). -/
def eulerGroupDil {M : ℝ} (hM : 1 < M) {a : ℝ} (ha : 0 < a) (t : ℝ) : L2w M →L[ℂ] L2w M :=
  sectorSum (fun n => NormedSpace.exp ((t : ℂ) • LsecDil hM ha n))
    (fun n => norm_exp_LsecDil_le hM ha n t)
    (mul_nonneg (mul_nonneg (dilConst_nonneg M a) (dilConst_nonneg M a⁻¹)) (Real.exp_pos _).le)

theorem secProf_eulerGroupDil {M : ℝ} (hM : 1 < M) {a : ℝ} (ha : 0 < a) (t : ℝ) (f : L2w M)
    (n : ℤ) :
    secProf M n (eulerGroupDil hM ha t f) =
      NormedSpace.exp ((t : ℂ) • LsecDil hM ha n) (secProf M n f) :=
  secProf_sectorSum _ _ _ f n

/-- **P7, `dilation_conj`** (`eq:st18-t00074`, `paper/main.tex` lines 1574–1578, unit `B0102`):
`e^{t𝓛_a} = J_a e^{(t/a²)𝓛} J_a⁻¹` on `L²_M` for every `a > 0` and `t ∈ ℝ`, where `𝓛_a` is the
frozen generator (`dilation_conj_sec`: `𝓛_{a,n} = a⁻²J_a𝓛ₙJ_a⁻¹` on every sector) and
`J_a⁻¹ = J_{a⁻¹}` (`dilW_comp_inv`, `dilW_inv_comp`). -/
theorem dilation_conj {M : ℝ} (hM : 1 < M) {a : ℝ} (ha : 0 < a) (t : ℝ) :
    eulerGroupDil hM ha t =
      dilW hM ha ∘L eulerGroupW hM (t / a ^ 2) ∘L dilW hM (inv_pos.2 ha) := by
  ext1 f
  apply eq_of_secProf
  intro n
  rw [secProf_eulerGroupDil, exp_LsecDil]
  simp only [ContinuousLinearMap.comp_apply]
  rw [secProf_dilW, secProf_eulerGroupW, secProf_dilW]

/-- The frozen evolution conserves the mass, hence acts on `𝒳_{0,M}`. -/
theorem eulerGroupDil_mem_X0 {M : ℝ} (hM : 1 < M) {a : ℝ} (ha : 0 < a) (t : ℝ) (f : L2w M)
    (hf : f ∈ X0 hM) : eulerGroupDil hM ha t f ∈ X0 hM := by
  rw [dilation_conj, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply]
  exact dilW_mem_X0 hM ha _ (eulerGroupW_mem_X0 hM _ _ (dilW_mem_X0 hM _ f hf))

/-! ### On `𝒳_{0,M}` -/

/-- `J_a` on `𝒳_{0,M}`. -/
def dilX0 {M : ℝ} (hM : 1 < M) {a : ℝ} (ha : 0 < a) : X0 hM →L[ℂ] X0 hM :=
  Infra.ExpSemigroup.restrictOp (dilW hM ha) (X0 hM) (dilW_mem_X0 hM ha)

@[simp] theorem coe_dilX0_apply {M : ℝ} (hM : 1 < M) {a : ℝ} (ha : 0 < a) (f : X0 hM) :
    (dilX0 hM ha f : L2w M) = dilW hM ha f := rfl

theorem norm_dilX0_le {M : ℝ} (hM : 1 < M) {a : ℝ} (ha : 0 < a) :
    ‖dilX0 hM ha‖ ≤ dilConst M a :=
  (Infra.ExpSemigroup.norm_restrictOp_le _ _ _).trans (norm_dilW_le hM ha)

/-- The frozen evolution `e^{t𝓛_a}` on `𝒳_{0,M}`. -/
def eulerSemigroupDil {M : ℝ} (hM : 1 < M) {a : ℝ} (ha : 0 < a) (t : ℝ) : X0 hM →L[ℂ] X0 hM :=
  Infra.ExpSemigroup.restrictOp (eulerGroupDil hM ha t) (X0 hM) (eulerGroupDil_mem_X0 hM ha t)

/-- **P7, `dilation_conj` on `𝒳_{0,M}`**: `e^{t𝓛_a} = J_a e^{(t/a²)𝓛} J_a⁻¹`. -/
theorem dilation_conj_X0 {M : ℝ} (hM : 1 < M) {a : ℝ} (ha : 0 < a) (t : ℝ) :
    eulerSemigroupDil hM ha t =
      dilX0 hM ha ∘L eulerSemigroup hM (t / a ^ 2) ∘L dilX0 hM (inv_pos.2 ha) := by
  ext1 f
  apply Subtype.ext
  show eulerGroupDil hM ha t f = _
  rw [dilation_conj]
  rfl

theorem dilX0_comp_inv {M : ℝ} (hM : 1 < M) {a : ℝ} (ha : 0 < a) :
    dilX0 hM ha ∘L dilX0 (M := M) hM (inv_pos.2 ha) = 1 := by
  ext1 f
  apply Subtype.ext
  show (dilW hM ha ∘L dilW hM (inv_pos.2 ha)) f = f
  rw [dilW_comp_inv]
  rfl

/-- **Uniform transfer of bounds for `a ∈ [1,A]`** (`paper/main.tex` line 1580: "the
complementary bounds hold uniformly"): `‖J_a S J_a⁻¹‖ ≤ A^{M/2}‖S‖` for every operator `S` on
`𝒳_{0,M}`. -/
theorem norm_dilX0_conj_le {M : ℝ} (hM : 1 < M) {a A : ℝ} (ha : 1 ≤ a) (haA : a ≤ A)
    (S : X0 hM →L[ℂ] X0 hM) :
    ‖dilX0 hM (zero_lt_one.trans_le ha) ∘L S ∘L dilX0 hM (inv_pos.2 (zero_lt_one.trans_le ha))‖ ≤
      A ^ (M / 2) * ‖S‖ := by
  have ha0 : 0 < a := zero_lt_one.trans_le ha
  calc ‖dilX0 hM ha0 ∘L S ∘L dilX0 hM (inv_pos.2 ha0)‖
      ≤ ‖dilX0 hM ha0‖ * (‖S‖ * ‖dilX0 hM (inv_pos.2 ha0)‖) :=
        (ContinuousLinearMap.opNorm_comp_le _ _).trans
          (mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _)
            (ContinuousLinearMap.opNorm_nonneg _))
    _ ≤ dilConst M a * (‖S‖ * dilConst M a⁻¹) :=
        mul_le_mul (norm_dilX0_le hM ha0)
          (mul_le_mul_of_nonneg_left (norm_dilX0_le hM _) (norm_nonneg S))
          (by positivity) (dilConst_nonneg M a)
    _ = dilConst M a * dilConst M a⁻¹ * ‖S‖ := by ring
    _ ≤ A ^ (M / 2) * ‖S‖ :=
        mul_le_mul_of_nonneg_right (dilConst_mul_inv_le hM ha haA) (norm_nonneg S)

/-- **Uniform frozen bound for `a ∈ [1,A]`**: `‖e^{t𝓛_a}‖ ≤ A^{M/2} e^{|t| B_M}` on `𝒳_{0,M}`. -/
theorem norm_eulerSemigroupDil_le_uniform {M : ℝ} (hM : 1 < M) {a A : ℝ} (ha : 1 ≤ a)
    (haA : a ≤ A) (t : ℝ) :
    ‖eulerSemigroupDil hM (zero_lt_one.trans_le ha) t‖ ≤
      A ^ (M / 2) * Real.exp (|t| * lsecBound hM) := by
  have ha0 : 0 < a := zero_lt_one.trans_le ha
  rw [dilation_conj_X0]
  refine (norm_dilX0_conj_le hM ha haA _).trans ?_
  refine mul_le_mul_of_nonneg_left ((norm_eulerSemigroup_le hM _).trans ?_)
    (Real.rpow_nonneg (by linarith) _)
  have h1 : |t / a ^ 2| ≤ |t| := by
    rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < a ^ 2)]
    exact div_le_self (abs_nonneg t) (one_le_pow₀ ha)
  exact Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right h1 (lsecBound_nonneg hM))

/-! ### Eigenvalues: the unstable rates `a⁻²λ` -/

/-- **Eigenvectors transfer** (`paper/main.tex` line 1580, "the unstable rates `a⁻²Re λ`"): if
`𝓛ₙw = zw` then `𝓛_{a,n}(J_aw) = a⁻²z J_aw`. -/
theorem LsecDil_eigen {M : ℝ} (hM : 1 < M) {a : ℝ} (ha : 0 < a) (n : ℤ) {z : ℂ}
    {w : ProfL2 M} (hw : Lsec hM n w = z • w) :
    LsecDil hM ha n (dilP hM ha w) = ((((a ^ 2)⁻¹ : ℝ) : ℂ) * z) • dilP hM ha w := by
  rw [dilation_conj_sec, ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.comp_apply, ← ContinuousLinearMap.comp_apply (dilP hM (inv_pos.2 ha)),
    ← ContinuousLinearMap.mul_def, dilP_inv_mul, ContinuousLinearMap.one_apply, hw, map_smul,
    smul_smul]

end UnforcedLeray.Planar
