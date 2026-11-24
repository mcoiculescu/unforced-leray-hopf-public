import UnforcedLeray.Lib.PlanarSpectralB.SimpleProj
import UnforcedLeray.Lib.ComplexODEC

/-!
# The growing spectrum of `L₀` on `X_G` and the decay of the complement (INF10 target G-6)


§5, Level G, target **G-6** (`X_G`: `σ(L₀) ∩ {Re > 0} = {λ}`;
`‖exp(t(L₀ - λ)) Q‖ ≤ C_δ exp(-(γ - δ)t)`, `eq:st18-t00063`). Manuscript (`paper/main.tex`):
lines 1424–1448 (units `B0087`: `L₀ = -2iΩ + 2ikR` bounded, a compact perturbation of imaginary
multiplication; `B0088`: `σ(L₀) ∩ {Re z > 0} = {λ}`, algebraically simple; `B0089`,
`eq:st18-t00063`: `‖e^{t(L₀ - λ)}Q‖_{X_G → X_G} ≤ C_δ e^{-(γ - δ)t}`), and line 1388
(unit `B0082`: "In `X_G` this transfer is even immediate").

**Route.** `X_G = L²((0,∞), G⁻¹ r dr)` embeds continuously and injectively into the profile
space `L²_2 = L²((0,∞), 2πr(1 + r²)² dr)` (`profileMeasure_two_le`: `(1 + r²)² ≤ 32 e^{r²/4}`),
and the embedding intertwines `L₀` with the sector generator `𝓛₂` (`xgEmb_L0`). Hence
eigenvectors of `L₀` with `Re z > 0` are eigenvectors of `𝓛₂` (G-2), the eigenfunctional of G-3
pulls back, and the abstract `isSimpleSpectralProj_of_compact` applies to
`L₀ = -2iΩ + 2ikR` on `X_G` (compactness: the compiled draft `isCompactOperator_kR`).

Main declarations (namespace `UnforcedLeray.Planar`): `profileMeasure_two_le`, `xgEmb`,
`coeFn_xgEmb`, `xgEmb_injective`, `xgEmb_L0`, `isUnit_sub_L0_transport`,
`exists_eigen_of_mem_spectrum_L0`, `L0_eigen_unique`, `spectrum_L0_rightHalf_subsingleton`,
`spectrum_L0_rightHalf_eq_singleton`, `exists_isSimpleSpectralProj_L0`,
`re_le_zero_of_mem_spectrum_L0`, `exists_adjoint_eigenvector_L0`, `exp_smul_sub_smul_one`, **`norm_exp_L0_sub_mul_one_sub_le`**
(`eq:st18-t00063`).

**Input.** The growing mode `q ∈ X_G`, `L₀ q = λ q`, `Re λ = γ > 0` (Prop.
`gaussian-existence`, INF18 part of block 3F) is a hypothesis.

Status: draft; Theorem A is not proved.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Real
open scoped ENNReal NNReal InnerProductSpace ComplexConjugate

namespace UnforcedLeray.Planar

open UnforcedLeray.GaussianVortex (radialOmega radialK radialOmega_pos)
open UnforcedLeray.Infra.Dunford (IsSimpleSpectralProj rankOneProj)
open UnforcedLeray.Infra.CompactPerturb (mem_spectrum_of_eigen)

/-! ### The embedding `X_G → L²_2` -/

/-- `2πr(1 + r²)² ≤ 16 · 4π e^{r²/4} r`: the profile measure of weight `M = 2` is dominated by
`16` times the `X_G` measure `G⁻¹ r dr`. -/
theorem profileMeasure_two_le : profileMeasure 2 ≤ (16 : ℝ≥0∞) • B0010.xGMeasure := by
  rw [profileMeasure, B0010.xGMeasure, ← withDensity_smul' (16 : ℝ≥0∞) _ (by norm_num)]
  refine withDensity_mono ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
  have hr0 : 0 < r := hr
  rw [Pi.smul_apply, smul_eq_mul, B0010.xGDensity_eq]
  rw [show ((Real.toNNReal (4 * π * Real.exp (r ^ 2 / 4) * r) : ℝ≥0) : ℝ≥0∞) =
      ENNReal.ofReal (4 * π * Real.exp (r ^ 2 / 4) * r) from rfl]
  rw [← ENNReal.ofReal_ofNat 16, ← ENNReal.ofReal_mul (by norm_num)]
  apply ENNReal.ofReal_le_ofReal
  rw [Real.rpow_two]
  have hx := Real.quadratic_le_exp_of_nonneg (by positivity : (0 : ℝ) ≤ r ^ 2 / 4)
  have h1 : (1 + r ^ 2) ^ 2 ≤ 32 * Real.exp (r ^ 2 / 4) := by
    nlinarith [sq_nonneg r, sq_nonneg (r ^ 2)]
  have hr' : 0 ≤ 2 * π * r := by positivity
  calc 2 * π * r * (1 + r ^ 2) ^ 2 ≤ 2 * π * r * (32 * Real.exp (r ^ 2 / 4)) :=
        mul_le_mul_of_nonneg_left h1 hr'
    _ = 16 * (4 * π * Real.exp (r ^ 2 / 4) * r) := by ring

theorem profile_two_ac_xG : profileMeasure 2 ≪ B0010.xGMeasure :=
  Measure.absolutelyContinuous_of_le_smul profileMeasure_two_le

theorem xG_ac_profile_two : B0010.xGMeasure ≪ profileMeasure 2 :=
  B0012.xG_ac.trans (ac_profileMeasure 2)

theorem memLp_xgEmb (f : B0010.XG) : MemLp (⇑f) 2 (profileMeasure 2) :=
  (Lp.memLp f).of_measure_le_smul (by norm_num) profileMeasure_two_le

/-- The embedding `X_G → L²_2` as a linear map (same profile). -/
def xgEmbLin : B0010.XG →ₗ[ℂ] ProfL2 2 where
  toFun f := (memLp_xgEmb f).toLp _
  map_add' f g := by
    apply Lp.ext
    filter_upwards [(memLp_xgEmb (f + g)).coeFn_toLp, (memLp_xgEmb f).coeFn_toLp,
      (memLp_xgEmb g).coeFn_toLp,
      Lp.coeFn_add ((memLp_xgEmb f).toLp _) ((memLp_xgEmb g).toLp _),
      profile_two_ac_xG.ae_le (Lp.coeFn_add f g)] with r h1 h2 h3 h4 h5
    rw [h1, h4, Pi.add_apply, h2, h3, h5, Pi.add_apply]
  map_smul' a f := by
    simp only [RingHom.id_apply]
    apply Lp.ext
    filter_upwards [(memLp_xgEmb (a • f)).coeFn_toLp, (memLp_xgEmb f).coeFn_toLp,
      Lp.coeFn_smul a ((memLp_xgEmb f).toLp _),
      profile_two_ac_xG.ae_le (Lp.coeFn_smul a f)] with r h1 h2 h3 h4
    rw [h1, h3, Pi.smul_apply, h2, h4, Pi.smul_apply]

/-- The embedding constant `16^{1/2}`. -/
def xgEmbConst : ℝ := ((16 : ℝ≥0∞) ^ ((1 / (2 : ℝ≥0∞)).toReal)).toReal

theorem norm_xgEmbLin_le (f : B0010.XG) : ‖xgEmbLin f‖ ≤ xgEmbConst * ‖f‖ := by
  have h := eLpNorm_le_of_measure_le_smul profileMeasure_two_le (f := ⇑f) (p := 2)
  rw [smul_eq_mul] at h
  have hK : (16 : ℝ≥0∞) ^ ((1 / (2 : ℝ≥0∞)).toReal) ≠ ⊤ :=
    ENNReal.rpow_ne_top_of_nonneg (by positivity) (by norm_num)
  change ‖(memLp_xgEmb f).toLp _‖ ≤ _
  rw [Lp.norm_toLp, Lp.norm_def, xgEmbConst, ← ENNReal.toReal_mul]
  exact ENNReal.toReal_mono (ENNReal.mul_ne_top hK (Lp.eLpNorm_ne_top f)) h

/-- **The embedding** `X_G → L²_2` (`f₂ ↦ f₂`), bounded (tex line 1388). -/
def xgEmb : B0010.XG →L[ℂ] ProfL2 2 := xgEmbLin.mkContinuous xgEmbConst norm_xgEmbLin_le

theorem coeFn_xgEmb (f : B0010.XG) : ⇑(xgEmb f) =ᵐ[profileMeasure 2] ⇑f :=
  (memLp_xgEmb f).coeFn_toLp

theorem xgEmb_injective {f : B0010.XG} (h : xgEmb f = 0) : f = 0 := by
  have h1 : ⇑f =ᵐ[profileMeasure 2] (0 : ℝ → ℂ) := by
    filter_upwards [coeFn_xgEmb f, Lp.coeFn_zero ℂ 2 (profileMeasure 2)] with r h1 h2
    rw [← h1, h, h2]
  apply Lp.ext
  filter_upwards [xG_ac_profile_two.ae_le h1, Lp.coeFn_zero ℂ 2 B0010.xGMeasure] with r h1 h2
  rw [h1, h2]

theorem xgEmb_ne_zero {f : B0010.XG} (h : f ≠ 0) : xgEmb f ≠ 0 := fun h0 =>
  h (xgEmb_injective h0)

/-- **The embedding intertwines `L₀` with the sector-two generator**:
`xgEmb (L₀ f) = 𝓛₂ (xgEmb f)` (both are `-2iΩ f + 2ik Δ₂⁻¹ f`, tex lines 685–689, 662–670). -/
theorem xgEmb_L0 (f : B0010.XG) : xgEmb (L0 f) = Lsec one_lt_two 2 (xgEmb f) := by
  have h2 : (2 : ℤ).natAbs = 2 := rfl
  apply Lp.ext
  filter_upwards [coeFn_xgEmb (L0 f), profile_two_ac_xG.ae_le (coeFn_L0 f),
    coeFn_Lsec one_lt_two 2 (xgEmb f), coeFn_xgEmb f] with r h1 h3 h4 h5
  rw [h1, h3, h4, h5, h2, greenN_congr 2 (coeFn_xgEmb f)]
  push_cast
  ring

/-! ### Spectrum of `L₀` in the right half-plane -/

theorem isUnit_sub_L0_transport {z : ℂ} (hz : 0 < z.re) :
    IsUnit (algebraMap ℂ (B0010.XG →L[ℂ] B0010.XG) z - (-2 * Complex.I) • B0012.omegaOp) :=
  isUnit_sub_smul_omega B0012.omegaOp B0012.coeFn_omegaOp (by simp) hz

theorem isCompactOperator_L0_coupling : IsCompactOperator ((2 * Complex.I) • B0012.kROp) :=
  isCompactOperator_kR.smul (2 * Complex.I)

/-- For `Re z > 0`, every spectral point of `L₀` on `X_G` is an eigenvalue (B0088). -/
theorem exists_eigen_of_mem_spectrum_L0 {z : ℂ} (hz : 0 < z.re) (h : z ∈ spectrum ℂ L0) :
    ∃ w : B0010.XG, w ≠ 0 ∧ L0 w = z • w :=
  Infra.CompactPerturb.exists_eigen_of_mem_spectrum isCompactOperator_L0_coupling
    (isUnit_sub_L0_transport hz) h

/-- An `X_G` eigenvector of `L₀` with `Re z > 0` is a sector-two eigenvector in `L²_2`. -/
theorem Lsec_xgEmb_eigen {z : ℂ} {w : B0010.XG} (hw : L0 w = z • w) :
    Lsec one_lt_two 2 (xgEmb w) = z • xgEmb w := by
  rw [← xgEmb_L0, hw, map_smul]

/-- **Uniqueness on `X_G`** (B0088): eigenvectors of `L₀` with eigenvalues in `{Re z > 0}` have
the same eigenvalue and are proportional. -/
theorem L0_eigen_unique {z z' : ℂ} (hz : 0 < z.re) (hz' : 0 < z'.re) {w w' : B0010.XG}
    (hw : L0 w = z • w) (hw' : L0 w' = z' • w') (h0 : w ≠ 0) (h0' : w' ≠ 0) :
    z' = z ∧ ∃ μ : ℂ, w' = μ • w := by
  obtain ⟨hzz, μ, hμ⟩ := Lsec_eigen_unique_of_natAbs_eq_two one_lt_two (m := 2) (by decide)
    hz hz' (Lsec_xgEmb_eigen hw) (Lsec_xgEmb_eigen hw') (xgEmb_ne_zero h0) (xgEmb_ne_zero h0')
  refine ⟨hzz, μ, ?_⟩
  have h : xgEmb (w' - μ • w) = 0 := by rw [map_sub, map_smul, hμ, sub_self]
  exact sub_eq_zero.1 (xgEmb_injective h)

/-- **G-6, spectrum** (B0088): `σ(L₀) ∩ {Re z > 0}` has at most one point on `X_G`. -/
theorem spectrum_L0_rightHalf_subsingleton :
    ({z : ℂ | 0 < z.re} ∩ spectrum ℂ L0).Subsingleton := by
  rintro z ⟨hz, hzs⟩ z' ⟨hz', hzs'⟩
  obtain ⟨w, hw0, hw⟩ := exists_eigen_of_mem_spectrum_L0 hz hzs
  obtain ⟨w', hw0', hw'⟩ := exists_eigen_of_mem_spectrum_L0 hz' hzs'
  exact (L0_eigen_unique hz hz' hw hw' hw0 hw0').1.symm

/-- **G-6, spectrum with the mode** (B0088): if `L₀ q = λ q`, `q ≠ 0`, `Re λ > 0`, then
`σ(L₀) ∩ {Re z > 0} = {λ}` on `X_G`. -/
theorem spectrum_L0_rightHalf_eq_singleton {z₀ : ℂ} (hz₀ : 0 < z₀.re) {q : B0010.XG}
    (hq0 : q ≠ 0) (hq : L0 q = z₀ • q) : {z : ℂ | 0 < z.re} ∩ spectrum ℂ L0 = {z₀} :=
  spectrum_L0_rightHalf_subsingleton.eq_singleton_of_mem ⟨hz₀, mem_spectrum_of_eigen hq0 hq⟩

/-- **G-6, simple eigenvalue** (B0088: "λ has algebraic multiplicity one (rank-one Riesz
projection)"): the eigenfunctional of G-3 pulled back to `X_G` gives the simple spectral
projection `ℓ(·) q` of `λ`. -/
theorem exists_isSimpleSpectralProj_L0 {z₀ : ℂ} (hz₀ : 0 < z₀.re) {q : B0010.XG}
    (hq0 : q ≠ 0) (hq : L0 q = z₀ • q) :
    ∃ ℓ : B0010.XG →L[ℂ] ℂ, ℓ q = 1 ∧ ℓ.comp L0 = z₀ • ℓ ∧
      IsSimpleSpectralProj L0 (rankOneProj ℓ q) z₀ := by
  obtain ⟨ℓ, hone, hcomp, -⟩ := exists_isSimpleSpectralProj_Lsec_two one_lt_two (m := 2)
    (by decide) hz₀ (xgEmb_ne_zero hq0) (Lsec_xgEmb_eigen hq)
  have hcomp' : (ℓ.comp xgEmb).comp L0 = z₀ • ℓ.comp xgEmb := by
    refine ContinuousLinearMap.ext fun w => ?_
    have h := congrArg (fun T : ProfL2 2 →L[ℂ] ℂ => T (xgEmb w)) hcomp
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply] at h ⊢
    rw [xgEmb_L0, h]
  have hone' : (ℓ.comp xgEmb) q = 1 := hone
  refine ⟨ℓ.comp xgEmb, hone', hcomp', ?_⟩
  have hL0 : L0 = (-2 * Complex.I) • B0012.omegaOp + (2 * Complex.I) • B0012.kROp :=
    L0_eq_mul_add_compact
  have hq' : ((-2 * Complex.I) • B0012.omegaOp + (2 * Complex.I) • B0012.kROp) q = z₀ • q := by
    rw [← hL0]; exact hq
  have hcomp'' : (ℓ.comp xgEmb).comp
      ((-2 * Complex.I) • B0012.omegaOp + (2 * Complex.I) • B0012.kROp) =
      z₀ • ℓ.comp xgEmb := by
    rw [← hL0]; exact hcomp'
  have key := Infra.CompactPerturb.isSimpleSpectralProj_of_compact
    (T := (-2 * Complex.I) • B0012.omegaOp) (K := (2 * Complex.I) • B0012.kROp)
    isCompactOperator_L0_coupling (U := {z : ℂ | 0 < z.re})
    (isOpen_lt continuous_const Complex.continuous_re)
    (fun z hz => isUnit_sub_L0_transport hz) hz₀ hq' hcomp'' hone'
    (fun z hz w hw0 hw => by
      rw [← hL0] at hw
      exact L0_eigen_unique hz₀ hz hq hw hq0 hw0)
  rw [hL0]
  exact key

/-- The spectrum of `L₀` other than `λ` lies in `{Re z ≤ 0}` (`σ(L₀|_{QX_G}) ⊆ {Re z ≤ 0}`,
`eq:st18-t00063`, first clause). -/
theorem re_le_zero_of_mem_spectrum_L0 {z₀ : ℂ} (hz₀ : 0 < z₀.re) {q : B0010.XG} (hq0 : q ≠ 0)
    (hq : L0 q = z₀ • q) {z : ℂ} (hz : z ∈ spectrum ℂ L0) (hzz : z ≠ z₀) : z.re ≤ 0 := by
  by_contra h
  push_neg at h
  have hmem : z ∈ {z : ℂ | 0 < z.re} ∩ spectrum ℂ L0 := ⟨h, hz⟩
  rw [spectrum_L0_rightHalf_eq_singleton hz₀ hq0 hq] at hmem
  exact hzz hmem

/-! ### The decay of the complement, `eq:st18-t00063` -/

/-- `e^{t(A - z)} = e^{-tz} e^{tA}` in `X →L[ℂ] X`. -/
theorem exp_smul_sub_smul_one {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]
    [CompleteSpace X] (A : X →L[ℂ] X) (z t : ℂ) :
    NormedSpace.exp (t • (A - z • (1 : X →L[ℂ] X))) =
      Complex.exp (-(t * z)) • NormedSpace.exp (t • A) := by
  have hsplit : t • (A - z • (1 : X →L[ℂ] X)) = t • A + (-(t * z)) • (1 : X →L[ℂ] X) := by
    rw [smul_sub, smul_smul, neg_smul, sub_eq_add_neg]
  have hc : Commute (t • A) ((-(t * z)) • (1 : X →L[ℂ] X)) :=
    (Commute.one_right _).smul_right _
  rw [hsplit, Infra.Dunford.Deflation.exp_add_of_commute hc]
  have h1 := Infra.Dunford.Deflation.exp_mul_of_mul_eq_smul
    (B := (-(t * z)) • (1 : X →L[ℂ] X)) (Q := (1 : X →L[ℂ] X)) (c := -(t * z))
    (by rw [mul_one])
  rw [mul_one] at h1
  rw [h1, mul_smul_comm, mul_one]

/-- **G-6, `eq:st18-t00063`** (tex lines 1439–1448, unit `B0089`): with `P = ℓ(·) q` the
rank-one Riesz projection of the growing eigenvalue `λ = z₀` (`γ = Re λ`) and `Q = I - P`,
for every `δ > 0` there is `C_δ` with `‖e^{t(L₀ - λ)} Q‖_{X_G → X_G} ≤ C_δ e^{-(γ - δ)t}` for all
`t ≥ 0`. -/
theorem norm_exp_L0_sub_mul_one_sub_le {z₀ : ℂ} (hz₀ : 0 < z₀.re) {q : B0010.XG}
    (hq0 : q ≠ 0) (hq : L0 q = z₀ • q) {P : B0010.XG →L[ℂ] B0010.XG}
    (hP : IsSimpleSpectralProj L0 P z₀) {δ : ℝ} (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 0 ≤ t →
      ‖NormedSpace.exp ((t : ℂ) • (L0 - z₀ • (1 : B0010.XG →L[ℂ] B0010.XG))) * (1 - P)‖ ≤
        C * Real.exp (-(z₀.re - δ) * t) := by
  obtain ⟨C, hC, hCb⟩ := hP.exists_norm_exp_mul_one_sub_le (σ := δ) fun z hz hzz =>
    (re_le_zero_of_mem_spectrum_L0 hz₀ hq0 hq hz hzz).trans_lt hδ
  refine ⟨C, hC, fun t ht => ?_⟩
  rw [exp_smul_sub_smul_one, smul_mul_assoc, norm_smul, Complex.norm_exp]
  have hre : (-((t : ℂ) * z₀)).re = -(t * z₀.re) := by simp [Complex.mul_re]
  rw [hre]
  calc Real.exp (-(t * z₀.re)) *
        ‖NormedSpace.exp ((t : ℂ) • L0) * (1 - P)‖
      ≤ Real.exp (-(t * z₀.re)) * (C * Real.exp (δ * t)) :=
        mul_le_mul_of_nonneg_left (hCb t ht) (Real.exp_pos _).le
    _ = C * Real.exp (-(z₀.re - δ) * t) := by
        rw [mul_left_comm, ← Real.exp_add]
        congr 2
        ring

/-- **G-3 on `X_G`: the adjoint eigenvector** (units B0090–B0092, tex lines 1454–1490; bypass B5
of the scoping note): a left eigenvector `ℓ` of `L₀` with `ℓ q = 1` is `ℓ = ⟪q†, ·⟫` for a vector
`q† ∈ X_G` with `L₀^† q† = λ̄ q†` and `⟪q†, q⟫ = 1` (Riesz representation). -/
theorem exists_adjoint_eigenvector_L0 {z₀ : ℂ} {q : B0010.XG} {ℓ : B0010.XG →L[ℂ] ℂ}
    (hone : ℓ q = 1) (hcomp : ℓ.comp L0 = z₀ • ℓ) :
    ∃ qd : B0010.XG, (∀ f, ℓ f = ⟪qd, f⟫_ℂ) ∧ ⟪qd, q⟫_ℂ = 1 ∧
      ContinuousLinearMap.adjoint L0 qd = conj z₀ • qd := by
  set qd := (InnerProductSpace.toDual ℂ B0010.XG).symm ℓ with hqd
  have hrep : ∀ f, ℓ f = ⟪qd, f⟫_ℂ := fun f => InnerProductSpace.toDual_symm_apply.symm
  refine ⟨qd, hrep, by rw [← hrep, hone], ?_⟩
  apply ext_inner_right ℂ
  intro f
  rw [ContinuousLinearMap.adjoint_inner_left, inner_smul_left, starRingEnd_self_apply, ← hrep,
    ← hrep]
  have h := congrArg (fun T : B0010.XG →L[ℂ] ℂ => T f) hcomp
  simpa using h

/-- The actual Gaussian mode supplies the nonzero right-half-plane eigenvector on `X_G`, so the
rank-one Riesz projection theorem applies to a concrete eigenpair (tex lines 968--969, 1424--1448).
The profile vector is nonzero because its Green streamfunction is nonzero. -/
theorem exists_actual_gaussian_mode_simple_spectral_projection :
    ∃ G : GaussianGrowingMode, ∃ ℓ : B0010.XG →L[ℂ] ℂ,
      ℓ ((G.h_memLp_XG).toLp G.h) = 1 ∧
      ℓ.comp L0 = G.eigenvalue • ℓ ∧
      IsSimpleSpectralProj L0 (rankOneProj ℓ ((G.h_memLp_XG).toLp G.h)) G.eigenvalue := by
  obtain ⟨G⟩ := exists_gaussianGrowingMode
  let q : B0010.XG := (G.h_memLp_XG).toLp G.h
  have hq0 : q ≠ 0 := by
    intro hq
    have hzeroX : G.h =ᵐ[B0010.xGMeasure] (0 : ℝ → ℂ) := by
      filter_upwards [G.h_memLp_XG.coeFn_toLp,
        (show (⇑q : ℝ → ℂ) =ᵐ[B0010.xGMeasure] 0 from by
          rw [hq]
          exact Lp.coeFn_zero ℂ 2 B0010.xGMeasure)]
        with r h1 h2
      rw [← h1, h2]
    have hzeroR : G.h =ᵐ[volume.restrict (Ioi (0 : ℝ))] (0 : ℝ → ℂ) :=
      B0012.restrict_ac.ae_le hzeroX
    obtain ⟨r, hr, hφ⟩ := G.φ_ne_zero
    have hgreen : greenN 2 G.h r = greenN 2 (0 : ℝ → ℂ) r :=
      ComplexODEC.greenN_congr_ae hzeroR r
    apply hφ
    rw [G.φ_eq_green r hr, hgreen]
    simp [greenN]
  have hqEig : L0 q = G.eigenvalue • q := by
    simpa [q, GaussianGrowingMode.eigenvalue] using G.L0_eigen
  obtain ⟨ℓ, hone, hcomp, hproj⟩ := exists_isSimpleSpectralProj_L0 G.growth_pos hq0 hqEig
  refine ⟨G, ℓ, by simpa [q] using hone, hcomp, ?_⟩
  simpa [GaussianGrowingMode.eigenvalue] using hproj

end UnforcedLeray.Planar
