import UnforcedLeray.Short.PartIIb.Sub.G1
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.Column.InletB.RawDiff
import UnforcedLeray.Short.PartIIa.Tasks.R02LateTable
import UnforcedLeray.Short.PartIIa.Tasks.R02.BlockB2
import UnforcedLeray.Units.B0186

/-!
# Part II-b, task `PartII-b:G1/1`: `RawProfileLate`

Source of record: `the November 2 reference manuscript`, lines 2412-2431
(display `short-bg:strong-late-coeff`, profile level SP 2424-2431) and lines 270-288 (BUC train).

For the raw profile `b_raw = (v₁, v₂ + εH)` of the actual train in `BgRegime`, at every chart
point `x = (s, (q, η))` with `s > S ≥ 1`, `b_raw` is differentiable at `x` (`rawProfDiffAt`) and
`lateProfileQuantity ε b_raw x ≤ C ν^{-k} (S^{-1/2} + ε)`.
The profile bounds are extracted from the Part I + Part II-a jet-class machinery
(`UnforcedLeray.Short.PartIIa.Jet` and `UnforcedLeray.Short.PartIIa.Jet.B2`), including the radial
mean cancellation `(K+1)\bar H = (K+1)h₁` (`B2.hbar_shift1`) and `B2.hP_shift_split`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

open UnforcedLeray.Cons.C03.Concrete UnforcedLeray.B0184 UnforcedLeray.B0185
  UnforcedLeray.B0186 UnforcedLeray.B0188 UnforcedLeray.B0190
open UnforcedLeray.Short.PartIIa UnforcedLeray.Short.PartIIa.Jet

/-! ### 1. Meridional vector norms and chart derivatives of `merProfile` -/

theorem norm_m0_le_one : ‖Axi.m0‖ ≤ 1 := by
  rw [Axi.m0, EuclideanSpace.single, PiLp.norm_single]
  simp

theorem norm_m1_le_one : ‖Axi.m1‖ ≤ 1 := by
  rw [Axi.m1, EuclideanSpace.single, PiLp.norm_single]
  simp

theorem norm_merid_pair_le (u v : ℝ) : ‖u • Axi.m0 + v • Axi.m1‖ ≤ |u| + |v| := by
  calc ‖u • Axi.m0 + v • Axi.m1‖
      ≤ ‖u • Axi.m0‖ + ‖v • Axi.m1‖ := norm_add_le _ _
    _ = |u| * ‖Axi.m0‖ + |v| * ‖Axi.m1‖ := by rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
    _ ≤ |u| * 1 + |v| * 1 := add_le_add
        (mul_le_mul_of_nonneg_left norm_m0_le_one (abs_nonneg u))
        (mul_le_mul_of_nonneg_left norm_m1_le_one (abs_nonneg v))
    _ = |u| + |v| := by ring

theorem diffAt_streamV1 {ψ : ProfilePoint → ℝ} {x' : ProfilePoint} (hC : ContDiffAt ℝ ∞ ψ x') :
    DifferentiableAt ℝ (streamV1 ψ) x' := by
  unfold streamV1 partialEta
  exact (rawDiff_fderiv_apply hC eηDir).neg

theorem diffAt_streamV2 {ψ : ProfilePoint → ℝ} {x' : ProfilePoint} (hC : ContDiffAt ℝ ∞ ψ x') :
    DifferentiableAt ℝ (streamV2 ψ) x' := by
  unfold streamV2 partialQ
  exact rawDiff_fderiv_apply hC eqDir

theorem diffAt_axialProfile {R : ℝ} {ψ : ProfilePoint → ℝ} {x' : ProfilePoint}
    (hC : ContDiffAt ℝ ∞ ψ x') :
    DifferentiableAt ℝ (axialProfile R ψ) x' := by
  unfold axialProfile
  exact (diffAt_streamV2 hC).add ((differentiableAt_const (ringEps R)).mul (rawDiff_ageDef_diffAt hC))

theorem fderiv_axialProfile {R : ℝ} {ψ : ProfilePoint → ℝ} {x' : ProfilePoint}
    (hC : ContDiffAt ℝ ∞ ψ x') (v : ProfilePoint) :
    fderiv ℝ (axialProfile R ψ) x' v =
      fderiv ℝ (streamV2 ψ) x' v + ringEps R * fderiv ℝ (B0185.ageDefect ψ) x' v := by
  unfold axialProfile
  rw [((diffAt_streamV2 hC).hasFDerivAt.fun_add
    ((rawDiff_ageDef_diffAt hC).hasFDerivAt.const_mul (ringEps R))).fderiv]
  simp

theorem fderiv_merid_pair {f g : ProfilePoint → ℝ} {x' : ProfilePoint}
    (hf : DifferentiableAt ℝ f x') (hg : DifferentiableAt ℝ g x') (v : ProfilePoint) :
    fderiv ℝ (fun w => f w • Axi.m0 + g w • Axi.m1) x' v =
      fderiv ℝ f x' v • Axi.m0 + fderiv ℝ g x' v • Axi.m1 := by
  rw [((hf.hasFDerivAt.smul_const Axi.m0).fun_add (hg.hasFDerivAt.smul_const Axi.m1)).fderiv]
  simp

theorem fderiv_merProfile_apply {R : ℝ} {ψ : ProfilePoint → ℝ} {x : ℝ × (ℝ × ℝ)}
    (hC : ContDiffAt ℝ ∞ ψ (toProfile x)) (v : ℝ × (ℝ × ℝ)) :
    fderiv ℝ (merProfile R ψ) x v =
      fderiv ℝ (streamV1 ψ) (toProfile x) (toProfile v) • Axi.m0 +
        (fderiv ℝ (streamV2 ψ) (toProfile x) (toProfile v) +
          ringEps R * fderiv ℝ (B0185.ageDefect ψ) (toProfile x) (toProfile v)) • Axi.m1 := by
  change fderiv ℝ ((fun w : ProfilePoint =>
      streamV1 ψ w • Axi.m0 + axialProfile R ψ w • Axi.m1) ∘ toProfile) x v = _
  rw [toProfile.comp_right_fderiv]
  change fderiv ℝ (fun w : ProfilePoint =>
      streamV1 ψ w • Axi.m0 + axialProfile R ψ w • Axi.m1) (toProfile x) (toProfile v) = _
  rw [fderiv_merid_pair (diffAt_streamV1 hC) (diffAt_axialProfile hC), fderiv_axialProfile hC]

theorem dS_merProfile {R : ℝ} {ψ : ProfilePoint → ℝ} {x : ℝ × (ℝ × ℝ)}
    (hC : ContDiffAt ℝ ∞ ψ (toProfile x)) :
    Axi.dS (merProfile R ψ) x =
      partialAge (streamV1 ψ) (toProfile x) • Axi.m0 +
        (partialAge (streamV2 ψ) (toProfile x) +
          ringEps R * partialAge (B0185.ageDefect ψ) (toProfile x)) • Axi.m1 :=
  fderiv_merProfile_apply hC (1, (0, 0))

theorem dQ_merProfile {R : ℝ} {ψ : ProfilePoint → ℝ} {x : ℝ × (ℝ × ℝ)}
    (hC : ContDiffAt ℝ ∞ ψ (toProfile x)) :
    Axi.dQ (merProfile R ψ) x =
      partialQ (streamV1 ψ) (toProfile x) • Axi.m0 +
        (partialQ (streamV2 ψ) (toProfile x) +
          ringEps R * partialQ (B0185.ageDefect ψ) (toProfile x)) • Axi.m1 :=
  fderiv_merProfile_apply hC (0, (1, 0))

theorem dEta_merProfile {R : ℝ} {ψ : ProfilePoint → ℝ} {x : ℝ × (ℝ × ℝ)}
    (hC : ContDiffAt ℝ ∞ ψ (toProfile x)) :
    Axi.dEta (merProfile R ψ) x =
      partialEta (streamV1 ψ) (toProfile x) • Axi.m0 +
        (partialEta (streamV2 ψ) (toProfile x) +
          ringEps R * partialEta (B0185.ageDefect ψ) (toProfile x)) • Axi.m1 :=
  fderiv_merProfile_apply hC (0, (0, 1))

theorem qEps_merProfile {R : ℝ} {ψ : ProfilePoint → ℝ} {x : ℝ × (ℝ × ℝ)}
    (hC : ContDiffAt ℝ ∞ ψ (toProfile x)) :
    Axi.dQ (merProfile R ψ) x -
        ringEps R • ((2 * x.1) • Axi.dS (merProfile R ψ) x +
          x.2.2 • Axi.dEta (merProfile R ψ) x + merProfile R ψ x) =
      (partialQ (streamV1 ψ) (toProfile x) -
          ringEps R * ageShift 1 (streamV1 ψ) (toProfile x)) • Axi.m0 +
        (partialQ (streamV2 ψ) (toProfile x) +
          ringEps R * partialQ (B0185.ageDefect ψ) (toProfile x) -
          ringEps R * ageShift 1 (streamV2 ψ) (toProfile x) -
          ringEps R * ringEps R * ageShift 1 (B0185.ageDefect ψ) (toProfile x)) • Axi.m1 := by
  rw [dQ_merProfile hC, dS_merProfile hC, dEta_merProfile hC]
  ext i
  fin_cases i
  · simp only [Fin.zero_eta, merProfile, axialProfile, ageShift, ageOperator, toProfile_apply,
      PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, Axi.m0_zero, Axi.m1_zero]
    ring
  · simp only [Fin.mk_one, merProfile, axialProfile, ageShift, ageOperator, toProfile_apply,
      PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, Axi.m0_one, Axi.m1_one]
    ring

/-! ### 2. Unconditional jet-class bounds for the raw profile components -/

/-- Pointwise absolute value of a family. -/
def absFam (F : Fam) : Fam := fun ν c tr x => |F ν c tr x|

theorem ww_absFam {a : ℝ} {F : Fam} (hF : WW a F) : WW a (absFam F) := by
  intro ρ m hρ
  obtain ⟨C, d, ν₀, hν₀, H⟩ := hF ρ m hρ
  refine ⟨C, d, ν₀, hν₀, fun ν hν hνle tr htr x hx => ?_⟩
  have h := H ν hν hνle tr htr x hx
  show (1 + x.2.1 ^ 2 / x.2.2) ^ m * |(|F ν (ν ^ (-ρ)) tr x|)| ≤ _
  rw [abs_abs]
  exact h

/-- Unconditional `LateIngredients` assembled from Part I tasks (as in `R02LateTable.lean`). -/
theorem lateIngredients_uncond : LateIngredients := by
  have hOFluct : UnforcedLeray.Short.PartI.OverlapFluctuationDecay :=
    UnforcedLeray.Short.PartI.overlap_fluctuation_decay
      UnforcedLeray.Short.PartI.overlap_highnorm_uniform
  have hOMean : UnforcedLeray.Short.PartI.OverlapMeanDecay :=
    UnforcedLeray.Short.PartI.overlap_mean_decay
      UnforcedLeray.Short.PartI.overlap_highnorm_uniform hOFluct
      UnforcedLeray.Short.PartI.overlap_mean_primitive
  have hOv : UnforcedLeray.Short.PartI.TrainOverlap :=
    UnforcedLeray.Short.PartI.trainOverlap_proof hOFluct hOMean
  have hVort : UnforcedLeray.Short.PartI.TrainVorticityGaussianTail :=
    UnforcedLeray.Short.PartI.train_vorticity_gaussian_tail hOv
  have hTails : UnforcedLeray.Short.PartI.TrainStreamVelocityPressureTails :=
    UnforcedLeray.Short.PartI.train_stream_velocity_pressure_tails hOv hVort
  have hFD : UnforcedLeray.Short.PartI.TrainFluctuationDecay :=
    UnforcedLeray.Short.PartI.trainFluctuationDecay_proof hTails hOFluct hOv
  have hME : UnforcedLeray.Short.PartI.TrainMeanExpansion :=
    UnforcedLeray.Short.PartI.trainMeanExpansion_proof hTails hFD
      UnforcedLeray.Short.PartI.overlap_mean_primitive
  have hS : LateProfileSmooth :=
    lateProfileSmooth_of UnforcedLeray.Short.PartI.trainStreamSmooth
  exact
    ⟨hS,
     lateFluctuationProfile_of hFD hS,
     lateMeanRemainder_of hME UnforcedLeray.Short.PartI.trainMeanEquations_proof hS,
     lateMeanCoeff_of hFD UnforcedLeray.Short.PartI.trainMeanEquations_proof,
     lateHeatProfile,
     lateMeanStress_of hFD UnforcedLeray.Short.PartI.trainMeanEquations_proof hS,
     profileCommutators⟩

/-- `(K+1)H` has weighted size `s^{-3/2}` by the mean heat cancellation `(K+1)G = 0`. -/
theorem ww_shift1_hP (hT : JetToolkit) (hF : FluctWords) (hM : WordsW (1 / 2) meanFam)
    (hR : WordsW (3 / 2) remFam0) : WW (3 / 2) (famShift 1 B2.hP) := by
  have chain : LateEq (famShift 1 B2.hP) (famShift 1 B2.h1 + famShift 1 B2.ht) :=
    (B2.hP_shift_split hT hF hM).trans
      (B2.leq_add (B2.hbar_shift1 hT hM hR) (LateEq.refl _))
  have hW : WW (3 / 2) (famShift 1 B2.h1 + famShift 1 B2.ht) :=
    (hT.jc.qshift 1 (B2.h1_JQ hT hR 1)).ww.add
      (hT.jc.qofE (3 / 2) (hT.jc.eshift 1 (B2.ht_JE hT hF 1))).ww
  exact WW.congr chain.symm hW

/-- Combined family of size `s^{-1/2}`: `|H|`. -/
def rawFam12 : Fam := absFam B2.hP

/-- Combined family of size `s^{-1}`:
`|v₁| + |v₂| + |∂_η H| + |(K+1)v₁| + |(K+1)v₂| + |∂_q H|`. -/
def rawFam1 : Fam :=
  absFam B2.v1P + absFam B2.v2P + absFam (famEta B2.hP) +
    absFam (famShift 1 B2.v1P) + absFam (famShift 1 B2.v2P) + absFam (famQ B2.hP)

/-- Combined family of size `s^{-3/2}`:
`|∂_η v₁| + |∂_η v₂| + |∂_q v₁| + |∂_q v₂| + |(K+1)H|`. -/
def rawFam32 : Fam :=
  absFam (famEta B2.v1P) + absFam (famEta B2.v2P) +
    absFam (famQ B2.v1P) + absFam (famQ B2.v2P) + absFam (famShift 1 B2.hP)

theorem ww_rawFam :
    WW (1 / 2) rawFam12 ∧ WW 1 rawFam1 ∧ WW (3 / 2) rawFam32 := by
  have ing := lateIngredients_uncond
  have hT := jetToolkit
  have hF : FluctWords := fluctWords_of ing
  have hS : MeanSmoothQ := meanSmoothQ_of ing
  have hH : HeatWords := heatWords_of ing.heat hT.iterLin
  have hM : WordsW (1 / 2) meanFam :=
    meanWords_of hS hH hT.iterLin (meanHeatPart_of ing) (meanRemPart_of ing)
  have hR : WordsW (3 / 2) remFam0 := B2.remWords32_of ing hS hH
  have hv1 := B2.v1P_JQ hT hF hM 1
  have hv2 := B2.v2P_JE hT hF hM 1
  have hhP := B2.hP_JQ hT hF hM 1
  have w_hP : WW (1 / 2) B2.hP := hhP.ww
  have w_v1 : WW 1 B2.v1P := hv1.ww
  have w_v2 : WW 1 B2.v2P := (hT.jc.qofE 1 hv2).ww
  have w_eta_hP : WW 1 (famEta B2.hP) := (hhP.eta.cast (by norm_num)).ww
  have w_sh_v1 : WW 1 (famShift 1 B2.v1P) := (hT.jc.qshift 1 hv1).ww
  have w_sh_v2 : WW 1 (famShift 1 B2.v2P) := (hT.jc.qofE 1 (hT.jc.eshift 1 hv2)).ww
  have w_q_hP : WW 1 (famQ B2.hP) := (hT.jc.qofE 1 hhP.q).ww
  have w_eta_v1 : WW (3 / 2) (famEta B2.v1P) := (hv1.eta.cast (by norm_num)).ww
  have w_eta_v2 : WW (3 / 2) (famEta B2.v2P) := (hT.jc.qofE (3 / 2) hv2.eta).ww
  have w_q_v1 : WW (3 / 2) (famQ B2.v1P) := (hT.jc.qofE (3 / 2) hv1.q).ww
  have w_q_v2 : WW (3 / 2) (famQ B2.v2P) := (hT.jc.qofE (3 / 2) hv2.q).ww
  have w_sh_hP : WW (3 / 2) (famShift 1 B2.hP) := ww_shift1_hP hT hF hM hR
  refine ⟨ww_absFam w_hP, ?_, ?_⟩
  · exact (((((ww_absFam w_v1).add (ww_absFam w_v2)).add (ww_absFam w_eta_hP)).add
      (ww_absFam w_sh_v1)).add (ww_absFam w_sh_v2)).add (ww_absFam w_q_hP)
  · exact ((((ww_absFam w_eta_v1).add (ww_absFam w_eta_v2)).add (ww_absFam w_q_v1)).add
      (ww_absFam w_q_v2)).add (ww_absFam w_sh_hP)

/-! ### 3. Specialization of `WW` to `BgRegime` -/

theorem wtdBound_of_c_eq {F : Fam} {a B ν c₁ c₂ : ℝ} (hc : c₁ = c₂)
    (H : ∀ tr : UnforcedLeray.B0140.TrainSol ν c₂,
      UnforcedLeray.Short.PartI.IsBUCTrain tr → WtdBound 0 (F ν c₂ tr) a B)
    (tr : UnforcedLeray.B0140.TrainSol ν c₁)
    (htr : UnforcedLeray.Short.PartI.IsBUCTrain tr) :
    WtdBound 0 (F ν c₁ tr) a B := by
  subst hc
  exact H tr htr

theorem ww_bound_bg {a : ℝ} {F : Fam} (hF : WW a F) :
    ∃ (C : ℝ) (k : ℕ) (ν₀ : ℝ), 0 < C ∧ 0 < ν₀ ∧
      ∀ (p : Params) (d dm dp : ℝ), BgRegime p d dm dp → p.ν ≤ ν₀ →
        ∀ x' : ProfilePoint, 1 ≤ x'.2.2 →
          F p.ν p.c p.train x' ≤ C * (p.ν ^ k)⁻¹ * x'.2.2 ^ (-a) := by
  obtain ⟨C₁, d₁, ν₁, hν₁, H1⟩ := hF 2 0 (by norm_num)
  have hC₁ : 0 < max C₁ 1 := lt_max_of_lt_right one_pos
  refine ⟨max C₁ 1 * 3 ^ d₁, 2 * d₁, min ν₁ 1, by positivity, lt_min hν₁ one_pos, ?_⟩
  intro p d dm dp hb hν x' hx'
  have hνpos : 0 < p.ν := p.ν_pos
  have hν1 : p.ν ≤ ν₁ := hν.trans (min_le_left _ _)
  have hνle1 : p.ν ≤ 1 := hν.trans (min_le_right _ _)
  have hc : p.c = p.ν ^ (-(2 : ℝ)) := hb.c_eq.trans (inv_sq_eq_rpow_neg_two hνpos)
  have hw := wtdBound_of_c_eq hc (H1 p.ν hνpos hν1) p.train hb.train_buc x' hx'
  simp only [pow_zero, one_mul] at hw
  have hX : (1 + p.ν ^ (-(2 : ℝ)) + p.ν⁻¹) ^ d₁ ≤ 3 ^ d₁ * (p.ν ^ (2 * d₁))⁻¹ := by
    calc (1 + p.ν ^ (-(2 : ℝ)) + p.ν⁻¹) ^ d₁ ≤ (3 * (p.ν ^ 2)⁻¹) ^ d₁ :=
          pow_le_pow_left₀ (by positivity) (one_add_inv_le hνpos hνle1) _
      _ = 3 ^ d₁ * (p.ν ^ (2 * d₁))⁻¹ := by rw [mul_pow, inv_pow, ← pow_mul]
  have hXn : 0 ≤ (1 + p.ν ^ (-(2 : ℝ)) + p.ν⁻¹) ^ d₁ := by
    apply pow_nonneg
    have : 0 < p.ν ^ (-(2 : ℝ)) := Real.rpow_pos_of_pos hνpos _
    have : 0 < p.ν⁻¹ := inv_pos.2 hνpos
    linarith
  have hpoly : polyConst C₁ d₁ p.ν (p.ν ^ (-(2 : ℝ))) ≤
      max C₁ 1 * 3 ^ d₁ * (p.ν ^ (2 * d₁))⁻¹ := by
    rw [polyConst]
    calc C₁ * (1 + p.ν ^ (-(2 : ℝ)) + p.ν⁻¹) ^ d₁
        ≤ max C₁ 1 * (1 + p.ν ^ (-(2 : ℝ)) + p.ν⁻¹) ^ d₁ :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) hXn
      _ ≤ max C₁ 1 * (3 ^ d₁ * (p.ν ^ (2 * d₁))⁻¹) :=
          mul_le_mul_of_nonneg_left hX hC₁.le
      _ = max C₁ 1 * 3 ^ d₁ * (p.ν ^ (2 * d₁))⁻¹ := by ring
  have hs : 0 ≤ x'.2.2 ^ (-a) := Real.rpow_nonneg (by linarith) _
  exact (le_abs_self _).trans (hw.trans (mul_le_mul_of_nonneg_right hpoly hs))

theorem inv_pow_mono {ν : ℝ} (hν0 : 0 < ν) (hν1 : ν ≤ 1) {j k : ℕ} (hjk : j ≤ k) :
    (ν ^ j)⁻¹ ≤ (ν ^ k)⁻¹ :=
  (inv_le_inv₀ (pow_pos hν0 j) (pow_pos hν0 k)).2 (pow_le_pow_of_le_one hν0.le hν1 hjk)

theorem bgRegime_eps_le_one {p : Params} {d dm dp : ℝ} (hb : BgRegime p d dm dp) :
    p.ε ≤ 1 := by
  rw [hb.eps_eq, Real.exp_le_one_iff]
  have hd : 0 ≤ d := le_trans hb.dm_pos.le hb.dm_le
  exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.2 hd) p.ν_pos.le

/-! ### 4. Pointwise bound on `lateProfileQuantity` and main theorem -/

theorem lateProfileQuantity_merProfile_le {p : Params} {d dm dp : ℝ} (hb : BgRegime p d dm dp)
    {x : ℝ × (ℝ × ℝ)} (hx : 0 < x.1) :
    lateProfileQuantity p.ε (merProfile p.R (trainProfile p.train.ψ)) x ≤
      Real.sqrt x.1 * rawFam1 p.ν p.c p.train (toProfile x) +
        p.ε * (Real.sqrt x.1 * rawFam12 p.ν p.c p.train (toProfile x)) +
        2 * (x.1 * rawFam32 p.ν p.c p.train (toProfile x)) +
        3 * p.ε * (x.1 * rawFam1 p.ν p.c p.train (toProfile x)) +
        p.ε * p.ε * (x.1 * rawFam32 p.ν p.c p.train (toProfile x)) := by
  set x' : ProfilePoint := toProfile x
  have hC : ContDiffAt ℝ ∞ (trainProfile p.train.ψ) x' :=
    rawDiff_trainProfile_contDiffAt hb (show 0 < x'.2.2 from hx)
  have hRε : ringEps p.R = p.ε := by
    show (p.ε⁻¹)⁻¹ = p.ε
    exact inv_inv p.ε
  have hε0 : 0 ≤ p.ε := p.ε_pos.le
  have hs0 : 0 ≤ x.1 := hx.le
  have hsq0 : 0 ≤ Real.sqrt x.1 := Real.sqrt_nonneg x.1
  set ψ := trainProfile p.train.ψ
  have hb_norm : ‖merProfile p.R ψ x‖ ≤
      |streamV1 ψ x'| + |streamV2 ψ x'| + p.ε * |B0185.ageDefect ψ x'| := by
    have h1 := norm_merid_pair_le (streamV1 ψ x') (axialProfile p.R ψ x')
    have h2 : |axialProfile p.R ψ x'| ≤ |streamV2 ψ x'| + p.ε * |B0185.ageDefect ψ x'| := by
      unfold axialProfile
      rw [hRε]
      calc |streamV2 ψ x' + p.ε * B0185.ageDefect ψ x'|
          ≤ |streamV2 ψ x'| + |p.ε * B0185.ageDefect ψ x'| := abs_add_le _ _
        _ = |streamV2 ψ x'| + p.ε * |B0185.ageDefect ψ x'| := by
          rw [abs_mul, abs_of_nonneg hε0]
    exact h1.trans (by linarith)
  have hb0 : |merProfile p.R ψ x 0| = |streamV1 ψ x'| := by
    simp [merProfile, x']
  have hdEta : ‖Axi.dEta (merProfile p.R ψ) x‖ ≤
      |partialEta (streamV1 ψ) x'| + |partialEta (streamV2 ψ) x'| +
        p.ε * |partialEta (B0185.ageDefect ψ) x'| := by
    rw [dEta_merProfile hC, hRε]
    have h1 := norm_merid_pair_le (partialEta (streamV1 ψ) x')
      (partialEta (streamV2 ψ) x' + p.ε * partialEta (B0185.ageDefect ψ) x')
    have h2 : |partialEta (streamV2 ψ) x' + p.ε * partialEta (B0185.ageDefect ψ) x'| ≤
        |partialEta (streamV2 ψ) x'| + p.ε * |partialEta (B0185.ageDefect ψ) x'| := by
      calc |partialEta (streamV2 ψ) x' + p.ε * partialEta (B0185.ageDefect ψ) x'|
          ≤ |partialEta (streamV2 ψ) x'| + |p.ε * partialEta (B0185.ageDefect ψ) x'| :=
            abs_add_le _ _
        _ = |partialEta (streamV2 ψ) x'| + p.ε * |partialEta (B0185.ageDefect ψ) x'| := by
            rw [abs_mul, abs_of_nonneg hε0]
    exact h1.trans (by linarith)
  have hqEps : ‖Axi.dQ (merProfile p.R ψ) x -
      p.ε • ((2 * x.1) • Axi.dS (merProfile p.R ψ) x +
        x.2.2 • Axi.dEta (merProfile p.R ψ) x + merProfile p.R ψ x)‖ ≤
      |partialQ (streamV1 ψ) x'| + |partialQ (streamV2 ψ) x'| +
        p.ε * (|ageShift 1 (streamV1 ψ) x'| + |ageShift 1 (streamV2 ψ) x'| +
          |partialQ (B0185.ageDefect ψ) x'|) +
        p.ε * p.ε * |ageShift 1 (B0185.ageDefect ψ) x'| := by
    have hq := qEps_merProfile (R := p.R) hC
    rw [hRε] at hq
    rw [hq]
    have h1 := norm_merid_pair_le
      (partialQ (streamV1 ψ) x' - p.ε * ageShift 1 (streamV1 ψ) x')
      (partialQ (streamV2 ψ) x' + p.ε * partialQ (B0185.ageDefect ψ) x' -
        p.ε * ageShift 1 (streamV2 ψ) x' - p.ε * p.ε * ageShift 1 (B0185.ageDefect ψ) x')
    have hu : |partialQ (streamV1 ψ) x' - p.ε * ageShift 1 (streamV1 ψ) x'| ≤
        |partialQ (streamV1 ψ) x'| + p.ε * |ageShift 1 (streamV1 ψ) x'| := by
      calc |partialQ (streamV1 ψ) x' - p.ε * ageShift 1 (streamV1 ψ) x'|
          ≤ |partialQ (streamV1 ψ) x'| + |p.ε * ageShift 1 (streamV1 ψ) x'| := abs_sub _ _
        _ = |partialQ (streamV1 ψ) x'| + p.ε * |ageShift 1 (streamV1 ψ) x'| := by
          rw [abs_mul, abs_of_nonneg hε0]
    have hv1 : |partialQ (streamV2 ψ) x' + p.ε * partialQ (B0185.ageDefect ψ) x' -
        p.ε * ageShift 1 (streamV2 ψ) x' - p.ε * p.ε * ageShift 1 (B0185.ageDefect ψ) x'| ≤
        |partialQ (streamV2 ψ) x' + p.ε * partialQ (B0185.ageDefect ψ) x' -
          p.ε * ageShift 1 (streamV2 ψ) x'| +
          |p.ε * p.ε * ageShift 1 (B0185.ageDefect ψ) x'| := abs_sub _ _
    have hv2 : |partialQ (streamV2 ψ) x' + p.ε * partialQ (B0185.ageDefect ψ) x' -
        p.ε * ageShift 1 (streamV2 ψ) x'| ≤
        |partialQ (streamV2 ψ) x' + p.ε * partialQ (B0185.ageDefect ψ) x'| +
          |p.ε * ageShift 1 (streamV2 ψ) x'| := abs_sub _ _
    have hv3 : |partialQ (streamV2 ψ) x' + p.ε * partialQ (B0185.ageDefect ψ) x'| ≤
        |partialQ (streamV2 ψ) x'| + |p.ε * partialQ (B0185.ageDefect ψ) x'| := abs_add_le _ _
    rw [abs_mul, abs_of_nonneg hε0] at hv3
    rw [abs_mul, abs_of_nonneg hε0] at hv2
    rw [abs_mul, abs_mul, abs_of_nonneg hε0] at hv1
    linarith
  have g1_def : rawFam1 p.ν p.c p.train x' =
      |streamV1 ψ x'| + |streamV2 ψ x'| + |partialEta (B0185.ageDefect ψ) x'| +
        |ageShift 1 (streamV1 ψ) x'| + |ageShift 1 (streamV2 ψ) x'| +
        |partialQ (B0185.ageDefect ψ) x'| := rfl
  have g12_def : rawFam12 p.ν p.c p.train x' = |B0185.ageDefect ψ x'| := rfl
  have g32_def : rawFam32 p.ν p.c p.train x' =
      |partialEta (streamV1 ψ) x'| + |partialEta (streamV2 ψ) x'| +
        |partialQ (streamV1 ψ) x'| + |partialQ (streamV2 ψ) x'| +
        |ageShift 1 (B0185.ageDefect ψ) x'| := rfl
  have a1 := abs_nonneg (streamV1 ψ x')
  have a2 := abs_nonneg (streamV2 ψ x')
  have a3 := abs_nonneg (partialEta (B0185.ageDefect ψ) x')
  have a4 := abs_nonneg (ageShift 1 (streamV1 ψ) x')
  have a5 := abs_nonneg (ageShift 1 (streamV2 ψ) x')
  have a6 := abs_nonneg (partialQ (B0185.ageDefect ψ) x')
  have b1 := abs_nonneg (partialEta (streamV1 ψ) x')
  have b2 := abs_nonneg (partialEta (streamV2 ψ) x')
  have b3 := abs_nonneg (partialQ (streamV1 ψ) x')
  have b4 := abs_nonneg (partialQ (streamV2 ψ) x')
  have b5 := abs_nonneg (ageShift 1 (B0185.ageDefect ψ) x')
  have l_b : ‖merProfile p.R ψ x‖ ≤
      rawFam1 p.ν p.c p.train x' + p.ε * rawFam12 p.ν p.c p.train x' := by
    rw [g12_def]
    linarith
  have l_b0 : p.ε * |merProfile p.R ψ x 0| ≤ p.ε * rawFam1 p.ν p.c p.train x' := by
    rw [hb0]
    exact mul_le_mul_of_nonneg_left (by linarith) hε0
  have l_dEta : ‖Axi.dEta (merProfile p.R ψ) x‖ ≤
      rawFam32 p.ν p.c p.train x' + p.ε * rawFam1 p.ν p.c p.train x' := by
    have : |partialEta (B0185.ageDefect ψ) x'| ≤ rawFam1 p.ν p.c p.train x' := by linarith
    have := mul_le_mul_of_nonneg_left this hε0
    linarith
  have l_qEps : ‖Axi.dQ (merProfile p.R ψ) x -
      p.ε • ((2 * x.1) • Axi.dS (merProfile p.R ψ) x +
        x.2.2 • Axi.dEta (merProfile p.R ψ) x + merProfile p.R ψ x)‖ ≤
      rawFam32 p.ν p.c p.train x' + p.ε * rawFam1 p.ν p.c p.train x' +
        p.ε * p.ε * rawFam32 p.ν p.c p.train x' := by
    have h_sh1 : |ageShift 1 (streamV1 ψ) x'| + |ageShift 1 (streamV2 ψ) x'| +
        |partialQ (B0185.ageDefect ψ) x'| ≤ rawFam1 p.ν p.c p.train x' := by linarith
    have h_sh2 : |ageShift 1 (B0185.ageDefect ψ) x'| ≤ rawFam32 p.ν p.c p.train x' := by linarith
    have m1 := mul_le_mul_of_nonneg_left h_sh1 hε0
    have m2 := mul_le_mul_of_nonneg_left h_sh2 (mul_nonneg hε0 hε0)
    linarith
  unfold lateProfileQuantity gradProfileQuantity
  have term1 := mul_le_mul_of_nonneg_left l_b hsq0
  have term2 := mul_le_mul_of_nonneg_left (add_le_add (add_le_add l_dEta l_qEps) l_b0) hs0
  linarith

/-- **`PartII-b:G1/1`**: profile-level strong late coefficient bound (`RawProfileLate`,
SP 2412-2431). -/
theorem rawProfileLate : UnforcedLeray.Short.IIb.RawProfileLate := by
  obtain ⟨w12, w1, w32⟩ := ww_rawFam
  obtain ⟨C₁₂, k₁₂, ν₁₂, hC₁₂, hν₁₂, H12⟩ := ww_bound_bg w12
  obtain ⟨C₁, k₁, ν₁, hC₁, hν₁, H1⟩ := ww_bound_bg w1
  obtain ⟨C₃₂, k₃₂, ν₃₂, hC₃₂, hν₃₂, H32⟩ := ww_bound_bg w32
  intro dm dp _
  set B : ℝ := max C₁₂ (max C₁ C₃₂)
  set k : ℕ := max k₁₂ (max k₁ k₃₂)
  set ν₀ : ℝ := min (min ν₁₂ ν₁) (min ν₃₂ 1)
  have hB : 0 < B := lt_max_of_lt_left hC₁₂
  have hν₀ : 0 < ν₀ := lt_min (lt_min hν₁₂ hν₁) (lt_min hν₃₂ one_pos)
  refine ⟨5 * B, k, ν₀, by positivity, hν₀, ?_⟩
  intro p d hb hν S hS x hxS
  have hx : 0 < x.1 := by linarith
  refine ⟨rawProfDiffAt dm dp p d hb x hx, ?_⟩
  have hopen : {y : Coord | 0 < y.1} ∈ 𝓝 x :=
    (isOpen_lt continuous_const continuous_fst).mem_nhds hx
  have hL : rawProf p =ᶠ[𝓝 x] merProfile p.R (trainProfile p.train.ψ) := by
    filter_upwards [hopen] with y hy
    exact rawProf_eq_merProfile_of_contDiff hb hy
  have hfderiv : fderiv ℝ (rawProf p) x =
      fderiv ℝ (merProfile p.R (trainProfile p.train.ψ)) x := hL.fderiv_eq
  have hlate_eq : lateProfileQuantity p.ε (rawProf p) x =
      lateProfileQuantity p.ε (merProfile p.R (trainProfile p.train.ψ)) x := by
    unfold lateProfileQuantity gradProfileQuantity Axi.dEta Axi.dQ Axi.dS
    rw [hL.eq_of_nhds, hfderiv]
  change lateProfileQuantity p.ε (rawProf p) x ≤ _
  rw [hlate_eq]
  have hs1 : 1 ≤ (toProfile x).2.2 := by
    change 1 ≤ x.1
    linarith
  have hνpos : 0 < p.ν := p.ν_pos
  have hνle1 : p.ν ≤ 1 := hν.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hν12 : p.ν ≤ ν₁₂ := hν.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hν1 : p.ν ≤ ν₁ := hν.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hν32 : p.ν ≤ ν₃₂ := hν.trans ((min_le_right _ _).trans (min_le_left _ _))
  set P : ℝ := B * (p.ν ^ k)⁻¹
  have hP0 : 0 ≤ P := by positivity
  have b12 : rawFam12 p.ν p.c p.train (toProfile x) ≤ P * x.1 ^ (-(1 / 2 : ℝ)) := by
    refine (H12 p d dm dp hb hν12 (toProfile x) hs1).trans ?_
    apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hx.le _)
    exact mul_le_mul (le_max_left _ _) (inv_pow_mono hνpos hνle1 (le_max_left _ _))
      (by positivity) hB.le
  have b1 : rawFam1 p.ν p.c p.train (toProfile x) ≤ P * x.1 ^ (-1 : ℝ) := by
    refine (H1 p d dm dp hb hν1 (toProfile x) hs1).trans ?_
    apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hx.le _)
    exact mul_le_mul ((le_max_left _ _).trans (le_max_right _ _))
      (inv_pow_mono hνpos hνle1 ((le_max_left _ _).trans (le_max_right _ _)))
      (by positivity) hB.le
  have b32 : rawFam32 p.ν p.c p.train (toProfile x) ≤ P * x.1 ^ (-(3 / 2 : ℝ)) := by
    refine (H32 p d dm dp hb hν32 (toProfile x) hs1).trans ?_
    apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hx.le _)
    exact mul_le_mul ((le_max_right _ _).trans (le_max_right _ _))
      (inv_pow_mono hνpos hνle1 ((le_max_right _ _).trans (le_max_right _ _)))
      (by positivity) hB.le
  have r1 : Real.sqrt x.1 * x.1 ^ (-1 : ℝ) = x.1 ^ (-(1 / 2 : ℝ)) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add hx]
    norm_num
  have r2 : Real.sqrt x.1 * x.1 ^ (-(1 / 2 : ℝ)) = 1 := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add hx]
    norm_num
  have r3 : x.1 * x.1 ^ (-(3 / 2 : ℝ)) = x.1 ^ (-(1 / 2 : ℝ)) := by
    calc x.1 * x.1 ^ (-(3 / 2 : ℝ))
        = x.1 ^ (1 : ℝ) * x.1 ^ (-(3 / 2 : ℝ)) := by rw [Real.rpow_one]
      _ = x.1 ^ (-(1 / 2 : ℝ)) := by rw [← Real.rpow_add hx]; norm_num
  have r4 : x.1 * x.1 ^ (-1 : ℝ) = 1 := by
    rw [Real.rpow_neg_one]
    exact mul_inv_cancel₀ hx.ne'
  have hsS : x.1 ^ (-(1 / 2 : ℝ)) ≤ S ^ (-(1 / 2 : ℝ)) :=
    Real.rpow_le_rpow_of_nonpos (by linarith) hxS.le (by norm_num)
  have hs1_pow : x.1 ^ (-(1 / 2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by norm_num)
  have t1 : Real.sqrt x.1 * rawFam1 p.ν p.c p.train (toProfile x) ≤ P * S ^ (-(1 / 2 : ℝ)) := by
    calc Real.sqrt x.1 * rawFam1 p.ν p.c p.train (toProfile x)
        ≤ Real.sqrt x.1 * (P * x.1 ^ (-1 : ℝ)) :=
          mul_le_mul_of_nonneg_left b1 (Real.sqrt_nonneg _)
      _ = P * (Real.sqrt x.1 * x.1 ^ (-1 : ℝ)) := by ring
      _ = P * x.1 ^ (-(1 / 2 : ℝ)) := by rw [r1]
      _ ≤ P * S ^ (-(1 / 2 : ℝ)) := mul_le_mul_of_nonneg_left hsS hP0
  have t2 : Real.sqrt x.1 * rawFam12 p.ν p.c p.train (toProfile x) ≤ P := by
    calc Real.sqrt x.1 * rawFam12 p.ν p.c p.train (toProfile x)
        ≤ Real.sqrt x.1 * (P * x.1 ^ (-(1 / 2 : ℝ))) :=
          mul_le_mul_of_nonneg_left b12 (Real.sqrt_nonneg _)
      _ = P * (Real.sqrt x.1 * x.1 ^ (-(1 / 2 : ℝ))) := by ring
      _ = P := by rw [r2, mul_one]
  have t3x : x.1 * rawFam32 p.ν p.c p.train (toProfile x) ≤ P * x.1 ^ (-(1 / 2 : ℝ)) := by
    calc x.1 * rawFam32 p.ν p.c p.train (toProfile x)
        ≤ x.1 * (P * x.1 ^ (-(3 / 2 : ℝ))) := mul_le_mul_of_nonneg_left b32 hx.le
      _ = P * (x.1 * x.1 ^ (-(3 / 2 : ℝ))) := by ring
      _ = P * x.1 ^ (-(1 / 2 : ℝ)) := by rw [r3]
  have t3 : x.1 * rawFam32 p.ν p.c p.train (toProfile x) ≤ P * S ^ (-(1 / 2 : ℝ)) :=
    t3x.trans (mul_le_mul_of_nonneg_left hsS hP0)
  have t3_one : x.1 * rawFam32 p.ν p.c p.train (toProfile x) ≤ P :=
    t3x.trans (by nlinarith)
  have t4 : x.1 * rawFam1 p.ν p.c p.train (toProfile x) ≤ P := by
    calc x.1 * rawFam1 p.ν p.c p.train (toProfile x)
        ≤ x.1 * (P * x.1 ^ (-1 : ℝ)) := mul_le_mul_of_nonneg_left b1 hx.le
      _ = P * (x.1 * x.1 ^ (-1 : ℝ)) := by ring
      _ = P := by rw [r4, mul_one]
  have hε0 : 0 ≤ p.ε := p.ε_pos.le
  have hε1 : p.ε ≤ 1 := bgRegime_eps_le_one hb
  have hS0 : 0 ≤ S ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg (by linarith) _
  have hPS0 : 0 ≤ P * S ^ (-(1 / 2 : ℝ)) := mul_nonneg hP0 hS0
  have m_t2 : p.ε * (Real.sqrt x.1 * rawFam12 p.ν p.c p.train (toProfile x)) ≤ p.ε * P :=
    mul_le_mul_of_nonneg_left t2 hε0
  have m_t4 : 3 * p.ε * (x.1 * rawFam1 p.ν p.c p.train (toProfile x)) ≤ 3 * p.ε * P :=
    mul_le_mul_of_nonneg_left t4 (by positivity)
  have m_t5 : p.ε * p.ε * (x.1 * rawFam32 p.ν p.c p.train (toProfile x)) ≤ p.ε * P := by
    calc p.ε * p.ε * (x.1 * rawFam32 p.ν p.c p.train (toProfile x))
        ≤ p.ε * p.ε * P := mul_le_mul_of_nonneg_left t3_one (mul_nonneg hε0 hε0)
      _ = p.ε * (p.ε * P) := by ring
      _ ≤ 1 * (p.ε * P) := mul_le_mul_of_nonneg_right hε1 (mul_nonneg hε0 hP0)
      _ = p.ε * P := one_mul _
  have hmain := lateProfileQuantity_merProfile_le hb hx
  have halg : 5 * B * (p.ν ^ k)⁻¹ * (S ^ (-(1 / 2 : ℝ)) + p.ε) =
      5 * (P * S ^ (-(1 / 2 : ℝ))) + 5 * (p.ε * P) := by
    dsimp [P]
    ring
  rw [halg]
  linarith

end UnforcedLeray.Short.IIb
