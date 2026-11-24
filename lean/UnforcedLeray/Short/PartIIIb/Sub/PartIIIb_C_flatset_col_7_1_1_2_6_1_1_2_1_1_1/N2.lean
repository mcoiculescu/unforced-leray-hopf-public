import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_6_1_1_2_1_1_1
import UnforcedLeray.Short.PartIIa.Tasks.N02LerayComparison.NonzeroMode.CutoffApprox.Pt
import UnforcedLeray.Short.PartIIa.Tasks.N02LerayComparison.GradMember

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

open UnforcedLeray.B0220 (HSpace measureH Profile QPeriodic)
open UnforcedLeray.B0223 (MeridC)
open UnforcedLeray.B0226 (ProfileTest IsProfileTest)

/-- Eta cut-off of a profile by the smooth bump `nzcoChi (η / R)`. -/
def gclCut (R : ℝ) (Ψ : Profile → ℝ) : Profile → ℝ :=
  fun p => UnforcedLeray.Short.PartIIa.nzcoChi (p.2.2 / R) * Ψ p

theorem gclCut_isProfileTest {c R : ℝ} (hR : 0 < R) {Ψ : Profile → ℝ}
    (hΨ : GaussGradProfile c Ψ) : IsProfileTest c (gclCut R Ψ) := by
  obtain ⟨hs, hper, ⟨s0, s1, hs0, hband⟩, -, -⟩ := hΨ
  refine ⟨?_, ?_, ?_⟩
  · have h1 : ContDiff ℝ ∞ (fun p : Profile => p.2.2 / R) :=
      (contDiff_snd.comp contDiff_snd).div_const R
    exact (UnforcedLeray.Short.PartIIa.nzcoChi_contDiff.comp h1).mul hs
  · intro p
    simp only [gclCut]
    rw [hper p]
  · refine ⟨s0, s1, 2 * R, hs0, fun p hp => ?_⟩
    have hΨp : Ψ p ≠ 0 := right_ne_zero_of_mul hp
    have hχ : UnforcedLeray.Short.PartIIa.nzcoChi (p.2.2 / R) ≠ 0 := left_ne_zero_of_mul hp
    refine ⟨hband p hΨp, ?_⟩
    by_contra hlt
    simp only [not_le] at hlt
    apply hχ
    apply UnforcedLeray.Short.PartIIa.nzcoChi_eq_zero
    rw [abs_div, abs_of_pos hR, le_div_iff₀ hR]
    linarith

theorem gclCut_fderiv {R : ℝ} (hR : 0 < R) {Ψ : Profile → ℝ} (hΨs : ContDiff ℝ ∞ Ψ)
    (p v : Profile) :
    fderiv ℝ (gclCut R Ψ) p v =
      UnforcedLeray.Short.PartIIa.nzcoChi (p.2.2 / R) * fderiv ℝ Ψ p v +
        Ψ p * (deriv UnforcedLeray.Short.PartIIa.nzcoChi (p.2.2 / R) * (v.2.2 / R)) := by
  have hdiv : HasFDerivAt (fun q : Profile => q.2.2 / R)
      (R⁻¹ • ((ContinuousLinearMap.snd ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ)))) p := by
    have h := (R⁻¹ • ((ContinuousLinearMap.snd ℝ ℝ ℝ).comp
      (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ)))).hasFDerivAt (x := p)
    convert h using 1
    funext q
    simp [div_eq_inv_mul]
  have hd : HasDerivAt UnforcedLeray.Short.PartIIa.nzcoChi
      (deriv UnforcedLeray.Short.PartIIa.nzcoChi (p.2.2 / R)) (p.2.2 / R) :=
    ((UnforcedLeray.Short.PartIIa.nzcoChi_contDiff.differentiable (by simp))
      (p.2.2 / R)).hasDerivAt
  have hχ := hd.comp_hasFDerivAt p hdiv
  have hΨd : HasFDerivAt Ψ (fderiv ℝ Ψ p) p :=
    ((hΨs.differentiable (by simp)) p).hasFDerivAt
  have hprod := hχ.mul hΨd
  have heq : gclCut R Ψ = fun q : Profile =>
      UnforcedLeray.Short.PartIIa.nzcoChi (q.2.2 / R) * Ψ q := rfl
  rw [heq, show (fun q : Profile => UnforcedLeray.Short.PartIIa.nzcoChi (q.2.2 / R) * Ψ q) =
    ((UnforcedLeray.Short.PartIIa.nzcoChi ∘ fun q : Profile => q.2.2 / R) * Ψ) from rfl,
    hprod.fderiv]
  have hL : ∀ w : Profile, ((ContinuousLinearMap.snd ℝ ℝ ℝ).comp
      (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ))) w = w.2.2 := fun w => rfl
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, hL, smul_eq_mul,
    Function.comp_apply, div_eq_mul_inv]
  ring

theorem gclCut_dQ {R : ℝ} (hR : 0 < R) {Ψ : Profile → ℝ} (hΨs : ContDiff ℝ ∞ Ψ) (p : Profile) :
    Axi.dQ (gclCut R Ψ) p = UnforcedLeray.Short.PartIIa.nzcoChi (p.2.2 / R) * Axi.dQ Ψ p := by
  unfold Axi.dQ
  rw [gclCut_fderiv hR hΨs] <;> simp

theorem gclCut_dEta {R : ℝ} (hR : 0 < R) {Ψ : Profile → ℝ} (hΨs : ContDiff ℝ ∞ Ψ) (p : Profile) :
    Axi.dEta (gclCut R Ψ) p = UnforcedLeray.Short.PartIIa.nzcoChi (p.2.2 / R) * Axi.dEta Ψ p +
      Ψ p * (deriv UnforcedLeray.Short.PartIIa.nzcoChi (p.2.2 / R) * (1 / R)) := by
  unfold Axi.dEta
  rw [gclCut_fderiv hR hΨs] <;> norm_num <;> ring

theorem cgrad0_eq (Φ : Profile → ℝ) (p : Profile) :
    UnforcedLeray.Short.PartIIa.cgrad 0 Φ p =
      !₂[((Axi.dQ Φ p : ℝ) : ℂ), ((Axi.dEta Φ p : ℝ) : ℂ)] := by
  unfold UnforcedLeray.Short.PartIIa.cgrad
  rw [UnforcedLeray.B0226.Deps_zero]

theorem vec2_sub (a b c d : ℂ) : (!₂[a, b] : MeridC) - !₂[c, d] = !₂[a - c, b - d] := by
  ext i
  fin_cases i <;> simp

theorem norm_comp_le (x : MeridC) : ‖x 0‖ ≤ ‖x‖ ∧ ‖x 1‖ ≤ ‖x‖ :=
  ⟨PiLp.norm_apply_le x 0, PiLp.norm_apply_le x 1⟩

/-- Pointwise difference bound for the eta cut-off of a profile. -/
theorem gcl_diff_bound {R : ℝ} (hR : 0 < R) {Ψ : Profile → ℝ} (hΨs : ContDiff ℝ ∞ Ψ) {B1 : ℝ}
    (hB : ∀ t : ℝ, |deriv UnforcedLeray.Short.PartIIa.nzcoChi t| ≤ B1) (p : Profile) :
    ‖UnforcedLeray.Short.PartIIa.cgrad 0 (gclCut R Ψ) p - UnforcedLeray.Short.PartIIa.cgrad 0 Ψ p‖ ≤
      |UnforcedLeray.Short.PartIIa.nzcoChi (p.2.2 / R) - 1| *
        (2 * ‖UnforcedLeray.Short.PartIIa.cgrad 0 Ψ p‖) + B1 * |Ψ p| / R := by
  have hdQ : |Axi.dQ Ψ p| ≤ ‖UnforcedLeray.Short.PartIIa.cgrad 0 Ψ p‖ := by
    have h := (norm_comp_le (UnforcedLeray.Short.PartIIa.cgrad 0 Ψ p)).1
    rw [cgrad0_eq] at h ⊢
    simpa [Complex.norm_real, Real.norm_eq_abs] using h
  have hdE : |Axi.dEta Ψ p| ≤ ‖UnforcedLeray.Short.PartIIa.cgrad 0 Ψ p‖ := by
    have h := (norm_comp_le (UnforcedLeray.Short.PartIIa.cgrad 0 Ψ p)).2
    rw [cgrad0_eq] at h ⊢
    simpa [Complex.norm_real, Real.norm_eq_abs] using h
  have hdiff : UnforcedLeray.Short.PartIIa.cgrad 0 (gclCut R Ψ) p -
      UnforcedLeray.Short.PartIIa.cgrad 0 Ψ p =
      !₂[((UnforcedLeray.Short.PartIIa.nzcoChi (p.2.2 / R) * Axi.dQ Ψ p : ℝ) : ℂ) -
          ((Axi.dQ Ψ p : ℝ) : ℂ),
        ((UnforcedLeray.Short.PartIIa.nzcoChi (p.2.2 / R) * Axi.dEta Ψ p +
          Ψ p * (deriv UnforcedLeray.Short.PartIIa.nzcoChi (p.2.2 / R) * (1 / R)) : ℝ) : ℂ) -
          ((Axi.dEta Ψ p : ℝ) : ℂ)] := by
    rw [cgrad0_eq, cgrad0_eq, gclCut_dQ hR hΨs, gclCut_dEta hR hΨs, vec2_sub]
  rw [hdiff]
  refine (UnforcedLeray.Short.PartIIa.nzco_norm_two _ _).trans ?_
  have hχ0 := UnforcedLeray.Short.PartIIa.nzcoChi_nonneg (p.2.2 / R)
  have hχ1 := UnforcedLeray.Short.PartIIa.nzcoChi_le_one (p.2.2 / R)
  have ha : |UnforcedLeray.Short.PartIIa.nzcoChi (p.2.2 / R) - 1| ≤ 1 := by
    rw [abs_le]; constructor <;> linarith
  have ha0 : 0 ≤ |UnforcedLeray.Short.PartIIa.nzcoChi (p.2.2 / R) - 1| := abs_nonneg _
  have e1 : ((UnforcedLeray.Short.PartIIa.nzcoChi (p.2.2 / R) * Axi.dQ Ψ p : ℝ) : ℂ) -
      ((Axi.dQ Ψ p : ℝ) : ℂ) = (((UnforcedLeray.Short.PartIIa.nzcoChi (p.2.2 / R) - 1) *
        Axi.dQ Ψ p : ℝ) : ℂ) := by push_cast; ring
  have e2 : ((UnforcedLeray.Short.PartIIa.nzcoChi (p.2.2 / R) * Axi.dEta Ψ p +
          Ψ p * (deriv UnforcedLeray.Short.PartIIa.nzcoChi (p.2.2 / R) * (1 / R)) : ℝ) : ℂ) -
          ((Axi.dEta Ψ p : ℝ) : ℂ) = (((UnforcedLeray.Short.PartIIa.nzcoChi (p.2.2 / R) - 1) *
            Axi.dEta Ψ p + Ψ p * (deriv UnforcedLeray.Short.PartIIa.nzcoChi (p.2.2 / R) *
            (1 / R)) : ℝ) : ℂ) := by push_cast; ring
  rw [e1, e2, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs]
  have h1 : |(UnforcedLeray.Short.PartIIa.nzcoChi (p.2.2 / R) - 1) * Axi.dQ Ψ p| ≤
      |UnforcedLeray.Short.PartIIa.nzcoChi (p.2.2 / R) - 1| *
        ‖UnforcedLeray.Short.PartIIa.cgrad 0 Ψ p‖ := by
    rw [abs_mul]; exact mul_le_mul_of_nonneg_left hdQ ha0
  have h2a : |(UnforcedLeray.Short.PartIIa.nzcoChi (p.2.2 / R) - 1) * Axi.dEta Ψ p| ≤
      |UnforcedLeray.Short.PartIIa.nzcoChi (p.2.2 / R) - 1| *
        ‖UnforcedLeray.Short.PartIIa.cgrad 0 Ψ p‖ := by
    rw [abs_mul]; exact mul_le_mul_of_nonneg_left hdE ha0
  have hψ : |Ψ p * (deriv UnforcedLeray.Short.PartIIa.nzcoChi (p.2.2 / R) * (1 / R))| ≤
      B1 * |Ψ p| / R := by
    rw [abs_mul, abs_mul, abs_of_pos (one_div_pos.2 hR)]
    have hb := hB (p.2.2 / R)
    have hpos : 0 ≤ |Ψ p| * (1 / R) := by positivity
    calc |Ψ p| * (|deriv UnforcedLeray.Short.PartIIa.nzcoChi (p.2.2 / R)| * (1 / R))
        ≤ |Ψ p| * (B1 * (1 / R)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hb (by positivity)) (abs_nonneg _)
      _ = B1 * |Ψ p| / R := by ring
  have h2 : |(UnforcedLeray.Short.PartIIa.nzcoChi (p.2.2 / R) - 1) * Axi.dEta Ψ p +
      Ψ p * (deriv UnforcedLeray.Short.PartIIa.nzcoChi (p.2.2 / R) * (1 / R))| ≤
      |UnforcedLeray.Short.PartIIa.nzcoChi (p.2.2 / R) - 1| *
        ‖UnforcedLeray.Short.PartIIa.cgrad 0 Ψ p‖ + B1 * |Ψ p| / R :=
    (abs_add_le _ _).trans (add_le_add h2a hψ)
  have hsplit : |UnforcedLeray.Short.PartIIa.nzcoChi (p.2.2 / R) - 1| *
      (2 * ‖UnforcedLeray.Short.PartIIa.cgrad 0 Ψ p‖) =
      |UnforcedLeray.Short.PartIIa.nzcoChi (p.2.2 / R) - 1| *
        ‖UnforcedLeray.Short.PartIIa.cgrad 0 Ψ p‖ +
      |UnforcedLeray.Short.PartIIa.nzcoChi (p.2.2 / R) - 1| *
        ‖UnforcedLeray.Short.PartIIa.cgrad 0 Ψ p‖ := by ring
  rw [hsplit]
  linarith [h1, h2]

theorem gcl_pt_tendsto {Ψ : Profile → ℝ} (hΨs : ContDiff ℝ ∞ Ψ) {B1 : ℝ}
    (hB : ∀ t : ℝ, |deriv UnforcedLeray.Short.PartIIa.nzcoChi t| ≤ B1) (p : Profile) :
    Tendsto (fun n : ℕ => ‖UnforcedLeray.Short.PartIIa.cgrad 0 (gclCut ((n : ℝ) + 1) Ψ) p -
      UnforcedLeray.Short.PartIIa.cgrad 0 Ψ p‖) atTop (𝓝 0) := by
  have hRlim : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
  have hη : Tendsto (fun n : ℕ => p.2.2 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hRlim
  have hχ : Tendsto (fun n : ℕ => UnforcedLeray.Short.PartIIa.nzcoChi (p.2.2 / ((n : ℝ) + 1)))
      atTop (𝓝 1) := by
    have hc : Continuous UnforcedLeray.Short.PartIIa.nzcoChi :=
      UnforcedLeray.Short.PartIIa.nzcoChi_contDiff.continuous
    have h := (hc.tendsto 0).comp hη
    have h0 : UnforcedLeray.Short.PartIIa.nzcoChi 0 = 1 :=
      UnforcedLeray.Short.PartIIa.nzcoChi_eq_one (by simp)
    rw [h0] at h
    exact h
  have hA : Tendsto (fun n : ℕ =>
      |UnforcedLeray.Short.PartIIa.nzcoChi (p.2.2 / ((n : ℝ) + 1)) - 1|) atTop (𝓝 0) := by
    have h := (hχ.sub_const 1).abs
    simpa using h
  have hB' : Tendsto (fun n : ℕ => B1 * |Ψ p| / ((n : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hRlim
  have hsum := (hA.mul_const (2 * ‖UnforcedLeray.Short.PartIIa.cgrad 0 Ψ p‖)).add hB'
  simp only [zero_mul, zero_add] at hsum
  refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) hsum
  exact gcl_diff_bound (by positivity) hΨs hB p

theorem gcl_eLpNorm_tendsto {c : ℝ} {Ψ : Profile → ℝ} (hΨ : GaussGradProfile c Ψ) {B1 : ℝ}
    (hB : ∀ t : ℝ, |deriv UnforcedLeray.Short.PartIIa.nzcoChi t| ≤ B1) :
    Tendsto (fun n : ℕ => eLpNorm (UnforcedLeray.Short.PartIIa.cgrad 0 (gclCut ((n : ℝ) + 1) Ψ) -
      UnforcedLeray.Short.PartIIa.cgrad 0 Ψ) 2 (measureH c)) atTop (𝓝 0) := by
  have hΨs : ContDiff ℝ ∞ Ψ := hΨ.1
  have hB0 : 0 ≤ B1 := (abs_nonneg _).trans (hB 0)
  have hRpos : ∀ n : ℕ, (0 : ℝ) < (n : ℝ) + 1 := fun n => by positivity
  have hbound : ∀ (n : ℕ) (p : Profile),
      ‖UnforcedLeray.Short.PartIIa.cgrad 0 (gclCut ((n : ℝ) + 1) Ψ) p -
        UnforcedLeray.Short.PartIIa.cgrad 0 Ψ p‖ ≤
        2 * ‖UnforcedLeray.Short.PartIIa.cgrad 0 Ψ p‖ + B1 * ‖Ψ p‖ := by
    intro n p
    have hR1 : (1 : ℝ) ≤ (n : ℝ) + 1 := by
      have := (Nat.cast_nonneg n : (0 : ℝ) ≤ n); linarith
    refine (gcl_diff_bound (hRpos n) hΨs hB p).trans ?_
    simp only [Real.norm_eq_abs]
    have ha : |UnforcedLeray.Short.PartIIa.nzcoChi (p.2.2 / ((n : ℝ) + 1)) - 1| ≤ 1 := by
      have h0 := UnforcedLeray.Short.PartIIa.nzcoChi_nonneg (p.2.2 / ((n : ℝ) + 1))
      have h1 := UnforcedLeray.Short.PartIIa.nzcoChi_le_one (p.2.2 / ((n : ℝ) + 1))
      rw [abs_le]; constructor <;> linarith
    have h1 : |UnforcedLeray.Short.PartIIa.nzcoChi (p.2.2 / ((n : ℝ) + 1)) - 1| *
        (2 * ‖UnforcedLeray.Short.PartIIa.cgrad 0 Ψ p‖) ≤ 2 * ‖UnforcedLeray.Short.PartIIa.cgrad 0 Ψ p‖ :=
      mul_le_of_le_one_left (by positivity) ha
    have h2 : B1 * |Ψ p| / ((n : ℝ) + 1) ≤ B1 * |Ψ p| :=
      div_le_self (mul_nonneg hB0 (abs_nonneg _)) hR1
    linarith
  have hMmem : MemLp (fun p : Profile => 2 * ‖UnforcedLeray.Short.PartIIa.cgrad 0 Ψ p‖ +
      B1 * ‖Ψ p‖) 2 (measureH c) :=
    ((hΨ.2.2.2.2).norm.const_mul 2).add (hΨ.2.2.2.1.norm.const_mul B1)
  have hM0 : ∀ p : Profile, 0 ≤ 2 * ‖UnforcedLeray.Short.PartIIa.cgrad 0 Ψ p‖ + B1 * ‖Ψ p‖ :=
    fun p => add_nonneg (by positivity) (mul_nonneg hB0 (norm_nonneg _))
  have hmeas : ∀ n : ℕ, Continuous (fun p : Profile =>
      UnforcedLeray.Short.PartIIa.cgrad 0 (gclCut ((n : ℝ) + 1) Ψ) p -
        UnforcedLeray.Short.PartIIa.cgrad 0 Ψ p) := by
    intro n
    have hs := gclCut_isProfileTest (c := c) (R := (n : ℝ) + 1) (hRpos n) hΨ
    exact (UnforcedLeray.Short.PartIIa.NearGradMemberAux.continuous_cgrad 0 hs.smooth).sub
      (UnforcedLeray.Short.PartIIa.NearGradMemberAux.continuous_cgrad 0 hΨs)
  have hfin : ∫⁻ p, ‖2 * ‖UnforcedLeray.Short.PartIIa.cgrad 0 Ψ p‖ + B1 * ‖Ψ p‖‖ₑ ^ (2 : ℝ)
      ∂(measureH c) ≠ ⊤ := by
    have h := (eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top
      (by norm_num : (2 : ℝ≥0∞) ≠ 0) (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)).1 hMmem.eLpNorm_lt_top
    rw [ENNReal.toReal_ofNat] at h
    exact h.ne
  have hint : Tendsto (fun n : ℕ => ∫⁻ p, ‖UnforcedLeray.Short.PartIIa.cgrad 0 (gclCut ((n : ℝ) + 1) Ψ) p -
      UnforcedLeray.Short.PartIIa.cgrad 0 Ψ p‖ₑ ^ (2 : ℝ) ∂(measureH c)) atTop (𝓝 0) := by
    have hdc := tendsto_lintegral_of_dominated_convergence (μ := measureH c)
      (F := fun n p => ‖UnforcedLeray.Short.PartIIa.cgrad 0 (gclCut ((n : ℝ) + 1) Ψ) p -
        UnforcedLeray.Short.PartIIa.cgrad 0 Ψ p‖ₑ ^ (2 : ℝ))
      (f := fun _ => 0)
      (bound := fun p => ‖2 * ‖UnforcedLeray.Short.PartIIa.cgrad 0 Ψ p‖ + B1 * ‖Ψ p‖‖ₑ ^ (2 : ℝ))
      (fun n => ((hmeas n).measurable.enorm).pow_const _)
      (fun n => Eventually.of_forall fun p => by
        have hle : ‖UnforcedLeray.Short.PartIIa.cgrad 0 (gclCut ((n : ℝ) + 1) Ψ) p -
            UnforcedLeray.Short.PartIIa.cgrad 0 Ψ p‖ₑ ≤
            ‖2 * ‖UnforcedLeray.Short.PartIIa.cgrad 0 Ψ p‖ + B1 * ‖Ψ p‖‖ₑ := by
          rw [← ofReal_norm_eq_enorm, ← ofReal_norm_eq_enorm, Real.norm_of_nonneg (hM0 p)]
          exact ENNReal.ofReal_le_ofReal (hbound n p)
        exact ENNReal.rpow_le_rpow hle (by norm_num))
      hfin
      (Eventually.of_forall fun p => by
        have h1 : Tendsto (fun n : ℕ => ‖UnforcedLeray.Short.PartIIa.cgrad 0 (gclCut ((n : ℝ) + 1) Ψ) p -
            UnforcedLeray.Short.PartIIa.cgrad 0 Ψ p‖ₑ) atTop (𝓝 0) := by
          have h := ENNReal.tendsto_ofReal (gcl_pt_tendsto hΨs hB p)
          simpa [ofReal_norm_eq_enorm] using h
        have h2 := ((ENNReal.continuous_rpow_const (y := (2 : ℝ))).tendsto 0).comp h1
        have h2' : Tendsto (fun n : ℕ => ‖UnforcedLeray.Short.PartIIa.cgrad 0 (gclCut ((n : ℝ) + 1) Ψ) p -
            UnforcedLeray.Short.PartIIa.cgrad 0 Ψ p‖ₑ ^ (2 : ℝ)) atTop
            (𝓝 ((0 : ℝ≥0∞) ^ (2 : ℝ))) := h2
        rw [ENNReal.zero_rpow_of_pos (by norm_num : (0 : ℝ) < 2)] at h2'
        exact h2')
    simpa using hdc
  have hmain := ((ENNReal.continuous_rpow_const (y := (1 / 2 : ℝ))).tendsto 0).comp hint
  rw [ENNReal.zero_rpow_of_pos (by norm_num : (0 : ℝ) < 1 / 2)] at hmain
  refine hmain.congr (fun n => ?_)
  simp only [Function.comp_apply]
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)]
  norm_num

theorem gaussGradInClosure_proof : GaussGradInClosure := by
  intro c Ψ hΨ
  obtain ⟨B1, B2, -, -, hd⟩ := UnforcedLeray.Short.PartIIa.nzco_bounds
  have hB : ∀ t : ℝ, |deriv UnforcedLeray.Short.PartIIa.nzcoChi t| ≤ B1 := fun t => (hd t).1
  have hRpos : ∀ n : ℕ, (0 : ℝ) < (n : ℝ) + 1 := fun n => by positivity
  have hmem : ∀ n : ℕ, MemLp (UnforcedLeray.Short.PartIIa.cgrad 0 (gclCut ((n : ℝ) + 1) Ψ)) 2
      (measureH c) := fun n =>
    UnforcedLeray.Short.PartIIa.NearGradMemberAux.memLp_cgrad (ε := 0)
      (gclCut_isProfileTest (hRpos n) hΨ)
  have hconv : Tendsto (fun n : ℕ => (hmem n).toLp (UnforcedLeray.Short.PartIIa.cgrad 0
      (gclCut ((n : ℝ) + 1) Ψ))) atTop (𝓝 (hΨ.2.2.2.2.toLp _)) := by
    refine Lp.tendsto_Lp_of_tendsto_eLpNorm (f := fun n : ℕ => (hmem n).toLp
      (UnforcedLeray.Short.PartIIa.cgrad 0 (gclCut ((n : ℝ) + 1) Ψ)))
      (UnforcedLeray.Short.PartIIa.cgrad 0 Ψ) hΨ.2.2.2.2 ?_
    refine Tendsto.congr (fun n => ?_) (gcl_eLpNorm_tendsto hΨ hB)
    exact (eLpNorm_congr_ae ((MemLp.coeFn_toLp _).sub EventuallyEq.rfl)).symm
  rw [← SetLike.mem_coe, Submodule.topologicalClosure_coe]
  refine mem_closure_of_tendsto hconv (Eventually.of_forall fun n => ?_)
  exact Submodule.subset_span ⟨⟨gclCut ((n : ℝ) + 1) Ψ, gclCut_isProfileTest (hRpos n) hΨ⟩,
    hmem n, rfl⟩

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
