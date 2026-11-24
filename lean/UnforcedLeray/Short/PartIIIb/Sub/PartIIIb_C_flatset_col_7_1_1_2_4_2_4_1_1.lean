import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_4_2_4_1_of
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_4_2_4_2_1
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# `SFCCausalHeatCont`: continuity of the Duhamel integral on `s > 0`
(task `PartIII-b:C/flatset/col/7/1/1/2/4/2/4/1/1`)

Source `the November 2 reference manuscript`
lines 1650-1656, 1684-1689, 3426-3430.

Strategy: by `SFCDatumReg`, for a.e. `σ` the periodized datum is replaced by `σ⁻¹ G(σ, ·)`, which is
jointly continuous, bounded and vanishes for `σ < s₀`.  For `s > 0` the causal heat is then the
integral over `σ ∈ (0, s)` of `(σ/s)^μ e^{ν(s-σ)Δ} W_σ`, and it is continuous in `(s, x)` by
dominated convergence, using continuity of the planar heat in `(θ, σ, x)` for `θ > 0`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

/-- Sup-norm bound for the plane heat (`θ > 0`: `Heat.norm_heatConv_le_of_bound`; `θ ≤ 0`: identity). -/
theorem sfc_planeHeat_norm_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {θ M : ℝ} {u : ℝ × ℝ → E} (hu : ∀ z, ‖u z‖ ≤ M) (x : ℝ × ℝ) :
    ‖UnforcedLeray.B0224.planeHeat θ u x‖ ≤ M := by
  by_cases hθ : 0 < θ
  · rw [UnforcedLeray.B0224.planeHeat_of_pos hθ]
    exact UnforcedLeray.Heat.norm_heatConv_le_of_bound UnforcedLeray.B0224.planeι hθ hu x
  · rw [UnforcedLeray.B0224.planeHeat_of_nonpos (not_lt.1 hθ)]
    exact hu x

/-- Continuity in the time variable of the Gaussian kernel at a positive time. -/
theorem sfc_gaussKernel_contAt (y : UnforcedLeray.Gaussian.Euc 2) {t₀ : ℝ} (ht₀ : 0 < t₀) :
    ContinuousAt (fun t : ℝ => UnforcedLeray.Gaussian.gaussKernel 2 t y) t₀ := by
  unfold UnforcedLeray.Gaussian.gaussKernel
  have hpos : 0 < 4 * Real.pi * t₀ := mul_pos (mul_pos (by norm_num) Real.pi_pos) ht₀
  have h1 : ContinuousAt (fun t : ℝ => (4 * Real.pi * t) ^ (-((2:ℕ):ℝ) / 2)) t₀ :=
    ContinuousAt.rpow_const (by fun_prop) (Or.inl hpos.ne')
  have h2 : ContinuousAt (fun t : ℝ => -‖y‖ ^ 2 / (4 * t)) t₀ :=
    ContinuousAt.div continuousAt_const (by fun_prop) (mul_pos (by norm_num) ht₀).ne'
  exact h1.mul (Real.continuous_exp.continuousAt.comp h2)

/-- Pointwise Gaussian bound, uniform for `t ∈ [a, b]`, with an integrable majorant in `y`. -/
theorem sfc_gaussKernel_le {t a b : ℝ} (ha : 0 < a) (hat : a ≤ t) (htb : t ≤ b)
    (y : UnforcedLeray.Gaussian.Euc 2) :
    UnforcedLeray.Gaussian.gaussKernel 2 t y ≤
      (4 * Real.pi * a) ^ (-((2:ℕ):ℝ) / 2) * Real.exp (-(1 / (4 * b)) * ‖y‖ ^ 2) := by
  have ht : 0 < t := lt_of_lt_of_le ha hat
  have hb : 0 < b := lt_of_lt_of_le ht htb
  unfold UnforcedLeray.Gaussian.gaussKernel
  have hA : 0 < 4 * Real.pi * a := mul_pos (mul_pos (by norm_num) Real.pi_pos) ha
  have h1 : (4 * Real.pi * t) ^ (-((2:ℕ):ℝ) / 2) ≤ (4 * Real.pi * a) ^ (-((2:ℕ):ℝ) / 2) :=
    Real.rpow_le_rpow_of_nonpos hA (by gcongr) (by norm_num)
  have h2 : Real.exp (-‖y‖ ^ 2 / (4 * t)) ≤ Real.exp (-(1 / (4 * b)) * ‖y‖ ^ 2) := by
    apply Real.exp_le_exp.2
    have h3 : ‖y‖ ^ 2 / (4 * b) ≤ ‖y‖ ^ 2 / (4 * t) :=
      div_le_div_of_nonneg_left (by positivity) (by linarith) (by linarith)
    have e1 : -(1 / (4 * b)) * ‖y‖ ^ 2 = -(‖y‖ ^ 2 / (4 * b)) := by ring
    rw [e1, neg_div]
    linarith
  exact mul_le_mul h1 h2 (Real.exp_pos _).le (Real.rpow_nonneg hA.le _)

/-- Joint continuity of `(θ, σ, x) ↦ e^{θΔ} W_σ (x)` at `θ₀ > 0`, for a jointly continuous bounded
family `W`. -/
theorem sfc_planeHeat_contAt {W : ℝ → ℝ × ℝ → UnforcedLeray.B0223.MeridC}
    (hW : Continuous (fun r : ℝ × (ℝ × ℝ) => W r.1 r.2)) {M : ℝ}
    (hM : ∀ σ z, ‖W σ z‖ ≤ M) {θ₀ : ℝ} (hθ₀ : 0 < θ₀) (σ₀ : ℝ) (x₀ : ℝ × ℝ) :
    ContinuousAt (fun q : ℝ × (ℝ × (ℝ × ℝ)) =>
      UnforcedLeray.B0224.planeHeat q.1 (W q.2.1) q.2.2) (θ₀, σ₀, x₀) := by
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0 0)
  have hθmem : θ₀ ∈ Ioo (θ₀ / 2) (2 * θ₀) := ⟨by linarith, by linarith⟩
  have hmem : Ioo (θ₀ / 2) (2 * θ₀) ∈ 𝓝 θ₀ := Ioo_mem_nhds hθmem.1 hθmem.2
  have hev : ∀ᶠ q : ℝ × (ℝ × (ℝ × ℝ)) in 𝓝 (θ₀, σ₀, x₀), q.1 ∈ Ioo (θ₀ / 2) (2 * θ₀) :=
    (continuous_fst.tendsto (θ₀, σ₀, x₀)).eventually hmem
  have hθpos : ∀ᶠ q : ℝ × (ℝ × (ℝ × ℝ)) in 𝓝 (θ₀, σ₀, x₀), 0 < q.1 :=
    hev.mono fun q hq => lt_trans (by linarith) hq.1
  have hmain : ContinuousAt (fun q : ℝ × (ℝ × (ℝ × ℝ)) =>
      ∫ y : UnforcedLeray.Gaussian.Euc 2,
        UnforcedLeray.Gaussian.gaussKernel 2 q.1 y •
          W q.2.1 (q.2.2 - UnforcedLeray.B0224.planeι y)) (θ₀, σ₀, x₀) := by
    refine continuousAt_of_dominated (bound := fun y : UnforcedLeray.Gaussian.Euc 2 =>
        (4 * Real.pi * (θ₀ / 2)) ^ (-((2:ℕ):ℝ) / 2) *
          Real.exp (-(1 / (4 * (2 * θ₀))) * ‖y‖ ^ 2) * M) ?_ ?_ ?_ ?_
    · refine Filter.Eventually.of_forall fun q => ?_
      have hWy : Continuous (fun y : UnforcedLeray.Gaussian.Euc 2 =>
          W q.2.1 (q.2.2 - UnforcedLeray.B0224.planeι y)) :=
        hW.comp (continuous_const.prodMk
          (continuous_const.sub UnforcedLeray.B0224.continuous_planeι))
      exact ((UnforcedLeray.Gaussian.continuous_gaussKernel (d := 2) q.1).smul hWy).aestronglyMeasurable
    · filter_upwards [hev] with q hq
      refine Filter.Eventually.of_forall fun y => ?_
      have hq0 : 0 < q.1 := lt_trans (by linarith) hq.1
      rw [norm_smul, Real.norm_of_nonneg (UnforcedLeray.Gaussian.gaussKernel_nonneg hq0 y)]
      calc UnforcedLeray.Gaussian.gaussKernel 2 q.1 y *
            ‖W q.2.1 (q.2.2 - UnforcedLeray.B0224.planeι y)‖
          ≤ UnforcedLeray.Gaussian.gaussKernel 2 q.1 y * M :=
            mul_le_mul_of_nonneg_left (hM _ _) (UnforcedLeray.Gaussian.gaussKernel_nonneg hq0 y)
        _ ≤ _ := mul_le_mul_of_nonneg_right
            (sfc_gaussKernel_le (by linarith) hq.1.le hq.2.le y) hM0
    · exact ((UnforcedLeray.Gaussian.integrable_exp_neg_mul_sq_norm
        (b := 1 / (4 * (2 * θ₀))) (div_pos one_pos (by linarith))).const_mul _).mul_const M
    · refine Filter.Eventually.of_forall fun y => ?_
      have h1 : ContinuousAt (fun q : ℝ × (ℝ × (ℝ × ℝ)) =>
          UnforcedLeray.Gaussian.gaussKernel 2 q.1 y) (θ₀, σ₀, x₀) :=
        ContinuousAt.comp (g := fun t : ℝ => UnforcedLeray.Gaussian.gaussKernel 2 t y)
          (f := fun q : ℝ × (ℝ × (ℝ × ℝ)) => q.1) (sfc_gaussKernel_contAt y hθ₀) continuousAt_fst
      have h2 : ContinuousAt (fun q : ℝ × (ℝ × (ℝ × ℝ)) =>
          W q.2.1 (q.2.2 - UnforcedLeray.B0224.planeι y)) (θ₀, σ₀, x₀) := by
        have hmap : Continuous (fun q : ℝ × (ℝ × (ℝ × ℝ)) =>
            (q.2.1, q.2.2 - UnforcedLeray.B0224.planeι y)) :=
          (continuous_fst.comp continuous_snd).prodMk
            ((continuous_snd.comp continuous_snd).sub continuous_const)
        exact (hW.comp hmap).continuousAt
      exact h1.smul h2
  have hEq : (fun q : ℝ × (ℝ × (ℝ × ℝ)) =>
      ∫ y : UnforcedLeray.Gaussian.Euc 2,
        UnforcedLeray.Gaussian.gaussKernel 2 q.1 y •
          W q.2.1 (q.2.2 - UnforcedLeray.B0224.planeι y))
      =ᶠ[𝓝 (θ₀, σ₀, x₀)]
      (fun q : ℝ × (ℝ × (ℝ × ℝ)) => UnforcedLeray.B0224.planeHeat q.1 (W q.2.1) q.2.2) := by
    filter_upwards [hθpos] with q hq
    rw [UnforcedLeray.B0224.planeHeat_of_pos hq]
  exact hmain.congr hEq

/-- The datum `W_σ = σ⁻¹ G(σ, ·)` of the flat projection. -/
def sfcW (G : UnforcedLeray.B0220.Profile → UnforcedLeray.B0223.MeridC) (σ : ℝ) :
    ℝ × ℝ → UnforcedLeray.B0223.MeridC :=
  fun z => (((σ : ℝ) : ℂ))⁻¹ • G (σ, z)

/-- The integrand of the Duhamel integral with datum `W`, cut off to `σ ∈ (0, s)`. -/
def sfcK (G : UnforcedLeray.B0220.Profile → UnforcedLeray.B0223.MeridC) (ν μ : ℝ)
    (p : ℝ × (ℝ × ℝ)) (σ : ℝ) : UnforcedLeray.B0223.MeridC :=
  Set.indicator (Set.Ioo 0 p.1) (fun σ' : ℝ =>
    (((σ' / p.1 : ℝ) : ℂ)) ^ (μ : ℂ) •
      UnforcedLeray.B0224.planeHeat (ν * (p.1 - σ')) (sfcW G σ') p.2) σ

theorem sfcW_cont (G : UnforcedLeray.B0220.Profile → UnforcedLeray.B0223.MeridC)
    (hGc : Continuous G) {s0 : ℝ} (hs0 : 0 < s0)
    (hGz : ∀ p : UnforcedLeray.B0220.Profile, p.1 < s0 → G p = 0) :
    Continuous (fun r : ℝ × (ℝ × ℝ) => sfcW G r.1 r.2) := by
  refine continuous_iff_continuousAt.2 fun r => ?_
  rcases lt_or_ge r.1 s0 with h | h
  · have hev : ∀ᶠ r' : ℝ × (ℝ × ℝ) in 𝓝 r, r'.1 < s0 :=
      ContinuousAt.eventually_lt continuous_fst.continuousAt continuousAt_const h
    refine (continuousAt_const : ContinuousAt (fun _ : ℝ × (ℝ × ℝ) =>
      (0 : UnforcedLeray.B0223.MeridC)) r).congr ?_
    filter_upwards [hev] with r' hr'
    simp [sfcW, hGz r' hr']
  · have hpos : 0 < r.1 := lt_of_lt_of_le hs0 h
    have hc1 : ContinuousAt (fun r' : ℝ × (ℝ × ℝ) => (((r'.1 : ℝ) : ℂ))⁻¹) r :=
      ContinuousAt.inv₀ (Complex.continuous_ofReal.continuousAt.comp continuous_fst.continuousAt)
        (Complex.ofReal_ne_zero.2 hpos.ne')
    have hc2 : ContinuousAt (fun r' : ℝ × (ℝ × ℝ) => G r') r := hGc.continuousAt
    exact hc1.smul hc2

theorem sfcW_bound (G : UnforcedLeray.B0220.Profile → UnforcedLeray.B0223.MeridC)
    {M s0 : ℝ} (hM : ∀ p, ‖G p‖ ≤ M) (hM0 : 0 ≤ M) (hs0 : 0 < s0)
    (hGz : ∀ p : UnforcedLeray.B0220.Profile, p.1 < s0 → G p = 0) (σ : ℝ) (z : ℝ × ℝ) :
    ‖sfcW G σ z‖ ≤ M / s0 := by
  show ‖(((σ : ℝ) : ℂ))⁻¹ • G (σ, z)‖ ≤ M / s0
  by_cases h : σ < s0
  · rw [hGz (σ, z) h, smul_zero, norm_zero]
    exact div_nonneg hM0 hs0.le
  · push_neg at h
    have hσ : 0 < σ := lt_of_lt_of_le hs0 h
    rw [norm_smul, norm_inv, Complex.norm_real, Real.norm_of_nonneg hσ.le]
    calc σ⁻¹ * ‖G (σ, z)‖ ≤ s0⁻¹ * M :=
          mul_le_mul (inv_anti₀ hs0 h) (hM _) (norm_nonneg _) (inv_nonneg.2 hs0.le)
      _ = M / s0 := by ring

/-- Continuity in `σ` of the coefficient-weighted heat term, for `0 < σ < s`. -/
theorem sfc_term_contAt {G : UnforcedLeray.B0220.Profile → UnforcedLeray.B0223.MeridC}
    {ν μ : ℝ} (hν : 0 < ν) {K : ℝ}
    (hWc : Continuous (fun r : ℝ × (ℝ × ℝ) => sfcW G r.1 r.2))
    (hWb : ∀ σ z, ‖sfcW G σ z‖ ≤ K) {s σ : ℝ} (hs : 0 < s) (hσ : 0 < σ) (hσs : σ < s)
    (x : ℝ × ℝ) :
    ContinuousAt (fun σ' : ℝ => (((σ' / s : ℝ) : ℂ)) ^ (μ : ℂ) •
      UnforcedLeray.B0224.planeHeat (ν * (s - σ')) (sfcW G σ') x) σ := by
  have hθ : 0 < ν * (s - σ) := mul_pos hν (sub_pos.2 hσs)
  have hcore := sfc_planeHeat_contAt (W := sfcW G) hWc hWb hθ σ x
  have hg : Continuous (fun σ' : ℝ => (ν * (s - σ'), σ', x)) := by fun_prop
  have hplan : ContinuousAt (fun σ' : ℝ =>
      UnforcedLeray.B0224.planeHeat (ν * (s - σ')) (sfcW G σ') x) σ :=
    hcore.comp (f := fun σ' : ℝ => (ν * (s - σ'), σ', x)) hg.continuousAt
  have hcoef : ContinuousAt (fun σ' : ℝ => (((σ' / s : ℝ) : ℂ)) ^ (μ : ℂ)) σ :=
    (Complex.continuousAt_ofReal_cpow_const (σ / s) (μ : ℂ)
      (Or.inr (div_pos hσ hs).ne')).comp (f := fun σ' : ℝ => σ' / s) (by fun_prop)
  exact hcoef.smul hplan

/-- Coefficient bound `|(σ/p)^μ| ≤ 1 + (s₀/(2t₀))^μ` for `s₀ ≤ σ < p < 2t₀`. -/
theorem sfc_coef_bound {s0 t₀ μ : ℝ} (hs0 : 0 < s0) (ht₀ : 0 < t₀) {σ p1 : ℝ}
    (hσ : 0 < σ) (hσ1 : σ < p1) (hs : s0 ≤ σ) (hp1 : p1 < 2 * t₀) :
    ‖(((σ / p1 : ℝ) : ℂ)) ^ (μ : ℂ)‖ ≤ 1 + (s0 / (2 * t₀)) ^ μ := by
  have hp0 : 0 < p1 := lt_trans hσ hσ1
  rw [Complex.norm_cpow_eq_rpow_re_of_pos (div_pos hσ hp0)]
  simp only [Complex.ofReal_re]
  have hA0 : 0 < s0 / (2 * t₀) := div_pos hs0 (by linarith)
  have hAt : s0 / (2 * t₀) ≤ σ / p1 := by
    rw [div_le_div_iff₀ (by linarith) hp0]
    nlinarith [mul_nonneg (sub_nonneg.2 hs) hp0.le, mul_nonneg hσ.le (sub_nonneg.2 hp1.le)]
  have ht1 : σ / p1 ≤ 1 := (div_le_one hp0).2 hσ1.le
  rcases le_total 0 μ with hμ | hμ
  · have := Real.rpow_le_one (div_pos hσ hp0).le ht1 hμ
    linarith [Real.rpow_nonneg hA0.le μ]
  · have := Real.rpow_le_rpow_of_nonpos hA0 hAt hμ
    linarith [Real.rpow_nonneg hA0.le μ]

/-- Continuity of the (cut-off) Duhamel integrand family in `p = (s, x)` at `(t₀, x₀)`, `t₀ > 0`. -/
theorem sfc_psi_contAt (G : UnforcedLeray.B0220.Profile → UnforcedLeray.B0223.MeridC)
    (ν μ : ℝ) (hν : 0 < ν) {K s0 : ℝ} (hK0 : 0 ≤ K) (hs0 : 0 < s0)
    (hWc : Continuous (fun r : ℝ × (ℝ × ℝ) => sfcW G r.1 r.2))
    (hWb : ∀ σ z, ‖sfcW G σ z‖ ≤ K)
    (hGz : ∀ p : UnforcedLeray.B0220.Profile, p.1 < s0 → G p = 0)
    (t₀ : ℝ) (x₀ : ℝ × ℝ) (ht₀ : 0 < t₀) :
    ContinuousAt (fun p : ℝ × (ℝ × ℝ) => ∫ σ, sfcK G ν μ p σ) (t₀, x₀) := by
  have hA0 : 0 < s0 / (2 * t₀) := div_pos hs0 (by linarith)
  have hApow : 0 ≤ (s0 / (2 * t₀)) ^ μ := Real.rpow_nonneg hA0.le μ
  have hC0 : 0 ≤ (1 + (s0 / (2 * t₀)) ^ μ) * K :=
    mul_nonneg (by linarith) hK0
  have hmem : Ioo (t₀ / 2) (2 * t₀) ∈ 𝓝 t₀ := Ioo_mem_nhds (by linarith) (by linarith)
  have hev : ∀ᶠ p : ℝ × (ℝ × ℝ) in 𝓝 (t₀, x₀), p.1 ∈ Ioo (t₀ / 2) (2 * t₀) :=
    (continuous_fst.tendsto (t₀, x₀)).eventually hmem
  refine continuousAt_of_dominated (bound := fun σ : ℝ =>
      Set.indicator (Set.Ioo 0 (2 * t₀)) (fun _ : ℝ => (1 + (s0 / (2 * t₀)) ^ μ) * K) σ)
    ?_ ?_ ?_ ?_
  · filter_upwards [hev] with p hp
    have hp0 : 0 < p.1 := lt_trans (by linarith) hp.1
    unfold sfcK
    rw [aestronglyMeasurable_indicator_iff measurableSet_Ioo]
    refine ContinuousOn.aestronglyMeasurable (fun σ hσ => ?_) measurableSet_Ioo
    exact (sfc_term_contAt hν hWc hWb hp0 hσ.1 hσ.2 p.2).continuousWithinAt
  · filter_upwards [hev] with p hp
    refine Filter.Eventually.of_forall fun σ => ?_
    have hp0 : 0 < p.1 := lt_trans (by linarith) hp.1
    unfold sfcK
    by_cases hσ : σ ∈ Set.Ioo 0 p.1
    · have hσb : σ ∈ Set.Ioo 0 (2 * t₀) := ⟨hσ.1, lt_trans hσ.2 hp.2⟩
      rw [Set.indicator_of_mem hσ, Set.indicator_of_mem hσb]
      rw [norm_smul]
      by_cases hσs : σ < s0
      · have hz : ∀ z, ‖sfcW G σ z‖ ≤ 0 := fun z => by simp [sfcW, hGz (σ, z) hσs]
        have hph := sfc_planeHeat_norm_le (θ := ν * (p.1 - σ)) hz p.2
        exact le_trans (mul_le_mul_of_nonneg_left hph (norm_nonneg _)) (by rw [mul_zero]; exact hC0)
      · push_neg at hσs
        have hph := sfc_planeHeat_norm_le (θ := ν * (p.1 - σ)) (fun z => hWb σ z) p.2
        have hcoef := sfc_coef_bound (μ := μ) hs0 ht₀ hσ.1 hσ.2 hσs hp.2
        exact mul_le_mul hcoef hph (norm_nonneg _) (by linarith)
    · rw [Set.indicator_of_notMem hσ, norm_zero]
      exact Set.indicator_nonneg (fun _ _ => hC0) σ
  · have hfin : volume (Ioo (0 : ℝ) (2 * t₀)) ≠ ⊤ := by
      rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top
    exact (integrableOn_const hfin).integrable_indicator measurableSet_Ioo
  · filter_upwards [(Set.countable_singleton t₀).ae_notMem volume] with σ hσ
    rcases le_or_gt σ 0 with hσ0 | hσ0
    · have hfun : (fun p : ℝ × (ℝ × ℝ) => sfcK G ν μ p σ) = fun _ => (0 : UnforcedLeray.B0223.MeridC) :=
        funext fun p => by
          unfold sfcK
          exact Set.indicator_of_notMem (fun h => by linarith [h.1]) _
      rw [hfun]
      exact continuousAt_const
    rcases lt_or_gt_of_ne (fun h => hσ (Set.mem_singleton_iff.2 h)) with hlt | hgt
    · have hev2 : ∀ᶠ p : ℝ × (ℝ × ℝ) in 𝓝 (t₀, x₀), σ < p.1 :=
        (continuous_fst.tendsto (t₀, x₀)).eventually (lt_mem_nhds hlt)
      have hEq : (fun p : ℝ × (ℝ × ℝ) => sfcK G ν μ p σ) =ᶠ[𝓝 (t₀, x₀)]
          (fun p : ℝ × (ℝ × ℝ) => (((σ / p.1 : ℝ) : ℂ)) ^ (μ : ℂ) •
            UnforcedLeray.B0224.planeHeat (ν * (p.1 - σ)) (sfcW G σ) p.2) := by
        filter_upwards [hev2] with p hp
        unfold sfcK
        exact Set.indicator_of_mem (show σ ∈ Set.Ioo 0 p.1 from ⟨hσ0, hp⟩) _
      have hc1 : ContinuousAt (fun a : ℝ => ((a : ℝ) : ℂ) ^ (μ : ℂ)) (σ / t₀) :=
        Complex.continuousAt_ofReal_cpow_const (σ / t₀) (μ : ℂ) (Or.inr (div_pos hσ0 ht₀).ne')
      have hc2 : ContinuousAt (fun p : ℝ × (ℝ × ℝ) => σ / p.1) (t₀, x₀) :=
        ContinuousAt.div continuousAt_const
          (continuous_fst.continuousAt : ContinuousAt (fun p : ℝ × (ℝ × ℝ) => p.1) (t₀, x₀))
          ht₀.ne'
      have hcoefC : ContinuousAt (fun p : ℝ × (ℝ × ℝ) => (((σ / p.1 : ℝ) : ℂ)) ^ (μ : ℂ))
          (t₀, x₀) :=
        ContinuousAt.comp (x := (t₀, x₀)) (f := fun p : ℝ × (ℝ × ℝ) => σ / p.1) hc1 hc2
      have hθ : 0 < ν * (t₀ - σ) := mul_pos hν (sub_pos.2 hlt)
      have hcore := sfc_planeHeat_contAt (W := sfcW G) hWc hWb hθ σ x₀
      have hmap : ContinuousAt (fun p : ℝ × (ℝ × ℝ) => (ν * (p.1 - σ), σ, p.2)) (t₀, x₀) := by
        fun_prop
      have hplanC : ContinuousAt (fun p : ℝ × (ℝ × ℝ) =>
          UnforcedLeray.B0224.planeHeat (ν * (p.1 - σ)) (sfcW G σ) p.2) (t₀, x₀) :=
        ContinuousAt.comp (x := (t₀, x₀)) (f := fun p : ℝ × (ℝ × ℝ) => (ν * (p.1 - σ), σ, p.2))
          hcore hmap
      exact (hcoefC.smul hplanC).congr hEq.symm
    · have hlt2 : ∀ᶠ p : ℝ × (ℝ × ℝ) in 𝓝 (t₀, x₀), p.1 < σ :=
        ContinuousAt.eventually_lt continuous_fst.continuousAt continuousAt_const hgt
      have hEq : (fun p : ℝ × (ℝ × ℝ) => sfcK G ν μ p σ) =ᶠ[𝓝 (t₀, x₀)]
          (fun _ : ℝ × (ℝ × ℝ) => (0 : UnforcedLeray.B0223.MeridC)) := by
        filter_upwards [hlt2] with p hp
        unfold sfcK
        exact Set.indicator_of_notMem (fun h => absurd h.2 (not_lt.2 hp.le)) _
      exact continuousAt_const.congr hEq.symm

/-- Pointwise causal heat as the integral of `sfcK` (uses the a.e. identity of `SFCDatumReg`). -/
theorem sfc_causal_eq (c ν μ : ℝ) (hc : 0 < c)
    (f' : UnforcedLeray.B0220.HSpace c UnforcedLeray.B0223.MeridC)
    (G : UnforcedLeray.B0220.Profile → UnforcedLeray.B0223.MeridC) (hν : 0 < ν)
    (hbr : ∀ᵐ σ ∂(volume : Measure ℝ), 0 < σ → ∀ θ : ℝ, 0 < θ →
      UnforcedLeray.B0224.planeHeat θ
          (fun z => UnforcedLeray.B0220.periodize c (sfcGp hc f') (σ, z)) =
        UnforcedLeray.B0224.planeHeat θ (sfcW G σ))
    (p : ℝ × (ℝ × ℝ)) (hp : 0 < p.1) :
    UnforcedLeray.B0225.causalHeat c ν (μ : ℂ) (sfcGp hc f') p = ∫ σ, sfcK G ν μ p σ := by
  unfold UnforcedLeray.B0225.causalHeat
  rw [intervalIntegral.integral_of_le hp.le, integral_Ioc_eq_integral_Ioo]
  have hW : ∫ σ in Set.Ioo 0 p.1, (((σ / p.1 : ℝ) : ℂ)) ^ (μ : ℂ) •
        UnforcedLeray.B0224.planeHeat (ν * (p.1 - σ))
          (fun z => UnforcedLeray.B0220.periodize c (sfcGp hc f') (σ, z)) p.2 =
      ∫ σ in Set.Ioo 0 p.1, (((σ / p.1 : ℝ) : ℂ)) ^ (μ : ℂ) •
        UnforcedLeray.B0224.planeHeat (ν * (p.1 - σ)) (sfcW G σ) p.2 := by
    refine setIntegral_congr_ae measurableSet_Ioo ?_
    filter_upwards [hbr] with σ h1 hσ
    have h2 : UnforcedLeray.B0224.planeHeat (ν * (p.1 - σ))
        (fun z => UnforcedLeray.B0220.periodize c (sfcGp hc f') (σ, z)) =
        UnforcedLeray.B0224.planeHeat (ν * (p.1 - σ)) (sfcW G σ) :=
      h1 hσ.1 (ν * (p.1 - σ)) (mul_pos hν (sub_pos.2 hσ.2))
    rw [h2]
  rw [hW]
  unfold sfcK
  rw [integral_indicator measurableSet_Ioo]

/-- **`SFCCausalHeatCont`** (source 1650-1656, 1684-1689, 3426-3430). -/
theorem sfcCausalHeatCont : SFCCausalHeatCont := by
  intro c ν μ hc R0 g hctx f' hlift i
  obtain ⟨hν, -, -, hsm⟩ := hctx
  obtain ⟨G, hGc, -, ⟨M, hM⟩, ⟨s0, hs0, hGz⟩, hbr⟩ := sfcDatumReg c hc g f' hsm hlift
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM (0, 0, 0))
  have hK0 : 0 ≤ M / s0 := div_nonneg hM0 hs0.le
  have hWc : Continuous (fun r : ℝ × (ℝ × ℝ) => sfcW G r.1 r.2) := sfcW_cont G hGc hs0 hGz
  have hWb : ∀ σ z, ‖sfcW G σ z‖ ≤ M / s0 := fun σ z => sfcW_bound G hM hM0 hs0 hGz σ z
  have hΨ : ContinuousOn (fun p : ℝ × (ℝ × ℝ) => ∫ σ, sfcK G ν μ p σ)
      (Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))) := by
    intro p hp
    exact (sfc_psi_contAt G ν μ hν hK0 hs0 hWc hWb hGz p.1 p.2 hp.1).continuousWithinAt
  have hproj : ContinuousOn (fun p : ℝ × (ℝ × ℝ) =>
      (EuclideanSpace.proj i : UnforcedLeray.B0223.MeridC →L[ℂ] ℂ) (∫ σ, sfcK G ν μ p σ))
      (Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))) :=
    (EuclideanSpace.proj i : UnforcedLeray.B0223.MeridC →L[ℂ] ℂ).continuous.comp_continuousOn hΨ
  refine hproj.congr (fun p hp => ?_)
  rw [sfc_causal_eq c ν μ hc f' G hν hbr p hp.1]
  simp

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
