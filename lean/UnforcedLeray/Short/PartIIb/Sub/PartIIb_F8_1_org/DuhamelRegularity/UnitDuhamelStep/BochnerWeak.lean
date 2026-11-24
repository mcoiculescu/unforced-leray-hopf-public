import UnforcedLeray.Short.PartIIb.Sub.PartIIb_F8_1_org.DuhamelRegularity.UnitDuhamelStep.Propagator
import UnforcedLeray.Short.PartIIb.Tasks.GlobalEnergy.TailSourceSlice.PeriodizeTest
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# `UnitDuhamelStep.BochnerWeak`: Bochner–Duhamel path `WPath`, `D²` path `d2Path`,
`H¹` continuity / initial trace / Duhamel bounds, and forced cell-slice weak equation

Helper module 2 for `PartII-b:F8/1/org/3/1` (`CylUnitDuhamelStep`, SP 2296–2305).
All declarations live inside `UnforcedLeray.Short.IIb.UnitDuhamelStepAux` (R6).
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff InnerProductSpace intervalIntegral

namespace UnforcedLeray.Short.IIb.UnitDuhamelStepAux

open UnforcedLeray.Short.IIb
open UnforcedLeray.Cons.C03.Concrete UnforcedLeray.PhaseSpace UnforcedLeray.B0411

local instance : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨by norm_num⟩
local instance : Fact ((2 : ℝ≥0∞) ≠ ⊤) := ⟨by norm_num⟩

/-! ## 1. Forcing `L¹` bridges and `(t - τ)^{-1/2}` singularity bound -/

lemma continuous_h1RealNorm (c : ℝ) : Continuous (h1RealNorm (c := c)) :=
  ((continuous_norm.comp continuous_fst).add
    (continuous_norm.comp (continuous_fst.comp continuous_snd))).add
      (continuous_norm.comp (continuous_snd.comp continuous_snd))

lemma integrable_h1RealNorm_comp {α : Type*} [MeasurableSpace α] {μ : Measure α} {c : ℝ}
    {F : α → X3 c} (hF : Integrable F μ) :
    Integrable (fun a => h1RealNorm (F a)) μ := by
  refine (hF.norm.const_mul 3).mono'
    ((continuous_h1RealNorm c).comp_aestronglyMeasurable hF.aestronglyMeasurable)
    (Eventually.of_forall fun a => ?_)
  rw [Real.norm_of_nonneg (h1RealNorm_nonneg _)]
  exact h1RealNorm_le_three_norm (F a)

lemma integrable_h1RealNorm_of_forcingPath {c σ : ℝ} {g₁ gq₁ gη₁ : CProf}
    {fp : ℝ → X3 c} (hfp_sm : StronglyMeasurable fp)
    (hfp_supp : ∀ τ ∉ Ioc σ (σ + 1), fp τ = 0)
    (hfp_le : ∀ τ, h1ENN (fp τ) ≤ sliceH1Norm c g₁ gq₁ gη₁ τ)
    (hint_g : ∫⁻ τ in Ioc σ (σ + 1), sliceH1Norm c g₁ gq₁ gη₁ τ < ⊤) :
    Integrable (fun τ => h1RealNorm (fp τ)) volume ∧ Integrable fp volume := by
  have hsm_n : StronglyMeasurable (fun τ => h1RealNorm (fp τ)) :=
    (continuous_h1RealNorm c).comp_stronglyMeasurable hfp_sm
  have hfin : HasFiniteIntegral (fun τ => h1RealNorm (fp τ)) volume := by
    rw [hasFiniteIntegral_iff_enorm]
    have hind : (fun τ : ℝ => ‖h1RealNorm (fp τ)‖ₑ) =
        (Ioc σ (σ + 1)).indicator (fun τ => h1ENN (fp τ)) := by
      funext τ
      by_cases hτ : τ ∈ Ioc σ (σ + 1)
      · rw [indicator_of_mem hτ, h1ENN_eq_ofReal, ← ofReal_norm,
          Real.norm_of_nonneg (h1RealNorm_nonneg _)]
      · rw [indicator_of_notMem hτ, hfp_supp τ hτ, h1RealNorm_zero, enorm_zero]
    rw [hind, lintegral_indicator measurableSet_Ioc]
    exact (lintegral_mono hfp_le).trans_lt hint_g
  have hint_n : Integrable (fun τ => h1RealNorm (fp τ)) volume :=
    ⟨hsm_n.aestronglyMeasurable, hfin⟩
  refine ⟨hint_n, hint_n.mono' hfp_sm.aestronglyMeasurable ?_⟩
  exact Eventually.of_forall fun τ => norm_le_h1RealNorm (fp τ)

lemma ofReal_setIntegral_h1RealNorm_le {c : ℝ} {g₁ gq₁ gη₁ : CProf}
    {fp : ℝ → X3 c} (hint : Integrable (fun τ => h1RealNorm (fp τ)) volume)
    (hfp_le : ∀ τ, h1ENN (fp τ) ≤ sliceH1Norm c g₁ gq₁ gη₁ τ) (S : Set ℝ) :
    ENNReal.ofReal (∫ τ in S, h1RealNorm (fp τ)) ≤
      ∫⁻ τ in S, sliceH1Norm c g₁ gq₁ gη₁ τ := by
  rw [ofReal_integral_eq_lintegral_ofReal hint.restrict
    (Eventually.of_forall fun τ => h1RealNorm_nonneg (fp τ))]
  refine lintegral_mono fun τ => ?_
  rw [← h1ENN_eq_ofReal]
  exact hfp_le τ

/-- Elementary singularity bound `∫_{(τ, b)} (t - τ)^{-1/2} dt ≤ 2` whenever `τ ≤ b ≤ τ + 1`. -/
lemma lintegral_inv_sqrt_Ioo_le_two {τ b : ℝ} (hτb : τ ≤ b) (hb1 : b ≤ τ + 1) :
    ∫⁻ t in Ioo τ b, ENNReal.ofReal ((t - τ) ^ (-1 / 2 : ℝ)) ≤ ENNReal.ofReal 2 := by
  let φ : ℝ → ℝ≥0∞ := fun t => ENNReal.ofReal ((t - τ) ^ (-1 / 2 : ℝ))
  have hφ_meas : Measurable φ :=
    ENNReal.measurable_ofReal.comp ((measurable_id.sub_const τ).pow_const (-1 / 2 : ℝ))
  let a : ℕ → ℝ := fun n => min b (τ + 1 / ((n : ℝ) + 1))
  let g : ℕ → ℝ → ℝ≥0∞ := fun n => (Ioo (a n) b).indicator φ
  have hg_meas : ∀ n, Measurable (g n) := fun n => hφ_meas.indicator measurableSet_Ioo
  have hg_mono : Monotone g := by
    intro n m hnm t
    have hstep : 1 / ((m : ℝ) + 1) ≤ 1 / ((n : ℝ) + 1) := by
      refine one_div_le_one_div_of_le (by positivity) ?_
      exact_mod_cast Nat.succ_le_succ hnm
    have hamn : a m ≤ a n := min_le_min_left b (by linarith)
    exact indicator_le_indicator_of_subset (Ioo_subset_Ioo_left hamn) (fun _ => bot_le) t
  have hg_sup : (fun t => ⨆ n, g n t) = (Ioo τ b).indicator φ := by
    funext t
    by_cases ht : t ∈ Ioo τ b
    · rw [indicator_of_mem ht]
      obtain ⟨N, hN⟩ := exists_nat_one_div_lt (sub_pos.2 ht.1)
      have htN : t ∈ Ioo (a N) b :=
        ⟨(min_le_right b _).trans_lt (by linarith), ht.2⟩
      refine le_antisymm (iSup_le fun n => ?_) ?_
      · by_cases htn : t ∈ Ioo (a n) b <;> simp [g, htn]
      · exact le_trans (by simp [g, htN]) (le_iSup (fun n => g n t) N)
    · rw [indicator_of_notMem ht]
      have hz : ∀ n, g n t = 0 := by
        intro n
        have hτ_le_an : τ ≤ a n := le_min hτb (by linarith [show 0 < 1 / ((n : ℝ) + 1) by positivity])
        exact indicator_of_notMem (fun hm => ht (Ioo_subset_Ioo_left hτ_le_an hm)) _
      simp [hz]
  have hg_int_le : ∀ n, ∫⁻ t, g n t ≤ ENNReal.ofReal 2 := by
    intro n
    dsimp only [g]
    rw [lintegral_indicator measurableSet_Ioo, Measure.restrict_congr_set Ioo_ae_eq_Ioc]
    by_cases han : a n < b
    · have hτ_lt_b : τ < b := by
        by_contra hle
        push Not at hle
        have hb_eq : b = τ := le_antisymm hle hτb
        have hpos_step : 0 < 1 / ((n : ℝ) + 1) := by positivity
        have : a n = τ := by
          dsimp [a]; rw [hb_eq]; exact min_eq_left (by linarith)
        linarith
      have hτ_lt_an : τ < a n := lt_min hτ_lt_b (by linarith [show 0 < 1 / ((n : ℝ) + 1) by positivity])
      let F : ℝ → ℝ := fun t => 2 * (t - τ) ^ (1 / 2 : ℝ)
      let f' : ℝ → ℝ := fun t => (t - τ) ^ (-1 / 2 : ℝ)
      have huIcc : uIcc (a n) b = Icc (a n) b := Set.uIcc_of_le han.le
      have hderiv : ∀ t ∈ uIcc (a n) b, HasDerivAt F (f' t) t := by
        intro t ht
        rw [huIcc] at ht
        have hpos : 0 < t - τ := sub_pos.2 (hτ_lt_an.trans_le ht.1)
        have hd1 := ((Real.hasDerivAt_rpow_const (p := (1 / 2 : ℝ)) (Or.inl hpos.ne')).comp t
          ((hasDerivAt_id t).sub_const τ)).const_mul 2
        have hval : 2 * ((1 / 2 : ℝ) * (t - τ) ^ ((1 / 2 : ℝ) - 1) * 1) = f' t := by
          dsimp [f']
          have hexp : (1 / 2 : ℝ) - 1 = -1 / 2 := by norm_num
          rw [hexp]
          ring
        rwa [hval] at hd1
      have hcont_f' : ContinuousOn f' (Icc (a n) b) :=
        (continuousOn_id.sub continuousOn_const).rpow_const fun t ht =>
          Or.inl (sub_pos.2 (hτ_lt_an.trans_le ht.1)).ne'
      have hint_iv : IntervalIntegrable f' volume (a n) b :=
        hcont_f'.intervalIntegrable_of_Icc han.le
      have hint_on : IntegrableOn f' (Ioc (a n) b) volume :=
        (intervalIntegrable_iff_integrableOn_Ioc_of_le han.le).1 hint_iv
      have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint_iv
      rw [intervalIntegral.integral_of_le han.le] at hftc
      have hnn : 0 ≤ᵐ[volume.restrict (Ioc (a n) b)] f' := by
        rw [Filter.EventuallyLE, ae_restrict_iff' measurableSet_Ioc]
        exact Eventually.of_forall fun t ht =>
          Real.rpow_nonneg (sub_pos.2 (hτ_lt_an.trans ht.1)).le _
      have heq_of : ∫⁻ t in Ioc (a n) b, φ t = ENNReal.ofReal (∫ t in Ioc (a n) b, f' t) :=
        (ofReal_integral_eq_lintegral_ofReal hint_on hnn).symm
      rw [heq_of, hftc]
      refine ENNReal.ofReal_le_ofReal ?_
      have hb_rpow : (b - τ) ^ (1 / 2 : ℝ) ≤ 1 := by
        have := Real.rpow_le_rpow (sub_nonneg.2 hτb) (by linarith : b - τ ≤ 1)
          (by norm_num : (0 : ℝ) ≤ 1 / 2)
        simpa using this
      have han_nn : 0 ≤ (a n - τ) ^ (1 / 2 : ℝ) :=
        Real.rpow_nonneg (sub_pos.2 hτ_lt_an).le _
      dsimp [F]
      linarith
    · push Not at han
      rw [Ioc_eq_empty (not_lt.2 han)]
      simp
  rw [← lintegral_indicator measurableSet_Ioo, ← hg_sup, lintegral_iSup hg_meas hg_mono]
  exact iSup_le hg_int_le

/-! ## 2. Duhamel paths `WPath` and `d2Path`: `H¹` regularity, continuity, trace, and `D²` bounds -/

open Classical in
/-- Unit-window Bochner–Duhamel `X3`-path on `Ioo σ (σ + 1)` (`0` outside). -/
def WPath {A : ℝ} {p : Params} (hflow : F8U.CylOseenFlowBound A p)
    (σ : ℝ) (x0 : X3 p.c) (fp : ℝ → X3 p.c) (t : ℝ) : X3 p.c :=
  if t ∈ Ioo σ (σ + 1) then
    S0Val hflow t σ x0 + ∫ τ, K0 hflow σ fp (t, τ)
  else 0

open Classical in
/-- Unit-window Bochner–Duhamel second-derivative `L2Cell`-path on `Ioo σ (σ + 1)` (`0` outside). -/
def d2Path {A : ℝ} {p : Params} (hflow : F8U.CylOseenFlowBound A p)
    (σ : ℝ) (x0 : X3 p.c) (fp : ℝ → X3 p.c) (i j : Fin 2) (t : ℝ) : L2Cell p.c :=
  if t ∈ Ioo σ (σ + 1) then
    SD2Val hflow i j t σ x0 + ∫ τ, KD2 hflow σ fp i j (t, τ)
  else 0

lemma K0_h1RealNorm_le {A : ℝ} (hA : 0 < A) {p : Params}
    (hflow : F8U.CylOseenFlowBound A p) {σ : ℝ} (hσ : 0 ≤ σ)
    {fp : ℝ → X3 p.c} (hfp_mem : ∀ τ, fp τ ∈ H1Set p.c) (t τ : ℝ) :
    h1RealNorm (K0 hflow σ fp (t, τ)) ≤ A * h1RealNorm (fp τ) := by
  dsimp [K0]
  by_cases hq : (t, τ) ∈ unitTriangle σ
  · rw [indicator_of_mem hq]
    exact (S0Val_and_SD2Val_bounds hA p.ν_pos hflow (by linarith [hq.1])
      ⟨hq.2.1, by linarith [hq.1, hq.2.2]⟩ (hfp_mem τ)).2.1
  · rw [indicator_of_notMem hq, h1RealNorm_zero]
    exact mul_nonneg hA.le (h1RealNorm_nonneg _)

lemma integrable_K0_slice_and_prod {dm dp : ℝ} {p : Params} {d A σ : ℝ}
    (hA : 0 < A) (hreg : BgRegime p d dm dp) (hflow : F8U.CylOseenFlowBound A p) (hσ : 0 ≤ σ)
    {fp : ℝ → X3 p.c} (hfp_sm : StronglyMeasurable fp) (hfp_mem : ∀ τ, fp τ ∈ H1Set p.c)
    (hfp_int : Integrable (fun τ => h1RealNorm (fp τ)) volume) :
    (∀ t : ℝ, Integrable (fun τ => K0 hflow σ fp (t, τ)) volume) ∧
      Integrable (K0 hflow σ fp) (volume.prod volume) := by
  have hK0_sm := (stronglyMeasurable_K0_and_KD2 hA hreg hflow hσ hfp_sm hfp_mem).1
  refine ⟨fun t => ?_, ?_⟩
  · have hsm_t : StronglyMeasurable (fun τ => K0 hflow σ fp (t, τ)) :=
      hK0_sm.comp_measurable (measurable_const.prodMk measurable_id)
    refine (hfp_int.const_mul A).mono' hsm_t.aestronglyMeasurable ?_
    exact Eventually.of_forall fun τ =>
      (norm_le_h1RealNorm _).trans (K0_h1RealNorm_le hA hflow hσ hfp_mem t τ)
  · let g1 : ℝ → ℝ := (Ioo σ (σ + 1)).indicator fun _ => (1 : ℝ)
    have hg1 : Integrable g1 volume := by
      refine (integrable_indicator_iff measurableSet_Ioo).2 ?_
      exact integrableOn_const (by rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top)
    have hprod : Integrable (fun q : ℝ × ℝ => g1 q.1 * (A * h1RealNorm (fp q.2)))
        (volume.prod volume) := hg1.mul_prod (hfp_int.const_mul A)
    refine hprod.mono' hK0_sm.aestronglyMeasurable (Eventually.of_forall fun q => ?_)
    by_cases hq : q ∈ unitTriangle σ
    · have ht : q.1 ∈ Ioo σ (σ + 1) := ⟨hq.1.trans hq.2.1, hq.2.2⟩
      simp only [g1, indicator_of_mem ht, one_mul]
      exact (norm_le_h1RealNorm _).trans (K0_h1RealNorm_le hA hflow hσ hfp_mem q.1 q.2)
    · dsimp [K0, g1]
      rw [indicator_of_notMem hq, norm_zero]
      exact mul_nonneg (indicator_nonneg (fun _ _ => zero_le_one) _)
        (mul_nonneg hA.le (h1RealNorm_nonneg _))

lemma stronglyMeasurable_WPath {dm dp : ℝ} {p : Params} {d A σ : ℝ}
    (hA : 0 < A) (hreg : BgRegime p d dm dp) (hflow : F8U.CylOseenFlowBound A p) (hσ : 0 ≤ σ)
    {x0 : X3 p.c} (hx0 : x0 ∈ H1Set p.c)
    {fp : ℝ → X3 p.c} (hfp_sm : StronglyMeasurable fp) (hfp_mem : ∀ τ, fp τ ∈ H1Set p.c) :
    StronglyMeasurable (WPath hflow σ x0 fp) := by
  have hK0_sm := (stronglyMeasurable_K0_and_KD2 hA hreg hflow hσ hfp_sm hfp_mem).1
  have h1 : StronglyMeasurable ((Ioo σ (σ + 1)).indicator fun t => S0Val hflow t σ x0) :=
    UnforcedLeray.Infra.JointMeasurableRep.stronglyMeasurable_indicator_of_continuousOn
      ((continuousOn_S0Val_and_SD2Val_left hflow hσ hx0).1.mono
        (fun t ht => ⟨ht.1, by linarith [ht.2]⟩))
      measurableSet_Ioo
  have h2 : StronglyMeasurable ((Ioo σ (σ + 1)).indicator fun t => ∫ τ, K0 hflow σ fp (t, τ)) :=
    hK0_sm.integral_prod_right'.indicator measurableSet_Ioo
  have heq : WPath hflow σ x0 fp = fun t =>
      (Ioo σ (σ + 1)).indicator (fun s => S0Val hflow s σ x0) t +
      (Ioo σ (σ + 1)).indicator (fun s => ∫ τ, K0 hflow σ fp (s, τ)) t := by
    funext t
    by_cases ht : t ∈ Ioo σ (σ + 1) <;> simp [WPath, ht]
  rw [heq]
  exact h1.add h2

lemma WPath_mem_H1Set_and_bound {dm dp : ℝ} {p : Params} {d A σ : ℝ}
    (hA : 0 < A) (hreg : BgRegime p d dm dp) (hflow : F8U.CylOseenFlowBound A p) (hσ : 0 ≤ σ)
    {u₀ uq₀ uη₀ : B0579.Plane → CMerid} (hu₀ : F8U.IsCylH1Datum p.c u₀ uq₀ uη₀)
    {g₁ gq₁ gη₁ : CProf}
    {fp : ℝ → X3 p.c} (hfp_sm : StronglyMeasurable fp) (hfp_mem : ∀ τ, fp τ ∈ H1Set p.c)
    (hfp_le : ∀ τ, h1ENN (fp τ) ≤ sliceH1Norm p.c g₁ gq₁ gη₁ τ)
    (hfp_int : Integrable (fun τ => h1RealNorm (fp τ)) volume)
    {t : ℝ} (ht : t ∈ Ioo σ (σ + 1)) :
    WPath hflow σ (datumToX3 hu₀) fp t ∈ H1Set p.c ∧
      h1ENN (WPath hflow σ (datumToX3 hu₀) fp t) ≤
        ENNReal.ofReal A *
          (F8U.cylH1 p.c u₀ uq₀ uη₀ + ∫⁻ τ in Ioc σ t, sliceH1Norm p.c g₁ gq₁ gη₁ τ) := by
  let x0 := datumToX3 hu₀
  have hx0 : x0 ∈ H1Set p.c := datumToX3_mem_H1Set hu₀
  have hint_t := (integrable_K0_slice_and_prod hA hreg hflow hσ hfp_sm hfp_mem hfp_int).1 t
  have hK_mem : ∀ τ, K0 hflow σ fp (t, τ) ∈ H1Set p.c := by
    intro τ
    dsimp [K0]
    by_cases hq : (t, τ) ∈ unitTriangle σ
    · rw [indicator_of_mem hq]
      exact S0Val_mem_H1Set p.c_pos hflow t τ (fp τ)
    · rw [indicator_of_notMem hq]
      exact zero_mem_H1Set p.c
  have hW_eq : WPath hflow σ x0 fp t = S0Val hflow t σ x0 + ∫ τ, K0 hflow σ fp (t, τ) := by
    simp [WPath, ht]
  rw [hW_eq]
  refine ⟨add_mem_H1Set (S0Val_mem_H1Set p.c_pos hflow t σ x0)
    (integral_mem_H1Set p.c_pos hint_t (Eventually.of_forall hK_mem)), ?_⟩
  have hcompl0 : ∀ τ ∉ Ioc σ t, K0 hflow σ fp (t, τ) = 0 := by
    intro τ hτ
    exact indicator_of_notMem (fun hq => hτ ⟨hq.1, hq.2.1.le⟩) _
  have hint_eq : ∫ τ, K0 hflow σ fp (t, τ) = ∫ τ in Ioc σ t, K0 hflow σ fp (t, τ) :=
    (setIntegral_eq_integral_of_forall_compl_eq_zero hcompl0).symm
  have hb0 := (S0Val_and_SD2Val_bounds hA p.ν_pos hflow hσ ⟨ht.1, ht.2.le⟩ hx0).2.1
  have hb_int : h1RealNorm (∫ τ, K0 hflow σ fp (t, τ)) ≤
      A * ∫ τ in Ioc σ t, h1RealNorm (fp τ) := by
    rw [hint_eq]
    calc h1RealNorm (∫ τ in Ioc σ t, K0 hflow σ fp (t, τ))
        ≤ ∫ τ in Ioc σ t, h1RealNorm (K0 hflow σ fp (t, τ)) :=
          h1RealNorm_integral_le hint_t.restrict
      _ ≤ ∫ τ in Ioc σ t, A * h1RealNorm (fp τ) :=
          integral_mono (integrable_h1RealNorm_comp hint_t.restrict)
            (hfp_int.const_mul A).restrict
            (fun τ => K0_h1RealNorm_le hA hflow hσ hfp_mem t τ)
      _ = A * ∫ τ in Ioc σ t, h1RealNorm (fp τ) := integral_const_mul A _
  have htot_real : h1RealNorm (S0Val hflow t σ x0 + ∫ τ, K0 hflow σ fp (t, τ)) ≤
      A * (h1RealNorm x0 + ∫ τ in Ioc σ t, h1RealNorm (fp τ)) := by
    have := h1RealNorm_add_le (S0Val hflow t σ x0) (∫ τ, K0 hflow σ fp (t, τ))
    linarith
  have hint_nn : 0 ≤ ∫ τ in Ioc σ t, h1RealNorm (fp τ) :=
    integral_nonneg fun τ => h1RealNorm_nonneg _
  rw [h1ENN_eq_ofReal]
  calc ENNReal.ofReal (h1RealNorm (S0Val hflow t σ x0 + ∫ τ, K0 hflow σ fp (t, τ)))
      ≤ ENNReal.ofReal (A * (h1RealNorm x0 + ∫ τ in Ioc σ t, h1RealNorm (fp τ))) :=
        ENNReal.ofReal_le_ofReal htot_real
    _ = ENNReal.ofReal A *
          (ENNReal.ofReal (h1RealNorm x0) +
            ENNReal.ofReal (∫ τ in Ioc σ t, h1RealNorm (fp τ))) := by
        rw [ENNReal.ofReal_mul hA.le, ENNReal.ofReal_add (h1RealNorm_nonneg x0) hint_nn]
    _ ≤ ENNReal.ofReal A *
          (F8U.cylH1 p.c u₀ uq₀ uη₀ + ∫⁻ τ in Ioc σ t, sliceH1Norm p.c g₁ gq₁ gη₁ τ) := by
        gcongr
        · rw [← h1ENN_eq_ofReal, h1ENN_datumToX3]
        · exact ofReal_setIntegral_h1RealNorm_le hfp_int hfp_le (Ioc σ t)

lemma tendsto_WPath_interior {dm dp : ℝ} {p : Params} {d A σ : ℝ}
    (hA : 0 < A) (hreg : BgRegime p d dm dp) (hflow : F8U.CylOseenFlowBound A p) (hσ : 0 ≤ σ)
    {x0 : X3 p.c} (hx0 : x0 ∈ H1Set p.c)
    {fp : ℝ → X3 p.c} (hfp_sm : StronglyMeasurable fp) (hfp_mem : ∀ τ, fp τ ∈ H1Set p.c)
    (hfp_int : Integrable (fun τ => h1RealNorm (fp τ)) volume)
    {t₀ : ℝ} (ht₀ : t₀ ∈ Ioo σ (σ + 1)) :
    Tendsto (fun t => h1RealNorm (WPath hflow σ x0 fp t - WPath hflow σ x0 fp t₀))
      (𝓝 t₀) (𝓝 0) := by
  have hint_slice := (integrable_K0_slice_and_prod hA hreg hflow hσ hfp_sm hfp_mem hfp_int).1
  have ht₀2 : t₀ ∈ Ioo σ (σ + 2) := ⟨ht₀.1, by linarith [ht₀.2]⟩
  have h1_lim : Tendsto (fun t => h1RealNorm (S0Val hflow t σ x0 - S0Val hflow t₀ σ x0))
      (𝓝 t₀) (𝓝 0) := by
    have hc_at : ContinuousAt (fun t => S0Val hflow t σ x0) t₀ :=
      (continuousOn_S0Val_and_SD2Val_left hflow hσ hx0).1.continuousAt
        (isOpen_Ioo.mem_nhds ht₀2)
    have hn_lim := tendsto_iff_norm_sub_tendsto_zero.1 hc_at
    have h3 : Tendsto (fun t => 3 * ‖S0Val hflow t σ x0 - S0Val hflow t₀ σ x0‖)
        (𝓝 t₀) (𝓝 0) := by simpa using hn_lim.const_mul 3
    exact squeeze_zero (fun _ => h1RealNorm_nonneg _)
      (fun _ => h1RealNorm_le_three_norm _) h3
  have h2_lim : Tendsto
      (fun t => ∫ τ, h1RealNorm (K0 hflow σ fp (t, τ) - K0 hflow σ fp (t₀, τ)))
      (𝓝 t₀) (𝓝 0) := by
    have h0 : (0 : ℝ) = ∫ _ : ℝ, (0 : ℝ) := by simp
    rw [h0]
    refine tendsto_integral_filter_of_dominated_convergence
      (fun τ => 2 * A * h1RealNorm (fp τ))
      (Eventually.of_forall fun t =>
        (integrable_h1RealNorm_comp ((hint_slice t).sub (hint_slice t₀))).aestronglyMeasurable)
      (Eventually.of_forall fun t => Eventually.of_forall fun τ => ?_)
      (hfp_int.const_mul (2 * A)) ?_
    · rw [Real.norm_of_nonneg (h1RealNorm_nonneg _)]
      have hsub := h1RealNorm_sub_le (K0 hflow σ fp (t, τ)) (K0 hflow σ fp (t₀, τ))
      have b1 := K0_h1RealNorm_le hA hflow hσ hfp_mem t τ
      have b2 := K0_h1RealNorm_le hA hflow hσ hfp_mem t₀ τ
      linarith
    · filter_upwards [compl_mem_ae_iff.2 (measure_singleton t₀)] with τ hne
      have hne' : τ ≠ t₀ := hne
      by_cases hστ : σ < τ
      · rcases lt_or_gt_of_ne hne' with hlt | hgt
        · have ht₀_in : t₀ ∈ Ioo τ (σ + 1) := ⟨hlt, ht₀.2⟩
          have ht₀_in2 : t₀ ∈ Ioo τ (τ + 2) := ⟨hlt, by linarith [ht₀.2, hστ]⟩
          have hc_at : ContinuousAt (fun t => S0Val hflow t τ (fp τ)) t₀ :=
            (continuousOn_S0Val_and_SD2Val_left hflow (by linarith) (hfp_mem τ)).1.continuousAt
              (isOpen_Ioo.mem_nhds ht₀_in2)
          have h3 : Tendsto
              (fun t => 3 * ‖S0Val hflow t τ (fp τ) - S0Val hflow t₀ τ (fp τ)‖)
              (𝓝 t₀) (𝓝 0) := by
            simpa using (tendsto_iff_norm_sub_tendsto_zero.1 hc_at).const_mul 3
          refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h3
            (Eventually.of_forall fun _ => h1RealNorm_nonneg _) ?_
          filter_upwards [isOpen_Ioo.mem_nhds ht₀_in] with t ht
          have hqt : (t, τ) ∈ unitTriangle σ := ⟨hστ, ht.1, ht.2⟩
          have hqt₀ : (t₀, τ) ∈ unitTriangle σ := ⟨hστ, hlt, ht₀.2⟩
          dsimp only [K0]
          rw [indicator_of_mem hqt, indicator_of_mem hqt₀]
          exact h1RealNorm_le_three_norm _
        · refine tendsto_const_nhds.congr' ?_
          filter_upwards [(isOpen_lt continuous_id continuous_const).mem_nhds hgt] with t ht
          have hnt : (t, τ) ∉ unitTriangle σ := fun h => not_lt_of_ge ht.le h.2.1
          have hnt₀ : (t₀, τ) ∉ unitTriangle σ := fun h => not_lt_of_ge hgt.le h.2.1
          dsimp only [K0]
          rw [indicator_of_notMem hnt, indicator_of_notMem hnt₀, sub_self, h1RealNorm_zero]
      · refine tendsto_const_nhds.congr' ?_
        filter_upwards with t
        have hnt : (t, τ) ∉ unitTriangle σ := fun h => hστ h.1
        have hnt₀ : (t₀, τ) ∉ unitTriangle σ := fun h => hστ h.1
        dsimp only [K0]
        rw [indicator_of_notMem hnt, indicator_of_notMem hnt₀, sub_self, h1RealNorm_zero]
  have hsum : Tendsto (fun t =>
      h1RealNorm (S0Val hflow t σ x0 - S0Val hflow t₀ σ x0) +
      ∫ τ, h1RealNorm (K0 hflow σ fp (t, τ) - K0 hflow σ fp (t₀, τ))) (𝓝 t₀) (𝓝 0) := by
    simpa using h1_lim.add h2_lim
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hsum
    (Eventually.of_forall fun _ => h1RealNorm_nonneg _) ?_
  filter_upwards [isOpen_Ioo.mem_nhds ht₀] with t ht
  simp only [WPath, ht, ht₀, ↓reduceIte]
  have hrew : (S0Val hflow t σ x0 + ∫ τ, K0 hflow σ fp (t, τ)) -
        (S0Val hflow t₀ σ x0 + ∫ τ, K0 hflow σ fp (t₀, τ)) =
      (S0Val hflow t σ x0 - S0Val hflow t₀ σ x0) +
        ∫ τ, (K0 hflow σ fp (t, τ) - K0 hflow σ fp (t₀, τ)) := by
    rw [integral_sub (hint_slice t) (hint_slice t₀)]
    abel
  rw [hrew]
  exact (h1RealNorm_add_le _ _).trans
    (add_le_add le_rfl (h1RealNorm_integral_le ((hint_slice t).sub (hint_slice t₀))))

lemma tendsto_WPath_initial {dm dp : ℝ} {p : Params} {d A σ : ℝ}
    (hA : 0 < A) (hreg : BgRegime p d dm dp) (hflow : F8U.CylOseenFlowBound A p) (hσ : 0 ≤ σ)
    {x0 : X3 p.c} (hx0 : x0 ∈ H1Set p.c)
    {fp : ℝ → X3 p.c} (hfp_sm : StronglyMeasurable fp) (hfp_mem : ∀ τ, fp τ ∈ H1Set p.c)
    (hfp_int : Integrable (fun τ => h1RealNorm (fp τ)) volume) :
    Tendsto (fun t => h1RealNorm (WPath hflow σ x0 fp t - x0)) (𝓝[>] σ) (𝓝 0) := by
  have hint_slice := (integrable_K0_slice_and_prod hA hreg hflow hσ hfp_sm hfp_mem hfp_int).1
  have h1_lim := (tendsto_S0Val_initial hflow hσ hx0).1
  let F : ℝ → ℝ → ℝ := fun t τ => (Ioo σ t).indicator (fun r => A * h1RealNorm (fp r)) τ
  have h2_lim : Tendsto (fun t => ∫ τ, F t τ) (𝓝[>] σ) (𝓝 0) := by
    have h0 : (0 : ℝ) = ∫ _ : ℝ, (0 : ℝ) := by simp
    rw [h0]
    refine tendsto_integral_filter_of_dominated_convergence
      (fun τ => A * h1RealNorm (fp τ))
      (Eventually.of_forall fun t =>
        ((hfp_int.const_mul A).indicator measurableSet_Ioo).aestronglyMeasurable)
      (Eventually.of_forall fun t => Eventually.of_forall fun τ => ?_)
      (hfp_int.const_mul A)
      (Eventually.of_forall fun τ => ?_)
    · by_cases hτ : τ ∈ Ioo σ t
      · have hnn : 0 ≤ A * h1RealNorm (fp τ) := mul_nonneg hA.le (h1RealNorm_nonneg _)
        dsimp only [F]
        rw [indicator_of_mem hτ, Real.norm_of_nonneg hnn]
      · dsimp only [F]
        rw [indicator_of_notMem hτ, norm_zero]
        exact mul_nonneg hA.le (h1RealNorm_nonneg _)
    · by_cases hστ : σ < τ
      · refine tendsto_const_nhds.congr' ?_
        filter_upwards [Ioo_mem_nhdsGT hστ] with t ht
        exact (indicator_of_notMem (fun hm => not_lt_of_ge ht.2.le hm.2) _).symm
      · refine tendsto_const_nhds.congr' ?_
        filter_upwards with t
        exact (indicator_of_notMem (fun hm => hστ hm.1) _).symm
  have hsum : Tendsto (fun t => h1RealNorm (S0Val hflow t σ x0 - x0) + ∫ τ, F t τ)
      (𝓝[>] σ) (𝓝 0) := by
    simpa using h1_lim.add h2_lim
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hsum
    (Eventually.of_forall fun _ => h1RealNorm_nonneg _) ?_
  filter_upwards [Ioo_mem_nhdsGT (by linarith : σ < σ + 1)] with t ht
  simp only [WPath, ht, ↓reduceIte]
  have hrew : S0Val hflow t σ x0 + (∫ τ, K0 hflow σ fp (t, τ)) - x0 =
      (S0Val hflow t σ x0 - x0) + ∫ τ, K0 hflow σ fp (t, τ) := by abel
  rw [hrew]
  refine (h1RealNorm_add_le _ _).trans (add_le_add le_rfl ?_)
  refine (h1RealNorm_integral_le (hint_slice t)).trans ?_
  refine integral_mono (integrable_h1RealNorm_comp (hint_slice t))
    ((hfp_int.const_mul A).indicator measurableSet_Ioo) fun τ => ?_
  dsimp [F]
  by_cases hτ : τ ∈ Ioo σ t
  · rw [indicator_of_mem hτ]
    exact K0_h1RealNorm_le hA hflow hσ hfp_mem t τ
  · have hq : (t, τ) ∉ unitTriangle σ := fun h => hτ ⟨h.1, h.2.1⟩
    dsimp [K0]
    rw [indicator_of_notMem hq, indicator_of_notMem hτ, h1RealNorm_zero]

/-- Scalar parabolic majorant on `unitTriangle σ` for `∑_{i,j} ‖KD2 i j‖`. -/
def majD2 (A : ℝ) (p : Params) (σ : ℝ) (fp : ℝ → X3 p.c) : ℝ × ℝ → ℝ :=
  (unitTriangle σ).indicator fun q : ℝ × ℝ =>
    A * p.ν ^ (-1 / 2 : ℝ) * (q.1 - q.2) ^ (-1 / 2 : ℝ) * h1RealNorm (fp q.2)

lemma majD2_nonneg {A : ℝ} (hA : 0 < A) (p : Params) (σ : ℝ)
    (fp : ℝ → X3 p.c) (q : ℝ × ℝ) :
    0 ≤ majD2 A p σ fp q := by
  dsimp [majD2]
  by_cases hq : q ∈ unitTriangle σ
  · rw [indicator_of_mem hq]
    exact mul_nonneg
      (mul_nonneg (mul_nonneg hA.le (Real.rpow_nonneg p.ν_pos.le _))
        (Real.rpow_nonneg (sub_pos.2 hq.2.1).le _))
      (h1RealNorm_nonneg _)
  · rw [indicator_of_notMem hq]

lemma sum_norm_KD2_le_majD2 {A : ℝ} (hA : 0 < A) {p : Params}
    (hflow : F8U.CylOseenFlowBound A p) {σ : ℝ} (hσ : 0 ≤ σ)
    {fp : ℝ → X3 p.c} (hfp_mem : ∀ τ, fp τ ∈ H1Set p.c) (q : ℝ × ℝ) :
    (∑ i : Fin 2, ∑ j : Fin 2, ‖KD2 hflow σ fp i j q‖) ≤ majD2 A p σ fp q := by
  dsimp [KD2, majD2]
  by_cases hq : q ∈ unitTriangle σ
  · simp_rw [indicator_of_mem hq]
    exact (S0Val_and_SD2Val_bounds hA p.ν_pos hflow (by linarith [hq.1])
      ⟨hq.2.1, by linarith [hq.1, hq.2.2]⟩ (hfp_mem q.2)).2.2.2
  · simp [hq]

lemma norm_KD2_le_majD2 {A : ℝ} (hA : 0 < A) {p : Params}
    (hflow : F8U.CylOseenFlowBound A p) {σ : ℝ} (hσ : 0 ≤ σ)
    {fp : ℝ → X3 p.c} (hfp_mem : ∀ τ, fp τ ∈ H1Set p.c)
    (i j : Fin 2) (q : ℝ × ℝ) :
    ‖KD2 hflow σ fp i j q‖ ≤ majD2 A p σ fp q := by
  refine le_trans ?_ (sum_norm_KD2_le_majD2 hA hflow hσ hfp_mem q)
  simp only [Fin.sum_univ_two]
  fin_cases i <;> fin_cases j <;> dsimp <;>
    linarith [norm_nonneg (KD2 hflow σ fp 0 0 q), norm_nonneg (KD2 hflow σ fp 0 1 q),
      norm_nonneg (KD2 hflow σ fp 1 0 q), norm_nonneg (KD2 hflow σ fp 1 1 q)]

lemma integrable_majD2_and_KD2 {dm dp : ℝ} {p : Params} {d A σ : ℝ}
    (hA : 0 < A) (hreg : BgRegime p d dm dp) (hflow : F8U.CylOseenFlowBound A p) (hσ : 0 ≤ σ)
    {fp : ℝ → X3 p.c} (hfp_sm : StronglyMeasurable fp) (hfp_mem : ∀ τ, fp τ ∈ H1Set p.c)
    (hfp_int : Integrable (fun τ => h1RealNorm (fp τ)) volume) :
    StronglyMeasurable (majD2 A p σ fp) ∧
      Integrable (majD2 A p σ fp) (volume.prod volume) ∧
      ∀ i j : Fin 2, Integrable (KD2 hflow σ fp i j) (volume.prod volume) := by
  have hker_cont : ContinuousOn
      (fun q : ℝ × ℝ => A * p.ν ^ (-1 / 2 : ℝ) * (q.1 - q.2) ^ (-1 / 2 : ℝ))
      (unitTriangle σ) :=
    continuousOn_const.mul ((continuousOn_fst.sub continuousOn_snd).rpow_const
      fun q hq => Or.inl (sub_pos.2 hq.2.1).ne')
  have hker_sm : StronglyMeasurable ((unitTriangle σ).indicator
      fun q : ℝ × ℝ => A * p.ν ^ (-1 / 2 : ℝ) * (q.1 - q.2) ^ (-1 / 2 : ℝ)) :=
    UnforcedLeray.Infra.JointMeasurableRep.stronglyMeasurable_indicator_of_continuousOn
      hker_cont (measurableSet_unitTriangle σ)
  have hn_sm : StronglyMeasurable (fun q : ℝ × ℝ => h1RealNorm (fp q.2)) :=
    ((continuous_h1RealNorm p.c).comp_stronglyMeasurable hfp_sm).comp_measurable measurable_snd
  have hmaj_eq : majD2 A p σ fp = fun q : ℝ × ℝ =>
      ((unitTriangle σ).indicator
        (fun r : ℝ × ℝ => A * p.ν ^ (-1 / 2 : ℝ) * (r.1 - r.2) ^ (-1 / 2 : ℝ)) q) *
        h1RealNorm (fp q.2) := by
    funext q
    by_cases hq : q ∈ unitTriangle σ <;> simp [majD2, hq]
  have hmaj_sm : StronglyMeasurable (majD2 A p σ fp) := by
    rw [hmaj_eq]; exact hker_sm.mul hn_sm
  have hmaj_fin : HasFiniteIntegral (majD2 A p σ fp) (volume.prod volume) := by
    rw [hasFiniteIntegral_iff_enorm]
    have hton := lintegral_prod_symm (μ := volume) (ν := volume)
      (fun q : ℝ × ℝ => ‖majD2 A p σ fp q‖ₑ) hmaj_sm.enorm.aemeasurable
    rw [hton]
    let C : ℝ := A * p.ν ^ (-1 / 2 : ℝ)
    have hC_nn : 0 ≤ C := mul_nonneg hA.le (Real.rpow_nonneg p.ν_pos.le _)
    have hinner : ∀ τ : ℝ, (∫⁻ t : ℝ, ‖majD2 A p σ fp (t, τ)‖ₑ) ≤
        ENNReal.ofReal (2 * C) * ENNReal.ofReal (h1RealNorm (fp τ)) := by
      intro τ
      by_cases hτ : τ ∈ Ioo σ (σ + 1)
      · have hind : (fun t : ℝ => ‖majD2 A p σ fp (t, τ)‖ₑ) =
            (Ioo τ (σ + 1)).indicator fun t =>
              (ENNReal.ofReal C * ENNReal.ofReal (h1RealNorm (fp τ))) *
                ENNReal.ofReal ((t - τ) ^ (-1 / 2 : ℝ)) := by
          funext t
          by_cases ht : t ∈ Ioo τ (σ + 1)
          · have hq : (t, τ) ∈ unitTriangle σ := ⟨hτ.1, ht.1, ht.2⟩
            rw [indicator_of_mem ht, ← ofReal_norm,
              Real.norm_of_nonneg (majD2_nonneg hA p σ fp (t, τ))]
            dsimp [majD2, C]
            rw [indicator_of_mem hq,
              ENNReal.ofReal_mul (mul_nonneg hC_nn (Real.rpow_nonneg (sub_pos.2 ht.1).le _)),
              ENNReal.ofReal_mul hC_nn]
            ring
          · have hq : (t, τ) ∉ unitTriangle σ := fun h => ht ⟨h.2.1, h.2.2⟩
            simp [majD2, ht, hq]
        rw [hind, lintegral_indicator measurableSet_Ioo,
          lintegral_const_mul' _ _ (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)]
        calc (ENNReal.ofReal C * ENNReal.ofReal (h1RealNorm (fp τ))) *
              (∫⁻ t in Ioo τ (σ + 1), ENNReal.ofReal ((t - τ) ^ (-1 / 2 : ℝ)))
            ≤ (ENNReal.ofReal C * ENNReal.ofReal (h1RealNorm (fp τ))) * ENNReal.ofReal 2 :=
              mul_le_mul_right (lintegral_inv_sqrt_Ioo_le_two hτ.2.le (by linarith [hτ.1])) _
          _ = ENNReal.ofReal (2 * C) * ENNReal.ofReal (h1RealNorm (fp τ)) := by
              rw [ENNReal.ofReal_mul zero_le_two]
              ring
      · have hz : (fun t : ℝ => ‖majD2 A p σ fp (t, τ)‖ₑ) = fun _ => 0 := by
          funext t
          have hq : (t, τ) ∉ unitTriangle σ := fun h => hτ ⟨h.1, h.2.1.trans h.2.2⟩
          simp [majD2, hq]
        simp [hz]
    have hfp_fin : (∫⁻ τ : ℝ, ENNReal.ofReal (h1RealNorm (fp τ))) < ⊤ := by
      have := hfp_int.2
      rw [hasFiniteIntegral_iff_enorm] at this
      refine (lintegral_mono fun τ => ?_).trans_lt this
      rw [← ofReal_norm, Real.norm_of_nonneg (h1RealNorm_nonneg _)]
    calc (∫⁻ τ : ℝ, ∫⁻ t : ℝ, ‖majD2 A p σ fp (t, τ)‖ₑ)
        ≤ ∫⁻ τ : ℝ, ENNReal.ofReal (2 * C) * ENNReal.ofReal (h1RealNorm (fp τ)) :=
          lintegral_mono hinner
      _ = ENNReal.ofReal (2 * C) * ∫⁻ τ : ℝ, ENNReal.ofReal (h1RealNorm (fp τ)) :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hfp_fin
  have hmaj_int : Integrable (majD2 A p σ fp) (volume.prod volume) :=
    ⟨hmaj_sm.aestronglyMeasurable, hmaj_fin⟩
  have hKD2_sm := (stronglyMeasurable_K0_and_KD2 hA hreg hflow hσ hfp_sm hfp_mem).2
  refine ⟨hmaj_sm, hmaj_int, fun i j => ?_⟩
  exact hmaj_int.mono' (hKD2_sm i j).aestronglyMeasurable
    (Eventually.of_forall fun q => norm_KD2_le_majD2 hA hflow hσ hfp_mem i j q)

lemma stronglyMeasurable_and_locL1_d2Path {dm dp : ℝ} {p : Params} {d A σ : ℝ}
    (hA : 0 < A) (hreg : BgRegime p d dm dp) (hflow : F8U.CylOseenFlowBound A p) (hσ : 0 ≤ σ)
    {x0 : X3 p.c} (hx0 : x0 ∈ H1Set p.c)
    {fp : ℝ → X3 p.c} (hfp_sm : StronglyMeasurable fp) (hfp_mem : ∀ τ, fp τ ∈ H1Set p.c)
    (hfp_int : Integrable (fun τ => h1RealNorm (fp τ)) volume) :
    (∫⁻ t in Ioo σ (σ + 1), h1ENN (WPath hflow σ x0 fp t)) < ⊤ ∧
      ∀ i j : Fin 2, StronglyMeasurable (d2Path hflow σ x0 fp i j) ∧
        (∫⁻ t in Ioo σ (σ + 1), ENNReal.ofReal ‖d2Path hflow σ x0 fp i j t‖) < ⊤ := by
  have hKD2_sm := (stronglyMeasurable_K0_and_KD2 hA hreg hflow hσ hfp_sm hfp_mem).2
  obtain ⟨_, _, hKD2_int⟩ :=
    integrable_majD2_and_KD2 hA hreg hflow hσ hfp_sm hfp_mem hfp_int
  have hW_l1 : (∫⁻ t in Ioo σ (σ + 1), h1ENN (WPath hflow σ x0 fp t)) < ⊤ := by
    let C : ℝ := A * (h1RealNorm x0 + ∫ τ, h1RealNorm (fp τ))
    have hle : ∀ t ∈ Ioo σ (σ + 1), h1ENN (WPath hflow σ x0 fp t) ≤ ENNReal.ofReal C := by
      intro t ht
      have hint_t := (integrable_K0_slice_and_prod hA hreg hflow hσ hfp_sm hfp_mem hfp_int).1 t
      simp only [WPath, ht, ↓reduceIte, h1ENN_eq_ofReal]
      refine ENNReal.ofReal_le_ofReal ?_
      have hb0 := (S0Val_and_SD2Val_bounds hA p.ν_pos hflow hσ ⟨ht.1, ht.2.le⟩ hx0).2.1
      have hb1 : h1RealNorm (∫ τ, K0 hflow σ fp (t, τ)) ≤ A * ∫ τ, h1RealNorm (fp τ) := by
        calc h1RealNorm (∫ τ, K0 hflow σ fp (t, τ))
            ≤ ∫ τ, h1RealNorm (K0 hflow σ fp (t, τ)) := h1RealNorm_integral_le hint_t
          _ ≤ ∫ τ, A * h1RealNorm (fp τ) :=
              integral_mono (integrable_h1RealNorm_comp hint_t) (hfp_int.const_mul A)
                (fun τ => K0_h1RealNorm_le hA hflow hσ hfp_mem t τ)
          _ = A * ∫ τ, h1RealNorm (fp τ) := integral_const_mul A _
      have htri := h1RealNorm_add_le (S0Val hflow t σ x0) (∫ τ, K0 hflow σ fp (t, τ))
      dsimp [C]
      linarith
    calc (∫⁻ t in Ioo σ (σ + 1), h1ENN (WPath hflow σ x0 fp t))
        ≤ ∫⁻ _ in Ioo σ (σ + 1), ENNReal.ofReal C := setLIntegral_mono' measurableSet_Ioo hle
      _ = ENNReal.ofReal C * volume (Ioo σ (σ + 1)) := by simp
      _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top
          (by rw [Real.volume_Ioo]; exact ENNReal.ofReal_lt_top)
  refine ⟨hW_l1, fun i j => ⟨?_, ?_⟩⟩
  · have h1 : StronglyMeasurable
        ((Ioo σ (σ + 1)).indicator fun t => SD2Val hflow i j t σ x0) :=
      UnforcedLeray.Infra.JointMeasurableRep.stronglyMeasurable_indicator_of_continuousOn
        ((continuousOn_S0Val_and_SD2Val_left hflow hσ hx0).2 i j |>.mono
          (fun t ht => ⟨ht.1, by linarith [ht.2]⟩))
        measurableSet_Ioo
    have h2 : StronglyMeasurable
        ((Ioo σ (σ + 1)).indicator fun t => ∫ τ, KD2 hflow σ fp i j (t, τ)) :=
      (hKD2_sm i j).integral_prod_right'.indicator measurableSet_Ioo
    have heq : d2Path hflow σ x0 fp i j = fun t =>
        (Ioo σ (σ + 1)).indicator (fun s => SD2Val hflow i j s σ x0) t +
        (Ioo σ (σ + 1)).indicator (fun s => ∫ τ, KD2 hflow σ fp i j (s, τ)) t := by
      funext t
      by_cases ht : t ∈ Ioo σ (σ + 1) <;> simp [d2Path, ht]
    rw [heq]
    exact h1.add h2
  · let C₀ : ℝ := A * p.ν ^ (-1 / 2 : ℝ) * h1RealNorm x0
    have hC₀_nn : 0 ≤ C₀ :=
      mul_nonneg (mul_nonneg hA.le (Real.rpow_nonneg p.ν_pos.le _)) (h1RealNorm_nonneg x0)
    have hpt : ∀ t ∈ Ioo σ (σ + 1),
        ENNReal.ofReal ‖d2Path hflow σ x0 fp i j t‖ ≤
          ENNReal.ofReal C₀ * ENNReal.ofReal ((t - σ) ^ (-1 / 2 : ℝ)) +
            ENNReal.ofReal (∫ τ, ‖KD2 hflow σ fp i j (t, τ)‖) := by
      intro t ht
      simp only [d2Path, ht, ↓reduceIte]
      have hb_init : ‖SD2Val hflow i j t σ x0‖ ≤ C₀ * (t - σ) ^ (-1 / 2 : ℝ) := by
        have hsum := (S0Val_and_SD2Val_bounds hA p.ν_pos hflow hσ ⟨ht.1, ht.2.le⟩ hx0).2.2.2
        have hle : ‖SD2Val hflow i j t σ x0‖ ≤
            ∑ a : Fin 2, ∑ b : Fin 2, ‖SD2Val hflow a b t σ x0‖ := by
          simp only [Fin.sum_univ_two]
          fin_cases i <;> fin_cases j <;> dsimp <;>
            linarith [norm_nonneg (SD2Val hflow 0 0 t σ x0), norm_nonneg (SD2Val hflow 0 1 t σ x0),
              norm_nonneg (SD2Val hflow 1 0 t σ x0), norm_nonneg (SD2Val hflow 1 1 t σ x0)]
        refine hle.trans (hsum.trans_eq ?_)
        dsimp [C₀]; ring
      have hb_int : ‖∫ τ, KD2 hflow σ fp i j (t, τ)‖ ≤ ∫ τ, ‖KD2 hflow σ fp i j (t, τ)‖ :=
        norm_integral_le_integral_norm _
      have htri := (norm_add_le (SD2Val hflow i j t σ x0)
        (∫ τ, KD2 hflow σ fp i j (t, τ))).trans (add_le_add hb_init hb_int)
      have h1_nn : 0 ≤ C₀ * (t - σ) ^ (-1 / 2 : ℝ) :=
        mul_nonneg hC₀_nn (Real.rpow_nonneg (sub_pos.2 ht.1).le _)
      have h2_nn : 0 ≤ ∫ τ, ‖KD2 hflow σ fp i j (t, τ)‖ :=
        integral_nonneg fun _ => norm_nonneg _
      calc ENNReal.ofReal ‖SD2Val hflow i j t σ x0 + ∫ τ, KD2 hflow σ fp i j (t, τ)‖
          ≤ ENNReal.ofReal (C₀ * (t - σ) ^ (-1 / 2 : ℝ) + ∫ τ, ‖KD2 hflow σ fp i j (t, τ)‖) :=
            ENNReal.ofReal_le_ofReal htri
        _ = ENNReal.ofReal C₀ * ENNReal.ofReal ((t - σ) ^ (-1 / 2 : ℝ)) +
              ENNReal.ofReal (∫ τ, ‖KD2 hflow σ fp i j (t, τ)‖) := by
            rw [ENNReal.ofReal_add h1_nn h2_nn, ENNReal.ofReal_mul hC₀_nn]
    have hf1_fin : (∫⁻ t in Ioo σ (σ + 1),
        ENNReal.ofReal C₀ * ENNReal.ofReal ((t - σ) ^ (-1 / 2 : ℝ))) < ⊤ := by
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top
        ((lintegral_inv_sqrt_Ioo_le_two (by linarith) le_rfl).trans_lt ENNReal.ofReal_lt_top)
    have hint_n : Integrable (fun t => ∫ τ, ‖KD2 hflow σ fp i j (t, τ)‖) volume :=
      (hKD2_int i j).integral_norm_prod_left
    have hf2_fin : (∫⁻ t in Ioo σ (σ + 1),
        ENNReal.ofReal (∫ τ, ‖KD2 hflow σ fp i j (t, τ)‖)) < ⊤ := by
      have hfin := (hint_n.integrableOn (s := Ioo σ (σ + 1))).2
      rw [hasFiniteIntegral_iff_enorm] at hfin
      refine (lintegral_mono fun t => ?_).trans_lt hfin
      rw [← ofReal_norm, Real.norm_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
    have hm_f1 : Measurable (fun t : ℝ =>
        ENNReal.ofReal C₀ * ENNReal.ofReal ((t - σ) ^ (-1 / 2 : ℝ))) :=
      measurable_const.mul (ENNReal.measurable_ofReal.comp ((measurable_id.sub_const σ).pow_const _))
    calc (∫⁻ t in Ioo σ (σ + 1), ENNReal.ofReal ‖d2Path hflow σ x0 fp i j t‖)
        ≤ ∫⁻ t in Ioo σ (σ + 1),
            (ENNReal.ofReal C₀ * ENNReal.ofReal ((t - σ) ^ (-1 / 2 : ℝ)) +
              ENNReal.ofReal (∫ τ, ‖KD2 hflow σ fp i j (t, τ)‖)) :=
          setLIntegral_mono' measurableSet_Ioo hpt
      _ = (∫⁻ t in Ioo σ (σ + 1),
            ENNReal.ofReal C₀ * ENNReal.ofReal ((t - σ) ^ (-1 / 2 : ℝ))) +
          (∫⁻ t in Ioo σ (σ + 1),
            ENNReal.ofReal (∫ τ, ‖KD2 hflow σ fp i j (t, τ)‖)) := lintegral_add_left hm_f1 _
      _ < ⊤ := ENNReal.add_lt_top.2 ⟨hf1_fin, hf2_fin⟩

/-- Almost-everywhere `D²` weak cell derivatives and `H¹ → H²` Duhamel bound on `Ioo σ (σ + 1)`. -/
lemma ae_weakD2_and_bound_d2Path {dm dp : ℝ} {p : Params} {d A σ : ℝ}
    (hA : 0 < A) (hreg : BgRegime p d dm dp) (hflow : F8U.CylOseenFlowBound A p) (hσ : 0 ≤ σ)
    {u₀ uq₀ uη₀ : B0579.Plane → CMerid} (hu₀ : F8U.IsCylH1Datum p.c u₀ uq₀ uη₀)
    {g₁ gq₁ gη₁ : CProf}
    {fp : ℝ → X3 p.c} (hfp_sm : StronglyMeasurable fp) (hfp_mem : ∀ τ, fp τ ∈ H1Set p.c)
    (hfp_le : ∀ τ, h1ENN (fp τ) ≤ sliceH1Norm p.c g₁ gq₁ gη₁ τ)
    (hfp_int : Integrable (fun τ => h1RealNorm (fp τ)) volume) :
    let x0 := datumToX3 hu₀
    ∀ᵐ t ∂volume, t ∈ Ioo σ (σ + 1) →
      (∀ j k : Fin 2,
        IIIa.HasWeakCellDerivC p.c j
          (fun y => (WPath hflow σ x0 fp t).2.1 y k)
          (fun y => d2Path hflow σ x0 fp 0 j t y k)) ∧
      (∀ j k : Fin 2,
        IIIa.HasWeakCellDerivC p.c j
          (fun y => (WPath hflow σ x0 fp t).2.2 y k)
          (fun y => d2Path hflow σ x0 fp 1 j t y k)) ∧
      (∑ i : Fin 2, ∑ j : Fin 2, ENNReal.ofReal ‖d2Path hflow σ x0 fp i j t‖ ≤
        ENNReal.ofReal (A * p.ν ^ (-1 / 2 : ℝ)) *
          (ENNReal.ofReal ((t - σ) ^ (-1 / 2 : ℝ)) * F8U.cylH1 p.c u₀ uq₀ uη₀ +
            ∫⁻ τ in Ioc σ t, ENNReal.ofReal ((t - τ) ^ (-1 / 2 : ℝ)) *
              sliceH1Norm p.c g₁ gq₁ gη₁ τ)) := by
  intro x0
  have hx0 : x0 ∈ H1Set p.c := datumToX3_mem_H1Set hu₀
  have hint_K0 := (integrable_K0_slice_and_prod hA hreg hflow hσ hfp_sm hfp_mem hfp_int).1
  obtain ⟨_, hmaj_int, hKD2_int⟩ :=
    integrable_majD2_and_KD2 hA hreg hflow hσ hfp_sm hfp_mem hfp_int
  filter_upwards [hmaj_int.prod_right_ae,
    (hKD2_int 0 0).prod_right_ae, (hKD2_int 0 1).prod_right_ae,
    (hKD2_int 1 0).prod_right_ae, (hKD2_int 1 1).prod_right_ae]
    with t hmaj_t hd00 hd01 hd10 hd11 ht
  have hd_t : ∀ i j : Fin 2, Integrable (fun τ => KD2 hflow σ fp i j (t, τ)) volume := by
    intro i j
    fin_cases i <;> fin_cases j
    · exact hd00
    · exact hd01
    · exact hd10
    · exact hd11
  have ht2 : t ∈ Ioo σ (σ + 2) := ⟨ht.1, by linarith [ht.2]⟩
  have hwk_i : ∀ (i j k : Fin 2)
      (projX : X3 p.c →L[ℝ] L2Cell p.c)
      (hproj_S0 : ∀ (τ : ℝ) (v : X3 p.c) (hτ : 0 ≤ τ) (htτ : t ∈ Ioo τ (τ + 2))
        (hv : v ∈ H1Set p.c),
        projX (S0Val hflow t τ v) =
          (orbit_memLp_1 (isCylOseenOrbit_orbitOf hflow hτ hv) htτ i).toLp
            (F8U.slice (F8U.pd i (orbitOf hflow τ v)) t)),
      IIIa.HasWeakCellDerivC p.c j
        (fun y => projX (WPath hflow σ x0 fp t) y k)
        (fun y => d2Path hflow σ x0 fp i j t y k) := by
    intro i j k projX hproj_S0
    let U : L2Cell p.c := projX (WPath hflow σ x0 fp t)
    let G : L2Cell p.c := d2Path hflow σ x0 fp i j t
    refine ⟨fun ψ hψ => ⟨integrableOn_coe_mul_cylTest p.c_pos U k (hψ.pd j),
      integrableOn_coe_mul_cylTest p.c_pos G k hψ⟩, fun ψ hψ => ?_⟩
    rw [← pairTestCLM_apply p.c_pos (hψ.pd j) k U, ← pairTestCLM_apply p.c_pos hψ k G]
    have hU_eq : U = projX (S0Val hflow t σ x0) + ∫ τ, projX (K0 hflow σ fp (t, τ)) := by
      dsimp only [U]
      simp only [WPath, ht, ↓reduceIte, map_add, projX.integral_comp_comm (hint_K0 t)]
    have hG_eq : G = SD2Val hflow i j t σ x0 + ∫ τ, KD2 hflow σ fp i j (t, τ) := by
      simp [G, d2Path, ht]
    have h1_int : Integrable (fun τ => projX (K0 hflow σ fp (t, τ))) volume :=
      projX.integrable_comp (hint_K0 t)
    rw [hU_eq, hG_eq, map_add, map_add,
      ← (pairTestCLM p.c_pos (hψ.pd j) k).integral_comp_comm h1_int,
      ← (pairTestCLM p.c_pos hψ k).integral_comp_comm (hd_t i j),
      neg_add, ← integral_neg]
    have hinit_wk : pairTestCLM p.c_pos (hψ.pd j) k (projX (S0Val hflow t σ x0)) =
        -pairTestCLM p.c_pos hψ k (SD2Val hflow i j t σ x0) := by
      have hW0 := isCylOseenOrbit_orbitOf hflow hσ hx0
      have hw := hasWeakCellDerivC_congr
        ((orbit_memLp_1 hW0 ht2 i).coeFn_toLp.symm.mono fun _ h => congrArg (· k) h)
        ((orbit_memLp_2 hW0 ht2 i j).coeFn_toLp.symm.mono fun _ h => congrArg (· k) h)
        (orbit_pd_hasWeakCellDerivC p.c_pos hW0 ht2 i j k)
      rw [hproj_S0 σ x0 hσ ht2 hx0, SD2Val_of_cond hflow i j hσ ht2 hx0,
        pairTestCLM_apply, pairTestCLM_apply]
      exact hw.2 ψ hψ
    have hint_wk : (∫ τ, (pairTestCLM p.c_pos (hψ.pd j) k) (projX (K0 hflow σ fp (t, τ)))) =
        ∫ τ, -(pairTestCLM p.c_pos hψ k) (KD2 hflow σ fp i j (t, τ)) := by
      refine integral_congr_ae (Eventually.of_forall fun τ => ?_)
      dsimp only [K0, KD2]
      by_cases hq : (t, τ) ∈ unitTriangle σ
      · rw [indicator_of_mem hq, indicator_of_mem hq]
        have hτ_nn : 0 ≤ τ := by linarith [hq.1]
        have htτ : t ∈ Ioo τ (τ + 2) := ⟨hq.2.1, by linarith [hq.1, hq.2.2]⟩
        have hWτ := isCylOseenOrbit_orbitOf hflow hτ_nn (hfp_mem τ)
        have hw := hasWeakCellDerivC_congr
          ((orbit_memLp_1 hWτ htτ i).coeFn_toLp.symm.mono fun _ h => congrArg (· k) h)
          ((orbit_memLp_2 hWτ htτ i j).coeFn_toLp.symm.mono fun _ h => congrArg (· k) h)
          (orbit_pd_hasWeakCellDerivC p.c_pos hWτ htτ i j k)
        rw [hproj_S0 τ (fp τ) hτ_nn htτ (hfp_mem τ),
          SD2Val_of_cond hflow i j hτ_nn htτ (hfp_mem τ),
          pairTestCLM_apply, pairTestCLM_apply]
        exact hw.2 ψ hψ
      · rw [indicator_of_notMem hq, indicator_of_notMem hq, map_zero, map_zero, map_zero, neg_zero]
    rw [hinit_wk, hint_wk]
  let p21 : X3 p.c →L[ℝ] L2Cell p.c :=
    (ContinuousLinearMap.fst ℝ (L2Cell p.c) (L2Cell p.c)).comp
      (ContinuousLinearMap.snd ℝ (L2Cell p.c) (L2Cell p.c × L2Cell p.c))
  let p22 : X3 p.c →L[ℝ] L2Cell p.c :=
    (ContinuousLinearMap.snd ℝ (L2Cell p.c) (L2Cell p.c)).comp
      (ContinuousLinearMap.snd ℝ (L2Cell p.c) (L2Cell p.c × L2Cell p.c))
  refine ⟨fun j k => hwk_i 0 j k p21 (fun τ v hτ htτ hv => by
      dsimp [p21]; rw [S0Val_of_cond hflow hτ htτ hv]),
    fun j k => hwk_i 1 j k p22 (fun τ v hτ htτ hv => by
      dsimp [p22]; rw [S0Val_of_cond hflow hτ htτ hv]),
    ?_⟩
  let C : ℝ := A * p.ν ^ (-1 / 2 : ℝ)
  have hC_nn : 0 ≤ C := mul_nonneg hA.le (Real.rpow_nonneg p.ν_pos.le _)
  have hsum_real : ∑ i : Fin 2, ∑ j : Fin 2, ‖d2Path hflow σ x0 fp i j t‖ ≤
      C * ((t - σ) ^ (-1 / 2 : ℝ) * h1RealNorm x0) + ∫ τ, majD2 A p σ fp (t, τ) := by
    have h1 : ∀ i j : Fin 2, ‖d2Path hflow σ x0 fp i j t‖ ≤
        ‖SD2Val hflow i j t σ x0‖ + ∫ τ, ‖KD2 hflow σ fp i j (t, τ)‖ := by
      intro i j
      simp only [d2Path, ht, ↓reduceIte]
      exact (norm_add_le _ _).trans (add_le_add le_rfl (norm_integral_le_integral_norm _))
    have hb_init : ∑ i : Fin 2, ∑ j : Fin 2, ‖SD2Val hflow i j t σ x0‖ ≤
        C * ((t - σ) ^ (-1 / 2 : ℝ) * h1RealNorm x0) := by
      have := (S0Val_and_SD2Val_bounds hA p.ν_pos hflow hσ ⟨ht.1, ht.2.le⟩ hx0).2.2.2
      dsimp [C]; linarith
    have hb_int : ∑ i : Fin 2, ∑ j : Fin 2, (∫ τ, ‖KD2 hflow σ fp i j (t, τ)‖) ≤
        ∫ τ, majD2 A p σ fp (t, τ) := by
      simp only [Fin.sum_univ_two]
      have h01 : Integrable (fun τ => ‖KD2 hflow σ fp 0 0 (t, τ)‖ + ‖KD2 hflow σ fp 0 1 (t, τ)‖)
          volume := (hd_t 0 0).norm.add (hd_t 0 1).norm
      have h1011 : Integrable (fun τ => ‖KD2 hflow σ fp 1 0 (t, τ)‖ + ‖KD2 hflow σ fp 1 1 (t, τ)‖)
          volume := (hd_t 1 0).norm.add (hd_t 1 1).norm
      rw [← integral_add (hd_t 0 0).norm (hd_t 0 1).norm,
        ← integral_add (hd_t 1 0).norm (hd_t 1 1).norm,
        ← integral_add h01 h1011]
      refine integral_mono (h01.add h1011) hmaj_t fun τ => ?_
      have := sum_norm_KD2_le_majD2 hA hflow hσ hfp_mem (t, τ)
      simpa only [Fin.sum_univ_two, Pi.add_apply] using this
    have hstep : ∑ i : Fin 2, ∑ j : Fin 2, ‖d2Path hflow σ x0 fp i j t‖ ≤
        (∑ i : Fin 2, ∑ j : Fin 2, ‖SD2Val hflow i j t σ x0‖) +
        (∑ i : Fin 2, ∑ j : Fin 2, ∫ τ, ‖KD2 hflow σ fp i j (t, τ)‖) := by
      simp only [Fin.sum_univ_two]
      linarith [h1 0 0, h1 0 1, h1 1 0, h1 1 1]
    linarith
  have hlhs_eq : ∑ i : Fin 2, ∑ j : Fin 2, ENNReal.ofReal ‖d2Path hflow σ x0 fp i j t‖ =
      ENNReal.ofReal (∑ i : Fin 2, ∑ j : Fin 2, ‖d2Path hflow σ x0 fp i j t‖) := by
    simp only [Fin.sum_univ_two]
    rw [ENNReal.ofReal_add (by positivity) (by positivity),
      ENNReal.ofReal_add (norm_nonneg _) (norm_nonneg _),
      ENNReal.ofReal_add (norm_nonneg _) (norm_nonneg _)]
  have h1_nn : 0 ≤ (t - σ) ^ (-1 / 2 : ℝ) * h1RealNorm x0 :=
    mul_nonneg (Real.rpow_nonneg (sub_pos.2 ht.1).le _) (h1RealNorm_nonneg x0)
  have h2_nn : 0 ≤ ∫ τ, majD2 A p σ fp (t, τ) :=
    integral_nonneg fun τ => majD2_nonneg hA p σ fp (t, τ)
  have hmaj_enn : ENNReal.ofReal (∫ τ, majD2 A p σ fp (t, τ)) ≤
      ENNReal.ofReal C *
        ∫⁻ τ in Ioc σ t, ENNReal.ofReal ((t - τ) ^ (-1 / 2 : ℝ)) *
          sliceH1Norm p.c g₁ gq₁ gη₁ τ := by
    rw [ofReal_integral_eq_lintegral_ofReal hmaj_t
      (Eventually.of_forall fun τ => majD2_nonneg hA p σ fp (t, τ))]
    have hind : (fun τ : ℝ => ENNReal.ofReal (majD2 A p σ fp (t, τ))) =
        (Ioo σ t).indicator fun τ =>
          ENNReal.ofReal C * (ENNReal.ofReal ((t - τ) ^ (-1 / 2 : ℝ)) * h1ENN (fp τ)) := by
      funext τ
      by_cases hτ : τ ∈ Ioo σ t
      · have hq : (t, τ) ∈ unitTriangle σ := ⟨hτ.1, hτ.2, ht.2⟩
        rw [indicator_of_mem hτ]
        dsimp [majD2, C]
        rw [indicator_of_mem hq,
          ENNReal.ofReal_mul (mul_nonneg hC_nn (Real.rpow_nonneg (sub_pos.2 hτ.2).le _)),
          ENNReal.ofReal_mul hC_nn, h1ENN_eq_ofReal, mul_assoc]
      · have hq : (t, τ) ∉ unitTriangle σ := fun h => hτ ⟨h.1, h.2.1⟩
        simp [majD2, hτ, hq]
    rw [hind, lintegral_indicator measurableSet_Ioo]
    have hsub := lintegral_mono_set (μ := volume) (s := Ioo σ t) (t := Ioc σ t)
      (f := fun τ => ENNReal.ofReal C *
        (ENNReal.ofReal ((t - τ) ^ (-1 / 2 : ℝ)) * h1ENN (fp τ)))
      Ioo_subset_Ioc_self
    refine hsub.trans ?_
    calc (∫⁻ τ in Ioc σ t, ENNReal.ofReal C *
            (ENNReal.ofReal ((t - τ) ^ (-1 / 2 : ℝ)) * h1ENN (fp τ)))
        ≤ ∫⁻ τ in Ioc σ t, ENNReal.ofReal C *
            (ENNReal.ofReal ((t - τ) ^ (-1 / 2 : ℝ)) * sliceH1Norm p.c g₁ gq₁ gη₁ τ) :=
          lintegral_mono fun τ => mul_le_mul_right (mul_le_mul_right (hfp_le τ) _) _
      _ = ENNReal.ofReal C *
            ∫⁻ τ in Ioc σ t, ENNReal.ofReal ((t - τ) ^ (-1 / 2 : ℝ)) *
              sliceH1Norm p.c g₁ gq₁ gη₁ τ := by
          rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  rw [hlhs_eq]
  calc ENNReal.ofReal (∑ i : Fin 2, ∑ j : Fin 2, ‖d2Path hflow σ x0 fp i j t‖)
      ≤ ENNReal.ofReal (C * ((t - σ) ^ (-1 / 2 : ℝ) * h1RealNorm x0) +
          ∫ τ, majD2 A p σ fp (t, τ)) := ENNReal.ofReal_le_ofReal hsum_real
    _ = ENNReal.ofReal C *
          (ENNReal.ofReal ((t - σ) ^ (-1 / 2 : ℝ)) * ENNReal.ofReal (h1RealNorm x0)) +
          ENNReal.ofReal (∫ τ, majD2 A p σ fp (t, τ)) := by
        rw [ENNReal.ofReal_add (mul_nonneg hC_nn h1_nn) h2_nn,
          ENNReal.ofReal_mul hC_nn,
          ENNReal.ofReal_mul (Real.rpow_nonneg (sub_pos.2 ht.1).le _)]
    _ ≤ ENNReal.ofReal C *
          (ENNReal.ofReal ((t - σ) ^ (-1 / 2 : ℝ)) * F8U.cylH1 p.c u₀ uq₀ uη₀) +
        ENNReal.ofReal C *
          ∫⁻ τ in Ioc σ t, ENNReal.ofReal ((t - τ) ^ (-1 / 2 : ℝ)) *
            sliceH1Norm p.c g₁ gq₁ gη₁ τ := by
        refine add_le_add ?_ hmaj_enn
        rw [← h1ENN_eq_ofReal, h1ENN_datumToX3]
    _ = ENNReal.ofReal C *
          (ENNReal.ofReal ((t - σ) ^ (-1 / 2 : ℝ)) * F8U.cylH1 p.c u₀ uq₀ uη₀ +
            ∫⁻ τ in Ioc σ t, ENNReal.ofReal ((t - τ) ^ (-1 / 2 : ℝ)) *
              sliceH1Norm p.c g₁ gq₁ gη₁ τ) := by
        rw [mul_add]

/-! ## 3. Periodized smooth test profiles, single-orbit FTC, and Duhamel Fubini weak equation -/

/-- Real meridional transpose `-∂_s Ψ - ν(∂_q² Ψ + ∂_η² Ψ)`. -/
def mtReal (ν : ℝ) (Ψ : Coord → Fin 2 → ℝ) (x : Coord) (i : Fin 2) : ℝ :=
  -cpd 0 (fun y => Ψ y i) x -
    ν * (cpd 1 (fun y => cpd 1 (fun z => Ψ z i) y) x +
      cpd 2 (fun y => cpd 2 (fun z => Ψ z i) y) x)

lemma meridTranspose_eq_ofReal_mtReal (ν : ℝ) (Ψ : Coord → Fin 2 → ℝ) (x : Coord) (i : Fin 2) :
    meridTranspose ν Ψ x i = ((mtReal ν Ψ x i : ℝ) : ℂ) := by
  simp [meridTranspose, mtReal, sub_eq_add_neg]

lemma isCoordTest_cpd {φ : Coord → ℝ} (hφ : IsCoordTest φ) (k : Fin 3) :
    IsCoordTest (cpd k φ) := by
  have hsub : tsupport (cpd k φ) ⊆ tsupport φ := by
    refine closure_minimal ?_ (isClosed_tsupport φ)
    intro x hx
    by_contra hnot
    exact hx (by simp [cpd, fderiv_of_notMem_tsupport (𝕜 := ℝ) hnot])
  refine ⟨(((contDiff_infty_iff_fderiv.1 hφ.smooth).2).clm_apply contDiff_const),
    hφ.compact.of_isClosed_subset (isClosed_tsupport _) hsub,
    hsub.trans hφ.supp⟩

lemma isCoordTest_add {φ ψ : Coord → ℝ} (hφ : IsCoordTest φ) (hψ : IsCoordTest ψ) :
    IsCoordTest (fun x => φ x + ψ x) := by
  have hsub : tsupport (fun x => φ x + ψ x) ⊆ tsupport φ ∪ tsupport ψ :=
    tsupport_add φ ψ
  refine ⟨hφ.smooth.add hψ.smooth,
    (hφ.compact.union hψ.compact).of_isClosed_subset (isClosed_tsupport _) hsub,
    hsub.trans (union_subset hφ.supp hψ.supp)⟩

lemma isCoordTest_const_mul (a : ℝ) {φ : Coord → ℝ} (hφ : IsCoordTest φ) :
    IsCoordTest (fun x => a * φ x) := by
  have hsub : tsupport (fun x => a * φ x) ⊆ tsupport φ := by
    refine closure_minimal ?_ (isClosed_tsupport φ)
    intro x hx
    by_contra hnot
    exact hx (by simp [image_eq_zero_of_notMem_tsupport hnot])
  refine ⟨contDiff_const.mul hφ.smooth,
    hφ.compact.of_isClosed_subset (isClosed_tsupport _) hsub,
    hsub.trans hφ.supp⟩

lemma isCoordTest_mtReal (ν : ℝ) {Ψ : Coord → Fin 2 → ℝ} (hΨ : IsPlanarSolTest Ψ) (i : Fin 2) :
    IsCoordTest (fun x => mtReal ν Ψ x i) := by
  have h0 := isCoordTest_const_mul (-1) (isCoordTest_cpd (hΨ.smooth i) 0)
  have h11 := isCoordTest_cpd (isCoordTest_cpd (hΨ.smooth i) 1) 1
  have h22 := isCoordTest_cpd (isCoordTest_cpd (hΨ.smooth i) 2) 2
  have hlap := isCoordTest_const_mul (-ν) (isCoordTest_add h11 h22)
  have heq : (fun x => mtReal ν Ψ x i) =
      fun x => (-1) * cpd 0 (fun y => Ψ y i) x +
        (-ν) * (cpd 1 (fun y => cpd 1 (fun z => Ψ z i) y) x +
          cpd 2 (fun y => cpd 2 (fun z => Ψ z i) y) x) := by
    funext x; dsimp [mtReal]; ring
  rw [heq]
  exact isCoordTest_add h0 hlap

/-- Strict inner time-space support box inside `Ioo σ (σ + 1)` for a planar solenoidal test `Ψ`. -/
lemma planarSolTest_Ioo_box {σ : ℝ} {Ψ : Coord → Fin 2 → ℝ}
    (hΨ : IsPlanarSolTest Ψ)
    (hΨ_supp : ∀ i : Fin 2, tsupport (fun x => Ψ x i) ⊆ Ioo σ (σ + 1) ×ˢ univ) :
    ∃ a'' a' b' b'' R : ℝ,
      σ < a'' ∧ a'' < a' ∧ a' ≤ b' ∧ b' < b'' ∧ b'' < σ + 1 ∧ 0 < R ∧
        ∀ (i : Fin 2) (x : Coord),
          (x.1 ∉ Icc a' b' ∨ R < |x.2.1| ∨ R < |x.2.2|) →
            x ∉ tsupport (fun y => Ψ y i) := by
  obtain ⟨_, _, R0, _, _, hR0, hbox0⟩ := TailPeriodizeAux.coordTest_box (hΨ.smooth 0)
  obtain ⟨_, _, R1, _, _, _, _⟩ := TailPeriodizeAux.coordTest_box (hΨ.smooth 1)
  obtain ⟨M0, hM0⟩ := (hΨ.smooth 0).compact.isBounded.subset_closedBall (0 : Coord)
  obtain ⟨M1, hM1⟩ := (hΨ.smooth 1).compact.isBounded.subset_closedBall (0 : Coord)
  let R : ℝ := max (max R0 R1) (max M0 M1)
  have hR_pos : 0 < R := lt_of_lt_of_le hR0 ((le_max_left R0 R1).trans (le_max_left _ _))
  have hR_tsupp : ∀ (i : Fin 2) (x : Coord), x ∈ tsupport (fun y => Ψ y i) →
      |x.2.1| ≤ R ∧ |x.2.2| ≤ R := by
    intro i x hx
    have hle_R : ‖x‖ ≤ R := by
      fin_cases i
      · have h := hM0 hx
        rw [Metric.mem_closedBall, dist_zero_right] at h
        exact h.trans ((le_max_left M0 M1).trans (le_max_right _ _))
      · have h := hM1 hx
        rw [Metric.mem_closedBall, dist_zero_right] at h
        exact h.trans ((le_max_right M0 M1).trans (le_max_right _ _))
    have h2 : ‖x.2‖ ≤ R := (norm_snd_le x).trans hle_R
    exact ⟨Real.norm_eq_abs x.2.1 ▸ (norm_fst_le x.2).trans h2,
      Real.norm_eq_abs x.2.2 ▸ (norm_snd_le x.2).trans h2⟩
  let K : Set ℝ :=
    Prod.fst '' (tsupport (fun x => Ψ x 0) ∪ tsupport (fun x => Ψ x 1))
  have hK_comp : IsCompact K :=
    ((hΨ.smooth 0).compact.union (hΨ.smooth 1).compact).image continuous_fst
  have hK_sub : K ⊆ Ioo σ (σ + 1) := by
    rintro s ⟨x, hx | hx, rfl⟩
    · exact (hΨ_supp 0 hx).1
    · exact (hΨ_supp 1 hx).1
  by_cases hne : K.Nonempty
  · let a' : ℝ := sInf K
    let b' : ℝ := sSup K
    have ha'_in : a' ∈ Ioo σ (σ + 1) := hK_sub (hK_comp.sInf_mem hne)
    have hb'_in : b' ∈ Ioo σ (σ + 1) := hK_sub (hK_comp.sSup_mem hne)
    have hab' : a' ≤ b' := csInf_le hK_comp.bddBelow (hK_comp.sSup_mem hne)
    let a'' : ℝ := (σ + a') / 2
    let b'' : ℝ := (b' + (σ + 1)) / 2
    refine ⟨a'', a', b', b'', R, by dsimp [a'']; linarith [ha'_in.1],
      by dsimp [a'']; linarith [ha'_in.1], hab',
      by dsimp [b'']; linarith [hb'_in.2], by dsimp [b'']; linarith [hb'_in.2],
      hR_pos, fun i x hx hxt => ?_⟩
    have hxK : x.1 ∈ K := by
      fin_cases i
      · exact ⟨x, Or.inl hxt, rfl⟩
      · exact ⟨x, Or.inr hxt, rfl⟩
    have hx_ab : x.1 ∈ Icc a' b' :=
      ⟨csInf_le hK_comp.bddBelow hxK, le_csSup hK_comp.bddAbove hxK⟩
    obtain ⟨hqR, hηR⟩ := hR_tsupp i x hxt
    rcases hx with h1 | h2 | h3
    · exact h1 hx_ab
    · linarith
    · linarith
  · rw [Set.not_nonempty_iff_eq_empty] at hne
    refine ⟨σ + 1 / 4, σ + 1 / 2, σ + 1 / 2, σ + 3 / 4, R,
      by linarith, by linarith, le_rfl, by linarith, by linarith, hR_pos,
      fun i x _ hxt => ?_⟩
    have hxK : x.1 ∈ K := by
      fin_cases i
      · exact ⟨x, Or.inl hxt, rfl⟩
      · exact ⟨x, Or.inr hxt, rfl⟩
    rw [hne] at hxK
    exact notMem_empty _ hxK

lemma vanish_derivs_of_notMem_tsupport {φ : Coord → ℝ} {x : Coord} (hx : x ∉ tsupport φ) :
    φ x = 0 ∧ (∀ k : Fin 3, cpd k φ x = 0) ∧ (∀ k l : Fin 3, cpd k (cpd l φ) x = 0) := by
  have hev : φ =ᶠ[𝓝 x] 0 := notMem_tsupport_iff_eventuallyEq.1 hx
  have hev1 : ∀ l : Fin 3, cpd l φ =ᶠ[𝓝 x] 0 := by
    intro l
    filter_upwards [hev.eventually_nhds] with y hy
    have hy' : φ =ᶠ[𝓝 y] 0 := hy
    change fderiv ℝ φ y (cdir l) = 0
    rw [hy'.fderiv_eq]; simp
  refine ⟨hev.eq_of_nhds, fun k => (hev1 k).eq_of_nhds, fun k l => ?_⟩
  change fderiv ℝ (cpd l φ) x (cdir k) = 0
  rw [(hev1 l).fderiv_eq]
  simp

/-- Joint `CProf` lift of `qPeriodizeVec c α`. -/
def perVecProf (c : ℝ) (α : Coord → Fin 2 → ℝ) : CProf :=
  fun x => WithLp.toLp 2 fun i : Fin 2 => (TailPeriodizeAux.qPeriodizeVec c α x.1 x.2 i : ℂ)

private lemma shift_outside_box_local {c R Q : ℝ} (hc : 0 < c)
    {N : ℕ} (hN : (Q + R) / c + 1 < (N : ℝ))
    {z : B0579.Plane} (hz : |z.1| ≤ Q) {k : ℤ} (hk : k ∉ Finset.Icc (-(N : ℤ)) (N : ℤ)) :
    R < |z.1 + (k : ℝ) * c| := by
  rw [Finset.mem_Icc, not_and_or, not_le, not_le] at hk
  have hk_abs : (N : ℝ) + 1 ≤ |(k : ℝ)| := by
    have hk_int : (N : ℤ) + 1 ≤ |k| := by
      rcases hk with hk | hk
      · rw [abs_of_neg (by omega)]; omega
      · rw [abs_of_nonneg (by omega)]; omega
    have hk_r : ((N : ℤ) + 1 : ℝ) ≤ (|k| : ℝ) := by exact_mod_cast hk_int
    simpa [Int.cast_abs] using hk_r
  have h1 : Q + R + c < ((N : ℝ) + 1) * c := by
    have hm := mul_lt_mul_of_pos_right hN hc
    have hdiv : ((Q + R) / c + 1) * c = Q + R + c := by field_simp [hc.ne']
    linarith
  have h2 : ((N : ℝ) + 1) * c ≤ |(k : ℝ)| * c := mul_le_mul_of_nonneg_right hk_abs hc.le
  have h3 : |(k : ℝ)| * c - |z.1| ≤ |z.1 + (k : ℝ) * c| := by
    have hsub := abs_sub_abs_le_abs_add ((k : ℝ) * c) z.1
    rw [add_comm, abs_mul, abs_of_pos hc] at hsub
    linarith
  linarith

lemma contDiff_and_derivs_perVecProf {c : ℝ} (hc : 0 < c) {α : Coord → Fin 2 → ℝ}
    (hα : ∀ i : Fin 2, IsCoordTest (fun x => α x i)) :
    ContDiff ℝ ∞ (perVecProf c α) ∧
      F8U.ps (perVecProf c α) = perVecProf c (fun x i => cpd 0 (fun y => α y i) x) ∧
      (∀ j : Fin 2,
        F8U.pd j (perVecProf c α) = perVecProf c (fun x i => cpd j.succ (fun y => α y i) x)) := by
  obtain ⟨_, _, R0, _, _, _, hbox0⟩ := TailPeriodizeAux.coordTest_box (hα 0)
  obtain ⟨_, _, R1, _, _, _, hbox1⟩ := TailPeriodizeAux.coordTest_box (hα 1)
  let R : ℝ := max R0 R1
  have hbox : ∀ (i : Fin 2) (x : Coord), R < |x.2.1| →
      α x i = 0 ∧ ∀ m : Fin 3, cpd m (fun y => α y i) x = 0 := by
    intro i x hq
    fin_cases i
    · exact hbox0 x (Or.inr (Or.inl ((le_max_left R0 R1).trans_lt hq)))
    · exact hbox1 x (Or.inr (Or.inl ((le_max_right R0 R1).trans_lt hq)))
  let e0 : CMerid := singleCylVec 0 (fun _ => 1) (0, 0)
  let e1 : CMerid := singleCylVec 1 (fun _ => 1) (0, 0)
  let term (k : ℤ) (x : Coord) : CMerid :=
    α (x.1, (x.2.1 + (k : ℝ) * c, x.2.2)) 0 • e0 +
      α (x.1, (x.2.1 + (k : ℝ) * c, x.2.2)) 1 • e1
  have hsh_sm : ∀ k : ℤ, ContDiff ℝ ∞ (fun x : Coord => (x.1, (x.2.1 + (k : ℝ) * c, x.2.2))) :=
    fun _ => contDiff_fst.prodMk ((contDiff_fst.comp contDiff_snd |>.add contDiff_const).prodMk
      (contDiff_snd.comp contDiff_snd))
  have hterm_sm : ∀ k : ℤ, ContDiff ℝ ∞ (term k) := fun k =>
    (((hα 0).smooth.comp (hsh_sm k)).smul contDiff_const).add
      (((hα 1).smooth.comp (hsh_sm k)).smul contDiff_const)
  have hloc : ∀ x₀ : Coord, ∃ S : Finset ℤ,
      (perVecProf c α =ᶠ[𝓝 x₀] fun x => ∑ k ∈ S, term k x) ∧
      ∀ m : Fin 3,
        perVecProf c (fun x i => cpd m (fun y => α y i) x) x₀ =
          ∑ k ∈ S, (cpd m (fun y => α y 0) (x₀.1, (x₀.2.1 + (k : ℝ) * c, x₀.2.2)) • e0 +
            cpd m (fun y => α y 1) (x₀.1, (x₀.2.1 + (k : ℝ) * c, x₀.2.2)) • e1) := by
    intro x₀
    obtain ⟨N, hN⟩ := exists_nat_gt (((|x₀.2.1| + 1) + R) / c + 1)
    let S : Finset ℤ := Finset.Icc (-(N : ℤ)) (N : ℤ)
    refine ⟨S, ?_, fun m => ?_⟩
    · have hU : {x : Coord | |x.2.1| < |x₀.2.1| + 1} ∈ 𝓝 x₀ :=
        (isOpen_lt (continuous_fst.comp continuous_snd).abs continuous_const).mem_nhds
          (lt_add_one |x₀.2.1|)
      filter_upwards [hU] with x hx
      have hts : ∀ i : Fin 2, TailPeriodizeAux.qPeriodize c (fun y => α y i) x.1 x.2 =
          ∑ k ∈ S, α (x.1, (x.2.1 + (k : ℝ) * c, x.2.2)) i := fun i =>
        tsum_eq_sum fun k hk =>
          (hbox i _ (shift_outside_box_local hc hN (le_of_lt hx) hk)).1
      ext i
      fin_cases i
      · change (TailPeriodizeAux.qPeriodize c (fun y => α y 0) x.1 x.2 : ℂ) = _
        rw [hts 0]; simp [term, e0, e1, singleCylVec, Complex.real_smul]
      · change (TailPeriodizeAux.qPeriodize c (fun y => α y 1) x.1 x.2 : ℂ) = _
        rw [hts 1]; simp [term, e0, e1, singleCylVec, Complex.real_smul]
    · have hts : ∀ i : Fin 2, TailPeriodizeAux.qPeriodize c (cpd m (fun y => α y i)) x₀.1 x₀.2 =
          ∑ k ∈ S, cpd m (fun y => α y i) (x₀.1, (x₀.2.1 + (k : ℝ) * c, x₀.2.2)) := fun i =>
        tsum_eq_sum fun k hk =>
          (hbox i _ (shift_outside_box_local hc hN (by linarith) hk)).2 m
      ext i
      fin_cases i
      · change (TailPeriodizeAux.qPeriodize c (cpd m (fun y => α y 0)) x₀.1 x₀.2 : ℂ) = _
        rw [hts 0]; simp [e0, e1, singleCylVec, Complex.real_smul]
      · change (TailPeriodizeAux.qPeriodize c (cpd m (fun y => α y 1)) x₀.1 x₀.2 : ℂ) = _
        rw [hts 1]; simp [e0, e1, singleCylVec, Complex.real_smul]
  have hterm_fderiv : ∀ (k : ℤ) (x : Coord) (m : Fin 3),
      fderiv ℝ (term k) x (cdir m) =
        cpd m (fun y => α y 0) (x.1, (x.2.1 + (k : ℝ) * c, x.2.2)) • e0 +
          cpd m (fun y => α y 1) (x.1, (x.2.1 + (k : ℝ) * c, x.2.2)) • e1 := by
    intro k x m
    let v_k : Coord := (0, ((k : ℝ) * c, 0))
    have hsh_eq : (fun z : Coord => (z.1, (z.2.1 + (k : ℝ) * c, z.2.2))) =
        fun z => z + v_k := by
      funext z; ext <;> simp [v_k]
    have hd_i : ∀ i : Fin 2, HasFDerivAt
        (fun z : Coord => α (z.1, (z.2.1 + (k : ℝ) * c, z.2.2)) i)
        (fderiv ℝ (fun y => α y i) (x.1, (x.2.1 + (k : ℝ) * c, x.2.2))) x := by
      intro i
      have h1 := ((hα i).smooth.contDiffAt.differentiableAt (by simp)).hasFDerivAt
        (x := x + v_k)
      have h2 := (hasFDerivAt_id (𝕜 := ℝ) x).add_const v_k
      have hc1 := h1.comp x h2
      have hxv : x + v_k = (x.1, (x.2.1 + (k : ℝ) * c, x.2.2)) := by ext <;> simp [v_k]
      rw [ContinuousLinearMap.comp_id, hxv] at hc1
      have hc_eq : (fun z : Coord => α (z.1, (z.2.1 + (k : ℝ) * c, z.2.2)) i) =
          ((fun x => α x i) ∘ fun x => id x + v_k) :=
        funext fun z => congrArg (fun p => α p i) (congrFun hsh_eq z)
      rwa [hc_eq]
    have hd_t : HasFDerivAt (term k)
        ((fderiv ℝ (fun y => α y 0) (x.1, (x.2.1 + (k : ℝ) * c, x.2.2))).smulRight e0 +
         (fderiv ℝ (fun y => α y 1) (x.1, (x.2.1 + (k : ℝ) * c, x.2.2))).smulRight e1) x :=
      ((hd_i 0).smul_const e0).add ((hd_i 1).smul_const e1)
    rw [hd_t.fderiv]
    simp [cpd]
  refine ⟨contDiff_iff_contDiffAt.2 fun x₀ => ?_, ?_, fun j => ?_⟩
  · obtain ⟨S, hev, _⟩ := hloc x₀
    exact (ContDiff.sum fun k _ => hterm_sm k).contDiffAt.congr_of_eventuallyEq hev
  · funext x₀
    obtain ⟨S, hev, hrhs⟩ := hloc x₀
    unfold F8U.ps
    have hcdir0 : ((1 : ℝ), ((0 : ℝ), (0 : ℝ))) = cdir 0 := rfl
    rw [hcdir0, hev.fderiv_eq,
      fderiv_fun_sum (fun k _ => (hterm_sm k).contDiffAt.differentiableAt (by simp)),
      FunLike.coe_sum, Finset.sum_apply, hrhs 0]
    exact Finset.sum_congr rfl fun k _ => hterm_fderiv k x₀ 0
  · funext x₀
    obtain ⟨S, hev, hrhs⟩ := hloc x₀
    unfold F8U.pd
    have hsdir : F8U.sdir j = cdir j.succ := by fin_cases j <;> rfl
    rw [hsdir, hev.fderiv_eq,
      fderiv_fun_sum (fun k _ => (hterm_sm k).contDiffAt.differentiableAt (by simp)),
      FunLike.coe_sum, Finset.sum_apply, hrhs j.succ]
    exact Finset.sum_congr rfl fun k _ => hterm_fderiv k x₀ j.succ

/-- Slice `MemLp 2 (cellMeas c)` for any jointly continuous `CProf` vanishing for `|y.2| > R`. -/
lemma memLp_slice_of_eta_vanish (c : ℝ) {R : ℝ}
    {G : CProf} (hG_cont : Continuous G)
    (hG_eta : ∀ x : Coord, R < |x.2.2| → G x = 0) (s : ℝ) :
    MemLp (F8U.slice G s) 2 (F8Sm.cellMeas c) := by
  have hcs : Continuous (F8U.slice G s) :=
    hG_cont.comp (continuous_const.prodMk continuous_id)
  let B : Set B0579.Plane := Ico (-(c / 2)) (c / 2) ×ˢ Icc (-R) R
  have hB_fin : volume B < ⊤ := by
    rw [Measure.volume_eq_prod, Measure.prod_prod, Real.volume_Ico, Real.volume_Icc]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top
  let K : Set B0579.Plane := Icc (-(c / 2)) (c / 2) ×ˢ Icc (-R) R
  obtain ⟨M, hM⟩ := (isCompact_Icc.prod isCompact_Icc).exists_bound_of_continuousOn
    (s := K) hcs.continuousOn
  let M' : ℝ := max 0 M
  have hbd : ∀ y ∈ B0579.cell c, ‖G (s, y)‖ ^ 2 ≤
      (Icc (-R) R).indicator (fun _ => M' ^ 2) y.2 := by
    intro y hy
    by_cases hη : y.2 ∈ Icc (-R) R
    · rw [indicator_of_mem hη]
      have hyK : y ∈ K := ⟨⟨hy.1.1, hy.1.2.le⟩, hη⟩
      have hn : ‖G (s, y)‖ ≤ M' := (hM y hyK).trans (le_max_right 0 M)
      exact pow_le_pow_left₀ (norm_nonneg _) hn 2
    · have hgt : R < |y.2| := by
        by_contra hle; push Not at hle; exact hη (abs_le.1 hle)
      rw [hG_eta (s, y) hgt, indicator_of_notMem hη]
      simp
  have hint_ind : IntegrableOn (fun y : B0579.Plane =>
      (Icc (-R) R).indicator (fun _ => M' ^ 2) y.2) (B0579.cell c) volume := by
    have heq : (B0579.cell c).indicator (fun y : B0579.Plane =>
          (Icc (-R) R).indicator (fun _ => M' ^ 2) y.2) =
        B.indicator (fun _ => M' ^ 2) := by
      funext y
      by_cases hyC : y ∈ B0579.cell c
      · by_cases hyR : y.2 ∈ Icc (-R) R
        · have hyB : y ∈ B := ⟨hyC.1, hyR⟩
          simp [hyC, hyR, hyB]
        · have hyB : y ∉ B := fun h => hyR h.2
          simp [hyC, hyR, hyB]
      · have hyB : y ∉ B := fun h => hyC ⟨h.1, trivial⟩
        simp [hyC, hyB]
    rw [← integrable_indicator_iff (B0579.measurableSet_cell c), heq,
      integrable_indicator_iff (measurableSet_Ico.prod measurableSet_Icc)]
    exact integrableOn_const hB_fin.ne
  exact (memLp_two_iff_integrable_sq_norm hcs.aestronglyMeasurable).2
    (hint_ind.mono' (hcs.norm.pow 2).aestronglyMeasurable
      ((ae_restrict_iff' (B0579.measurableSet_cell c)).2
        (Eventually.of_forall fun y hy =>
          (Real.norm_of_nonneg (sq_nonneg _)).trans_le (hbd y hy))))

/-- Any jointly continuous `CProf` vanishing for `|y.2| > R` induces a continuous `L2Cell c` path. -/
lemma memLp_and_continuous_toLp_of_eta_vanish {c R : ℝ} (hc : 0 < c) (hR : 0 < R)
    {G : CProf} (hG_cont : Continuous G)
    (hG_eta : ∀ x : Coord, R < |x.2.2| → G x = 0) :
    (∀ s : ℝ, MemLp (F8U.slice G s) 2 (F8Sm.cellMeas c)) ∧
      Continuous (fun s : ℝ =>
        (memLp_slice_of_eta_vanish c hG_cont hG_eta s).toLp (F8U.slice G s)) := by
  have _ : 0 < c ∧ 0 < R := ⟨hc, hR⟩
  let hm : ∀ s : ℝ, MemLp (F8U.slice G s) 2 (F8Sm.cellMeas c) :=
    memLp_slice_of_eta_vanish c hG_cont hG_eta
  refine ⟨hm, continuous_iff_continuousAt.2 fun s₀ => ?_⟩
  rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
  let B : Set B0579.Plane := Ico (-(c / 2)) (c / 2) ×ˢ Icc (-R) R
  have hB_fin : volume B < ⊤ := by
    rw [Measure.volume_eq_prod, Measure.prod_prod, Real.volume_Ico, Real.volume_Icc]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top
  let K : Set Coord := Icc (s₀ - 1) (s₀ + 1) ×ˢ (Icc (-(c / 2)) (c / 2) ×ˢ Icc (-R) R)
  obtain ⟨M0, hM0⟩ := (isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)).exists_bound_of_continuousOn
    (s := K) hG_cont.continuousOn
  let M : ℝ := max 0 M0
  let dom : B0579.Plane → ℝ := fun y => (Icc (-R) R).indicator (fun _ => (2 * M) ^ 2) y.2
  have hdom_int : Integrable dom (F8Sm.cellMeas c) := by
    change IntegrableOn dom (B0579.cell c) volume
    have heq : (B0579.cell c).indicator dom = B.indicator (fun _ => (2 * M) ^ 2) := by
      funext y
      by_cases hyC : y ∈ B0579.cell c
      · by_cases hyR : y.2 ∈ Icc (-R) R
        · have hyB : y ∈ B := ⟨hyC.1, hyR⟩
          simp [dom, hyC, hyR, hyB]
        · have hyB : y ∉ B := fun h => hyR h.2
          simp [dom, hyC, hyR, hyB]
      · have hyB : y ∉ B := fun h => hyC ⟨h.1, trivial⟩
        simp [dom, hyC, hyB]
    rw [← integrable_indicator_iff (B0579.measurableSet_cell c), heq,
      integrable_indicator_iff (measurableSet_Ico.prod measurableSet_Icc)]
    exact integrableOn_const hB_fin.ne
  have hsq_lim : Tendsto
      (fun s => ∫ y, ‖G (s, y) - G (s₀, y)‖ ^ 2 ∂(F8Sm.cellMeas c)) (𝓝 s₀) (𝓝 0) := by
    have h0 : (0 : ℝ) = ∫ _ : B0579.Plane, (0 : ℝ) ∂(F8Sm.cellMeas c) := by simp
    rw [h0]
    refine tendsto_integral_filter_of_dominated_convergence dom
      (Eventually.of_forall fun s =>
        (((hG_cont.comp (continuous_const.prodMk continuous_id)).sub
          (hG_cont.comp (continuous_const.prodMk continuous_id))).norm.pow 2).aestronglyMeasurable)
      ?_ hdom_int (Eventually.of_forall fun y => ?_)
    · filter_upwards [Ioo_mem_nhds (by linarith : s₀ - 1 < s₀) (by linarith : s₀ < s₀ + 1)]
        with s hs
      rw [ae_restrict_iff' (B0579.measurableSet_cell c)]
      refine Eventually.of_forall fun y hyC => ?_
      rw [Real.norm_of_nonneg (sq_nonneg _)]
      by_cases hyR : y.2 ∈ Icc (-R) R
      · dsimp [dom]
        rw [indicator_of_mem hyR]
        have h1 : ‖G (s, y)‖ ≤ M :=
          (hM0 (s, y) ⟨⟨hs.1.le, hs.2.le⟩, ⟨hyC.1.1, hyC.1.2.le⟩, hyR⟩).trans (le_max_right 0 M0)
        have h2 : ‖G (s₀, y)‖ ≤ M :=
          (hM0 (s₀, y) ⟨⟨by linarith, by linarith⟩, ⟨hyC.1.1, hyC.1.2.le⟩, hyR⟩).trans
            (le_max_right 0 M0)
        have hsub : ‖G (s, y) - G (s₀, y)‖ ≤ 2 * M := by
          have := norm_sub_le (G (s, y)) (G (s₀, y))
          linarith
        exact pow_le_pow_left₀ (norm_nonneg _) hsub 2
      · have hgt : R < |y.2| := by
          by_contra hle; push Not at hle; exact hyR (abs_le.1 hle)
        dsimp [dom]
        rw [hG_eta (s, y) hgt, hG_eta (s₀, y) hgt, indicator_of_notMem hyR]
        simp
    · have hc_y : Continuous (fun s : ℝ => ‖G (s, y) - G (s₀, y)‖ ^ 2) :=
        (((hG_cont.comp (continuous_id.prodMk continuous_const)).sub
          continuous_const).norm.pow 2)
      simpa using hc_y.tendsto s₀
  have hsqrt_lim := (Real.continuous_sqrt.tendsto' 0 0 Real.sqrt_zero).comp hsq_lim
  refine hsqrt_lim.congr fun s => ?_
  let D : L2Cell c := (hm s).toLp (F8U.slice G s) - (hm s₀).toLp (F8U.slice G s₀)
  have hsq_eq : ∫ y, ‖G (s, y) - G (s₀, y)‖ ^ 2 ∂(F8Sm.cellMeas c) = ‖D‖ ^ 2 := by
    have hinn : inner ℂ D D =
        ∫ y, inner ℂ (G (s, y) - G (s₀, y)) (G (s, y) - G (s₀, y)) ∂(F8Sm.cellMeas c) := by
      rw [L2.inner_def (𝕜 := ℂ)]
      refine integral_congr_ae ?_
      filter_upwards [Lp.coeFn_sub ((hm s).toLp (F8U.slice G s))
          ((hm s₀).toLp (F8U.slice G s₀)),
        (hm s).coeFn_toLp, (hm s₀).coeFn_toLp] with y hsub h1 h2
      simp only [Pi.sub_apply] at hsub
      rw [hsub, h1, h2]; rfl
    have hre := congrArg Complex.re hinn
    have hself : (inner ℂ D D).re = ‖D‖ ^ 2 := by
      simpa only [RCLike.re_to_complex] using inner_self_eq_norm_sq (𝕜 := ℂ) D
    rw [hself] at hre
    have hint_DD : Integrable
        (fun y => inner ℂ (G (s, y) - G (s₀, y)) (G (s, y) - G (s₀, y))) (F8Sm.cellMeas c) :=
      (L2.integrable_inner (𝕜 := ℂ) D D).congr (by
        filter_upwards [Lp.coeFn_sub ((hm s).toLp (F8U.slice G s))
            ((hm s₀).toLp (F8U.slice G s₀)),
          (hm s).coeFn_toLp, (hm s₀).coeFn_toLp] with y hsub h1 h2
        simp only [Pi.sub_apply] at hsub
        rw [hsub, h1, h2]; rfl)
    have hre_comm :
        (∫ y, inner ℂ (G (s, y) - G (s₀, y)) (G (s, y) - G (s₀, y)) ∂(F8Sm.cellMeas c)).re =
          ∫ y, (inner ℂ (G (s, y) - G (s₀, y)) (G (s, y) - G (s₀, y))).re ∂(F8Sm.cellMeas c) :=
      (Complex.reCLM.integral_comp_comm hint_DD).symm
    rw [hre, hre_comm]
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    simpa only [RCLike.re_to_complex] using
      (inner_self_eq_norm_sq (𝕜 := ℂ) (G (s, y) - G (s₀, y))).symm
  change Real.sqrt (∫ y, ‖G (s, y) - G (s₀, y)‖ ^ 2 ∂(F8Sm.cellMeas c)) = ‖D‖
  rw [hsq_eq, Real.sqrt_sq (norm_nonneg D)]

lemma isCylTest_mul_periodic {c : ℝ} {a ψ : B0579.Plane → ℝ}
    (ha_sm : ContDiff ℝ ∞ a) (ha_per : UnforcedLeray.Cyl.IsPeriodic c a)
    (hψ : B0579.IsCylTest c ψ) :
    B0579.IsCylTest c (fun y => a y * ψ y) := by
  obtain ⟨R, hR⟩ := hψ.band
  refine ⟨ha_sm.mul hψ.smooth, fun y => ?_, ⟨R, fun y hy => by rw [hR y hy, mul_zero]⟩⟩
  rw [ha_per y, hψ.periodic y]

/-- Cell-slice LHS functional of the meridional Oseen equation paired against `qPeriodizeVec Ψ`. -/
def sliceLHSVal (p : Params) (Ψ : Coord → Fin 2 → ℝ) (s : ℝ) (X : X3 p.c) : ℂ :=
  (∑ i : Fin 2, ∫ y in B0579.cell p.c,
      X.1 y i * (TailPeriodizeAux.qPeriodize p.c (fun x => mtReal p.ν Ψ x i) s y : ℂ)) +
  (∑ i : Fin 2, ∫ y in B0579.cell p.c,
      bvTripleSlice (p.train.v s) X.1 X.2.1 X.2.2 y i *
        (TailPeriodizeAux.qPeriodize p.c (fun x => Ψ x i) s y : ℂ))

lemma perVecProf_eta_vanish {c R : ℝ} {α : Coord → Fin 2 → ℝ}
    (hα_eta : ∀ (i : Fin 2) (x : Coord), R < |x.2.2| → α x i = 0) :
    ∀ x : Coord, R < |x.2.2| → perVecProf c α x = 0 := by
  intro x hx
  ext i
  have hz : TailPeriodizeAux.qPeriodize c (fun z => α z i) x.1 x.2 = 0 := by
    unfold TailPeriodizeAux.qPeriodize
    have h0 : (fun k : ℤ => α (x.1, (x.2.1 + (k : ℝ) * c, x.2.2)) i) = fun _ => 0 :=
      funext fun k => hα_eta i (x.1, (x.2.1 + (k : ℝ) * c, x.2.2)) hx
    rw [h0, tsum_zero]
  fin_cases i <;>
    simpa [perVecProf, TailPeriodizeAux.qPeriodizeVec] using congrArg (Complex.ofReal) hz

lemma sum_integral_mul_qPeriodize_eq_inner {c : ℝ} (hc : 0 < c) {s : ℝ}
    {α : Coord → Fin 2 → ℝ} (hα : ∀ i : Fin 2, IsCoordTest (fun x => α x i))
    {U : B0579.Plane → CMerid} (hU : MemLp U 2 (F8Sm.cellMeas c))
    {hmG : MemLp (F8U.slice (perVecProf c α) s) 2 (F8Sm.cellMeas c)} :
    (∑ i : Fin 2, ∫ y in B0579.cell c,
        U y i * (TailPeriodizeAux.qPeriodize c (fun x => α x i) s y : ℂ)) =
      inner ℂ (hmG.toLp (F8U.slice (perVecProf c α) s)) (hU.toLp U) := by
  have hi : ∀ i : Fin 2, IntegrableOn
      (fun y => U y i * (TailPeriodizeAux.qPeriodize c (fun x => α x i) s y : ℂ))
      (B0579.cell c) volume := by
    intro i
    have ht := TailPeriodizeAux.isCylTest_qPeriodize hc (hα i) s
    have hm1 := F8Sm.memLp_coord_cmerid hU i
    have hm2 : MemLp (fun y => (TailPeriodizeAux.qPeriodize c (fun x => α x i) s y : ℂ))
        2 (F8Sm.cellMeas c) := by
      simpa [singleCylVec] using F8Sm.memLp_coord_cmerid (memLp_singleCylVec hc i ht) i
    exact hm1.integrable_mul hm2
  rw [Fin.sum_univ_two, ← integral_add (hi 0) (hi 1),
    ← F8Sm.integral_inner_eq_L2_inner hmG hU]
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  simp only [F8U.slice, perVecProf, TailPeriodizeAux.qPeriodizeVec, PiLp.inner_apply,
    Fin.sum_univ_two, RCLike.inner_apply, Complex.conj_ofReal]

private lemma stronglyMeasurable_pair_eta_vanish {c R : ℝ} (hc : 0 < c) (hR : 0 < R)
    (m : Fin 2) {H : Coord → ℝ} (hH_cont : Continuous H)
    (hH_eta : ∀ x : Coord, R < |x.2.2| → H x = 0)
    {U : ℝ × ℝ → L2Cell c} (hU : StronglyMeasurable U) :
    StronglyMeasurable (fun q : ℝ × ℝ =>
      ∫ y in B0579.cell c, U q y m * (H (q.1, y) : ℂ)) := by
  let G : CProf := fun x => WithLp.toLp 2 fun i : Fin 2 => if i = m then (H x : ℂ) else 0
  have hG_cont : Continuous G := by
    refine (PiLp.continuous_toLp 2 _).comp (continuous_pi fun i => ?_)
    by_cases him : i = m
    · simp only [him, ↓reduceIte]; exact Complex.continuous_ofReal.comp hH_cont
    · simp only [him, ↓reduceIte]; exact continuous_const
  have hG_eta : ∀ x : Coord, R < |x.2.2| → G x = 0 := fun x hx => by
    ext i; simp [G, hH_eta x hx]
  obtain ⟨hmG, hlpG_cont⟩ := memLp_and_continuous_toLp_of_eta_vanish hc hR hG_cont hG_eta
  let lpG : ℝ → L2Cell c := fun s => (hmG s).toLp (F8U.slice G s)
  have heq : (fun q : ℝ × ℝ => ∫ y in B0579.cell c, U q y m * (H (q.1, y) : ℂ)) =
      fun q => inner ℂ (lpG q.1) (U q) := by
    funext q
    rw [L2.inner_def (𝕜 := ℂ)]
    refine (integral_congr_ae ?_).symm
    filter_upwards [(hmG q.1).coeFn_toLp] with y hy
    rw [hy, PiLp.inner_apply, Fin.sum_univ_two]
    fin_cases m <;> simp [F8U.slice, G, RCLike.inner_apply]
  rw [heq]
  have hcont_in : Continuous (fun p : L2Cell c × L2Cell c => inner ℂ p.1 p.2) :=
    (contDiff_inner (𝕜 := ℂ) (E := L2Cell c) (n := 0)).continuous
  exact hcont_in.comp_stronglyMeasurable
    ((hlpG_cont.stronglyMeasurable.comp_measurable measurable_fst).prodMk hU)

/-- Representation of `sliceLHSVal p Ψ s` (`0 ≤ s`) as a continuous `ℝ`-linear functional on `X3`
together with uniform `h1RealNorm` boundedness and joint strong measurability in `(s, τ)`. -/
lemma sliceLHSVal_clm_and_fubini {dm dp : ℝ} {p : Params} {d : ℝ} (hreg : BgRegime p d dm dp)
    {Ψ : Coord → Fin 2 → ℝ} (hΨ : IsPlanarSolTest Ψ)
    {a'' b'' R : ℝ} (ha'' : 0 < a'') (hab'' : a'' ≤ b'') (hR : 0 < R)
    (hΨ_box : ∀ (i : Fin 2) (x : Coord), R < |x.2.2| →
      Ψ x i = 0 ∧ mtReal p.ν Ψ x i = 0) :
    (∀ s : ℝ, 0 ≤ s → ∃ L : X3 p.c →L[ℝ] ℂ, ∀ X : X3 p.c, sliceLHSVal p Ψ s X = L X) ∧
    (∃ C : ℝ, 0 ≤ C ∧ ∀ s ∈ Icc (0 : ℝ) (b'' + 2), ∀ X : X3 p.c,
      ‖sliceLHSVal p Ψ s X‖ ≤ C * h1RealNorm X) ∧
    (∀ {F : ℝ × ℝ → X3 p.c}, StronglyMeasurable F →
      StronglyMeasurable ((Icc a'' b'' ×ˢ (univ : Set ℝ)).indicator
        fun q : ℝ × ℝ => sliceLHSVal p Ψ q.1 (F q))) := by
  let Φ (i : Fin 2) (s : ℝ) (y : B0579.Plane) : ℝ :=
    TailPeriodizeAux.qPeriodize p.c (fun x => Ψ x i) s y
  let MT (i : Fin 2) (s : ℝ) (y : B0579.Plane) : ℝ :=
    TailPeriodizeAux.qPeriodize p.c (fun x => mtReal p.ν Ψ x i) s y
  have hMT_test_coord : ∀ i : Fin 2, IsCoordTest (fun x => mtReal p.ν Ψ x i) :=
    fun i => isCoordTest_mtReal p.ν hΨ i
  have hΦ_test : ∀ (i : Fin 2) (s : ℝ), B0579.IsCylTest p.c (Φ i s) :=
    fun i s => TailPeriodizeAux.isCylTest_qPeriodize p.c_pos (hΨ.smooth i) s
  have hMT_test : ∀ (i : Fin 2) (s : ℝ), B0579.IsCylTest p.c (MT i s) :=
    fun i s => TailPeriodizeAux.isCylTest_qPeriodize p.c_pos (hMT_test_coord i) s
  have hV_sm : ∀ {s : ℝ}, 0 ≤ s → ContDiff ℝ ∞ (p.train.v s) := by
    intro s hs
    exact contDiffOn_univ.1 (p.train.isTrain.smooth_v.comp
      (contDiff_const.prodMk contDiff_id).contDiffOn
      (fun y _ => ⟨mem_Ici.2 hs, mem_univ y⟩))
  have hV_per : ∀ {s : ℝ}, 0 ≤ s → ∀ k : Fin 2,
      UnforcedLeray.Cyl.IsPeriodic p.c (fun y => p.train.v s y k) :=
    fun hs k y => congrArg (· k) (p.train.isTrain.periodic_v _ hs y)
  have hdV_sm : ∀ {s : ℝ}, 0 ≤ s → ∀ (j k : Fin 2),
      ContDiff ℝ ∞ (fun y => fderiv ℝ (fun z => p.train.v s z k) y (B0579.dir j)) := by
    intro s hs j k
    have hc_vk : ContDiff ℝ ∞ (fun z => p.train.v s z k) :=
      (EuclideanSpace.proj k : UnforcedLeray.Train.Vec →L[ℝ] ℝ).contDiff.comp (hV_sm hs)
    exact ((contDiff_infty_iff_fderiv.1 hc_vk).2).clm_apply contDiff_const
  have hdV_per : ∀ {s : ℝ}, 0 ≤ s → ∀ (j k : Fin 2),
      UnforcedLeray.Cyl.IsPeriodic p.c
        (fun y => fderiv ℝ (fun z => p.train.v s z k) y (B0579.dir j)) := by
    intro s hs j k y
    let g : B0579.Plane → ℝ := fun z => p.train.v s z k
    have hg_sm : ContDiff ℝ ∞ g :=
      (EuclideanSpace.proj k : UnforcedLeray.Train.Vec →L[ℝ] ℝ).contDiff.comp (hV_sm hs)
    let v₀ : B0579.Plane := (p.c, 0)
    have hfn : (fun z : B0579.Plane => g (z + v₀)) = g := by
      funext z
      have hz : z + v₀ = (z.1 + p.c, z.2) := Prod.ext rfl (add_zero z.2)
      rw [hz]; exact hV_per hs k z
    have h1 := (hg_sm.contDiffAt.differentiableAt (by simp)).hasFDerivAt (x := y + v₀)
    have h2 := (hasFDerivAt_id (𝕜 := ℝ) y).add_const v₀
    have hc1 := h1.comp y h2
    have hy : y + v₀ = (y.1 + p.c, y.2) := Prod.ext rfl (add_zero y.2)
    rw [ContinuousLinearMap.comp_id, hy] at hc1
    change HasFDerivAt (fun z => g (z + v₀)) (fderiv ℝ g (y.1 + p.c, y.2)) y at hc1
    rw [hfn] at hc1
    exact congrArg (fun L => L (B0579.dir j)) hc1.fderiv.symm
  have hexp_bv : ∀ {s : ℝ}, 0 ≤ s → ∀ (X : X3 p.c) (i : Fin 2),
      (∫ y in B0579.cell p.c,
        bvTripleSlice (p.train.v s) X.1 X.2.1 X.2.2 y i * (Φ i s y : ℂ)) =
      (((∫ y in B0579.cell p.c, X.2.1 y i * ((p.train.v s y 0 * Φ i s y : ℝ) : ℂ)) +
        (∫ y in B0579.cell p.c, X.2.2 y i * ((p.train.v s y 1 * Φ i s y : ℝ) : ℂ))) +
        (∫ y in B0579.cell p.c, X.1 y 0 *
          ((fderiv ℝ (fun z => p.train.v s z i) y (B0579.dir 0) * Φ i s y : ℝ) : ℂ))) +
        (∫ y in B0579.cell p.c, X.1 y 1 *
          ((fderiv ℝ (fun z => p.train.v s z i) y (B0579.dir 1) * Φ i s y : ℝ) : ℂ)) := by
    intro s hs X i
    have ht_vq : B0579.IsCylTest p.c (fun y => p.train.v s y 0 * Φ i s y) :=
      isCylTest_mul_periodic
        ((EuclideanSpace.proj 0 : UnforcedLeray.Train.Vec →L[ℝ] ℝ).contDiff.comp (hV_sm hs))
        (hV_per hs 0) (hΦ_test i s)
    have ht_vη : B0579.IsCylTest p.c (fun y => p.train.v s y 1 * Φ i s y) :=
      isCylTest_mul_periodic
        ((EuclideanSpace.proj 1 : UnforcedLeray.Train.Vec →L[ℝ] ℝ).contDiff.comp (hV_sm hs))
        (hV_per hs 1) (hΦ_test i s)
    have ht_dq : ∀ j : Fin 2, B0579.IsCylTest p.c
        (fun y => fderiv ℝ (fun z => p.train.v s z i) y (B0579.dir j) * Φ i s y) :=
      fun j => isCylTest_mul_periodic (hdV_sm hs j i) (hdV_per hs j i) (hΦ_test i s)
    have i1 := integrableOn_coe_mul_cylTest p.c_pos X.2.1 i ht_vq
    have i2 := integrableOn_coe_mul_cylTest p.c_pos X.2.2 i ht_vη
    have i3 := integrableOn_coe_mul_cylTest p.c_pos X.1 0 (ht_dq 0)
    have i4 := integrableOn_coe_mul_cylTest p.c_pos X.1 1 (ht_dq 1)
    have i12 : IntegrableOn (fun y =>
        X.2.1 y i * ((p.train.v s y 0 * Φ i s y : ℝ) : ℂ) +
        X.2.2 y i * ((p.train.v s y 1 * Φ i s y : ℝ) : ℂ)) (B0579.cell p.c) volume := i1.add i2
    have i123 : IntegrableOn (fun y =>
        (X.2.1 y i * ((p.train.v s y 0 * Φ i s y : ℝ) : ℂ) +
         X.2.2 y i * ((p.train.v s y 1 * Φ i s y : ℝ) : ℂ)) +
        X.1 y 0 * ((fderiv ℝ (fun z => p.train.v s z i) y (B0579.dir 0) * Φ i s y : ℝ) : ℂ))
        (B0579.cell p.c) volume := i12.add i3
    rw [← integral_add i1 i2, ← integral_add i12 i3, ← integral_add i123 i4]
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    simp only [bvTripleSlice, B0579.dir, Complex.ofReal_mul]
    fin_cases i <;> dsimp <;> ring
  have hclm : ∀ s : ℝ, 0 ≤ s → ∃ L : X3 p.c →L[ℝ] ℂ,
      ∀ X : X3 p.c, sliceLHSVal p Ψ s X = L X := by
    intro s hs
    let p1 : X3 p.c →L[ℝ] L2Cell p.c :=
      ContinuousLinearMap.fst ℝ (L2Cell p.c) (L2Cell p.c × L2Cell p.c)
    let p21 : X3 p.c →L[ℝ] L2Cell p.c :=
      (ContinuousLinearMap.fst ℝ (L2Cell p.c) (L2Cell p.c)).comp
        (ContinuousLinearMap.snd ℝ (L2Cell p.c) (L2Cell p.c × L2Cell p.c))
    let p22 : X3 p.c →L[ℝ] L2Cell p.c :=
      (ContinuousLinearMap.snd ℝ (L2Cell p.c) (L2Cell p.c)).comp
        (ContinuousLinearMap.snd ℝ (L2Cell p.c) (L2Cell p.c × L2Cell p.c))
    have ht_vq : ∀ i : Fin 2, B0579.IsCylTest p.c (fun y => p.train.v s y 0 * Φ i s y) :=
      fun i => isCylTest_mul_periodic
        ((EuclideanSpace.proj 0 : UnforcedLeray.Train.Vec →L[ℝ] ℝ).contDiff.comp (hV_sm hs))
        (hV_per hs 0) (hΦ_test i s)
    have ht_vη : ∀ i : Fin 2, B0579.IsCylTest p.c (fun y => p.train.v s y 1 * Φ i s y) :=
      fun i => isCylTest_mul_periodic
        ((EuclideanSpace.proj 1 : UnforcedLeray.Train.Vec →L[ℝ] ℝ).contDiff.comp (hV_sm hs))
        (hV_per hs 1) (hΦ_test i s)
    have ht_dq : ∀ (j i : Fin 2), B0579.IsCylTest p.c
        (fun y => fderiv ℝ (fun z => p.train.v s z i) y (B0579.dir j) * Φ i s y) :=
      fun j i => isCylTest_mul_periodic (hdV_sm hs j i) (hdV_per hs j i) (hΦ_test i s)
    let L : X3 p.c →L[ℝ] ℂ :=
      ((pairTestCLM p.c_pos (hMT_test 0 s) 0).comp p1 +
       (pairTestCLM p.c_pos (hMT_test 1 s) 1).comp p1) +
      (((pairTestCLM p.c_pos (ht_vq 0) 0).comp p21 +
        (pairTestCLM p.c_pos (ht_vη 0) 0).comp p22 +
        (pairTestCLM p.c_pos (ht_dq 0 0) 0).comp p1 +
        (pairTestCLM p.c_pos (ht_dq 1 0) 1).comp p1) +
       ((pairTestCLM p.c_pos (ht_vq 1) 1).comp p21 +
        (pairTestCLM p.c_pos (ht_vη 1) 1).comp p22 +
        (pairTestCLM p.c_pos (ht_dq 0 1) 0).comp p1 +
        (pairTestCLM p.c_pos (ht_dq 1 1) 1).comp p1))
    refine ⟨L, fun X => ?_⟩
    simp only [sliceLHSVal, L, p1, p21, p22, add_apply, ContinuousLinearMap.comp_apply,
      Fin.sum_univ_two, pairTestCLM_apply]
    dsimp [MT, Φ] at hexp_bv ⊢
    linear_combination (hexp_bv hs X 0) + (hexp_bv hs X 1)
  have hΦ_prof_sm := (contDiff_and_derivs_perVecProf p.c_pos hΨ.smooth).1
  have hMT_prof_sm := (contDiff_and_derivs_perVecProf p.c_pos hMT_test_coord).1
  obtain ⟨hmΦ, hlpΦ_cont⟩ := memLp_and_continuous_toLp_of_eta_vanish p.c_pos hR
    hΦ_prof_sm.continuous (perVecProf_eta_vanish fun i x hx => (hΨ_box i x hx).1)
  obtain ⟨hmMT, hlpMT_cont⟩ := memLp_and_continuous_toLp_of_eta_vanish p.c_pos hR
    hMT_prof_sm.continuous (perVecProf_eta_vanish fun i x hx => (hΨ_box i x hx).2)
  refine ⟨hclm, ?_, fun {F} hF_sm => ?_⟩
  · have hT_nn : 0 ≤ b'' + 2 := by linarith
    obtain ⟨M_tr, hM_tr, hV_s, _, hb0, hb1⟩ := uniform_train_C1 hreg (T := b'' + 2) hT_nn
    obtain ⟨MΦ0, hMΦ0⟩ := isCompact_Icc.exists_bound_of_continuousOn
      (s := Icc (0 : ℝ) (b'' + 2)) hlpΦ_cont.continuousOn
    obtain ⟨MMT0, hMMT0⟩ := isCompact_Icc.exists_bound_of_continuousOn
      (s := Icc (0 : ℝ) (b'' + 2)) hlpMT_cont.continuousOn
    let MΦ : ℝ := max 0 MΦ0
    let MMT : ℝ := max 0 MMT0
    have hMΦ_nn : 0 ≤ MΦ := le_max_left 0 MΦ0
    have hMMT_nn : 0 ≤ MMT := le_max_left 0 MMT0
    let C : ℝ := MMT + 4 * MΦ * M_tr
    refine ⟨C, by positivity, fun s hs X => ?_⟩
    obtain ⟨hm_bv, hbv_le⟩ := memLp_and_cellL2_bvTripleSlice hM_tr (hV_s s hs) (hb0 s hs)
      (hb1 s hs) (Lp.memLp X.1) (Lp.memLp X.2.1) (Lp.memLp X.2.2)
    have htr_norm : ∀ u : L2Cell p.c, (F8U.cellL2 p.c u).toReal = ‖u‖ := fun u => by
      rw [cellL2_coe_eq_ofReal_norm, ENNReal.toReal_ofReal (norm_nonneg u)]
    rw [htr_norm X.1, htr_norm X.2.1, htr_norm X.2.2] at hbv_le
    have hbv_norm : ‖hm_bv.toLp (bvTripleSlice (p.train.v s) X.1 X.2.1 X.2.2)‖ ≤
        4 * M_tr * h1RealNorm X := by
      rw [F8Sm.norm_toLp_eq_cellL2 hm_bv]
      refine hbv_le.trans ?_
      unfold h1RealNorm
      nlinarith [norm_nonneg X.1, norm_nonneg X.2.1, norm_nonneg X.2.2]
    have hto_X1 : (Lp.memLp X.1).toLp X.1 = X.1 := Lp.ext_iff.2 (Lp.memLp X.1).coeFn_toLp
    have hs1 := sum_integral_mul_qPeriodize_eq_inner p.c_pos hMT_test_coord
      (Lp.memLp X.1) (hmG := hmMT s)
    have hs2 := sum_integral_mul_qPeriodize_eq_inner p.c_pos hΨ.smooth hm_bv (hmG := hmΦ s)
    unfold sliceLHSVal
    rw [hs1, hs2, hto_X1]
    have b1 : ‖inner ℂ ((hmMT s).toLp (F8U.slice (perVecProf p.c (mtReal p.ν Ψ)) s)) X.1‖ ≤
        MMT * h1RealNorm X := by
      calc ‖inner ℂ ((hmMT s).toLp (F8U.slice (perVecProf p.c (mtReal p.ν Ψ)) s)) X.1‖
          ≤ ‖(hmMT s).toLp (F8U.slice (perVecProf p.c (mtReal p.ν Ψ)) s)‖ * ‖X.1‖ :=
            norm_inner_le_norm _ _
        _ ≤ MMT * ‖X.1‖ :=
            mul_le_mul_of_nonneg_right ((hMMT0 s hs).trans (le_max_right 0 MMT0)) (norm_nonneg _)
        _ ≤ MMT * h1RealNorm X := by
            refine mul_le_mul_of_nonneg_left ?_ hMMT_nn
            unfold h1RealNorm
            linarith [norm_nonneg X.2.1, norm_nonneg X.2.2]
    have b2 : ‖inner ℂ ((hmΦ s).toLp (F8U.slice (perVecProf p.c Ψ) s))
          (hm_bv.toLp (bvTripleSlice (p.train.v s) X.1 X.2.1 X.2.2))‖ ≤
        MΦ * (4 * M_tr * h1RealNorm X) := by
      calc ‖inner ℂ ((hmΦ s).toLp (F8U.slice (perVecProf p.c Ψ) s))
              (hm_bv.toLp (bvTripleSlice (p.train.v s) X.1 X.2.1 X.2.2))‖
          ≤ ‖(hmΦ s).toLp (F8U.slice (perVecProf p.c Ψ) s)‖ *
              ‖hm_bv.toLp (bvTripleSlice (p.train.v s) X.1 X.2.1 X.2.2)‖ :=
            norm_inner_le_norm _ _
        _ ≤ MΦ * (4 * M_tr * h1RealNorm X) :=
            mul_le_mul ((hMΦ0 s hs).trans (le_max_right 0 MΦ0)) hbv_norm
              (norm_nonneg _) hMΦ_nn
    refine (norm_add_le _ _).trans ?_
    dsimp [C]
    linarith
  · let clamp (s : ℝ) : ℝ := max a'' (min b'' s)
    have hclamp_cont : Continuous clamp :=
      continuous_const.max (continuous_const.min continuous_id)
    have hclamp_pos : ∀ s : ℝ, 0 < clamp s := fun s => lt_of_lt_of_le ha'' (le_max_left _ _)
    have hclamp_eq : ∀ {s : ℝ}, s ∈ Icc a'' b'' → clamp s = s := fun hs => by
      dsimp [clamp]
      rw [min_eq_right hs.2, max_eq_right hs.1]
    let clCoord (x : Coord) : Coord := (clamp x.1, x.2)
    have hcl_cont : Continuous clCoord := (hclamp_cont.comp continuous_fst).prodMk continuous_snd
    have hΦ_coord_cont : ∀ i : Fin 2, Continuous (fun x : Coord => Φ i x.1 x.2) := by
      intro i
      have heq : (fun x : Coord => Φ i x.1 x.2) =
          fun x => (perVecProf p.c Ψ x i).re := by
        funext x; simp [Φ, perVecProf, TailPeriodizeAux.qPeriodizeVec]
      rw [heq]
      exact Complex.continuous_re.comp
        ((EuclideanSpace.proj i : CMerid →L[ℂ] ℂ).continuous.comp hΦ_prof_sm.continuous)
    have hMT_coord_cont : ∀ i : Fin 2, Continuous (fun x : Coord => MT i x.1 x.2) := by
      intro i
      have heq : (fun x : Coord => MT i x.1 x.2) =
          fun x => (perVecProf p.c (mtReal p.ν Ψ) x i).re := by
        funext x; simp [MT, perVecProf, TailPeriodizeAux.qPeriodizeVec]
      rw [heq]
      exact Complex.continuous_re.comp
        ((EuclideanSpace.proj i : CMerid →L[ℂ] ℂ).continuous.comp hMT_prof_sm.continuous)
    have hΦ_eta : ∀ (i : Fin 2) (x : Coord), R < |x.2.2| → Φ i x.1 x.2 = 0 := by
      intro i x hx
      have h0 := perVecProf_eta_vanish (c := p.c) (fun k z hz => (hΨ_box k z hz).1) x hx
      simpa [Φ, perVecProf, TailPeriodizeAux.qPeriodizeVec] using
        congrArg (fun v : CMerid => (v i).re) h0
    have hMT_eta : ∀ (i : Fin 2) (x : Coord), R < |x.2.2| → MT i x.1 x.2 = 0 := by
      intro i x hx
      have h0 := perVecProf_eta_vanish (c := p.c) (fun k z hz => (hΨ_box k z hz).2) x hx
      simpa [MT, perVecProf, TailPeriodizeAux.qPeriodizeVec] using
        congrArg (fun v : CMerid => (v i).re) h0
    have hv_cl_cont : ∀ k : Fin 2,
        Continuous (fun x : Coord => p.train.v (clamp x.1) x.2 k) := fun k =>
      (EuclideanSpace.proj k : UnforcedLeray.Train.Vec →L[ℝ] ℝ).continuous.comp
        (p.train.isTrain.smooth_v.continuousOn.comp_continuous hcl_cont
          fun x => ⟨mem_Ici.2 (hclamp_pos x.1).le, trivial⟩)
    let Upos : Set Coord := Ioi (0 : ℝ) ×ˢ univ
    have hUpos_open : IsOpen Upos := isOpen_Ioi.prod isOpen_univ
    have hdv_cl_cont : ∀ (j i : Fin 2),
        Continuous (fun x : Coord =>
          fderiv ℝ (fun z => p.train.v (clamp x.1) z i) x.2 (B0579.dir j)) := by
      intro j i
      let vi : Coord → ℝ := fun x => p.train.v x.1 x.2 i
      have hvi_sm : ContDiffOn ℝ ∞ vi Upos :=
        (EuclideanSpace.proj i : UnforcedLeray.Train.Vec →L[ℝ] ℝ).contDiff.comp_contDiffOn
          (p.train.isTrain.smooth_v.mono (prod_mono_left Ioi_subset_Ici_self))
      have hdvi_cont : ContinuousOn (fun x : Coord => fderiv ℝ vi x (0, B0579.dir j)) Upos := by
        intro x hx
        exact (((hvi_sm.contDiffAt (hUpos_open.mem_nhds hx)).fderiv_right
          (m := ∞) (by simp)).clm_apply contDiffAt_const).continuousAt.continuousWithinAt
      have heq_fd : (fun x : Coord =>
            fderiv ℝ (fun z => p.train.v (clamp x.1) z i) x.2 (B0579.dir j)) =
          fun x => fderiv ℝ vi (clCoord x) (0, B0579.dir j) := by
        funext x
        have hs_pos : 0 < clamp x.1 := hclamp_pos x.1
        have hfa : DifferentiableAt ℝ vi (clamp x.1, x.2) :=
          (hvi_sm.contDiffAt
            (hUpos_open.mem_nhds (show (clamp x.1, x.2) ∈ Upos from ⟨hs_pos, trivial⟩))).differentiableAt
            (by simp)
        have hin : HasFDerivAt (fun z : B0579.Plane => (clamp x.1, z))
            ((0 : B0579.Plane →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ B0579.Plane)) x.2 :=
          (hasFDerivAt_const (clamp x.1) x.2).prodMk (hasFDerivAt_id x.2)
        change fderiv ℝ (vi ∘ Prod.mk (clamp x.1)) x.2 (B0579.dir j) = _
        rw [(hfa.hasFDerivAt.comp x.2 hin).fderiv]
        rfl
      rw [heq_fd]
      exact hdvi_cont.comp_continuous hcl_cont fun x => ⟨hclamp_pos x.1, trivial⟩
    have hF1 : StronglyMeasurable (fun q : ℝ × ℝ => (F q).1) :=
      (ContinuousLinearMap.fst ℝ (L2Cell p.c) (L2Cell p.c × L2Cell p.c)).continuous.comp_stronglyMeasurable hF_sm
    have hF21 : StronglyMeasurable (fun q : ℝ × ℝ => (F q).2.1) :=
      ((ContinuousLinearMap.fst ℝ (L2Cell p.c) (L2Cell p.c)).comp
        (ContinuousLinearMap.snd ℝ (L2Cell p.c) (L2Cell p.c × L2Cell p.c))).continuous.comp_stronglyMeasurable hF_sm
    have hF22 : StronglyMeasurable (fun q : ℝ × ℝ => (F q).2.2) :=
      ((ContinuousLinearMap.snd ℝ (L2Cell p.c) (L2Cell p.c)).comp
        (ContinuousLinearMap.snd ℝ (L2Cell p.c) (L2Cell p.c × L2Cell p.c))).continuous.comp_stronglyMeasurable hF_sm
    have sm_mt : ∀ i : Fin 2, StronglyMeasurable (fun q : ℝ × ℝ =>
        ∫ y in B0579.cell p.c, (F q).1 y i * (MT i q.1 y : ℂ)) :=
      fun i => stronglyMeasurable_pair_eta_vanish p.c_pos hR i (hMT_coord_cont i) (hMT_eta i) hF1
    have sm_vq : ∀ i : Fin 2, StronglyMeasurable (fun q : ℝ × ℝ =>
        ∫ y in B0579.cell p.c, (F q).2.1 y i *
          ((p.train.v (clamp q.1) y 0 * Φ i q.1 y : ℝ) : ℂ)) :=
      fun i => stronglyMeasurable_pair_eta_vanish p.c_pos hR i
        ((hv_cl_cont 0).mul (hΦ_coord_cont i))
        (fun x hx => by simp [hΦ_eta i x hx]) hF21
    have sm_vη : ∀ i : Fin 2, StronglyMeasurable (fun q : ℝ × ℝ =>
        ∫ y in B0579.cell p.c, (F q).2.2 y i *
          ((p.train.v (clamp q.1) y 1 * Φ i q.1 y : ℝ) : ℂ)) :=
      fun i => stronglyMeasurable_pair_eta_vanish p.c_pos hR i
        ((hv_cl_cont 1).mul (hΦ_coord_cont i))
        (fun x hx => by simp [hΦ_eta i x hx]) hF22
    have sm_dq : ∀ (j i : Fin 2), StronglyMeasurable (fun q : ℝ × ℝ =>
        ∫ y in B0579.cell p.c, (F q).1 y j *
          ((fderiv ℝ (fun z => p.train.v (clamp q.1) z i) y (B0579.dir j) * Φ i q.1 y : ℝ) : ℂ)) :=
      fun j i => stronglyMeasurable_pair_eta_vanish p.c_pos hR j
        ((hdv_cl_cont j i).mul (hΦ_coord_cont i))
        (fun x hx => by simp [hΦ_eta i x hx]) hF1
    let LHS_cl (q : ℝ × ℝ) : ℂ :=
      ((∫ y in B0579.cell p.c, (F q).1 y 0 * (MT 0 q.1 y : ℂ)) +
       (∫ y in B0579.cell p.c, (F q).1 y 1 * (MT 1 q.1 y : ℂ))) +
      (((((∫ y in B0579.cell p.c, (F q).2.1 y 0 *
            ((p.train.v (clamp q.1) y 0 * Φ 0 q.1 y : ℝ) : ℂ)) +
          (∫ y in B0579.cell p.c, (F q).2.2 y 0 *
            ((p.train.v (clamp q.1) y 1 * Φ 0 q.1 y : ℝ) : ℂ))) +
          (∫ y in B0579.cell p.c, (F q).1 y 0 *
            ((fderiv ℝ (fun z => p.train.v (clamp q.1) z 0) y (B0579.dir 0) * Φ 0 q.1 y : ℝ) : ℂ))) +
          (∫ y in B0579.cell p.c, (F q).1 y 1 *
            ((fderiv ℝ (fun z => p.train.v (clamp q.1) z 0) y (B0579.dir 1) * Φ 0 q.1 y : ℝ) : ℂ))) +
       ((((∫ y in B0579.cell p.c, (F q).2.1 y 1 *
            ((p.train.v (clamp q.1) y 0 * Φ 1 q.1 y : ℝ) : ℂ)) +
          (∫ y in B0579.cell p.c, (F q).2.2 y 1 *
            ((p.train.v (clamp q.1) y 1 * Φ 1 q.1 y : ℝ) : ℂ))) +
          (∫ y in B0579.cell p.c, (F q).1 y 0 *
            ((fderiv ℝ (fun z => p.train.v (clamp q.1) z 1) y (B0579.dir 0) * Φ 1 q.1 y : ℝ) : ℂ))) +
          (∫ y in B0579.cell p.c, (F q).1 y 1 *
            ((fderiv ℝ (fun z => p.train.v (clamp q.1) z 1) y (B0579.dir 1) * Φ 1 q.1 y : ℝ) : ℂ))))
    have hLHS_cl_sm : StronglyMeasurable LHS_cl :=
      ((sm_mt 0).add (sm_mt 1)).add
        (((((sm_vq 0).add (sm_vη 0)).add (sm_dq 0 0)).add (sm_dq 1 0)).add
         ((((sm_vq 1).add (sm_vη 1)).add (sm_dq 0 1)).add (sm_dq 1 1)))
    have hind_eq : ((Icc a'' b'' ×ˢ (univ : Set ℝ)).indicator
          fun q : ℝ × ℝ => sliceLHSVal p Ψ q.1 (F q)) =
        (Icc a'' b'' ×ˢ (univ : Set ℝ)).indicator LHS_cl := by
      funext q
      by_cases hq : q ∈ Icc a'' b'' ×ˢ (univ : Set ℝ)
      · rw [indicator_of_mem hq, indicator_of_mem hq]
        have hq1_nn : 0 ≤ q.1 := (lt_of_lt_of_le ha'' hq.1.1).le
        dsimp only [sliceLHSVal, LHS_cl]
        simp only [Fin.sum_univ_two, hclamp_eq hq.1]
        congr 1
        rw [hexp_bv hq1_nn (F q) 0, hexp_bv hq1_nn (F q) 1]
      · simp [hq]
    rw [hind_eq]
    exact hLHS_cl_sm.indicator (measurableSet_Icc.prod MeasurableSet.univ)

/-- Unified single-orbit FTC on `(τ, b'']` (`0 ≤ τ < b'' ≤ τ + 1`, `b' < b''`): works identically
both for the initial orbit (`τ = σ`, `v = x0`) and for every forcing slice (`τ ∈ (σ, b'')`, `v = fp τ`). -/
lemma single_orbit_ftc {dm dp : ℝ} {p : Params} {d A : ℝ}
    (hA : 0 < A) (hreg : BgRegime p d dm dp) (hflow : F8U.CylOseenFlowBound A p)
    {Ψ : Coord → Fin 2 → ℝ} (hΨ : IsPlanarSolTest Ψ)
    {b' b'' R : ℝ} (hb' : b' < b'') (hR : 0 < R)
    (hΨ_hi : ∀ (i : Fin 2) (x : Coord), b' < x.1 → Ψ x i = 0)
    (hΨ_eta : ∀ (i : Fin 2) (x : Coord), R < |x.2.2| →
      Ψ x i = 0 ∧ mtReal p.ν Ψ x i = 0)
    {τ : ℝ} (hτ : 0 ≤ τ) (hτb'' : τ < b'') (hb''1 : b'' ≤ τ + 1)
    {v : X3 p.c} (hv : v ∈ H1Set p.c) :
    IntegrableOn (fun s => sliceLHSVal p Ψ s (S0Val hflow s τ v)) (Ioc τ b'') volume ∧
      (∫ s in Ioc τ b'', sliceLHSVal p Ψ s (S0Val hflow s τ v)) =
        ∑ i : Fin 2, ∫ y in B0579.cell p.c,
          v.1 y i * (TailPeriodizeAux.qPeriodize p.c (fun x => Ψ x i) τ y : ℂ) := by
  let Φ : CProf := perVecProf p.c Ψ
  let Ψs : Coord → Fin 2 → ℝ := fun x i => cpd 0 (fun y => Ψ y i) x
  let Φs : CProf := perVecProf p.c Ψs
  obtain ⟨hΦ_sm, hΦ_ps, hΦ_pd⟩ := contDiff_and_derivs_perVecProf p.c_pos hΨ.smooth
  have hΦ_sm' : ContDiff ℝ ∞ Φ := hΦ_sm
  have hΨs_test : ∀ i : Fin 2, IsCoordTest (fun x => Ψs x i) :=
    fun i => isCoordTest_cpd (hΨ.smooth i) 0
  have hΦs_sm : ContDiff ℝ ∞ Φs := (contDiff_and_derivs_perVecProf p.c_pos hΨs_test).1
  have hΨs_eta : ∀ (i : Fin 2) (x : Coord), R < |x.2.2| → Ψs x i = 0 := by
    intro i x hx
    have hev : (fun y : Coord => Ψ y i) =ᶠ[𝓝 x] 0 := by
      filter_upwards [(isOpen_lt continuous_const (continuous_snd.comp continuous_snd).abs).mem_nhds hx]
        with y hy
      exact (hΨ_eta i y hy).1
    change fderiv ℝ (fun y => Ψ y i) x (cdir 0) = 0
    rw [hev.fderiv_eq]; simp
  have hΦ_eta : ∀ x : Coord, R < |x.2.2| → Φ x = 0 :=
    perVecProf_eta_vanish fun i x hx => (hΨ_eta i x hx).1
  have hΦs_eta : ∀ x : Coord, R < |x.2.2| → Φs x = 0 :=
    perVecProf_eta_vanish hΨs_eta
  let hmΦ : ∀ s : ℝ, MemLp (F8U.slice Φ s) 2 (F8Sm.cellMeas p.c) :=
    memLp_slice_of_eta_vanish p.c hΦ_sm'.continuous hΦ_eta
  let hmΦs : ∀ s : ℝ, MemLp (F8U.slice Φs s) 2 (F8Sm.cellMeas p.c) :=
    memLp_slice_of_eta_vanish p.c hΦs_sm.continuous hΦs_eta
  let lpΦ : ℝ → L2Cell p.c := fun s => (hmΦ s).toLp (F8U.slice Φ s)
  let lpΦs : ℝ → L2Cell p.c := fun s => (hmΦs s).toLp (F8U.slice Φs s)
  have hlpΦ_cont : Continuous lpΦ :=
    (memLp_and_continuous_toLp_of_eta_vanish p.c_pos hR hΦ_sm'.continuous hΦ_eta).2
  have hlpΦs_cont : Continuous lpΦs :=
    (memLp_and_continuous_toLp_of_eta_vanish p.c_pos hR hΦs_sm.continuous hΦs_eta).2
  have hderiv_Φ : ∀ s ∈ Ioo τ (τ + 2), HasDerivAt lpΦ (lpΦs s) s := by
    intro s hs
    have hms' : MemLp (F8U.slice (F8U.ps Φ) s) 2 (F8Sm.cellMeas p.c) := hΦ_ps.symm ▸ hmΦs s
    have hfs_cont : Tendsto
        (fun t => F8U.cellL2 p.c (fun y => F8U.ps Φ (t, y) - F8U.ps Φ (s, y)))
        (𝓝 s) (𝓝 0) := by
      have hn : Tendsto (fun t => ENNReal.ofReal ‖lpΦs t - lpΦs s‖) (𝓝 s) (𝓝 0) := by
        rw [← ENNReal.ofReal_zero]
        exact ENNReal.continuous_ofReal.continuousAt.tendsto.comp
          (tendsto_iff_norm_sub_tendsto_zero.1 hlpΦs_cont.continuousAt)
      refine hn.congr fun t => ?_
      rw [← cellL2_coe_eq_ofReal_norm, hΦ_ps]
      refine eLpNorm_congr_ae ?_
      filter_upwards [Lp.coeFn_sub (lpΦs t) (lpΦs s), (hmΦs t).coeFn_toLp, (hmΦs s).coeFn_toLp]
        with y hsub h1 h2
      simp only [Pi.sub_apply] at hsub ⊢
      rw [hsub, h1, h2]; rfl
    have hd := hasDerivAt_sliceLpOn (c := p.c) (τ := τ) (T := τ + 2)
      hΦ_sm.contDiffOn (fun r _ => hmΦ r) hms' hfs_cont hs
    have hto_eq : hms'.toLp (F8U.slice (F8U.ps Φ) s) = lpΦs s := by
      apply Lp.ext_iff.2
      filter_upwards [hms'.coeFn_toLp, (hmΦs s).coeFn_toLp] with y hy1 hy2
      rw [hy1, hy2, hΦ_ps]
    rw [hto_eq] at hd
    refine hd.congr_of_eventuallyEq ?_
    filter_upwards [isOpen_Ioo.mem_nhds hs] with r hr
    exact (sliceLpOn_of_mem (fun t _ => hmΦ t) hr).symm
  let W : CProf := orbitOf hflow τ v
  have hW : F8U.IsCylOseenOrbit p τ W v.1 v.2.1 v.2.2 := isCylOseenOrbit_orbitOf hflow hτ hv
  let hmW : ∀ s ∈ Ioo τ (τ + 2), MemLp (F8U.slice W s) 2 (F8Sm.cellMeas p.c) :=
    fun s hs => orbit_memLp_0 hW hs
  let hmsW : ∀ s ∈ Ioo τ (τ + 2), MemLp (F8U.slice (F8U.ps W) s) 2 (F8Sm.cellMeas p.c) :=
    fun s hs => hW.memL2_s s hs 0 (by decide) ![]
  let lw : ℝ → L2Cell p.c := sliceLpOn W hmW
  have hlw_eq : ∀ {s : ℝ}, s ∈ Ioo τ (τ + 2) → lw s = (S0Val hflow s τ v).1 := by
    intro s hs
    dsimp only [lw]
    rw [sliceLpOn_of_mem hmW hs, S0Val_of_cond hflow hτ hs hv]
  have hlw_cont : ContinuousOn lw (Ioo τ (τ + 2)) :=
    (continuous_fst.comp_continuousOn (continuousOn_S0Val_and_SD2Val_left hflow hτ hv).1).congr
      fun s hs => hlw_eq hs
  have hlw_ps_cont : ContinuousOn
      (UnforcedLeray.BochnerTime.toPathLq 2 (F8Sm.cellMeas p.c) (F8U.ps W)) (Ioo τ (τ + 2)) :=
    F8Duh.continuousOn_toPathLq_of_cellL2 hmsW (fun s hs => hW.cont_s s hs 0 (by decide) ![])
  have hderiv_W : ∀ s (hs : s ∈ Ioo τ (τ + 2)),
      HasDerivAt lw ((hmsW s hs).toLp (F8U.slice (F8U.ps W) s)) s :=
    fun s hs => hasDerivAt_sliceLpOn hW.smooth hmW (hmsW s hs)
      (hW.cont_s s hs 0 (by decide) ![]) hs
  obtain ⟨M_tr, hM_tr, hV_s, _, hb0_tr, hb1_tr⟩ :=
    uniform_train_C1 hreg (T := τ + 2) (by linarith)
  -- Pointwise derivative identity on `Ioo τ (τ + 2)` via `hW.projected` and double cell IBP
  have hg'_ident : ∀ s (hs : s ∈ Ioo τ (τ + 2)),
      inner ℂ (lpΦ s) ((hmsW s hs).toLp (F8U.slice (F8U.ps W) s)) +
          inner ℂ (lpΦs s) (lw s) =
        - sliceLHSVal p Ψ s (S0Val hflow s τ v) := by
    intro s hs
    have hs_icc : s ∈ Icc (0 : ℝ) (τ + 2) := ⟨by linarith [hs.1], hs.2.le⟩
    have hΦ_s_sm : ContDiff ℝ ∞ (F8U.slice Φ s) := F8Sm.contDiff_slice hΦ_sm.contDiffOn hs
    have hΦ_s_per : UnforcedLeray.Cyl.IsPeriodic p.c (F8U.slice Φ s) := fun y => by
      ext i
      simpa [F8U.slice, Φ, perVecProf, TailPeriodizeAux.qPeriodizeVec] using
        congrArg Complex.ofReal (TailPeriodizeAux.qPeriodize_periodic (fun x => Ψ x i) s y)
    have hΦ_sol : F8U.IsCellSolenoidal p.c (F8U.slice Φ s) := by
      refine F8Sm.isCellSolenoidal_of_div_free p.c_pos hΦ_s_sm hΦ_s_per fun y => ?_
      rw [F8Sm.pdir_slice_eq hΦ_sm.contDiffOn hs 0, F8Sm.pdir_slice_eq hΦ_sm.contDiffOn hs 1,
        hΦ_pd 0, hΦ_pd 1]
      have hdiv := (TailPeriodizeAux.isDivFreeTestField_qPeriodizeVec p.c_pos hΨ s).2 y
      change B0579.pd 0 (TailPeriodizeAux.qPeriodize p.c (fun x => Ψ x 0) s) y +
          B0579.pd 1 (TailPeriodizeAux.qPeriodize p.c (fun x => Ψ x 1) s) y = 0 at hdiv
      rw [TailPeriodizeAux.pd_qPeriodize p.c_pos (hΨ.smooth 0) s 0 y,
        TailPeriodizeAux.pd_qPeriodize p.c_pos (hΨ.smooth 1) s 1 y] at hdiv
      simpa [F8U.slice, perVecProf, TailPeriodizeAux.qPeriodizeVec, ← Complex.ofReal_add] using
        congrArg Complex.ofReal hdiv
    have hproj := hW.projected s hs (F8U.slice Φ s) (hmΦ s) hΦ_sol
    have hm_bv := (memLp_and_cellL2_bvTripleSlice hM_tr (hV_s s hs_icc)
      (hb0_tr s hs_icc) (hb1_tr s hs_icc) (orbit_memLp_0 hW hs)
      (orbit_memLp_1 hW hs 0) (orbit_memLp_1 hW hs 1)).1
    have hm_d00 := orbit_memLp_2 hW hs 0 0
    have hm_d11 := orbit_memLp_2 hW hs 1 1
    have hi_ps : IntegrableOn
        (fun y => inner ℂ (F8U.slice Φ s y) (F8U.ps W (s, y)))
        (B0579.cell p.c) volume := F8Sm.integrableOn_inner_cell (hmΦ s) (hmsW s hs)
    have hi_d00 : IntegrableOn
        (fun y => inner ℂ (F8U.slice Φ s y) (F8U.pd 0 (F8U.pd 0 W) (s, y)))
        (B0579.cell p.c) volume := F8Sm.integrableOn_inner_cell (hmΦ s) hm_d00
    have hi_d11 : IntegrableOn
        (fun y => inner ℂ (F8U.slice Φ s y) (F8U.pd 1 (F8U.pd 1 W) (s, y)))
        (B0579.cell p.c) volume := F8Sm.integrableOn_inner_cell (hmΦ s) hm_d11
    have hi_d_sum : IntegrableOn
        (fun y => inner ℂ (F8U.slice Φ s y) (F8U.pd 0 (F8U.pd 0 W) (s, y)) +
          inner ℂ (F8U.slice Φ s y) (F8U.pd 1 (F8U.pd 1 W) (s, y)))
        (B0579.cell p.c) volume := hi_d00.add hi_d11
    have hi_lap : IntegrableOn
        (fun y => (p.ν : ℂ) * (inner ℂ (F8U.slice Φ s y) (F8U.pd 0 (F8U.pd 0 W) (s, y)) +
          inner ℂ (F8U.slice Φ s y) (F8U.pd 1 (F8U.pd 1 W) (s, y))))
        (B0579.cell p.c) volume := hi_d_sum.const_mul (p.ν : ℂ)
    have hi_ps_sub : IntegrableOn
        (fun y => inner ℂ (F8U.slice Φ s y) (F8U.ps W (s, y)) -
          (p.ν : ℂ) * (inner ℂ (F8U.slice Φ s y) (F8U.pd 0 (F8U.pd 0 W) (s, y)) +
            inner ℂ (F8U.slice Φ s y) (F8U.pd 1 (F8U.pd 1 W) (s, y))))
        (B0579.cell p.c) volume := hi_ps.sub hi_lap
    have hi_bv : IntegrableOn
        (fun y => inner ℂ (F8U.slice Φ s y)
          (bvTripleSlice (p.train.v s) (F8U.slice W s) (F8U.slice (F8U.pd 0 W) s)
            (F8U.slice (F8U.pd 1 W) s) y))
        (B0579.cell p.c) volume := F8Sm.integrableOn_inner_cell (hmΦ s) hm_bv
    have hproj_exp :
        ((∫ y in B0579.cell p.c, inner ℂ (F8U.slice Φ s y) (F8U.ps W (s, y))) -
          (p.ν : ℂ) * ((∫ y in B0579.cell p.c,
              inner ℂ (F8U.slice Φ s y) (F8U.pd 0 (F8U.pd 0 W) (s, y))) +
            (∫ y in B0579.cell p.c,
              inner ℂ (F8U.slice Φ s y) (F8U.pd 1 (F8U.pd 1 W) (s, y))))) +
          (∫ y in B0579.cell p.c, inner ℂ (F8U.slice Φ s y)
            (bvTripleSlice (p.train.v s) (F8U.slice W s) (F8U.slice (F8U.pd 0 W) s)
              (F8U.slice (F8U.pd 1 W) s) y)) = 0 := by
      rw [← integral_add hi_d00 hi_d11, ← integral_const_mul,
        ← integral_sub hi_ps hi_lap, ← integral_add hi_ps_sub hi_bv]
      refine (integral_congr_ae (Eventually.of_forall fun y => ?_)).trans hproj
      unfold F8U.homResidual
      rw [congrFun (flatBv_eq_bvTripleSlice p.train W (F8U.pd 0 W) (F8U.pd 1 W) s) y,
        inner_add_right, inner_sub_right]
      have hsm : p.ν • (F8U.pd 0 (F8U.pd 0 W) (s, y) + F8U.pd 1 (F8U.pd 1 W) (s, y)) =
          (p.ν : ℂ) • (F8U.pd 0 (F8U.pd 0 W) (s, y) + F8U.pd 1 (F8U.pd 1 W) (s, y)) := by
        ext k; simp [Complex.real_smul]
      rw [hsm, inner_smul_right, inner_add_right]
    -- Double cell IBP on `j = 0, 1`
    have hibp2 : ∀ j : Fin 2,
        (∫ y in B0579.cell p.c,
          inner ℂ (F8U.slice Φ s y) (F8U.pd j (F8U.pd j W) (s, y))) =
        ∫ y in B0579.cell p.c,
          inner ℂ (F8U.slice (perVecProf p.c
            (fun x i => cpd j.succ (fun z => cpd j.succ (fun w => Ψ w i) z) x)) s y)
            (F8U.slice W s y) := by
      intro j
      let Ψj : Coord → Fin 2 → ℝ := fun x i => cpd j.succ (fun z => Ψ z i) x
      let Ψjj : Coord → Fin 2 → ℝ := fun x i => cpd j.succ (fun z => Ψj z i) x
      have hΨj_t : ∀ i : Fin 2, IsCoordTest (fun x => Ψj x i) :=
        fun i => isCoordTest_cpd (hΨ.smooth i) j.succ
      have hΨjj_t : ∀ i : Fin 2, IsCoordTest (fun x => Ψjj x i) :=
        fun i => isCoordTest_cpd (hΨj_t i) j.succ
      obtain ⟨hΦj_sm, _, hΦj_pd⟩ := contDiff_and_derivs_perVecProf p.c_pos hΨj_t
      have hΦjj_sm := (contDiff_and_derivs_perVecProf p.c_pos hΨjj_t).1
      have hp1_Φ : F8Sm.pdir j (F8U.slice Φ s) = F8U.slice (perVecProf p.c Ψj) s := by
        rw [F8Sm.pdir_slice_eq hΦ_sm.contDiffOn hs j, hΦ_pd j]
      have hp2_Φ : F8Sm.pdir j (F8Sm.pdir j (F8U.slice Φ s)) =
          F8U.slice (perVecProf p.c Ψjj) s := by
        rw [hp1_Φ, F8Sm.pdir_slice_eq hΦj_sm.contDiffOn hs j, hΦj_pd j]
      have hη_j : ∀ (i : Fin 2) (x : Coord), R < |x.2.2| → Ψj x i = 0 := by
        intro i x hx
        have hev : (fun y : Coord => Ψ y i) =ᶠ[𝓝 x] 0 := by
          filter_upwards [(isOpen_lt continuous_const
            (continuous_snd.comp continuous_snd).abs).mem_nhds hx] with y hy
          exact (hΨ_eta i y hy).1
        change fderiv ℝ (fun y => Ψ y i) x (cdir j.succ) = 0
        rw [hev.fderiv_eq]; simp
      have hη_jj : ∀ (i : Fin 2) (x : Coord), R < |x.2.2| → Ψjj x i = 0 := by
        intro i x hx
        have hev : (fun y : Coord => Ψj y i) =ᶠ[𝓝 x] 0 := by
          filter_upwards [(isOpen_lt continuous_const
            (continuous_snd.comp continuous_snd).abs).mem_nhds hx] with y hy
          exact hη_j i y hy
        change fderiv ℝ (fun y => Ψj y i) x (cdir j.succ) = 0
        rw [hev.fderiv_eq]; simp
      have hmΦj := memLp_slice_of_eta_vanish p.c
        hΦj_sm.continuous (perVecProf_eta_vanish hη_j) s
      have hmΦjj := memLp_slice_of_eta_vanish p.c
        hΦjj_sm.continuous (perVecProf_eta_vanish hη_jj) s
      have hW_s_sm := F8Sm.contDiff_slice hW.smooth hs
      have hWj_s_sm := F8Sm.contDiff_slice (F8Sm.contDiffOn_pd hW.smooth j) hs
      have hW_s_per : UnforcedLeray.Cyl.IsPeriodic p.c (F8U.slice W s) :=
        fun y => hW.periodic (s, y) hs
      have hWj_s_per : UnforcedLeray.Cyl.IsPeriodic p.c (F8U.slice (F8U.pd j W) s) :=
        fun y => F8Sm.periodic_fderiv_dir hW.periodic (F8U.sdir j) (s, y) hs
      have hp_W : F8Sm.pdir j (F8U.slice W s) = F8U.slice (F8U.pd j W) s :=
        F8Sm.pdir_slice_eq hW.smooth hs j
      have hp_Wj : F8Sm.pdir j (F8U.slice (F8U.pd j W) s) =
          F8U.slice (F8U.pd j (F8U.pd j W)) s :=
        F8Sm.pdir_slice_eq (F8Sm.contDiffOn_pd hW.smooth j) hs j
      have ibp1 := F8Sm.cell_ibp_pdir p.c_pos j hΦ_s_sm hWj_s_sm hΦ_s_per hWj_s_per
        (hmΦ s) (hp1_Φ.symm ▸ hmΦj) (orbit_memLp_1 hW hs j)
        (hp_Wj.symm ▸ orbit_memLp_2 hW hs j j)
      have ibp2 := F8Sm.cell_ibp_pdir p.c_pos j (F8Sm.contDiff_pdir hΦ_s_sm j) hW_s_sm
        (F8Sm.periodic_pdir hΦ_s_per j) hW_s_per
        (hp1_Φ.symm ▸ hmΦj) (hp2_Φ.symm ▸ hmΦjj) (orbit_memLp_0 hW hs)
        (hp_W.symm ▸ orbit_memLp_1 hW hs j)
      rw [hp_Wj] at ibp1
      rw [hp_W, hp2_Φ] at ibp2
      have h1 : (∫ y in B0579.cell p.c,
            inner ℂ (F8U.slice Φ s y) (F8U.slice (F8U.pd j (F8U.pd j W)) s y)) =
          - ∫ y in B0579.cell p.c,
            inner ℂ (F8Sm.pdir j (F8U.slice Φ s) y) (F8U.slice (F8U.pd j W) s y) := by
        rw [← neg_inj, neg_neg]; exact ibp1.symm
      exact h1.trans ibp2.symm
    -- Express all inner products on slice `s`
    have heq_in_ps : inner ℂ (lpΦ s) ((hmsW s hs).toLp (F8U.slice (F8U.ps W) s)) =
        ∫ y in B0579.cell p.c, inner ℂ (F8U.slice Φ s y) (F8U.ps W (s, y)) :=
      (F8Sm.integral_inner_eq_L2_inner (hmΦ s) (hmsW s hs)).symm
    have heq_in_s : inner ℂ (lpΦs s) (lw s) =
        ∫ y in B0579.cell p.c, inner ℂ (F8U.slice Φs s y) (F8U.slice W s y) := by
      dsimp only [lw]
      rw [sliceLpOn_of_mem hmW hs]
      exact (F8Sm.integral_inner_eq_L2_inner (hmΦs s) (hmW s hs)).symm
    -- Relate `sliceLHSVal p Ψ s (S0Val hflow s τ v)` to the classical slice `W (s, ·)`
    have hMT_coord : ∀ i : Fin 2, IsCoordTest (fun x => mtReal p.ν Ψ x i) :=
      fun i => isCoordTest_mtReal p.ν hΨ i
    have hmMT_s := memLp_slice_of_eta_vanish p.c
      (contDiff_and_derivs_perVecProf p.c_pos hMT_coord).1.continuous
      (perVecProf_eta_vanish fun i x hx => (hΨ_eta i x hx).2) s
    have hS0_s := S0Val_of_cond hflow hτ hs hv
    have hlhs_1 : (∑ i : Fin 2, ∫ y in B0579.cell p.c,
          (S0Val hflow s τ v).1 y i *
            (TailPeriodizeAux.qPeriodize p.c (fun x => mtReal p.ν Ψ x i) s y : ℂ)) =
        ∫ y in B0579.cell p.c,
          inner ℂ (F8U.slice (perVecProf p.c (mtReal p.ν Ψ)) s y) (F8U.slice W s y) := by
      rw [sum_integral_mul_qPeriodize_eq_inner p.c_pos hMT_coord
        (Lp.memLp (S0Val hflow s τ v).1) (hmG := hmMT_s)]
      have hto : (Lp.memLp (S0Val hflow s τ v).1).toLp (S0Val hflow s τ v).1 =
          (hmW s hs).toLp (F8U.slice W s) := by
        rw [Lp.ext_iff.2 (Lp.memLp (S0Val hflow s τ v).1).coeFn_toLp, hS0_s]
      rw [hto, ← F8Sm.integral_inner_eq_L2_inner hmMT_s (hmW s hs)]
    have hlhs_2 : (∑ i : Fin 2, ∫ y in B0579.cell p.c,
          bvTripleSlice (p.train.v s) (S0Val hflow s τ v).1 (S0Val hflow s τ v).2.1
            (S0Val hflow s τ v).2.2 y i *
            (TailPeriodizeAux.qPeriodize p.c (fun x => Ψ x i) s y : ℂ)) =
        ∫ y in B0579.cell p.c, inner ℂ (F8U.slice Φ s y)
          (bvTripleSlice (p.train.v s) (F8U.slice W s) (F8U.slice (F8U.pd 0 W) s)
            (F8U.slice (F8U.pd 1 W) s) y) := by
      obtain ⟨hm_bv_S0, _⟩ := memLp_and_cellL2_bvTripleSlice hM_tr (hV_s s hs_icc)
        (hb0_tr s hs_icc) (hb1_tr s hs_icc) (Lp.memLp (S0Val hflow s τ v).1)
        (Lp.memLp (S0Val hflow s τ v).2.1) (Lp.memLp (S0Val hflow s τ v).2.2)
      rw [sum_integral_mul_qPeriodize_eq_inner p.c_pos hΨ.smooth hm_bv_S0 (hmG := hmΦ s)]
      have hto_bv : hm_bv_S0.toLp (bvTripleSlice (p.train.v s) (S0Val hflow s τ v).1
            (S0Val hflow s τ v).2.1 (S0Val hflow s τ v).2.2) =
          hm_bv.toLp (bvTripleSlice (p.train.v s) (F8U.slice W s)
            (F8U.slice (F8U.pd 0 W) s) (F8U.slice (F8U.pd 1 W) s)) := by
        apply Lp.ext_iff.2
        filter_upwards [hm_bv_S0.coeFn_toLp, hm_bv.coeFn_toLp,
          (orbit_memLp_0 hW hs).coeFn_toLp, (orbit_memLp_1 hW hs 0).coeFn_toLp,
          (orbit_memLp_1 hW hs 1).coeFn_toLp] with y hb1 hb2 h0 h10 h11
        rw [hb1, hb2, hS0_s]
        dsimp only [bvTripleSlice]
        rw [h0, h10, h11]
      rw [hto_bv, ← F8Sm.integral_inner_eq_L2_inner (hmΦ s) hm_bv]
    -- Pointwise identity `- qPeriodize mtReal = qPeriodize (cpd 0 Ψ) + ν * (qPeriodize Ψ_11 + qPeriodize Ψ_22)`
    let Ψ11 : Coord → Fin 2 → ℝ := fun x i => cpd 1 (fun z => cpd 1 (fun w => Ψ w i) z) x
    let Ψ22 : Coord → Fin 2 → ℝ := fun x i => cpd 2 (fun z => cpd 2 (fun w => Ψ w i) z) x
    have hΨ11_t : ∀ i : Fin 2, IsCoordTest (fun x => Ψ11 x i) :=
      fun i => isCoordTest_cpd (isCoordTest_cpd (hΨ.smooth i) 1) 1
    have hΨ22_t : ∀ i : Fin 2, IsCoordTest (fun x => Ψ22 x i) :=
      fun i => isCoordTest_cpd (isCoordTest_cpd (hΨ.smooth i) 2) 2
    have hη_11 : ∀ (i : Fin 2) (x : Coord), R < |x.2.2| → Ψ11 x i = 0 := by
      intro i x hx
      have hnot : x ∉ tsupport (fun y => Ψ y i) := by
        rw [notMem_tsupport_iff_eventuallyEq]
        filter_upwards [(isOpen_lt continuous_const
          (continuous_snd.comp continuous_snd).abs).mem_nhds hx] with y hy
        exact (hΨ_eta i y hy).1
      exact (vanish_derivs_of_notMem_tsupport hnot).2.2 1 1
    have hη_22 : ∀ (i : Fin 2) (x : Coord), R < |x.2.2| → Ψ22 x i = 0 := by
      intro i x hx
      have hnot : x ∉ tsupport (fun y => Ψ y i) := by
        rw [notMem_tsupport_iff_eventuallyEq]
        filter_upwards [(isOpen_lt continuous_const
          (continuous_snd.comp continuous_snd).abs).mem_nhds hx] with y hy
        exact (hΨ_eta i y hy).1
      exact (vanish_derivs_of_notMem_tsupport hnot).2.2 2 2
    have hmΦ11 := memLp_slice_of_eta_vanish p.c
      (contDiff_and_derivs_perVecProf p.c_pos hΨ11_t).1.continuous
      (perVecProf_eta_vanish hη_11) s
    have hmΦ22 := memLp_slice_of_eta_vanish p.c
      (contDiff_and_derivs_perVecProf p.c_pos hΨ22_t).1.continuous
      (perVecProf_eta_vanish hη_22) s
    have hi_sW := F8Sm.integrableOn_inner_cell (hmΦs s) (hmW s hs)
    have hi_11W := F8Sm.integrableOn_inner_cell hmΦ11 (hmW s hs)
    have hi_22W := F8Sm.integrableOn_inner_cell hmΦ22 (hmW s hs)
    have hi_11_22 : IntegrableOn
        (fun y => inner ℂ (F8U.slice (perVecProf p.c Ψ11) s y) (F8U.slice W s y) +
          inner ℂ (F8U.slice (perVecProf p.c Ψ22) s y) (F8U.slice W s y))
        (B0579.cell p.c) volume := hi_11W.add hi_22W
    have hi_ν : IntegrableOn
        (fun y => (p.ν : ℂ) *
          (inner ℂ (F8U.slice (perVecProf p.c Ψ11) s y) (F8U.slice W s y) +
            inner ℂ (F8U.slice (perVecProf p.c Ψ22) s y) (F8U.slice W s y)))
        (B0579.cell p.c) volume := hi_11_22.const_mul (p.ν : ℂ)
    have hmt_sum :
        (∫ y in B0579.cell p.c, inner ℂ (F8U.slice Φs s y) (F8U.slice W s y)) +
          (p.ν : ℂ) * ((∫ y in B0579.cell p.c,
              inner ℂ (F8U.slice (perVecProf p.c Ψ11) s y) (F8U.slice W s y)) +
            (∫ y in B0579.cell p.c,
              inner ℂ (F8U.slice (perVecProf p.c Ψ22) s y) (F8U.slice W s y))) =
        - ∫ y in B0579.cell p.c,
            inner ℂ (F8U.slice (perVecProf p.c (mtReal p.ν Ψ)) s y) (F8U.slice W s y) := by
      rw [← integral_add hi_11W hi_22W, ← integral_const_mul,
        ← integral_add hi_sW hi_ν, ← integral_neg]
      refine integral_congr_ae (Eventually.of_forall fun y => ?_)
      have hq_mt : ∀ i : Fin 2,
          TailPeriodizeAux.qPeriodize p.c (fun x => mtReal p.ν Ψ x i) s y =
            -TailPeriodizeAux.qPeriodize p.c (fun x => Ψs x i) s y -
              p.ν * (TailPeriodizeAux.qPeriodize p.c (fun x => Ψ11 x i) s y +
                TailPeriodizeAux.qPeriodize p.c (fun x => Ψ22 x i) s y) := by
        intro i
        obtain ⟨_, _, R_i, _, _, _, hbox_i⟩ := TailPeriodizeAux.coordTest_box (hΨ.smooth i)
        obtain ⟨N, hN⟩ := exists_nat_gt ((|y.1| + R_i) / p.c + 1)
        let S : Finset ℤ := Finset.Icc (-(N : ℤ)) (N : ℤ)
        have hout_not : ∀ k ∉ S, (s, (y.1 + (k : ℝ) * p.c, y.2)) ∉ tsupport (fun z => Ψ z i) := by
          intro k hk hmem
          have hout := shift_outside_box_local p.c_pos hN (le_refl |y.1|) hk
          have hev : (fun z : Coord => Ψ z i) =ᶠ[𝓝 (s, (y.1 + (k : ℝ) * p.c, y.2))] 0 := by
            filter_upwards [(isOpen_lt continuous_const
              (continuous_fst.comp continuous_snd).abs).mem_nhds hout] with z hz
            exact (hbox_i z (Or.inr (Or.inl hz))).1
          exact notMem_tsupport_iff_eventuallyEq.2 hev hmem
        have eq_mt : TailPeriodizeAux.qPeriodize p.c (fun x => mtReal p.ν Ψ x i) s y =
            ∑ k ∈ S, mtReal p.ν Ψ (s, (y.1 + (k : ℝ) * p.c, y.2)) i :=
          tsum_eq_sum fun k hk => by
            obtain ⟨_, h1, h2⟩ := vanish_derivs_of_notMem_tsupport (hout_not k hk)
            simp [mtReal, h1 0, h2 1 1, h2 2 2]
        have eq_0 : TailPeriodizeAux.qPeriodize p.c (fun x => Ψs x i) s y =
            ∑ k ∈ S, Ψs (s, (y.1 + (k : ℝ) * p.c, y.2)) i :=
          tsum_eq_sum fun k hk => (vanish_derivs_of_notMem_tsupport (hout_not k hk)).2.1 0
        have eq_11 : TailPeriodizeAux.qPeriodize p.c (fun x => Ψ11 x i) s y =
            ∑ k ∈ S, Ψ11 (s, (y.1 + (k : ℝ) * p.c, y.2)) i :=
          tsum_eq_sum fun k hk => (vanish_derivs_of_notMem_tsupport (hout_not k hk)).2.2 1 1
        have eq_22 : TailPeriodizeAux.qPeriodize p.c (fun x => Ψ22 x i) s y =
            ∑ k ∈ S, Ψ22 (s, (y.1 + (k : ℝ) * p.c, y.2)) i :=
          tsum_eq_sum fun k hk => (vanish_derivs_of_notMem_tsupport (hout_not k hk)).2.2 2 2
        rw [eq_mt, eq_0, eq_11, eq_22, ← Finset.sum_add_distrib, Finset.mul_sum, ← Finset.sum_neg_distrib,
          ← Finset.sum_sub_distrib]
        rfl
      simp only [F8U.slice, Φs, perVecProf, TailPeriodizeAux.qPeriodizeVec,
        PiLp.inner_apply, Fin.sum_univ_two, RCLike.inner_apply, Complex.conj_ofReal,
        hq_mt 0, hq_mt 1]
      push_cast
      ring
    rw [heq_in_ps, heq_in_s]
    unfold sliceLHSVal
    have hibp2_0 : (∫ y in B0579.cell p.c,
          inner ℂ (F8U.slice Φ s y) (F8U.pd 0 (F8U.pd 0 W) (s, y))) =
        ∫ y in B0579.cell p.c,
          inner ℂ (F8U.slice (perVecProf p.c Ψ11) s y) (F8U.slice W s y) := hibp2 0
    have hibp2_1 : (∫ y in B0579.cell p.c,
          inner ℂ (F8U.slice Φ s y) (F8U.pd 1 (F8U.pd 1 W) (s, y))) =
        ∫ y in B0579.cell p.c,
          inner ℂ (F8U.slice (perVecProf p.c Ψ22) s y) (F8U.slice W s y) := hibp2 1
    rw [hibp2_0, hibp2_1] at hproj_exp
    rw [hlhs_1, hlhs_2]
    change _ = - ((∫ y in B0579.cell p.c,
        inner ℂ (F8U.slice (perVecProf p.c (mtReal p.ν Ψ)) s y) (F8U.slice W s y)) +
      (∫ y in B0579.cell p.c, inner ℂ (F8U.slice Φ s y)
        (bvTripleSlice (p.train.v s) (F8U.slice W s) (F8U.slice (F8U.pd 0 W) s)
          (F8U.slice (F8U.pd 1 W) s) y)))
    have hps_val : (∫ y in B0579.cell p.c, inner ℂ (F8U.slice Φ s y) (F8U.ps W (s, y))) =
        (p.ν : ℂ) * ((∫ y in B0579.cell p.c,
            inner ℂ (F8U.slice (perVecProf p.c Ψ11) s y) (F8U.slice W s y)) +
          (∫ y in B0579.cell p.c,
            inner ℂ (F8U.slice (perVecProf p.c Ψ22) s y) (F8U.slice W s y))) -
        (∫ y in B0579.cell p.c, inner ℂ (F8U.slice Φ s y)
          (bvTripleSlice (p.train.v s) (F8U.slice W s) (F8U.slice (F8U.pd 0 W) s)
            (F8U.slice (F8U.pd 1 W) s) y)) := by
      linear_combination hproj_exp
    rw [hps_val]
    linear_combination hmt_sum
  -- Apply `intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto` on `(τ, b'')`
  let g : ℝ → ℂ := fun s => inner ℂ (lpΦ s) (lw s)
  let g' : ℝ → ℂ := fun s => - sliceLHSVal p Ψ s (S0Val hflow s τ v)
  have hsub_ioo : Ioo τ b'' ⊆ Ioo τ (τ + 2) := fun s hs => ⟨hs.1, by linarith [hs.2]⟩
  have hderiv_g : ∀ s ∈ Ioo τ b'', HasDerivAt g (g' s) s := by
    intro s hs
    have hs2 := hsub_ioo hs
    have hd := (hderiv_Φ s hs2).inner ℂ (hderiv_W s hs2)
    rwa [hg'_ident s hs2] at hd
  have hg'_cont : ContinuousOn g' (Ioo τ b'') := by
    have hc1 : ContinuousOn (fun s => inner ℂ (lpΦ s)
        (UnforcedLeray.BochnerTime.toPathLq 2 (F8Sm.cellMeas p.c) (F8U.ps W) s))
        (Ioo τ (τ + 2)) :=
      ContinuousOn.inner (𝕜 := ℂ) (E := L2Cell p.c) hlpΦ_cont.continuousOn hlw_ps_cont
    have hc2 : ContinuousOn (fun s => inner ℂ (lpΦs s) (lw s)) (Ioo τ (τ + 2)) :=
      ContinuousOn.inner (𝕜 := ℂ) (E := L2Cell p.c) hlpΦs_cont.continuousOn hlw_cont
    refine ((hc1.add hc2).mono hsub_ioo).congr fun s hs => ?_
    have hs2 := hsub_ioo hs
    have hm_s : MemLp (fun y => F8U.ps W (s, y)) 2 (F8Sm.cellMeas p.c) := hmsW s hs2
    have hto : UnforcedLeray.BochnerTime.toPathLq 2 (F8Sm.cellMeas p.c) (F8U.ps W) s =
        (hmsW s hs2).toLp (F8U.slice (F8U.ps W) s) :=
      UnforcedLeray.BochnerTime.toPathLq_of_memLp hm_s
    dsimp only [g', Pi.add_apply]
    rw [← hg'_ident s hs2, hto]
  obtain ⟨_, ⟨C_lhs, hC_lhs_nn, hLHS_bd⟩, _⟩ :=
    sliceLHSVal_clm_and_fubini hreg hΨ (a'' := b'' + 1) (b'' := b'' + 1)
      (by linarith) le_rfl hR hΨ_eta
  have hg'_int_ioo : IntegrableOn g' (Ioo τ b'') volume := by
    let B : ℝ := C_lhs * (A * h1RealNorm v)
    refine (integrableOn_const (C := B) (by rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top)).mono'
      (hg'_cont.aestronglyMeasurable measurableSet_Ioo) ?_
    rw [ae_restrict_iff' measurableSet_Ioo]
    refine Eventually.of_forall fun s hs => ?_
    have hs_icc : s ∈ Icc (0 : ℝ) ((b'' + 1) + 2) := ⟨by linarith [hs.1], by linarith [hs.2]⟩
    have hs_ioc : s ∈ Ioc τ (τ + 1) := ⟨hs.1, by linarith [hs.2]⟩
    dsimp only [g']
    rw [norm_neg]
    exact (hLHS_bd s hs_icc _).trans
      (mul_le_mul_of_nonneg_left
        (S0Val_and_SD2Val_bounds hA p.ν_pos hflow hτ hs_ioc hv).2.1 hC_lhs_nn)
  have hg'_int_ioc : IntegrableOn g' (Ioc τ b'') volume :=
    hg'_int_ioo.congr_set_ae Ioo_ae_eq_Ioc.symm
  have hint_lhs : IntegrableOn (fun s => sliceLHSVal p Ψ s (S0Val hflow s τ v))
      (Ioc τ b'') volume := by
    simpa [g'] using hg'_int_ioc.neg
  have hint_iv : IntervalIntegrable g' volume τ b'' :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hτb''.le).2 hg'_int_ioc
  have ha_lim : Tendsto g (𝓝[>] τ) (𝓝 (inner ℂ (lpΦ τ) v.1)) := by
    have hlw_τ : Tendsto lw (𝓝[>] τ) (𝓝 v.1) := by
      refine (continuous_fst.continuousAt.tendsto.comp
        (tendsto_S0Val_initial hflow hτ hv).2).congr' ?_
      filter_upwards [Ioo_mem_nhdsGT (by linarith : τ < τ + 2)] with s hs
      exact (hlw_eq hs).symm
    exact Filter.Tendsto.inner (𝕜 := ℂ) (E := L2Cell p.c)
      (hlpΦ_cont.continuousAt.tendsto.mono_left nhdsWithin_le_nhds) hlw_τ
  have hb_lim : Tendsto g (𝓝[<] b'') (𝓝 0) := by
    have hb''_ioo : b'' ∈ Ioo τ (τ + 2) := ⟨hτb'', by linarith⟩
    have hg_at : ContinuousAt g b'' :=
      ContinuousAt.inner (𝕜 := ℂ) (E := L2Cell p.c)
        hlpΦ_cont.continuousAt (hlw_cont.continuousAt (isOpen_Ioo.mem_nhds hb''_ioo))
    have hlpΦ_b'' : lpΦ b'' = 0 := by
      apply Lp.ext_iff.2
      filter_upwards [(hmΦ b'').coeFn_toLp, Lp.coeFn_zero CMerid 2 (F8Sm.cellMeas p.c)]
        with y hy1 hy0
      rw [hy1, hy0]
      ext i
      have hz : TailPeriodizeAux.qPeriodize p.c (fun x => Ψ x i) b'' y = 0 := by
        unfold TailPeriodizeAux.qPeriodize
        have h0 : (fun k : ℤ => Ψ (b'', (y.1 + (k : ℝ) * p.c, y.2)) i) = fun _ => 0 :=
          funext fun k => hΨ_hi i (b'', (y.1 + (k : ℝ) * p.c, y.2)) hb'
        rw [h0, tsum_zero]
      fin_cases i <;>
        simpa [F8U.slice, Φ, perVecProf, TailPeriodizeAux.qPeriodizeVec] using
          congrArg Complex.ofReal hz
    have hgb'' : g b'' = 0 := by simp [g, hlpΦ_b'']
    simpa [hgb''] using hg_at.tendsto.mono_left nhdsWithin_le_nhds
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto
    hτb'' hderiv_g hint_iv ha_lim hb_lim
  rw [intervalIntegral.integral_of_le hτb''.le, zero_sub] at hftc
  have hftc' : - ∫ s in Ioc τ b'', sliceLHSVal p Ψ s (S0Val hflow s τ v) =
      - inner ℂ (lpΦ τ) v.1 := by
    simpa [g', integral_neg] using hftc
  refine ⟨hint_lhs, (neg_inj.1 hftc').trans ?_⟩
  have hto_v1 : (Lp.memLp v.1).toLp v.1 = v.1 := Lp.ext_iff.2 (Lp.memLp v.1).coeFn_toLp
  rw [sum_integral_mul_qPeriodize_eq_inner p.c_pos hΨ.smooth (Lp.memLp v.1) (hmG := hmΦ τ),
    hto_v1]

/-- Full Bochner–Fubini slice weak identity for `WPath` on `[a'', b''] ⊂ (σ, σ + 1)`. -/
lemma duhamel_slice_weak_eq {dm dp : ℝ} {p : Params} {d A σ : ℝ}
    (hA : 0 < A) (hreg : BgRegime p d dm dp) (hflow : F8U.CylOseenFlowBound A p) (hσ : 0 ≤ σ)
    {x0 : X3 p.c} (hx0 : x0 ∈ H1Set p.c)
    {fp : ℝ → X3 p.c} (hfp_sm : StronglyMeasurable fp) (hfp_mem : ∀ τ, fp τ ∈ H1Set p.c)
    (hfp_int : Integrable (fun τ => h1RealNorm (fp τ)) volume)
    {Ψ : Coord → Fin 2 → ℝ} (hΨ : IsPlanarSolTest Ψ)
    {a'' a' b' b'' R : ℝ}
    (ha'' : σ < a'') (ha' : a'' < a') (hab' : a' ≤ b') (hb' : b' < b'') (hb'' : b'' < σ + 1)
    (hR : 0 < R)
    (hΨ_tsupp : ∀ (i : Fin 2) (x : Coord),
      (x.1 ∉ Icc a' b' ∨ R < |x.2.1| ∨ R < |x.2.2|) → x ∉ tsupport (fun y => Ψ y i)) :
    (∫ s in Icc a'' b'', sliceLHSVal p Ψ s (WPath hflow σ x0 fp s)) =
      ∫ τ in Icc a'' b'', ∑ i : Fin 2, ∫ y in B0579.cell p.c,
        (fp τ).1 y i * (TailPeriodizeAux.qPeriodize p.c (fun x => Ψ x i) τ y : ℂ) := by
  have ha''_pos : 0 < a'' := by linarith
  have hab'' : a'' ≤ b'' := by linarith
  have hΨ_eta : ∀ (i : Fin 2) (x : Coord), R < |x.2.2| →
      Ψ x i = 0 ∧ mtReal p.ν Ψ x i = 0 := by
    intro i x hx
    obtain ⟨h0, h1, h2⟩ := vanish_derivs_of_notMem_tsupport (hΨ_tsupp i x (Or.inr (Or.inr hx)))
    exact ⟨h0, by simp [mtReal, h1 0, h2 1 1, h2 2 2]⟩
  have hΨ_hi : ∀ (i : Fin 2) (x : Coord), b' < x.1 → Ψ x i = 0 := fun i x hx =>
    (vanish_derivs_of_notMem_tsupport
      (hΨ_tsupp i x (Or.inl fun hm => not_le_of_gt hx hm.2))).1
  have hΨ_lo_zero : ∀ {s : ℝ}, s < a' → ∀ (i : Fin 2) (y : B0579.Plane),
      TailPeriodizeAux.qPeriodize p.c (fun x => Ψ x i) s y = 0 ∧
        TailPeriodizeAux.qPeriodize p.c (fun x => mtReal p.ν Ψ x i) s y = 0 := by
    intro s hs i y
    have hnot : ∀ k : ℤ, (s, (y.1 + (k : ℝ) * p.c, y.2)) ∉ tsupport (fun z => Ψ z i) :=
      fun k => hΨ_tsupp i _ (Or.inl fun hm => not_le_of_gt hs hm.1)
    refine ⟨?_, ?_⟩ <;> unfold TailPeriodizeAux.qPeriodize
    · have h0 : (fun k : ℤ => Ψ (s, (y.1 + (k : ℝ) * p.c, y.2)) i) = fun _ => 0 :=
        funext fun k => (vanish_derivs_of_notMem_tsupport (hnot k)).1
      rw [h0, tsum_zero]
    · have h0 : (fun k : ℤ => mtReal p.ν Ψ (s, (y.1 + (k : ℝ) * p.c, y.2)) i) = fun _ => 0 :=
        funext fun k => by
          obtain ⟨_, h1, h2⟩ := vanish_derivs_of_notMem_tsupport (hnot k)
          simp [mtReal, h1 0, h2 1 1, h2 2 2]
      rw [h0, tsum_zero]
  have hLHS_lo : ∀ {s : ℝ}, s ≤ a'' → ∀ X : X3 p.c,
      sliceLHSVal p Ψ s X = 0 ∧
        (∑ i : Fin 2, ∫ y in B0579.cell p.c,
          X.1 y i * (TailPeriodizeAux.qPeriodize p.c (fun x => Ψ x i) s y : ℂ)) = 0 := by
    intro s hs X
    have hsa' : s < a' := lt_of_le_of_lt hs ha'
    have hq0 : ∀ i y, TailPeriodizeAux.qPeriodize p.c (fun x => Ψ x i) s y = 0 :=
      fun i y => (hΨ_lo_zero hsa' i y).1
    have hmt0 : ∀ i y, TailPeriodizeAux.qPeriodize p.c (fun x => mtReal p.ν Ψ x i) s y = 0 :=
      fun i y => (hΨ_lo_zero hsa' i y).2
    refine ⟨?_, ?_⟩
    · simp [sliceLHSVal, hq0, hmt0]
    · simp [hq0]
  obtain ⟨hclm, ⟨C_lhs, hC_lhs_nn, hLHS_bd⟩, hLHS_sm⟩ :=
    sliceLHSVal_clm_and_fubini hreg hΨ ha''_pos hab'' hR hΨ_eta
  -- Initial orbit contribution vanishes on `Icc a'' b''`
  obtain ⟨hint_init_ioc, hftc_init⟩ := single_orbit_ftc hA hreg hflow hΨ hb' hR hΨ_hi hΨ_eta
    hσ (by linarith : σ < b'') hb''.le hx0
  rw [(hLHS_lo ha''.le x0).2] at hftc_init
  have hind_init : (Icc a'' b'').indicator (fun s => sliceLHSVal p Ψ s (S0Val hflow s σ x0)) =
      (Ioc σ b'').indicator (fun s => sliceLHSVal p Ψ s (S0Val hflow s σ x0)) := by
    funext s
    by_cases hs_icc : s ∈ Icc a'' b''
    · have hs_ioc : s ∈ Ioc σ b'' := ⟨lt_of_lt_of_le ha'' hs_icc.1, hs_icc.2⟩
      rw [indicator_of_mem hs_icc, indicator_of_mem hs_ioc]
    · rw [indicator_of_notMem hs_icc]
      by_cases hs_ioc : s ∈ Ioc σ b''
      · rw [indicator_of_mem hs_ioc]
        have hs_lt : s < a'' := by
          by_contra hge; exact hs_icc ⟨not_lt.1 hge, hs_ioc.2⟩
        exact ((hLHS_lo hs_lt.le _).1).symm
      · rw [indicator_of_notMem hs_ioc]
  have hint_init_icc : IntegrableOn (fun s => sliceLHSVal p Ψ s (S0Val hflow s σ x0))
      (Icc a'' b'') volume := by
    rw [← integrable_indicator_iff measurableSet_Icc, hind_init,
      integrable_indicator_iff measurableSet_Ioc]
    exact hint_init_ioc
  have hint_eq_init : (∫ s in Icc a'' b'', sliceLHSVal p Ψ s (S0Val hflow s σ x0)) = 0 := by
    rw [← integral_indicator measurableSet_Icc, hind_init,
      integral_indicator measurableSet_Ioc, hftc_init]
  -- Fubini on `H_prod (s, τ) = 1_{s ∈ [a'', b'']} sliceLHSVal s (K0 (s, τ))`
  have hint_K0 := (integrable_K0_slice_and_prod hA hreg hflow hσ hfp_sm hfp_mem hfp_int).1
  have hK0_sm := (stronglyMeasurable_K0_and_KD2 hA hreg hflow hσ hfp_sm hfp_mem).1
  let H_prod : ℝ × ℝ → ℂ :=
    (Icc a'' b'' ×ˢ (univ : Set ℝ)).indicator fun q => sliceLHSVal p Ψ q.1 (K0 hflow σ fp q)
  have hH_sm : StronglyMeasurable H_prod := hLHS_sm hK0_sm
  have hH_int : Integrable H_prod (volume.prod volume) := by
    let g1 : ℝ → ℝ := (Icc a'' b'').indicator fun _ => (1 : ℝ)
    have hg1 : Integrable g1 volume :=
      (integrable_indicator_iff measurableSet_Icc).2
        (integrableOn_const (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top))
    have hg2 : Integrable (fun τ => C_lhs * (A * h1RealNorm (fp τ))) volume :=
      (hfp_int.const_mul A).const_mul C_lhs
    refine (hg1.mul_prod hg2).mono' hH_sm.aestronglyMeasurable (Eventually.of_forall fun q => ?_)
    by_cases hq : q.1 ∈ Icc a'' b''
    · have hq_mem : q ∈ Icc a'' b'' ×ˢ (univ : Set ℝ) := ⟨hq, trivial⟩
      have hq_icc : q.1 ∈ Icc (0 : ℝ) (b'' + 2) := ⟨by linarith [hq.1], by linarith [hq.2]⟩
      dsimp only [H_prod, g1]
      rw [indicator_of_mem hq_mem, indicator_of_mem hq, one_mul]
      exact (hLHS_bd q.1 hq_icc _).trans
        (mul_le_mul_of_nonneg_left (K0_h1RealNorm_le hA hflow hσ hfp_mem q.1 q.2) hC_lhs_nn)
    · have hq_not : q ∉ Icc a'' b'' ×ˢ (univ : Set ℝ) := fun hm => hq hm.1
      dsimp only [H_prod, g1]
      rw [indicator_of_notMem hq_not, indicator_of_notMem hq, norm_zero, zero_mul]
  have hfub : (∫ s, ∫ τ, H_prod (s, τ)) = ∫ τ, ∫ s, H_prod (s, τ) := by
    rw [← integral_prod H_prod hH_int, integral_prod_symm H_prod hH_int]
  -- Decompose `sliceLHSVal p Ψ s (WPath ... s)` on `s ∈ Icc a'' b''`
  have hW_split : ∀ s ∈ Icc a'' b'',
      sliceLHSVal p Ψ s (WPath hflow σ x0 fp s) =
        sliceLHSVal p Ψ s (S0Val hflow s σ x0) + ∫ τ, H_prod (s, τ) := by
    intro s hs
    have hs_ioo : s ∈ Ioo σ (σ + 1) := ⟨lt_of_lt_of_le ha'' hs.1, lt_of_le_of_lt hs.2 hb''⟩
    have hs_nn : 0 ≤ s := (lt_of_lt_of_le ha''_pos hs.1).le
    obtain ⟨L, hL⟩ := hclm s hs_nn
    have hH_s : (fun τ => H_prod (s, τ)) =
        fun τ => L (K0 hflow σ fp (s, τ)) := by
      funext τ
      have hm : (s, τ) ∈ Icc a'' b'' ×ˢ (univ : Set ℝ) := ⟨hs, trivial⟩
      dsimp only [H_prod]
      rw [indicator_of_mem hm, hL]
    rw [hH_s, L.integral_comp_comm (hint_K0 s)]
    simp only [WPath, hs_ioo, ↓reduceIte, hL, map_add]
  have hH_left_ind : (fun s => ∫ τ, H_prod (s, τ)) =
      (Icc a'' b'').indicator (fun s => ∫ τ, H_prod (s, τ)) := by
    funext s
    by_cases hs : s ∈ Icc a'' b''
    · rw [indicator_of_mem hs]
    · rw [indicator_of_notMem hs]
      have hz : (fun τ => H_prod (s, τ)) = 0 :=
        funext fun τ => indicator_of_notMem (fun hm => hs hm.1) _
      simp [hz]
  have hint_H_icc : IntegrableOn (fun s => ∫ τ, H_prod (s, τ)) (Icc a'' b'') volume := by
    rw [← integrable_indicator_iff measurableSet_Icc, ← hH_left_ind]
    exact hH_int.integral_prod_left
  have hlhs_eq_fub :
      (∫ s in Icc a'' b'', sliceLHSVal p Ψ s (WPath hflow σ x0 fp s)) =
        ∫ τ, ∫ s, H_prod (s, τ) := by
    rw [setIntegral_congr_fun measurableSet_Icc hW_split,
      integral_add hint_init_icc hint_H_icc, hint_eq_init, zero_add,
      ← integral_indicator measurableSet_Icc, ← hH_left_ind, hfub]
  -- Evaluate `∫ s, H_prod (s, τ)` for every `τ : ℝ`
  let rhs_fn (τ : ℝ) : ℂ :=
    ∑ i : Fin 2, ∫ y in B0579.cell p.c,
      (fp τ).1 y i * (TailPeriodizeAux.qPeriodize p.c (fun x => Ψ x i) τ y : ℂ)
  have hinner_τ : (fun τ => ∫ s, H_prod (s, τ)) = (Icc a'' b'').indicator rhs_fn := by
    funext τ
    by_cases hτ_ioo : τ ∈ Ioo σ b''
    · have hτ_nn : 0 ≤ τ := by linarith [hτ_ioo.1]
      have hb''_τ1 : b'' ≤ τ + 1 := by linarith [hτ_ioo.1, hb'']
      obtain ⟨_, hftc_τ⟩ := single_orbit_ftc hA hreg hflow hΨ hb' hR hΨ_hi hΨ_eta
        hτ_nn hτ_ioo.2 hb''_τ1 (hfp_mem τ)
      have hae_s : (fun s => H_prod (s, τ)) =ᵐ[volume]
          (Ioc τ b'').indicator (fun s => sliceLHSVal p Ψ s (S0Val hflow s τ (fp τ))) := by
        have hne_ae : ∀ᵐ s ∂volume, s ≠ τ := by
          rw [ae_iff]; simp
        filter_upwards [hne_ae] with s hs_ne
        by_cases hs_icc : s ∈ Icc a'' b''
        · have hm : (s, τ) ∈ Icc a'' b'' ×ˢ (univ : Set ℝ) := ⟨hs_icc, trivial⟩
          dsimp only [H_prod]
          rw [indicator_of_mem hm]
          rcases lt_or_gt_of_ne hs_ne with hslt | hsgt
          · have hnot_tri : (s, τ) ∉ unitTriangle σ := fun ht => not_lt.2 hslt.le ht.2.1
            have hnot_ioc : s ∉ Ioc τ b'' := fun hm' => not_lt.2 hslt.le hm'.1
            obtain ⟨L, hL⟩ := hclm s (by linarith [hs_icc.1])
            simp only [K0, indicator_of_notMem hnot_tri, indicator_of_notMem hnot_ioc, hL, map_zero]
          · have htri : (s, τ) ∈ unitTriangle σ :=
              ⟨hτ_ioo.1, hsgt, lt_of_le_of_lt hs_icc.2 hb''⟩
            have hioc : s ∈ Ioc τ b'' := ⟨hsgt, hs_icc.2⟩
            simp only [K0, indicator_of_mem htri, indicator_of_mem hioc]
        · have hnot_m : (s, τ) ∉ Icc a'' b'' ×ˢ (univ : Set ℝ) := fun hm => hs_icc hm.1
          dsimp only [H_prod]
          rw [indicator_of_notMem hnot_m]
          by_cases hioc : s ∈ Ioc τ b''
          · rw [indicator_of_mem hioc]
            have hs_lt : s < a'' := by
              by_contra hge; exact hs_icc ⟨not_lt.1 hge, hioc.2⟩
            exact ((hLHS_lo hs_lt.le _).1).symm
          · rw [indicator_of_notMem hioc]
      rw [integral_congr_ae hae_s, integral_indicator measurableSet_Ioc, hftc_τ]
      by_cases hτ_icc : τ ∈ Icc a'' b''
      · rw [indicator_of_mem hτ_icc]
      · rw [indicator_of_notMem hτ_icc]
        have hτ_lt : τ < a'' := by
          by_contra hge; exact hτ_icc ⟨not_lt.1 hge, hτ_ioo.2.le⟩
        exact (hLHS_lo hτ_lt.le (fp τ)).2
    · have hz_s : (fun s => H_prod (s, τ)) = fun _ => 0 := by
        funext s
        by_cases hs_icc : s ∈ Icc a'' b''
        · have hm : (s, τ) ∈ Icc a'' b'' ×ˢ (univ : Set ℝ) := ⟨hs_icc, trivial⟩
          have hnot_tri : (s, τ) ∉ unitTriangle σ :=
            fun ht => hτ_ioo ⟨ht.1, lt_of_lt_of_le ht.2.1 hs_icc.2⟩
          obtain ⟨L, hL⟩ := hclm s (by linarith [hs_icc.1])
          simp only [H_prod, indicator_of_mem hm, K0, indicator_of_notMem hnot_tri, hL, map_zero]
        · have hnot_m : (s, τ) ∉ Icc a'' b'' ×ˢ (univ : Set ℝ) := fun hm => hs_icc hm.1
          simp [H_prod, hnot_m]
      rw [hz_s, integral_zero]
      by_cases hτ_icc : τ ∈ Icc a'' b''
      · rw [indicator_of_mem hτ_icc]
        have hτ_eq : τ = b'' := by
          by_contra hne
          exact hτ_ioo ⟨lt_of_lt_of_le ha'' hτ_icc.1, lt_of_le_of_ne hτ_icc.2 hne⟩
        rw [hτ_eq]
        have hq0 : ∀ i y, TailPeriodizeAux.qPeriodize p.c (fun x => Ψ x i) b'' y = 0 := by
          intro i y
          unfold TailPeriodizeAux.qPeriodize
          have h0 : (fun k : ℤ => Ψ (b'', (y.1 + (k : ℝ) * p.c, y.2)) i) = fun _ => 0 :=
            funext fun k => hΨ_hi i _ hb'
          rw [h0, tsum_zero]
        simp [rhs_fn, hq0]
      · rw [indicator_of_notMem hτ_icc]
  rw [hlhs_eq_fub, hinner_τ, integral_indicator measurableSet_Icc]

end UnforcedLeray.Short.IIb.UnitDuhamelStepAux

end
