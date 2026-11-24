import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.AdjTruncOrg.StreamPotOrg.Sub.PartIIIb_IIIb_D2_1_3_1_2_1_2_6.Defs
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.AdjTruncOrg.StreamPotOrg.Sub.PartIIIb_IIIb_D2_1_3_1_2_1_2_6.HLMaxMeasurable
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.AdjTruncOrg.StreamPotOrg.Sub.PartIIIb_IIIb_D2_1_3_1_2_1_2_6.HLMaxWeakL1
import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Marcinkiewicz (layer cake) for the Hardy-Littlewood maximal function: `HLMaxL2`

Source `the November 2 reference manuscript`, stream potential `L² -> L⁶` route.
Weak type `(1,1)` (`hlMaxWeakL1`) gives, for `l > 0`,
`hlMax G ≤ l + hlMax (G·1_{G>l})` pointwise, hence
`l · |{2l < M G}| ≤ 125 ∫_{G>l} G`.  The layer cake formula (Mathlib's
`lintegral_rpow_eq_lintegral_meas_lt_mul`, applied to the truncation `min (M G) c`, `c` finite)
and Tonelli then give `∫ (min (M G) c)² ≤ 1000 ∫ G²`; monotone convergence in `c = N`
gives `HLMaxL2`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Metric
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411

/-- Measurability of the truncated function `G·1_{G>l}`. -/
lemma hl_ind_meas (G : Space → ℝ≥0∞) (hG : Measurable G) (l : ℝ≥0∞) :
    Measurable ({z : Space | l < G z}.indicator G) :=
  hG.indicator (measurableSet_lt measurable_const hG)

/-- `M G ≤ l + M (G·1_{G>l})` pointwise. -/
lemma hl_pointwise_split (G : Space → ℝ≥0∞) (l : ℝ≥0∞) (y : Space) :
    hlMax G y ≤ l + hlMax ({z : Space | l < G z}.indicator G) y := by
  unfold hlMax
  refine iSup_le fun r => ?_
  have hV0 : volume (ball y r.1) ≠ 0 := (measure_ball_pos volume y r.2).ne'
  have hVt : volume (ball y r.1) ≠ ⊤ := measure_ball_lt_top.ne
  have hpt : ∀ z, G z ≤ l + {z : Space | l < G z}.indicator G z := by
    intro z
    by_cases hz : l < G z
    · rw [indicator_of_mem (show z ∈ {z : Space | l < G z} from hz)]
      exact le_add_self
    · rw [indicator_of_notMem (show z ∉ {z : Space | l < G z} from hz), add_zero]
      exact (not_lt.mp hz)
  have hint : ∫⁻ z in ball y r.1, G z
      ≤ l * volume (ball y r.1) + ∫⁻ z in ball y r.1, {z : Space | l < G z}.indicator G z := by
    calc ∫⁻ z in ball y r.1, G z
        ≤ ∫⁻ z in ball y r.1, (l + {z : Space | l < G z}.indicator G z) :=
          lintegral_mono fun z => hpt z
      _ = l * volume (ball y r.1) + ∫⁻ z in ball y r.1, {z : Space | l < G z}.indicator G z := by
          rw [lintegral_add_left measurable_const, setLIntegral_const]
  have hinv : (volume (ball y r.1))⁻¹ * (l * volume (ball y r.1)) = l := by
    rw [mul_comm l, ← mul_assoc, ENNReal.inv_mul_cancel hV0 hVt, one_mul]
  have hbound : (volume (ball y r.1))⁻¹ * ∫⁻ z in ball y r.1, G z
      ≤ l + (volume (ball y r.1))⁻¹ * ∫⁻ z in ball y r.1, {z : Space | l < G z}.indicator G z := by
    calc (volume (ball y r.1))⁻¹ * ∫⁻ z in ball y r.1, G z
        ≤ (volume (ball y r.1))⁻¹ *
            (l * volume (ball y r.1) + ∫⁻ z in ball y r.1, {z : Space | l < G z}.indicator G z) :=
          mul_le_mul_of_nonneg_left hint zero_le
      _ = l + (volume (ball y r.1))⁻¹ * ∫⁻ z in ball y r.1, {z : Space | l < G z}.indicator G z := by
          rw [mul_add, hinv]
  exact hbound.trans (add_le_add le_rfl
    (le_iSup (fun r' : {r : ℝ // 0 < r} =>
      (volume (ball y r'.1))⁻¹ * ∫⁻ z in ball y r'.1, {z : Space | l < G z}.indicator G z) r))

/-- Key Chebyshev-type inequality: `(l + l) |{2l < M G}| ≤ 250 ∫_{G>l} G`. -/
lemma hl_key_ineq (G : Space → ℝ≥0∞) (hG : Measurable G) (l : ℝ≥0∞) (hl0 : 0 < l)
    (hlt : l ≠ ⊤) :
    (l + l) * volume {y : Space | l + l < hlMax G y}
      ≤ 250 * ∫⁻ z, {z : Space | l < G z}.indicator G z := by
  have hIm : Measurable ({z : Space | l < G z}.indicator G) := hl_ind_meas G hG l
  have hsub : {y : Space | l + l < hlMax G y}
      ⊆ {y : Space | l < hlMax ({z : Space | l < G z}.indicator G) y} := by
    intro y hy
    simp only [mem_setOf_eq] at hy ⊢
    by_contra h
    push_neg at h
    have h2 := hl_pointwise_split G l y
    have h3 : hlMax G y ≤ l + l := h2.trans (add_le_add le_rfl h)
    exact lt_irrefl _ (lt_of_lt_of_le hy h3)
  have hW := hlMaxWeakL1 _ hIm l hl0 hlt
  have h1 : l * volume {y : Space | l + l < hlMax G y}
      ≤ 125 * ∫⁻ z, {z : Space | l < G z}.indicator G z := by
    calc l * volume {y : Space | l + l < hlMax G y}
        ≤ l * volume {y : Space | l < hlMax ({z : Space | l < G z}.indicator G) y} :=
          mul_le_mul_of_nonneg_left (measure_mono hsub) zero_le
      _ ≤ 125 * ∫⁻ z, {z : Space | l < G z}.indicator G z := hW
  calc (l + l) * volume {y : Space | l + l < hlMax G y}
      = l * volume {y : Space | l + l < hlMax G y} + l * volume {y : Space | l + l < hlMax G y} := by
        rw [add_mul]
    _ ≤ (125 * ∫⁻ z, {z : Space | l < G z}.indicator G z)
          + (125 * ∫⁻ z, {z : Space | l < G z}.indicator G z) := add_le_add h1 h1
    _ = 250 * ∫⁻ z, {z : Space | l < G z}.indicator G z := by ring

/-- Real-threshold form: for `t > 0`, `t · |{t < M G}| ≤ 250 ∫_{G > t/2} G`. -/
lemma hl_key_real (G : Space → ℝ≥0∞) (hG : Measurable G) (t : ℝ) (ht : 0 < t) :
    ENNReal.ofReal t * volume {y : Space | ENNReal.ofReal t < hlMax G y}
      ≤ 250 * ∫⁻ z, {z : Space | ENNReal.ofReal (t / 2) < G z}.indicator G z := by
  have hl2 : ENNReal.ofReal (t / 2) + ENNReal.ofReal (t / 2) = ENNReal.ofReal t := by
    rw [← ENNReal.ofReal_add (show (0:ℝ) ≤ t / 2 by linarith) (show (0:ℝ) ≤ t / 2 by linarith)]
    congr 1
    ring
  have h := hl_key_ineq G hG (ENNReal.ofReal (t / 2)) (ENNReal.ofReal_pos.mpr (by linarith))
    ENNReal.ofReal_ne_top
  rw [hl2] at h
  exact h

/-- Truncated layer cake: `∫ (min (M G) c)² ≤ 1000 ∫ G²` for finite `c`. -/
lemma hl_trunc_bound (G : Space → ℝ≥0∞) (hG : Measurable G) (c : ℝ≥0∞) (hc : c ≠ ⊤) :
    ∫⁻ y, (min (hlMax G y) c) ^ 2 ≤ 1000 * ∫⁻ z, (G z) ^ 2 := by
  have hMm : Measurable (hlMax G) := hlMaxMeasurable G hG
  set f : Space → ℝ := fun y => (min (hlMax G y) c).toReal with hf
  have hf_nn : 0 ≤ᵐ[volume] f :=
    Filter.Eventually.of_forall fun y => ENNReal.toReal_nonneg
  have hf_m : AEMeasurable f volume :=
    (ENNReal.measurable_toReal.comp (hMm.min measurable_const)).aemeasurable
  have hpt : ∀ y, (min (hlMax G y) c) ^ 2 = ENNReal.ofReal (f y ^ (2 : ℝ)) := by
    intro y
    have hxt : min (hlMax G y) c ≠ ⊤ := ne_top_of_le_ne_top hc (min_le_right _ _)
    rw [Real.rpow_two, hf]
    simp only
    rw [ENNReal.ofReal_pow ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hxt]
  have hL := lintegral_rpow_eq_lintegral_meas_lt_mul volume hf_nn hf_m (by norm_num : (0:ℝ) < 2)
  have hexp : ∀ t : ℝ, t ^ ((2 : ℝ) - 1) = t := by
    intro t
    norm_num
  -- pointwise bound for each `t > 0`
  have hstep : ∀ t ∈ Ioi (0:ℝ),
      volume {a : Space | t < f a} * ENNReal.ofReal (t ^ ((2 : ℝ) - 1))
        ≤ 250 * ∫⁻ z, {z : Space | ENNReal.ofReal (t / 2) < G z}.indicator G z := by
    intro t ht
    have ht' : (0:ℝ) < t := ht
    rw [hexp t]
    have hsub : {a : Space | t < f a} ⊆ {a : Space | ENNReal.ofReal t < hlMax G a} := by
      intro a ha
      simp only [mem_setOf_eq, hf] at ha ⊢
      have hxt : min (hlMax G a) c ≠ ⊤ := ne_top_of_le_ne_top hc (min_le_right _ _)
      have h1 : ENNReal.ofReal t < min (hlMax G a) c :=
        (ENNReal.ofReal_lt_iff_lt_toReal ht'.le hxt).mpr ha
      exact lt_of_lt_of_le h1 (min_le_left _ _)
    have hm := measure_mono (μ := volume) hsub
    calc volume {a : Space | t < f a} * ENNReal.ofReal t
        ≤ volume {a : Space | ENNReal.ofReal t < hlMax G a} * ENNReal.ofReal t :=
          mul_le_mul_of_nonneg_right hm zero_le
      _ = ENNReal.ofReal t * volume {a : Space | ENNReal.ofReal t < hlMax G a} := mul_comm _ _
      _ ≤ 250 * ∫⁻ z, {z : Space | ENNReal.ofReal (t / 2) < G z}.indicator G z :=
          hl_key_real G hG t ht'
  -- Tonelli
  set F : ℝ → Space → ℝ≥0∞ :=
    fun t z => {z : Space | ENNReal.ofReal (t / 2) < G z}.indicator G z with hFdef
  have hUnc : Measurable (Function.uncurry F) := by
    have hA : Measurable (fun p : ℝ × Space => ENNReal.ofReal (p.1 / 2)) :=
      ENNReal.measurable_ofReal.comp (measurable_fst.div_const 2)
    have hB : Measurable (fun p : ℝ × Space => G p.2) := hG.comp measurable_snd
    have hS : MeasurableSet {p : ℝ × Space | ENNReal.ofReal (p.1 / 2) < G p.2} :=
      measurableSet_lt hA hB
    have heq : Function.uncurry F
        = {p : ℝ × Space | ENNReal.ofReal (p.1 / 2) < G p.2}.indicator (fun p => G p.2) := by
      ext p
      simp [hFdef, Function.uncurry, Set.indicator]
    rw [heq]
    exact hB.indicator hS
  -- for each z, the t-integral of `F t z` is at most `2 G(z)²`
  have hzbound : ∀ z : Space, ∫⁻ t in Ioi (0:ℝ), F t z ≤ 2 * (G z) ^ 2 := by
    intro z
    rcases eq_or_ne (G z) ⊤ with hgz | hgz
    · rw [hgz, ENNReal.top_pow two_ne_zero, ENNReal.mul_top two_ne_zero]
      exact le_top
    · have hg := hgz
      set a : ℝ := 2 * (G z).toReal with ha
      have hpt2 : ∀ t ∈ Ioi (0:ℝ), F t z ≤ (Ioo 0 a).indicator (fun _ => G z) t := by
        intro t ht
        have ht' : (0:ℝ) < t := ht
        by_cases hc2 : ENNReal.ofReal (t / 2) < G z
        · have hFt : F t z = G z := by
            simp only [hFdef]
            rw [indicator_of_mem (show z ∈ {z : Space | ENNReal.ofReal (t / 2) < G z} from hc2)]
          have hta : t < a := by
            have := (ENNReal.ofReal_lt_iff_lt_toReal (show (0:ℝ) ≤ t / 2 by linarith) hg).mp hc2
            rw [ha]
            linarith
          rw [hFt, indicator_of_mem (show t ∈ Ioo 0 a from ⟨ht', hta⟩)]
        · have hFt : F t z = 0 := by
            simp only [hFdef]
            rw [indicator_of_notMem (show z ∉ {z : Space | ENNReal.ofReal (t / 2) < G z} from hc2)]
          rw [hFt]
          exact zero_le
      have hmeas : Measurable ((Ioo (0:ℝ) a).indicator (fun _ : ℝ => G z)) :=
        measurable_const.indicator measurableSet_Ioo
      calc ∫⁻ t in Ioi (0:ℝ), F t z
          ≤ ∫⁻ t in Ioi (0:ℝ), (Ioo 0 a).indicator (fun _ => G z) t :=
            setLIntegral_mono hmeas hpt2
        _ ≤ ∫⁻ t, (Ioo 0 a).indicator (fun _ => G z) t := setLIntegral_le_lintegral _ _
        _ = G z * volume (Ioo (0:ℝ) a) := lintegral_indicator_const measurableSet_Ioo _
        _ = G z * (2 * G z) := by
            rw [Real.volume_Ioo, sub_zero, ha, ENNReal.ofReal_mul zero_le_two,
              ENNReal.ofReal_toReal hg, ENNReal.ofReal_ofNat]
        _ ≤ 2 * (G z) ^ 2 := le_of_eq (by ring)
  -- measurability of the t-integrand
  have hmeasI : Measurable (fun t : ℝ => 250 * ∫⁻ z, F t z) :=
    measurable_const.mul hUnc.lintegral_prod_right'
  -- assemble
  calc ∫⁻ y, (min (hlMax G y) c) ^ 2
      = ∫⁻ y, ENNReal.ofReal (f y ^ (2 : ℝ)) := lintegral_congr fun y => hpt y
    _ = ENNReal.ofReal 2 * ∫⁻ t in Ioi 0, volume {a : Space | t < f a}
          * ENNReal.ofReal (t ^ ((2 : ℝ) - 1)) := hL
    _ ≤ ENNReal.ofReal 2 * ∫⁻ t in Ioi 0, 250 * ∫⁻ z, F t z :=
        mul_le_mul_of_nonneg_left (setLIntegral_mono hmeasI hstep) zero_le
    _ = 500 * ∫⁻ t in Ioi 0, ∫⁻ z, F t z := by
        rw [ENNReal.ofReal_ofNat, lintegral_const_mul' 250 (fun t => ∫⁻ z, F t z) (by norm_num)]
        ring
    _ = 500 * ∫⁻ z, ∫⁻ t in Ioi 0, F t z := by
        rw [lintegral_lintegral_swap hUnc.aemeasurable]
    _ ≤ 500 * ∫⁻ z, 2 * (G z) ^ 2 :=
        mul_le_mul_of_nonneg_left (lintegral_mono fun z => hzbound z) zero_le
    _ = 1000 * ∫⁻ z, (G z) ^ 2 := by
        rw [lintegral_const_mul' 2 (fun z => (G z) ^ 2) (by norm_num)]
        ring

/-- `HLMaxL2`: the strong `(2,2)` bound for the Hardy-Littlewood maximal function. -/
theorem hlMaxL2 : HLMaxL2 := by
  intro G hG
  have hMm : Measurable (hlMax G) := hlMaxMeasurable G hG
  have hNle : ∀ N : ℕ, (N : ℝ≥0∞) ≤ (N : ℝ≥0∞) ^ 2 := by
    intro N
    rcases Nat.eq_zero_or_pos N with h0 | hpos
    · subst h0
      simp
    · have h1 : (1 : ℝ≥0∞) ≤ N := by exact_mod_cast hpos
      calc (N : ℝ≥0∞) = N * 1 := (mul_one _).symm
        _ ≤ N * N := by gcongr
        _ = (N : ℝ≥0∞) ^ 2 := (sq _).symm
  have hpt : ∀ y, hlMax G y ^ 2 = ⨆ N : ℕ, (min (hlMax G y) (N : ℝ≥0∞)) ^ 2 := by
    intro y
    apply le_antisymm
    · by_cases hM : hlMax G y = ⊤
      · rw [hM, ENNReal.top_pow two_ne_zero]
        calc (⊤ : ℝ≥0∞) = ⨆ N : ℕ, (N : ℝ≥0∞) := ENNReal.iSup_natCast.symm
          _ ≤ ⨆ N : ℕ, (min ⊤ (N : ℝ≥0∞)) ^ 2 :=
              iSup_mono fun N => by rw [min_eq_right le_top]; exact hNle N
      · obtain ⟨N, hN⟩ := ENNReal.exists_nat_gt hM
        calc hlMax G y ^ 2 = (min (hlMax G y) (N : ℝ≥0∞)) ^ 2 := by rw [min_eq_left hN.le]
          _ ≤ ⨆ N : ℕ, (min (hlMax G y) (N : ℝ≥0∞)) ^ 2 :=
              le_iSup (fun N : ℕ => (min (hlMax G y) (N : ℝ≥0∞)) ^ 2) N
    · exact iSup_le fun N => by gcongr; exact min_le_left _ _
  calc ∫⁻ y, hlMax G y ^ 2
      = ∫⁻ y, ⨆ N : ℕ, (min (hlMax G y) (N : ℝ≥0∞)) ^ 2 := lintegral_congr fun y => hpt y
    _ = ⨆ N : ℕ, ∫⁻ y, (min (hlMax G y) (N : ℝ≥0∞)) ^ 2 := by
        refine lintegral_iSup (f := fun N : ℕ => fun y => (min (hlMax G y) (N : ℝ≥0∞)) ^ 2)
          (fun N => (hMm.min measurable_const).pow_const 2) ?_
        intro a b hab y
        dsimp only
        gcongr
    _ ≤ 1000 * ∫⁻ z, (G z) ^ 2 :=
        iSup_le fun N => hl_trunc_bound G hG (N : ℝ≥0∞) (ENNReal.natCast_ne_top N)

end UnforcedLeray.Short.PartIIIb.Concrete
