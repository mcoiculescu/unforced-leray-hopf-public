import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_1.LerayDefs

/-!
# `L²` membership of a decaying band field (`MemLpOfDecay`)

Source `the November 2 reference manuscript` 1642-1644 (weight `s^{-3/2}` of `H`).
A continuous field supported in an `s`-band `[s0, s1]` with `s0 > 0` and exponential decay in `η`
is dominated by `G(p) = 2|C| 1_{[s0,s1]}(s) e^{-κ|η|}`, and `G² = 4C² 1_{[s0,s1]}(s) e^{-2κ|η|}`
has finite `measureH c`-integral: `measureH c = (volume.restrict cell).withDensity weightH`, the
cell lies in `s > 0`, `q ∈ (0, c]`, and the integral factorises over `s`, `q`, `η`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

theorem memLpOfDecay : MemLpOfDecay := by
  intro c hc v hcont hband hdec
  obtain ⟨s0, s1, hs0, hsupp⟩ := hband
  obtain ⟨C, κ, hκ, hdec'⟩ := hdec
  have hκ2 : (0 : ℝ) < 2 * κ := by linarith
  have hnorm2 : ∀ w : Fin 2 → ℝ, ‖cvec w‖ ^ 2 = w 0 ^ 2 + w 1 ^ 2 := by
    intro w
    simp [cvec, PiLp.norm_sq_eq_of_L2, Fin.sum_univ_two, Complex.norm_real, Real.norm_eq_abs,
      sq_abs]
  have hdec2 : ∀ (p : Chart) (i : Fin 2), |v p i| ≤ |C| * Real.exp (-(κ * |p.2.2|)) := fun p i =>
    (hdec' p i).trans (mul_le_mul_of_nonneg_right (le_abs_self C) (Real.exp_pos _).le)
  have he2 : ∀ η : ℝ, Real.exp (-(κ * |η|)) ^ 2 = Real.exp (-((2 * κ) * |η|)) := by
    intro η
    rw [sq, ← Real.exp_add]
    congr 1
    ring
  -- the real majorant
  obtain ⟨G, hG⟩ : ∃ G : Chart → ℝ, G = fun p =>
      (Icc s0 s1).indicator (fun _ => 2 * |C|) p.1 * Real.exp (-(κ * |p.2.2|)) := ⟨_, rfl⟩
  have hGp_in : ∀ p : Chart, p.1 ∈ Icc s0 s1 → G p = 2 * |C| * Real.exp (-(κ * |p.2.2|)) := by
    intro p hp
    rw [hG]
    simp [Set.indicator_of_mem hp]
  have hGp_out : ∀ p : Chart, p.1 ∉ Icc s0 s1 → G p = 0 := by
    intro p hp
    rw [hG]
    simp [Set.indicator_of_notMem hp]
  have hGle : ∀ p : Chart, ‖cvec (v p)‖ ≤ G p := by
    intro p
    by_cases hp : p.1 ∈ Icc s0 s1
    · rw [hGp_in p hp]
      have hsq := hnorm2 (v p)
      have h0 := hdec2 p 0
      have h1 := hdec2 p 1
      have e0 : 0 ≤ Real.exp (-(κ * |p.2.2|)) := (Real.exp_pos _).le
      have a0 := sq_le_sq' (abs_le.mp h0).1 (abs_le.mp h0).2
      have a1 := sq_le_sq' (abs_le.mp h1).1 (abs_le.mp h1).2
      have hX : 0 ≤ 2 * |C| * Real.exp (-(κ * |p.2.2|)) := by positivity
      have hsq2 : ‖cvec (v p)‖ ^ 2 ≤ (2 * |C| * Real.exp (-(κ * |p.2.2|))) ^ 2 := by
        rw [hsq]
        nlinarith [a0, a1, sq_nonneg (|C| * Real.exp (-(κ * |p.2.2|)))]
      nlinarith [norm_nonneg (cvec (v p)), hX, hsq2]
    · have hv : v p = 0 := by
        by_contra h
        exact hp (hsupp p h)
      have h0 : cvec (0 : Fin 2 → ℝ) = 0 := by
        ext i
        simp [cvec]
      rw [hGp_out p hp, hv, h0, norm_zero]
  have hcv : Continuous fun p : Chart => cvec (v p) := by
    simp only [cvec]
    exact (PiLp.continuous_toLp 2 _).comp
      (continuous_pi fun i => Complex.continuous_ofReal.comp (hcont i))
  have hGm : Measurable G := by
    rw [hG]
    exact Measurable.mul ((measurable_const.indicator measurableSet_Icc).comp measurable_fst)
      (by fun_prop)
  have hG2m : Measurable fun p : Chart => G p ^ 2 := hGm.pow_const 2
  -- the one-dimensional factors
  obtain ⟨A, hA⟩ : ∃ A : ℝ → ℝ≥0∞, A = fun s =>
      (Icc s0 s1).indicator (fun s => ENNReal.ofReal (s ^ (-(3 / 2 : ℝ)))) s := ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ B : ℝ → ℝ≥0∞, B = fun q => (Ioc 0 c).indicator (fun _ => (1 : ℝ≥0∞)) q :=
    ⟨_, rfl⟩
  obtain ⟨E, hE⟩ : ∃ E : ℝ → ℝ≥0∞, E = fun η =>
      ENNReal.ofReal (Real.exp (-((2 * κ) * |η|))) := ⟨_, rfl⟩
  have hAm : Measurable A := by
    rw [hA]
    exact Measurable.indicator (ENNReal.measurable_ofReal.comp (measurable_id.pow_const _))
      measurableSet_Icc
  have hBm : Measurable B := by
    rw [hB]
    exact measurable_const.indicator measurableSet_Ioc
  have hEm : Measurable E := by
    rw [hE]
    exact ENNReal.measurable_ofReal.comp
      (Real.continuous_exp.comp (by fun_prop : Continuous fun η : ℝ => -((2 * κ) * |η|))).measurable
  -- integrability of the η-factor
  have hEint : Integrable (fun η : ℝ => Real.exp (-((2 * κ) * |η|))) := by
    have h1 : IntegrableOn (fun η : ℝ => Real.exp (-((2 * κ) * |η|))) (Ioi 0) := by
      refine (exp_neg_integrableOn_Ioi 0 hκ2).congr_fun (fun x hx => ?_) measurableSet_Ioi
      have hx' : 0 < x := hx
      show Real.exp (-(2 * κ) * x) = Real.exp (-((2 * κ) * |x|))
      rw [abs_of_pos hx', neg_mul]
    have h2 : IntegrableOn (fun η : ℝ => Real.exp (-((2 * κ) * |η|))) (Iic 0) := by
      refine (integrableOn_exp_mul_Iic hκ2 0).congr_fun (fun x hx => ?_) measurableSet_Iic
      have hx' : x ≤ 0 := hx
      show Real.exp ((2 * κ) * x) = Real.exp (-((2 * κ) * |x|))
      rw [abs_of_nonpos hx', mul_neg, neg_neg]
    have h3 : IntegrableOn (fun η : ℝ => Real.exp (-((2 * κ) * |η|))) (Ioi 0 ∪ Iic 0) :=
      h1.union h2
    rw [Set.union_comm, Set.Iic_union_Ioi] at h3
    exact integrableOn_univ.mp h3
  have hEfin : ∫⁻ η, E η < ⊤ := by
    rw [hE]
    exact hEint.lintegral_lt_top
  have hAfin : ∫⁻ s, A s < ⊤ := by
    have hApt : ∀ s : ℝ, A s ≤ (Icc s0 s1).indicator (fun _ => ENNReal.ofReal (s0 ^ (-(3 / 2 : ℝ)))) s := by
      intro s
      rw [hA]
      by_cases hs : s ∈ Icc s0 s1
      · simp only [Set.indicator_of_mem hs]
        exact ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow_of_nonpos hs0 hs.1 (by norm_num))
      · simp [Set.indicator_of_notMem hs]
    refine lt_of_le_of_lt (lintegral_mono hApt) ?_
    rw [lintegral_indicator_const measurableSet_Icc]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top
      (by rw [Real.volume_Icc]; exact ENNReal.ofReal_lt_top)
  have hBfin : ∫⁻ q, B q < ⊤ := by
    simp only [hB]
    rw [lintegral_indicator_const measurableSet_Ioc, one_mul, Real.volume_Ioc]
    exact ENNReal.ofReal_lt_top
  -- the product integral
  have hfin : ∫⁻ p : Chart, A p.1 * (B p.2.1 * (ENNReal.ofReal (4 * C ^ 2) * E p.2.2)) < ⊤ := by
    have hvol3 : (volume : Measure (ℝ × (ℝ × ℝ))) =
        (volume : Measure ℝ).prod (volume : Measure (ℝ × ℝ)) := Measure.volume_eq_prod _ _
    have hvol2 : (volume : Measure (ℝ × ℝ)) = (volume : Measure ℝ).prod (volume : Measure ℝ) :=
      Measure.volume_eq_prod _ _
    have hg1 : Measurable fun y : ℝ × ℝ => B y.1 * (ENNReal.ofReal (4 * C ^ 2) * E y.2) :=
      (hBm.comp measurable_fst).mul (measurable_const.mul (hEm.comp measurable_snd))
    have hg2 : Measurable fun η : ℝ => ENNReal.ofReal (4 * C ^ 2) * E η :=
      measurable_const.mul hEm
    have step1 : ∫⁻ p : Chart, A p.1 * (B p.2.1 * (ENNReal.ofReal (4 * C ^ 2) * E p.2.2)) =
        (∫⁻ s, A s) * ∫⁻ y : ℝ × ℝ, B y.1 * (ENNReal.ofReal (4 * C ^ 2) * E y.2) := by
      rw [hvol3]
      exact lintegral_prod_mul hAm.aemeasurable hg1.aemeasurable
    have step2 : ∫⁻ y : ℝ × ℝ, B y.1 * (ENNReal.ofReal (4 * C ^ 2) * E y.2) =
        (∫⁻ q, B q) * ∫⁻ η, ENNReal.ofReal (4 * C ^ 2) * E η := by
      rw [hvol2]
      exact lintegral_prod_mul hBm.aemeasurable hg2.aemeasurable
    have step3 : ∫⁻ η, ENNReal.ofReal (4 * C ^ 2) * E η =
        ENNReal.ofReal (4 * C ^ 2) * ∫⁻ η, E η :=
      lintegral_const_mul _ hEm
    rw [step1, step2, step3]
    exact ENNReal.mul_lt_top hAfin
      (ENNReal.mul_lt_top hBfin (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hEfin))
  -- the lower-dimensional lintegral bound for `G²` against `measureH c`
  have hmain : ∫⁻ p : Chart, ENNReal.ofReal (G p ^ 2) ∂(UnforcedLeray.B0220.measureH c) < ⊤ := by
    have hΦm : Measurable fun p : Chart => ENNReal.ofReal (G p ^ 2) :=
      ENNReal.measurable_ofReal.comp hG2m
    rw [UnforcedLeray.B0220.measureH,
      lintegral_withDensity_eq_lintegral_mul _ UnforcedLeray.B0220.measurable_weightH hΦm]
    rw [UnforcedLeray.B0220.cellMeasure, ← lintegral_indicator (UnforcedLeray.B0220.measurableSet_cell c)]
    refine lt_of_le_of_lt (lintegral_mono fun p => ?_) hfin
    by_cases hp : p ∈ UnforcedLeray.B0220.cell c
    · have hs : 0 < p.1 := hp.1
      have hq : p.2.1 ∈ Ioc 0 c := hp.2.1
      rw [Set.indicator_of_mem hp]
      by_cases hI : p.1 ∈ Icc s0 s1
      · have hsq_eq : G p ^ 2 = 4 * C ^ 2 * Real.exp (-((2 * κ) * |p.2.2|)) := by
          rw [hGp_in p hI, mul_pow, mul_pow, sq_abs, he2]
          ring
        simp only [hA, hB, hE, Pi.mul_apply, UnforcedLeray.B0220.weightH, Set.indicator_of_mem hI,
          Set.indicator_of_mem hq, hsq_eq, one_mul]
        rw [ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 4 * C ^ 2)]
      · have hG0 : G p ^ 2 = 0 := by
          rw [hGp_out p hI]
          norm_num
        simp [hA, hB, hE, Pi.mul_apply, UnforcedLeray.B0220.weightH, hG0]
    · rw [Set.indicator_of_notMem hp]
      exact zero_le
  refine MemLp.of_le (g := G) ?_ hcv.aestronglyMeasurable (Filter.Eventually.of_forall fun p => by
      rw [Real.norm_eq_abs]
      exact (hGle p).trans (le_abs_self _))
  rw [memLp_two_iff_integrable_sq hGm.aestronglyMeasurable]
  exact ⟨hG2m.aestronglyMeasurable,
    (hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall fun p => sq_nonneg (G p))).2 hmain⟩

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
