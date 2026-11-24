import UnforcedLeray.Short.PartIIa.Tasks.F03cWindowBackEquation.Transfer

/-!
# Part II-a, task `PartII-a:F03/3` helper: integrability for `WindowBackEquation`

Integrability facts used by `WindowBackEquation` (`Sub/F03.lean`):

* `slab_memLp`: the component `W · c` of a jointly measurable representative is `L^r` on every
  slab `[A, B] × ℝ³` (`lintegral_rep`, `lintegral_window_lt_top`);
* `integrable_of_memLp_mul`: an `L^r` function times a continuous compactly supported function
  is integrable (Hölder with `conjExp r`);
* `windowField_memLp`: the transformed field `windowField χ τ₀ W c` is `L^r(ℝ × ℝ³)`
  (the charts `expChart`, `dilChart` and the window cutoff `χ`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace UnforcedLeray.Short.PartIIa.WinBack

open UnforcedLeray.PhaseSpace UnforcedLeray.Parabolic UnforcedLeray.B0424
  UnforcedLeray.Short.PartIIa.Rep

variable {P : ℝ} [Fact (0 < P)]

theorem rpow_pos_of_one_le {r : ℝ≥0∞} [Fact (1 ≤ r)] (hrt : r ≠ ⊤) : 0 < r.toReal :=
  ENNReal.toReal_pos (zero_lt_one.trans_le Fact.out).ne' hrt

theorem enorm_ofReal_cast (x : ℝ) : ‖(x : ℂ)‖ₑ = ‖x‖ₑ := by
  rw [← ofReal_norm, ← ofReal_norm, Complex.norm_real]

theorem measurable_slab (A B : ℝ) : MeasurableSet (Icc A B ×ˢ (univ : Set Space)) :=
  measurableSet_Icc.prod MeasurableSet.univ

/-! ### Slab integrals of the representative -/

theorem slab_lintegral_lt_top {r : ℝ≥0∞} [Fact (1 ≤ r)] (hrt : r ≠ ⊤) {w : Yq P r}
    {W : ℝ × Space → CVec3} (hW : IsRep w W) (τ₀ A B : ℝ) :
    ∫⁻ q, (Icc A B ×ˢ (univ : Set Space)).indicator (fun q => ‖W q‖ₑ ^ r.toReal) q < ⊤ := by
  set m : ℝ → ℝ≥0∞ := (Icc (A - τ₀) (B - τ₀)).indicator (fun _ => 1) with hm
  have hmm : Measurable m := measurable_const.indicator measurableSet_Icc
  have hsl : ∀ q : ℝ × Space,
      (Icc A B ×ˢ (univ : Set Space)).indicator (fun q => ‖W q‖ₑ ^ r.toReal) (τ₀ + q.1, q.2) =
        m q.1 * ‖W (τ₀ + q.1, q.2)‖ₑ ^ r.toReal := by
    intro q
    by_cases hq : τ₀ + q.1 ∈ Icc A B
    · have hq' : q.1 ∈ Icc (A - τ₀) (B - τ₀) := ⟨by linarith [hq.1], by linarith [hq.2]⟩
      have hp : (τ₀ + q.1, q.2) ∈ Icc A B ×ˢ (univ : Set Space) := ⟨hq, mem_univ _⟩
      rw [Set.indicator_of_mem hp, hm, Set.indicator_of_mem hq']
      simp
    · have hq' : q.1 ∉ Icc (A - τ₀) (B - τ₀) :=
        fun h => hq ⟨by linarith [h.1], by linarith [h.2]⟩
      have hp : (τ₀ + q.1, q.2) ∉ Icc A B ×ˢ (univ : Set Space) := fun h => hq h.1
      rw [Set.indicator_of_notMem hp, hm, Set.indicator_of_notMem hq']
      simp
  have h1 : ∫⁻ q, (Icc A B ×ˢ (univ : Set Space)).indicator (fun q => ‖W q‖ₑ ^ r.toReal) q =
      ∫⁻ p : ℝ × Space, m p.1 * ‖W (τ₀ + p.1, p.2)‖ₑ ^ r.toReal :=
    (lintegral_shift τ₀ ((Icc A B ×ˢ (univ : Set Space)).indicator
      (fun q => ‖W q‖ₑ ^ r.toReal))).symm.trans (lintegral_congr fun p => hsl p)
  have hm2 : ∀ t : ℝ, m t * ‖w ((τ₀ + t : ℝ) : AddCircle P)‖ₑ ^ r.toReal =
      (Icc (A - τ₀) (B - τ₀)).indicator
        (fun t => ‖w ((τ₀ + t : ℝ) : AddCircle P)‖ₑ ^ r.toReal) t := by
    intro t
    by_cases ht : t ∈ Icc (A - τ₀) (B - τ₀)
    · simp [hm, ht]
    · simp [hm, ht]
  have h3 : ∫⁻ t, m t * ‖w ((τ₀ + t : ℝ) : AddCircle P)‖ₑ ^ r.toReal =
      ∫⁻ t in Icc (A - τ₀) (B - τ₀), ‖w ((τ₀ + t : ℝ) : AddCircle P)‖ₑ ^ r.toReal := by
    rw [lintegral_congr hm2, lintegral_indicator measurableSet_Icc]
  rw [h1, lintegral_rep hrt hW τ₀ hmm, h3]
  exact lintegral_window_lt_top hrt w τ₀ (A - τ₀) (B - τ₀)

theorem slab_memLp {r : ℝ≥0∞} [Fact (1 ≤ r)] (hrt : r ≠ ⊤) {w : Yq P r}
    {W : ℝ × Space → CVec3} (hW : IsRep w W) (τ₀ A B : ℝ) (c : Fin 3) :
    MemLp ((Icc A B ×ˢ (univ : Set Space)).indicator (fun q => W q c)) r volume := by
  have hs : 0 < r.toReal := rpow_pos_of_one_le hrt
  have hcomp : Measurable (fun v : CVec3 => v c) := (PiLp.continuous_apply 2 (fun _ : Fin 3 => ℂ) c).measurable
  have hmeas : Measurable ((Icc A B ×ˢ (univ : Set Space)).indicator (fun q => W q c)) :=
    (hcomp.comp hW.meas.measurable).indicator (measurable_slab A B)
  refine ⟨hmeas.aestronglyMeasurable, ?_⟩
  have hfin := slab_lintegral_lt_top hrt hW τ₀ A B
  have hpt : ∀ x : ℝ × Space,
      ‖(Icc A B ×ˢ (univ : Set Space)).indicator (fun q => W q c) x‖ₑ ^ r.toReal ≤
        (Icc A B ×ˢ (univ : Set Space)).indicator (fun q => ‖W q‖ₑ ^ r.toReal) x := by
    intro x
    by_cases hx : x ∈ Icc A B ×ˢ (univ : Set Space)
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx]
      exact ENNReal.rpow_le_rpow (PiLp.enorm_apply_le (W x) c) hs.le
    · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx]
      simp [ENNReal.zero_rpow_of_pos hs]
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (zero_lt_one.trans_le (Fact.out : (1 : ℝ≥0∞) ≤ r)).ne'
    hrt]
  refine ENNReal.rpow_lt_top_of_nonneg (one_div_nonneg.2 hs.le) ?_
  exact ((lintegral_mono hpt).trans_lt hfin).ne

/-! ### Products with continuous compactly supported tests -/

theorem integrable_of_memLp_mul {r : ℝ≥0∞} [Fact (1 ≤ r)] {f : ℝ × Space → ℂ}
    (hf : MemLp f r volume) {g : ℝ × Space → ℂ} (hg : Continuous g)
    (hgc : HasCompactSupport g) : Integrable (fun p => f p * g p) volume := by
  have : ENNReal.HolderConjugate r (conjExp r) := inferInstance
  have hg' : MemLp g (conjExp r) volume := hg.memLp_of_hasCompactSupport hgc
  exact hf.integrable_mul hg'

/-! ### The transformed field is `L^r` -/

theorem measurable_windowField {χ : ℝ → ℝ} (hχ : WindowCutoff χ) (τ₀ : ℝ)
    {W : ℝ × Space → CVec3} (hW : Measurable W) (c : Fin 3) :
    Measurable (windowField χ τ₀ W c) := by
  have hχm : Measurable χ := hχ.smooth.continuous.measurable
  have hlog : Measurable (fun p : PS 3 => Real.log p.1) := Real.measurable_log.comp measurable_fst
  have hr : Measurable (fun p : PS 3 =>
      ((χ (Real.log p.1) * Real.exp (-(Real.log p.1 / 2)) : ℝ) : ℂ)) :=
    Complex.measurable_ofReal.comp
      ((hχm.comp hlog).mul (Real.measurable_exp.comp (hlog.div_const 2).neg))
  have hcomp : Measurable (fun v : CVec3 => v c) := (PiLp.continuous_apply 2 (fun _ : Fin 3 => ℂ) c).measurable
  have hpt : Measurable (fun p : PS 3 =>
      W (τ₀ + Real.log p.1, Real.exp (-(Real.log p.1 / 2)) • p.2) c) :=
    hcomp.comp (hW.comp (by fun_prop))
  unfold windowField
  exact Measurable.ite (measurableSet_lt measurable_const measurable_fst) (hr.mul hpt)
    measurable_const

theorem lintegral_norm_expChart {f : PS 3 → ℂ} {s : ℝ} (hs : 0 < s)
    (hf0 : ∀ p : ℝ × Space, p.1 ≤ 0 → f p = 0) :
    ∫⁻ p, ‖f p‖ₑ ^ s = ∫⁻ p, ENNReal.ofReal (Real.exp p.1) * ‖f (expChart p)‖ₑ ^ s := by
  have hsupp : (fun p => ‖f p‖ₑ ^ s).support ⊆ Ioi (0 : ℝ) ×ˢ (univ : Set Space) := by
    intro p hp
    rw [Function.mem_support] at hp
    by_contra h
    apply hp
    have hp1 : p.1 ≤ 0 := by
      simp only [mem_prod, mem_Ioi, mem_univ, and_true, not_lt] at h
      exact h
    simp [hf0 p hp1, ENNReal.zero_rpow_of_pos hs]
  calc ∫⁻ p, ‖f p‖ₑ ^ s = ∫⁻ p in Ioi (0 : ℝ) ×ˢ (univ : Set Space), ‖f p‖ₑ ^ s :=
        (setLIntegral_eq_of_support_subset hsupp).symm
    _ = ∫⁻ p, ENNReal.ofReal (Real.exp p.1) * ‖f (expChart p)‖ₑ ^ s :=
        lintegral_expChart' (fun p => ‖f p‖ₑ ^ s)

theorem lintegral_pullback {r : ℝ≥0∞} [Fact (1 ≤ r)] (hrt : r ≠ ⊤) {w : Yq P r}
    {W : ℝ × Space → CVec3} (hW : IsRep w W) (τ₀ : ℝ) {m : ℝ → ℝ≥0∞} (hm : Measurable m) :
    ∫⁻ p : ℝ × Space, m p.1 * ‖W (τ₀ + p.1, Real.exp (-(p.1 / 2)) • p.2)‖ₑ ^ r.toReal =
      ∫⁻ t, ENNReal.ofReal (Real.exp (3 * t / 2)) * m t *
        ‖w ((τ₀ + t : ℝ) : AddCircle P)‖ₑ ^ r.toReal := by
  have hm' : Measurable fun t : ℝ => ENNReal.ofReal (Real.exp (3 * t / 2)) * m t := by
    fun_prop
  calc ∫⁻ p : ℝ × Space, m p.1 * ‖W (τ₀ + p.1, Real.exp (-(p.1 / 2)) • p.2)‖ₑ ^ r.toReal
      = ∫⁻ p : ℝ × Space, ENNReal.ofReal (Real.exp (3 * p.1 / 2)) * m p.1 *
          ‖W (τ₀ + p.1, p.2)‖ₑ ^ r.toReal := by
        conv_lhs => rw [lintegral_dilChart']
        refine lintegral_congr fun p => ?_
        simp only [dilChart, rhoD, smul_smul, ← Real.exp_add, neg_add_cancel, Real.exp_zero,
          one_smul]
        ring
    _ = ∫⁻ t, ENNReal.ofReal (Real.exp (3 * t / 2)) * m t *
          ‖w ((τ₀ + t : ℝ) : AddCircle P)‖ₑ ^ r.toReal :=
        lintegral_rep hrt hW τ₀ hm'

theorem windowField_memLp {r : ℝ≥0∞} [Fact (1 ≤ r)] (hrt : r ≠ ⊤) {w : Yq P r}
    {W : ℝ × Space → CVec3} (hW : IsRep w W) {χ : ℝ → ℝ} (hχ : WindowCutoff χ) (τ₀ : ℝ)
    (c : Fin 3) : MemLp (windowField χ τ₀ W c) r volume := by
  have hs : 0 < r.toReal := rpow_pos_of_one_le hrt
  obtain ⟨M, hM⟩ := hχ.smooth.continuous.bounded_above_of_compact_support hχ.compact
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  have hcont : Continuous χ := hχ.smooth.continuous
  set s := r.toReal with hsdef
  set m : ℝ → ℝ≥0∞ := fun t => ENNReal.ofReal (Real.exp t) *
    (ENNReal.ofReal (|χ t| * Real.exp (-(t / 2)))) ^ s with hmdef
  have hmm : Measurable m := by
    have h1 : Measurable (fun t : ℝ => ENNReal.ofReal (Real.exp t)) :=
      ENNReal.measurable_ofReal.comp Real.continuous_exp.measurable
    have h2 : Measurable (fun t : ℝ => ENNReal.ofReal (|χ t| * Real.exp (-(t / 2)))) :=
      ENNReal.measurable_ofReal.comp
        ((hcont.abs.mul (by fun_prop : Continuous fun t : ℝ => Real.exp (-(t / 2)))).measurable)
    exact h1.mul (h2.pow_const s)
  have hP1 : ∀ p : ℝ × Space,
      ENNReal.ofReal (Real.exp p.1) * ‖windowField χ τ₀ W c (expChart p)‖ₑ ^ s ≤
        m p.1 * ‖W (τ₀ + p.1, Real.exp (-(p.1 / 2)) • p.2)‖ₑ ^ s := by
    intro p
    have hf : windowField χ τ₀ W c (expChart p) =
        ((χ p.1 * Real.exp (-(p.1 / 2)) : ℝ) : ℂ) *
          W (τ₀ + p.1, Real.exp (-(p.1 / 2)) • p.2) c := by
      simp only [windowField, expChart, Real.exp_pos, ite_true, Real.log_exp]
    have hc : ‖((χ p.1 * Real.exp (-(p.1 / 2)) : ℝ) : ℂ)‖ₑ =
        ENNReal.ofReal (|χ p.1| * Real.exp (-(p.1 / 2))) := by
      rw [enorm_ofReal_cast, Real.enorm_eq_ofReal_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
    have hn : ‖windowField χ τ₀ W c (expChart p)‖ₑ ≤
        ENNReal.ofReal (|χ p.1| * Real.exp (-(p.1 / 2))) *
          ‖W (τ₀ + p.1, Real.exp (-(p.1 / 2)) • p.2)‖ₑ := by
      rw [hf, enorm_mul, hc]
      exact mul_le_mul_of_nonneg_left (PiLp.enorm_apply_le _ c) zero_le
    calc ENNReal.ofReal (Real.exp p.1) * ‖windowField χ τ₀ W c (expChart p)‖ₑ ^ s
        ≤ ENNReal.ofReal (Real.exp p.1) *
            (ENNReal.ofReal (|χ p.1| * Real.exp (-(p.1 / 2))) *
              ‖W (τ₀ + p.1, Real.exp (-(p.1 / 2)) • p.2)‖ₑ) ^ s :=
          mul_le_mul_of_nonneg_left (ENNReal.rpow_le_rpow hn hs.le) zero_le
      _ = m p.1 * ‖W (τ₀ + p.1, Real.exp (-(p.1 / 2)) • p.2)‖ₑ ^ s := by
          rw [ENNReal.mul_rpow_of_nonneg _ _ hs.le]
          simp only [hmdef]
          ring
  have hf0 : ∀ p : ℝ × Space, p.1 ≤ 0 → windowField χ τ₀ W c p = 0 := fun p hp => by
    simp [windowField, not_lt.2 hp]
  have hI : ∫⁻ X, ‖windowField χ τ₀ W c X‖ₑ ^ s ≤
      ∫⁻ p : ℝ × Space, m p.1 * ‖W (τ₀ + p.1, Real.exp (-(p.1 / 2)) • p.2)‖ₑ ^ s := by
    rw [lintegral_norm_expChart hs hf0]
    exact lintegral_mono hP1
  have hII : ∫⁻ p : ℝ × Space, m p.1 * ‖W (τ₀ + p.1, Real.exp (-(p.1 / 2)) • p.2)‖ₑ ^ s =
      ∫⁻ t, ENNReal.ofReal (Real.exp (3 * t / 2)) * m t *
        ‖w ((τ₀ + t : ℝ) : AddCircle P)‖ₑ ^ s :=
    lintegral_pullback hrt hW τ₀ hmm
  set C : ℝ≥0∞ := ENNReal.ofReal (Real.exp (2 * |5 / 2 - s / 2|) * M ^ s) with hC
  have hbound : ∀ t : ℝ, ENNReal.ofReal (Real.exp (3 * t / 2)) * m t *
      ‖w ((τ₀ + t : ℝ) : AddCircle P)‖ₑ ^ s ≤
        C * (Ioo (-2 : ℝ) 2).indicator (fun t => ‖w ((τ₀ + t : ℝ) : AddCircle P)‖ₑ ^ s) t := by
    intro t
    by_cases ht : t ∈ Ioo (-2 : ℝ) 2
    · rw [Set.indicator_of_mem ht]
      refine mul_le_mul_of_nonneg_right ?_ zero_le
      have hχM : |χ t| ≤ M := by
        have := hM t
        rwa [Real.norm_eq_abs] at this
      have hY : (ENNReal.ofReal (|χ t| * Real.exp (-(t / 2)))) ^ s =
          ENNReal.ofReal ((|χ t| * Real.exp (-(t / 2))) ^ s) :=
        ENNReal.ofReal_rpow_of_nonneg (mul_nonneg (abs_nonneg _) (Real.exp_pos _).le) hs.le
      have hpow : (|χ t| * Real.exp (-(t / 2))) ^ s =
          |χ t| ^ s * Real.exp (-(t / 2) * s) := by
        rw [Real.mul_rpow (abs_nonneg _) (Real.exp_pos _).le, ← Real.exp_mul]
      have h2 : |χ t| ^ s ≤ M ^ s := Real.rpow_le_rpow (abs_nonneg _) hχM hs.le
      have h3 : Real.exp (3 * t / 2) * (Real.exp t * (|χ t| ^ s * Real.exp (-(t / 2) * s))) =
          |χ t| ^ s * Real.exp ((5 / 2 - s / 2) * t) := by
        rw [show (5 / 2 - s / 2) * t = 3 * t / 2 + t + -(t / 2) * s by ring, Real.exp_add,
          Real.exp_add]
        ring
      have ht2 : |t| ≤ 2 := abs_le.2 ⟨ht.1.le, ht.2.le⟩
      have hlin : (5 / 2 - s / 2) * t ≤ 2 * |5 / 2 - s / 2| := by
        calc (5 / 2 - s / 2) * t ≤ |(5 / 2 - s / 2) * t| := le_abs_self _
          _ = |5 / 2 - s / 2| * |t| := abs_mul _ _
          _ ≤ |5 / 2 - s / 2| * 2 := mul_le_mul_of_nonneg_left ht2 (abs_nonneg _)
          _ = 2 * |5 / 2 - s / 2| := by ring
      have h4 : Real.exp ((5 / 2 - s / 2) * t) ≤ Real.exp (2 * |5 / 2 - s / 2|) :=
        Real.exp_le_exp.2 hlin
      have hreal : Real.exp (3 * t / 2) * (Real.exp t * (|χ t| * Real.exp (-(t / 2))) ^ s) ≤
          Real.exp (2 * |5 / 2 - s / 2|) * M ^ s := by
        rw [hpow]
        calc Real.exp (3 * t / 2) * (Real.exp t * (|χ t| ^ s * Real.exp (-(t / 2) * s)))
            = |χ t| ^ s * Real.exp ((5 / 2 - s / 2) * t) := h3
          _ ≤ M ^ s * Real.exp (2 * |5 / 2 - s / 2|) :=
            mul_le_mul h2 h4 (Real.exp_pos _).le (Real.rpow_nonneg hM0 _)
          _ = Real.exp (2 * |5 / 2 - s / 2|) * M ^ s := by ring
      calc ENNReal.ofReal (Real.exp (3 * t / 2)) * m t
          = ENNReal.ofReal (Real.exp (3 * t / 2) * (Real.exp t * (|χ t| * Real.exp (-(t / 2))) ^ s)) := by
            simp only [hmdef]
            rw [hY, ENNReal.ofReal_mul (Real.exp_pos (3 * t / 2)).le,
              ENNReal.ofReal_mul (Real.exp_pos t).le]
        _ ≤ C := ENNReal.ofReal_le_ofReal hreal
    · have hχt : χ t = 0 := image_eq_zero_of_notMem_tsupport (fun h => ht (hχ.support h))
      simp [hmdef, hχt, Set.indicator_of_notMem ht, ENNReal.zero_rpow_of_pos hs]
  have hfin : ∫⁻ t, C * (Ioo (-2 : ℝ) 2).indicator
      (fun t => ‖w ((τ₀ + t : ℝ) : AddCircle P)‖ₑ ^ s) t < ⊤ := by
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_indicator measurableSet_Ioo]
    refine ENNReal.mul_lt_top ENNReal.ofReal_lt_top ?_
    exact ((lintegral_mono_set Ioo_subset_Icc_self).trans_lt
      (lintegral_window_lt_top hrt w τ₀ (-2) 2))
  have hfinal : ∫⁻ X, ‖windowField χ τ₀ W c X‖ₑ ^ s < ⊤ :=
    lt_of_le_of_lt (hI.trans (hII.le.trans (lintegral_mono hbound))) hfin
  refine ⟨(measurable_windowField hχ τ₀ hW.meas.measurable c).aestronglyMeasurable, ?_⟩
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (zero_lt_one.trans_le (Fact.out : (1 : ℝ≥0∞) ≤ r)).ne'
    hrt]
  exact ENNReal.rpow_lt_top_of_nonneg (one_div_nonneg.2 hs.le) hfinal.ne

end UnforcedLeray.Short.PartIIa.WinBack
