import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_13_8_2
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_13_8_2.L2
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_13_8_2.L3

/-!
# `PartIII-b:C/ward/13/8/2/4`: the Deny-Lions constant

Statement `DenyLionsConst` from `Sub/PartIII-b_C_ward_13_8_2.lean` (source 117-118, 2641-2642).

Route: with `t = 2^n` and `A_n = {t <= |y| <= 4t}`, the annular Poincare inequality gives means `m_n`.
Tail integrals of `|grad p|^2` tend to `0`, so `E_n = int_{A_n} |grad p|^2 -> 0`.  On the overlap
`{2t <= |y| <= 4t}` (volume at least `V t^3 / 8`), comparing `m_n` and `m_{n+1}` gives the increment
bound needed by `dyadicDrift`.  The limit `c` of the dyadic means then controls the annular integrals
at every real radius `R` with `2^n <= R < 2^(n+1)`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete

namespace DL

abbrev Sp := UnforcedLeray.Space

/-- The annulus `2^n <= |y| <= 4 * 2^n`. -/
def annSet (n : ℕ) : Set Sp := {y | (2:ℝ) ^ n ≤ ‖y‖ ∧ ‖y‖ ≤ 4 * (2:ℝ) ^ n}

/-- Energy of the gradient on `annSet n`. -/
def annE (p : Sp → ℝ) (n : ℕ) : ℝ := ∫ y in annSet n, ‖physGrad p y‖ ^ 2

/-- The exterior `|y| >= 2^n`. -/
def tailS (n : ℕ) : Set Sp := {y | (2:ℝ) ^ n ≤ ‖y‖}

/-- Energy of the gradient on `tailS n`. -/
def tailE (p : Sp → ℝ) (n : ℕ) : ℝ := ∫ y in tailS n, ‖physGrad p y‖ ^ 2

/-- The overlap `2^(n+1) <= |y| <= 4 * 2^n` of `annSet n` and `annSet (n+1)`. -/
def oSet (n : ℕ) : Set Sp := {y | (2:ℝ) ^ (n + 1) ≤ ‖y‖ ∧ ‖y‖ ≤ 4 * (2:ℝ) ^ n}

/-- Volume of the unit ball in `Sp`. -/
def Vb : ℝ := (volume (Metric.ball (0 : Sp) 1)).toReal

theorem Vb_pos : 0 < Vb :=
  ENNReal.toReal_pos (Metric.measure_ball_pos volume 0 one_pos).ne' measure_ball_lt_top.ne

theorem volReal_ball (x : Sp) {r : ℝ} (hr : 0 ≤ r) :
    (volume : Measure Sp).real (Metric.ball x r) = r ^ 3 * Vb := by
  rw [measureReal_def, Measure.addHaar_ball volume x hr, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (by positivity)]
  simp [Vb, finrank_euclideanSpace_fin]

theorem volReal_closedBall (x : Sp) {r : ℝ} (hr : 0 ≤ r) :
    (volume : Measure Sp).real (Metric.closedBall x r) = r ^ 3 * Vb := by
  rw [measureReal_def, Measure.addHaar_closedBall volume x hr, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (by positivity)]
  simp [Vb, finrank_euclideanSpace_fin]

theorem annSet_isCompact (n : ℕ) : IsCompact (annSet n) := by
  apply Metric.isCompact_of_isClosed_isBounded
  · unfold annSet
    exact (isClosed_le continuous_const continuous_norm).inter
      (isClosed_le continuous_norm continuous_const)
  · apply (Metric.isBounded_closedBall (x := (0 : Sp)) (r := 4 * (2:ℝ) ^ n)).subset
    intro y hy
    rw [mem_closedBall_zero_iff]
    exact hy.2

theorem integrableOn_sq_sub {p : Sp → ℝ} (hp : Continuous p) (m : ℝ) (n : ℕ) :
    IntegrableOn (fun y => (p y - m) ^ 2) (annSet n) :=
  ContinuousOn.integrableOn_compact (annSet_isCompact n)
    ((hp.sub continuous_const).pow 2).continuousOn

theorem oSet_isClosed (n : ℕ) : IsClosed (oSet n) := by
  unfold oSet
  exact (isClosed_le continuous_const continuous_norm).inter
    (isClosed_le continuous_norm continuous_const)

theorem oSet_ne_top (n : ℕ) : (volume : Measure Sp) (oSet n) ≠ ⊤ := by
  have hOsub : oSet n ⊆ Metric.closedBall 0 (4 * (2:ℝ) ^ n) := by
    intro y hy
    rw [mem_closedBall_zero_iff]
    exact hy.2
  exact ne_top_of_le_ne_top
    (measure_closedBall_lt_top (μ := volume) (x := (0:Sp)) (r := 4 * (2:ℝ) ^ n)).ne
    (measure_mono hOsub)

theorem annE_nonneg (p : Sp → ℝ) (n : ℕ) : 0 ≤ annE p n :=
  setIntegral_nonneg (annSet_isCompact n).isClosed.measurableSet (fun y _ => sq_nonneg _)

theorem tailE_tendsto {p : Sp → ℝ} (hL : MemLp (physGrad p) 2 volume) :
    Tendsto (tailE p) atTop (𝓝 0) := by
  have hint : Integrable (fun y => ‖physGrad p y‖ ^ 2) volume := hL.norm.integrable_sq
  have hanti : Antitone tailS := by
    intro i j hij y hy
    exact le_trans (pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) hij) hy
  have hempty : (⋂ n, {y : Sp | (2:ℝ) ^ n ≤ ‖y‖}) = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.2
    intro y hy
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt ‖y‖ (by norm_num : (1:ℝ) < 2)
    exact absurd (Set.mem_iInter.1 hy n : (2:ℝ) ^ n ≤ ‖y‖) (not_le.2 hn)
  have hlim := tendsto_setIntegral_of_antitone (μ := volume) (f := fun y => ‖physGrad p y‖ ^ 2)
    (fun n => (isClosed_le continuous_const continuous_norm).measurableSet) hanti
    ⟨0, hint.integrableOn⟩
  rw [hempty, Measure.restrict_empty, integral_zero_measure] at hlim
  exact hlim

theorem annE_le_tail {p : Sp → ℝ} (hL : MemLp (physGrad p) 2 volume) (n : ℕ) :
    annE p n ≤ tailE p n := by
  have hint : Integrable (fun y => ‖physGrad p y‖ ^ 2) volume := hL.norm.integrable_sq
  unfold annE tailE
  exact setIntegral_mono_set hint.integrableOn (ae_of_all _ fun y => sq_nonneg _)
    (ae_of_all _ fun y hy => hy.1)

theorem rpow_half_sq (n : ℕ) : ((2:ℝ) ^ ((n:ℝ) / 2)) ^ 2 = (2:ℝ) ^ n := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
  rw [show (n:ℝ) / 2 * ((2:ℕ):ℝ) = (n:ℝ) by push_cast; ring, Real.rpow_natCast]

theorem rpow_neg_half_sq (n : ℕ) : ((2:ℝ) ^ (-(n:ℝ) / 2)) ^ 2 = ((2:ℝ) ^ n)⁻¹ := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
  rw [show -(n:ℝ) / 2 * ((2:ℕ):ℝ) = -(n:ℝ) by push_cast; ring, Real.rpow_neg (by norm_num),
    Real.rpow_natCast]

/-- The bound on the annulus `{R <= |y| <= 2R}` in terms of the dyadic data at `n`. -/
theorem ann_bound {p : Sp → ℝ} (hp : Continuous p) (C : ℝ) (m : ℕ → ℝ)
    (hmA : ∀ n : ℕ, ∫ y in annSet n, (p y - m n) ^ 2 ≤ |C| * ((2:ℝ) ^ n) ^ 2 * annE p n)
    (c : ℝ) (n : ℕ) (R : ℝ) (hR1 : (2:ℝ) ^ n ≤ R) (hR2 : R < 2 * (2:ℝ) ^ n) :
    0 ≤ (1 / R ^ 2) * ∫ y in {y : Sp | R ≤ ‖y‖ ∧ ‖y‖ ≤ 2 * R}, (p y - c) ^ 2 ∧
    (1 / R ^ 2) * ∫ y in {y : Sp | R ≤ ‖y‖ ∧ ‖y‖ ≤ 2 * R}, (p y - c) ^ 2 ≤
      2 * |C| * annE p n + 32 * Vb * ((2:ℝ) ^ ((n:ℝ) / 2) * |m n - c|) ^ 2 := by
  have hRpos : 0 < R := lt_of_lt_of_le (by positivity) hR1
  have hVb : 0 < Vb := Vb_pos
  have ha0 : (0:ℝ) < (2:ℝ) ^ n := by positivity
  have hAsub : {y : Sp | R ≤ ‖y‖ ∧ ‖y‖ ≤ 2 * R} ⊆ annSet n := by
    intro y hy
    exact ⟨le_trans hR1 hy.1, by linarith [hy.2]⟩
  have hAclosed : IsClosed {y : Sp | R ≤ ‖y‖ ∧ ‖y‖ ≤ 2 * R} :=
    (isClosed_le continuous_const continuous_norm).inter
      (isClosed_le continuous_norm continuous_const)
  have hAmeas : MeasurableSet {y : Sp | R ≤ ‖y‖ ∧ ‖y‖ ≤ 2 * R} := hAclosed.measurableSet
  have hAfin : (volume : Measure Sp) {y : Sp | R ≤ ‖y‖ ∧ ‖y‖ ≤ 2 * R} ≠ ⊤ :=
    ne_top_of_le_ne_top (annSet_isCompact n).measure_lt_top.ne (measure_mono hAsub)
  have hIp : ∀ d : ℝ, IntegrableOn (fun y => (p y - d) ^ 2) {y : Sp | R ≤ ‖y‖ ∧ ‖y‖ ≤ 2 * R} :=
    fun d => (integrableOn_sq_sub hp d n).mono_set hAsub
  have hIc : IntegrableOn (fun _ : Sp => (m n - c) ^ 2) {y : Sp | R ≤ ‖y‖ ∧ ‖y‖ ≤ 2 * R} :=
    integrableOn_const hAfin
  have hvol : (volume : Measure Sp).real {y : Sp | R ≤ ‖y‖ ∧ ‖y‖ ≤ 2 * R} ≤ (2 * R) ^ 3 * Vb := by
    have hsub2 : {y : Sp | R ≤ ‖y‖ ∧ ‖y‖ ≤ 2 * R} ⊆ Metric.closedBall 0 (2 * R) := by
      intro y hy
      rw [mem_closedBall_zero_iff]
      exact hy.2
    have h := measureReal_mono (μ := volume) hsub2
      (measure_closedBall_lt_top (μ := volume) (x := (0:Sp)) (r := 2 * R)).ne
    rw [volReal_closedBall _ (by linarith)] at h
    exact h
  have hpt : ∀ y ∈ {y : Sp | R ≤ ‖y‖ ∧ ‖y‖ ≤ 2 * R},
      (p y - c) ^ 2 ≤ 2 * (p y - m n) ^ 2 + 2 * (m n - c) ^ 2 :=
    fun y _ => by nlinarith [sq_nonneg (p y - m n - (m n - c))]
  have hJ : ∫ y in {y : Sp | R ≤ ‖y‖ ∧ ‖y‖ ≤ 2 * R}, (p y - c) ^ 2 ≤
      ∫ y in {y : Sp | R ≤ ‖y‖ ∧ ‖y‖ ≤ 2 * R}, (2 * (p y - m n) ^ 2 + 2 * (m n - c) ^ 2) :=
    setIntegral_mono_on ((integrableOn_sq_sub hp c n).mono_set hAsub)
      (((hIp (m n)).const_mul 2).add (hIc.const_mul 2)) hAmeas hpt
  rw [integral_add ((hIp (m n)).const_mul 2) (hIc.const_mul 2), integral_const_mul,
    integral_const_mul, setIntegral_const, smul_eq_mul] at hJ
  have hJ0 : ∫ y in {y : Sp | R ≤ ‖y‖ ∧ ‖y‖ ≤ 2 * R}, (p y - m n) ^ 2 ≤
      |C| * ((2:ℝ) ^ n) ^ 2 * annE p n :=
    (setIntegral_mono_set (integrableOn_sq_sub hp (m n) n)
      (ae_of_all _ fun y => sq_nonneg _) (ae_of_all _ fun y hy => hAsub hy)).trans (hmA n)
  have hpos : 0 ≤ (m n - c) ^ 2 := sq_nonneg _
  have hgnn : 0 ≤ ∫ y in {y : Sp | R ≤ ‖y‖ ∧ ‖y‖ ≤ 2 * R}, (p y - c) ^ 2 :=
    setIntegral_nonneg hAmeas (fun y _ => sq_nonneg _)
  refine ⟨mul_nonneg (by positivity) hgnn, ?_⟩
  have hR2' : (0:ℝ) ≤ 1 / R ^ 2 := by positivity
  have hE := annE_nonneg p n
  have hC0 : 0 ≤ |C| := abs_nonneg C
  have hstep : ∫ y in {y : Sp | R ≤ ‖y‖ ∧ ‖y‖ ≤ 2 * R}, (p y - c) ^ 2 ≤
      2 * (|C| * ((2:ℝ) ^ n) ^ 2 * annE p n) + 2 * ((m n - c) ^ 2 * ((2 * R) ^ 3 * Vb)) := by
    have h1 : (m n - c) ^ 2 * (volume : Measure Sp).real {y : Sp | R ≤ ‖y‖ ∧ ‖y‖ ≤ 2 * R}
        ≤ (m n - c) ^ 2 * ((2 * R) ^ 3 * Vb) := mul_le_mul_of_nonneg_left hvol hpos
    linarith
  have hsq : ((2:ℝ) ^ ((n:ℝ) / 2) * |m n - c|) ^ 2 = (2:ℝ) ^ n * (m n - c) ^ 2 := by
    rw [mul_pow, rpow_half_sq, sq_abs]
  rw [hsq]
  have e1 : (1 / R ^ 2) * (2 * (|C| * ((2:ℝ) ^ n) ^ 2 * annE p n))
      ≤ 2 * |C| * annE p n := by
    have hr : ((2:ℝ) ^ n) ^ 2 / R ^ 2 ≤ 1 := by
      rw [div_le_one (by positivity)]
      nlinarith
    calc (1 / R ^ 2) * (2 * (|C| * ((2:ℝ) ^ n) ^ 2 * annE p n))
        = (2 * |C| * annE p n) * (((2:ℝ) ^ n) ^ 2 / R ^ 2) := by ring
      _ ≤ (2 * |C| * annE p n) * 1 :=
          mul_le_mul_of_nonneg_left hr (by positivity)
      _ = 2 * |C| * annE p n := mul_one _
  have e2 : (1 / R ^ 2) * (2 * ((m n - c) ^ 2 * ((2 * R) ^ 3 * Vb)))
      ≤ 32 * Vb * ((2:ℝ) ^ n * (m n - c) ^ 2) := by
    calc (1 / R ^ 2) * (2 * ((m n - c) ^ 2 * ((2 * R) ^ 3 * Vb)))
        = (16 * (m n - c) ^ 2 * Vb) * R := by
          field_simp
          ring
      _ ≤ (16 * (m n - c) ^ 2 * Vb) * (2 * (2:ℝ) ^ n) :=
          mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      _ = 32 * Vb * ((2:ℝ) ^ n * (m n - c) ^ 2) := by ring
  calc (1 / R ^ 2) * ∫ y in {y : Sp | R ≤ ‖y‖ ∧ ‖y‖ ≤ 2 * R}, (p y - c) ^ 2
      ≤ (1 / R ^ 2) * (2 * (|C| * ((2:ℝ) ^ n) ^ 2 * annE p n)
          + 2 * ((m n - c) ^ 2 * ((2 * R) ^ 3 * Vb))) :=
        mul_le_mul_of_nonneg_left hstep hR2'
    _ = (1 / R ^ 2) * (2 * (|C| * ((2:ℝ) ^ n) ^ 2 * annE p n))
          + (1 / R ^ 2) * (2 * ((m n - c) ^ 2 * ((2 * R) ^ 3 * Vb))) := by ring
    _ ≤ 2 * |C| * annE p n + 32 * Vb * ((2:ℝ) ^ n * (m n - c) ^ 2) := add_le_add e1 e2

end DL

open DL

/-- **Deny-Lions constant** (source 117-118, 2641-2642): a smooth `p` with `grad p` in `L²` is
asymptotically constant in the annular `L²` sense. -/
theorem denyLionsConst : DenyLionsConst := by
  intro p hpC hL
  have hp1 : ContDiff ℝ 1 p := hpC.of_le (by simp)
  have hcont : Continuous p := hp1.continuous
  obtain ⟨C, hC⟩ := annularPoincare
  choose m hm using fun n : ℕ => hC p hp1 ((2:ℝ) ^ n) (by positivity)
  have hmA : ∀ n : ℕ, ∫ y in annSet n, (p y - m n) ^ 2 ≤ |C| * ((2:ℝ) ^ n) ^ 2 * annE p n := by
    intro n
    refine (hm n).trans ?_
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity)) (annE_nonneg p n)
  have hE0 : Tendsto (annE p) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (tailE_tendsto hL)
      (fun n => annE_nonneg p n) (fun n => annE_le_tail hL n)
  have hE'T : Tendsto (fun n => annE p n + 4 * annE p (n + 1)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun n => annE p (n + 1)) atTop (𝓝 0) :=
      (tendsto_add_atTop_iff_nat 1).2 hE0
    simpa using hE0.add (h1.const_mul 4)
  obtain ⟨e, he⟩ : ∃ e : Sp, ‖e‖ = 1 := exists_norm_eq Sp zero_le_one
  have hVol : ∀ n : ℕ, Vb * ((2:ℝ) ^ n) ^ 3 / 8 ≤ (volume : Measure Sp).real (oSet n) := by
    intro n
    have ht0 : (0:ℝ) < (2:ℝ) ^ n := by positivity
    have hpow : (2:ℝ) ^ (n + 1) = 2 * (2:ℝ) ^ n := by
      rw [pow_succ]; ring
    have hsub : Metric.ball (((3:ℝ) * (2:ℝ) ^ n) • e) ((2:ℝ) ^ n / 2) ⊆ oSet n := by
      intro y hy
      rw [Metric.mem_ball, dist_eq_norm] at hy
      have hx : ‖((3:ℝ) * (2:ℝ) ^ n) • e‖ = 3 * (2:ℝ) ^ n := by
        rw [norm_smul, he, Real.norm_eq_abs, abs_of_pos (by positivity)]
        ring
      have h2 := norm_sub_norm_le (((3:ℝ) * (2:ℝ) ^ n) • e) y
      have h3 := norm_sub_norm_le y (((3:ℝ) * (2:ℝ) ^ n) • e)
      rw [norm_sub_rev] at h2
      show (2:ℝ) ^ (n + 1) ≤ ‖y‖ ∧ ‖y‖ ≤ 4 * (2:ℝ) ^ n
      constructor
      · rw [hpow]
        linarith
      · linarith
    have h := measureReal_mono (μ := volume) hsub (oSet_ne_top n)
    rw [volReal_ball _ (by positivity)] at h
    have : ((2:ℝ) ^ n / 2) ^ 3 * Vb = Vb * ((2:ℝ) ^ n) ^ 3 / 8 := by ring
    linarith
  have hinc : ∀ n : ℕ, |m (n + 1) - m n| ≤
      Real.sqrt (16 * |C| / Vb) * (2:ℝ) ^ (-(n:ℝ) / 2)
        * Real.sqrt (annE p n + 4 * annE p (n + 1)) := by
    intro n
    have ht0 : (0:ℝ) < (2:ℝ) ^ n := by positivity
    have hpow : (2:ℝ) ^ (n + 1) = 2 * (2:ℝ) ^ n := by
      rw [pow_succ]; ring
    have hOA : oSet n ⊆ annSet n := by
      intro y hy
      show (2:ℝ) ^ n ≤ ‖y‖ ∧ ‖y‖ ≤ 4 * (2:ℝ) ^ n
      exact ⟨by linarith [hy.1, hpow], hy.2⟩
    have hOA1 : oSet n ⊆ annSet (n + 1) := by
      intro y hy
      show (2:ℝ) ^ (n + 1) ≤ ‖y‖ ∧ ‖y‖ ≤ 4 * (2:ℝ) ^ (n + 1)
      exact ⟨hy.1, by linarith [hy.2, hpow]⟩
    have hI0 : IntegrableOn (fun y => (p y - m n) ^ 2) (oSet n) :=
      (integrableOn_sq_sub hcont (m n) n).mono_set hOA
    have hI1 : IntegrableOn (fun y => (p y - m (n + 1)) ^ 2) (oSet n) :=
      (integrableOn_sq_sub hcont (m (n + 1)) (n + 1)).mono_set hOA1
    have hpt : ∀ y ∈ oSet n, (m (n + 1) - m n) ^ 2
        ≤ 2 * (p y - m n) ^ 2 + 2 * (p y - m (n + 1)) ^ 2 :=
      fun y _ => by nlinarith [sq_nonneg (p y - m n + (p y - m (n + 1)))]
    have hD1 : ∫ y in oSet n, (m (n + 1) - m n) ^ 2 ≤
        ∫ y in oSet n, (2 * (p y - m n) ^ 2 + 2 * (p y - m (n + 1)) ^ 2) :=
      setIntegral_mono_on (integrableOn_const (oSet_ne_top n))
        ((hI0.const_mul 2).add (hI1.const_mul 2)) (oSet_isClosed n).measurableSet hpt
    rw [integral_add (hI0.const_mul 2) (hI1.const_mul 2), integral_const_mul,
      integral_const_mul] at hD1
    have hJ0 : ∫ y in oSet n, (p y - m n) ^ 2 ≤ |C| * ((2:ℝ) ^ n) ^ 2 * annE p n :=
      (setIntegral_mono_set (integrableOn_sq_sub hcont (m n) n)
        (ae_of_all _ fun y => sq_nonneg _) (ae_of_all _ fun y hy => hOA hy)).trans (hmA n)
    have hJ1 : ∫ y in oSet n, (p y - m (n + 1)) ^ 2
        ≤ |C| * ((2:ℝ) ^ (n + 1)) ^ 2 * annE p (n + 1) :=
      (setIntegral_mono_set (integrableOn_sq_sub hcont (m (n + 1)) (n + 1))
        (ae_of_all _ fun y => sq_nonneg _) (ae_of_all _ fun y hy => hOA1 hy)).trans
        (hmA (n + 1))
    rw [hpow] at hJ1
    have hLHS : (m (n + 1) - m n) ^ 2 * (volume : Measure Sp).real (oSet n)
        = ∫ y in oSet n, (m (n + 1) - m n) ^ 2 := by
      rw [setIntegral_const, smul_eq_mul, mul_comm]
    have hVt := Vb_pos
    have hmul := mul_le_mul_of_nonneg_left (hVol n) (sq_nonneg (m (n + 1) - m n))
    have key : (m (n + 1) - m n) ^ 2 * (Vb * ((2:ℝ) ^ n) ^ 3 / 8)
        ≤ 2 * |C| * ((2:ℝ) ^ n) ^ 2 * (annE p n + 4 * annE p (n + 1)) := by
      nlinarith
    have hpos8 : 0 < Vb * ((2:ℝ) ^ n) ^ 3 / 8 := by positivity
    have hD : (m (n + 1) - m n) ^ 2
        ≤ 16 * |C| / Vb * ((2:ℝ) ^ n)⁻¹ * (annE p n + 4 * annE p (n + 1)) := by
      have e : 16 * |C| / Vb * ((2:ℝ) ^ n)⁻¹ * (annE p n + 4 * annE p (n + 1))
          * (Vb * ((2:ℝ) ^ n) ^ 3 / 8)
          = 2 * |C| * ((2:ℝ) ^ n) ^ 2 * (annE p n + 4 * annE p (n + 1)) := by
        field_simp
        ring
      refine le_of_mul_le_mul_right ?_ hpos8
      rw [e]
      exact key
    have hK2 : (Real.sqrt (16 * |C| / Vb)) ^ 2 = 16 * |C| / Vb :=
      Real.sq_sqrt (div_nonneg (mul_nonneg (by norm_num) (abs_nonneg C)) hVt.le)
    have hE'nn : 0 ≤ annE p n + 4 * annE p (n + 1) := by
      linarith [annE_nonneg p n, annE_nonneg p (n + 1)]
    have hs2 := rpow_neg_half_sq n
    rw [← sq_le_sq₀ (abs_nonneg _) (by positivity)]
    rw [sq_abs, mul_pow, mul_pow, hK2, hs2, Real.sq_sqrt hE'nn]
    exact hD
  obtain ⟨c, hc⟩ := dyadicDrift m (fun n => annE p n + 4 * annE p (n + 1))
    (Real.sqrt (16 * |C| / Vb))
    (fun n => add_nonneg (annE_nonneg p n) (mul_nonneg (by norm_num) (annE_nonneg p (n + 1))))
    hE'T hinc
  refine ⟨c, ?_⟩
  have hH : Tendsto (fun n : ℕ => 2 * |C| * annE p n
      + 32 * Vb * ((2:ℝ) ^ ((n:ℝ) / 2) * |m n - c|) ^ 2) atTop (𝓝 0) := by
    have h2 := (hc.pow 2).const_mul (32 * Vb)
    have h1 := hE0.const_mul (2 * |C|)
    have h3 := h1.add h2
    simpa using h3
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 (Metric.tendsto_nhds.1 hH ε hε)
  rw [Filter.eventually_atTop]
  refine ⟨(2:ℝ) ^ N, fun R hR => ?_⟩
  have hR1 : (1:ℝ) ≤ R := le_trans (one_le_pow₀ (by norm_num)) hR
  obtain ⟨n, hn1, hn2⟩ := exists_nat_pow_near hR1 (by norm_num : (1:ℝ) < 2)
  have hNn : N ≤ n := by
    have h := lt_of_le_of_lt hR hn2
    have h' := (pow_lt_pow_iff_right₀ (by norm_num : (1:ℝ) < 2)).1 h
    omega
  have hR2 : R < 2 * (2:ℝ) ^ n := by
    have h := hn2
    rw [pow_succ] at h
    linarith
  obtain ⟨hg0, hgle⟩ := ann_bound hcont C m hmA c n R hn1 hR2
  have hHn := hN n hNn
  rw [Real.dist_eq, sub_zero] at hHn
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hg0]
  exact lt_of_le_of_lt hgle ((le_abs_self _).trans_lt hHn)

end UnforcedLeray.Short.PartIIIb.Concrete
