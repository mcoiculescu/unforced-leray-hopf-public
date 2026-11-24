import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T13_1_4_4

/-!
# Part II-b, task `PartII-b:T13/1/4/4/4` (`ChmPairLim`): pairing limits in periodic `L^r(cylMeas c)`

Source of record: `the November 2 reference manuscript` (SP) lines 1933-1935.

Local bound (`cpl_key`). Let `T = ℝ × cell c` and `A_k = {x | x + cplW c k ∈ T}` (the cells
`T + k c` in the `q`-variable). The sets `A_k` partition `Coord`, so
`∫ |e ψ| dvol = ∑_k ∫_T |e(y - w_k)| |ψ(y - w_k)| dvol(y)`. By periodicity of `e` (a.e., for
every integer shift) this is `∫_T |e(y)| ∑_k |ψ(y - w_k)|`. Since `ψ` is bounded with compact
support, only finitely many `k` contribute, and the sum is bounded by a constant times the indicator
of a fixed ball `Box`. Finally `cylMeas c = c⁻¹ • vol|_T`, and `L^1 ≤ L^r` on the finite measure
`cylMeas|_Box` (Hölder) gives `∫ |e ψ| ≤ C ‖e‖_{L^r(cylMeas c)}`.
Convergence of the pairings then follows from `‖∫ (g n - h) ψ‖ ≤ C ‖g n - h‖`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.IIb

open MeasureTheory Set Filter Topology
open scoped ENNReal ContDiff

/-- Translation by `k` periods in the `q` variable (as a vector of `Coord`). -/
def cplW (c : ℝ) (k : ℤ) : Coord := (0, (-(c * (k : ℝ)), 0))

/-- The strip `T = ℝ × cell c` in `Coord`. -/
def cplT (c : ℝ) : Set Coord := univ ×ˢ UnforcedLeray.Cyl.cell c

/-- The `k`-th cell `A_k = {x | x + cplW c k ∈ T}`. -/
def cplA (c : ℝ) (k : ℤ) : Set Coord := (fun x : Coord => x + cplW c k) ⁻¹' cplT c

theorem cplW_add (c : ℝ) (k m : ℤ) : cplW c (k + m) = cplW c k + cplW c m := by
  simp only [cplW, Prod.mk_add_mk, add_zero, Prod.mk.injEq, true_and, and_true]
  push_cast
  ring

theorem cplW_neg (c : ℝ) (k : ℤ) : cplW c (-k) = -cplW c k := by
  simp [cplW]

theorem cplW_zero (c : ℝ) : cplW c 0 = 0 := by
  simp [cplW]

theorem cplT_meas (c : ℝ) : MeasurableSet (cplT c) :=
  MeasurableSet.univ.prod (measurableSet_Ico.prod MeasurableSet.univ)

theorem cplT_mem_iff (c : ℝ) (x : Coord) : x ∈ cplT c ↔ x.2.1 ∈ Ico (-c / 2) (c / 2) := by
  unfold cplT UnforcedLeray.Cyl.cell
  simp only [Set.mem_prod, Set.mem_univ, true_and, and_true]

theorem cplA_meas (c : ℝ) (k : ℤ) : MeasurableSet (cplA c k) :=
  (cplT_meas c).preimage (measurable_add_const _)

theorem cplA_mem_iff (c : ℝ) (k : ℤ) (x : Coord) :
    x ∈ cplA c k ↔ x.2.1 - c * (k : ℝ) ∈ Ico (-c / 2) (c / 2) := by
  have h2 : (x + cplW c k).2.1 = x.2.1 - c * (k : ℝ) := by
    simp [cplW, sub_eq_add_neg]
  show x + cplW c k ∈ cplT c ↔ _
  rw [cplT_mem_iff, h2]

theorem cpl_cover (c : ℝ) (hc : 0 < c) (x : Coord) : ∃ k : ℤ, x ∈ cplA c k := by
  refine ⟨⌊(x.2.1 + c / 2) / c⌋, ?_⟩
  rw [cplA_mem_iff, Set.mem_Ico]
  have hc' : c ≠ 0 := hc.ne'
  have h1 : ((⌊(x.2.1 + c / 2) / c⌋ : ℤ) : ℝ) ≤ (x.2.1 + c / 2) / c := Int.floor_le _
  have h2 : (x.2.1 + c / 2) / c < ((⌊(x.2.1 + c / 2) / c⌋ : ℤ) : ℝ) + 1 :=
    Int.lt_floor_add_one _
  have hu : c * ((x.2.1 + c / 2) / c) = x.2.1 + c / 2 := by field_simp
  have h3 := mul_le_mul_of_nonneg_left h1 hc.le
  have h4 := mul_lt_mul_of_pos_left h2 hc
  rw [mul_add, mul_one] at h4
  constructor <;> linarith

theorem cpl_eq_of_mem (c : ℝ) (hc : 0 < c) {k j : ℤ} (x : Coord) (hk : x ∈ cplA c k)
    (hj : x ∈ cplA c j) : k = j := by
  rw [cplA_mem_iff, Set.mem_Ico] at hk hj
  obtain ⟨hk1, hk2⟩ := hk
  obtain ⟨hj1, hj2⟩ := hj
  have e1 : c * ((k : ℝ) - j) = c * k - c * j := mul_sub _ _ _
  have e2 : c * ((j : ℝ) - k) = c * j - c * k := mul_sub _ _ _
  have u1 : c * ((k : ℝ) - j) < c * 1 := by rw [mul_one]; linarith
  have u2 : c * ((j : ℝ) - k) < c * 1 := by rw [mul_one]; linarith
  have v1 : (k : ℝ) - j < 1 := lt_of_mul_lt_mul_left u1 hc.le
  have v2 : (j : ℝ) - k < 1 := lt_of_mul_lt_mul_left u2 hc.le
  have w1 : k - j < 1 := by exact_mod_cast v1
  have w2 : j - k < 1 := by exact_mod_cast v2
  omega

theorem cpl_lintegral_split (c : ℝ) (hc : 0 < c) (F : Coord → ℝ≥0∞) :
    ∫⁻ x, F x ∂volume = ∑' k : ℤ, ∫⁻ x in cplA c k, F x ∂volume := by
  have huniv : (⋃ k : ℤ, cplA c k) = univ := by
    apply Set.eq_univ_of_forall
    intro x
    exact Set.mem_iUnion.2 (cpl_cover c hc x)
  have hdisj : Pairwise (Function.onFun Disjoint (fun k : ℤ => cplA c k)) := by
    intro k j hkj
    rw [Function.onFun, Set.disjoint_left]
    intro x hk hj
    exact hkj (cpl_eq_of_mem c hc x hk hj)
  conv_lhs => rw [← Measure.restrict_univ (μ := (volume : Measure Coord))]
  rw [← huniv, lintegral_iUnion (fun k => cplA_meas c k) hdisj]

theorem cpl_lintegral_translate (c : ℝ) (k : ℤ) (F : Coord → ℝ≥0∞) :
    ∫⁻ x in cplA c k, F x ∂volume = ∫⁻ y in cplT c, F (y - cplW c k) ∂volume := by
  have h := (measurePreserving_add_right (volume : Measure Coord) (cplW c k)).setLIntegral_comp_preimage_emb
    (measurableEmbedding_addRight (cplW c k)) (fun y => F (y - cplW c k)) (cplT c)
  simp only [add_sub_cancel_right] at h
  exact h

theorem cpl_periodic_ae (c : ℝ) (e : Coord → ℂ) (he : QPeriodicS c e) (k : ℤ) :
    ∀ᵐ y ∂(volume : Measure Coord), e (y - cplW c k) = e y := by
  unfold QPeriodicS at he
  have hU : ∀ᵐ z ∂(volume : Measure Coord), e (z + cplW c 1) = e z := by
    have h1 := (measurePreserving_add_right (volume : Measure Coord) (cplW c 1)).quasiMeasurePreserving.ae he
    filter_upwards [h1] with z hz
    have hq : qShift c (z + cplW c 1) = z := by
      (simp [qShift, cplW]) <;> ring
    rw [hq] at hz
    exact hz.symm
  have hstep : ∀ j : ℤ, ∀ᵐ y ∂(volume : Measure Coord), e (y + cplW c (j + 1)) = e (y + cplW c j) := by
    intro j
    have h1 := (measurePreserving_add_right (volume : Measure Coord) (cplW c j)).quasiMeasurePreserving.ae hU
    filter_upwards [h1] with y hy
    rw [cplW_add c j 1, ← add_assoc]
    exact hy
  have hall : ∀ k : ℤ, ∀ᵐ y ∂(volume : Measure Coord), e (y + cplW c k) = e y := by
    intro k
    refine Int.induction_on k ?_ ?_ ?_
    · exact Filter.Eventually.of_forall (fun y => by rw [cplW_zero, add_zero])
    · intro i ih
      filter_upwards [hstep (i : ℤ), ih] with y h1 h2
      rw [h1]
      exact h2
    · intro i ih
      have h1 := hstep (-(i : ℤ) - 1)
      simp only [sub_add_cancel] at h1
      filter_upwards [h1, ih] with y h1' h2
      rw [← h1']
      exact h2
  have := hall (-k)
  filter_upwards [this] with y hy
  rw [sub_eq_add_neg, ← cplW_neg]
  exact hy

theorem cpl_cyl (c : ℝ) :
    cylMeas c = ENNReal.ofReal c⁻¹ • (volume : Measure Coord).restrict (cplT c) := by
  unfold cylMeas UnforcedLeray.Cyl.avgμ UnforcedLeray.Cyl.cellμ cplT
  rw [Measure.prod_smul_right]
  have h := Measure.prod_restrict (univ : Set ℝ) (UnforcedLeray.Cyl.cell c)
    (μ := (volume : Measure ℝ)) (ν := (volume : Measure (ℝ × ℝ)))
  rw [Measure.restrict_univ] at h
  rw [h]
  rfl

theorem cpl_cyl_apply (c : ℝ) {t : Set Coord} (ht : MeasurableSet t) :
    cylMeas c t = ENNReal.ofReal c⁻¹ * volume (t ∩ cplT c) := by
  rw [cpl_cyl c, Measure.smul_apply, Measure.restrict_apply ht, smul_eq_mul]

theorem cpl_lint_T (c : ℝ) (hc : 0 < c) (s : Set Coord) (g : Coord → ℝ≥0∞) :
    ∫⁻ y in s, g y ∂((volume : Measure Coord).restrict (cplT c)) =
      ENNReal.ofReal c * ∫⁻ y in s, g y ∂(cylMeas c) := by
  rw [cpl_cyl c, Measure.restrict_smul, lintegral_smul_measure, smul_eq_mul, ← mul_assoc,
    ← ENNReal.ofReal_mul hc.le, mul_inv_cancel₀ hc.ne', ENNReal.ofReal_one, one_mul]

theorem cpl_ac (c : ℝ) : cylMeas c ≪ volume := by
  intro s hs
  have ht : volume (toMeasurable volume s) = 0 := by
    rw [measure_toMeasurable]
    exact hs
  have h0 : volume (toMeasurable volume s ∩ cplT c) = 0 :=
    measure_mono_null inter_subset_left ht
  refine measure_mono_null (subset_toMeasurable volume s) ?_
  rw [cpl_cyl_apply c (measurableSet_toMeasurable _ _), h0, mul_zero]

/-- The key local bound: for a periodic `e` the weighted integral is bounded by
`C ‖e‖_{L^r(cylMeas c)}` with `C` depending only on `ψ`, `c`, `r`. -/
theorem cpl_key (r c : ℝ) (hr : 1 < r) (hc : 0 < c) (ψ : Coord → ℝ) (hψ : Continuous ψ)
    (hψs : HasCompactSupport ψ) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ e : Coord → ℂ, QPeriodicS c e → AEStronglyMeasurable e volume →
      ∫⁻ x, ‖e x * (ψ x : ℂ)‖ₑ ∂volume ≤ C * cylNorm c r e := by
  classical
  obtain ⟨M, hM⟩ := hψ.bounded_above_of_compact_support hψs
  obtain ⟨R, hR⟩ := (Metric.isBounded_iff_subset_closedBall (0 : Coord)).1
    hψs.isCompact.isBounded
  have hR0 : ∀ x : Coord, ψ x ≠ 0 → ‖x‖ ≤ R := fun x hx =>
    mem_closedBall_zero_iff.1 (hR (subset_tsupport ψ (Function.mem_support.2 hx)))
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  have hψb : ∀ x : Coord, ‖((ψ x : ℝ) : ℂ)‖ₑ ≤ ENNReal.ofReal M := fun x => by
    rw [← Real.enorm_eq_ofReal hM0, enorm_le_iff_norm_le, Complex.norm_real,
      Real.norm_of_nonneg hM0]
    exact hM x
  have hψz : ∀ x : Coord, ψ x = 0 → ‖((ψ x : ℝ) : ℂ)‖ₑ = 0 := fun x hx => by
    simp [hx]
  set K : ℕ := ⌈(R + c) / c⌉₊ with hK
  set Box : Set Coord := Metric.closedBall (0 : Coord) (R + c) with hBox
  have hBoxM : MeasurableSet Box := measurableSet_closedBall
  set Cst : ℝ≥0∞ := ∑ k ∈ Finset.Icc (-(K : ℤ)) (K : ℤ), ENNReal.ofReal M with hCst
  have hCstT : Cst ≠ ⊤ := ENNReal.sum_ne_top.2 (fun k _ => ENNReal.ofReal_ne_top)
  -- the bound on the nonzero terms
  have hnz : ∀ b : Coord, b ∈ cplT c → ∀ k : ℤ, ψ (b - cplW c k) ≠ 0 →
      |k| ≤ (K : ℤ) ∧ b ∈ Box := by
    intro b hb k hk
    obtain ⟨hb1, hb2⟩ := Set.mem_Ico.1 ((cplT_mem_iff c b).1 hb)
    have hn := hR0 _ hk
    have e21 : (b - cplW c k).2.1 = b.2.1 + c * (k : ℝ) := by
      simp [cplW, sub_eq_add_neg]
    have e11 : (b - cplW c k).1 = b.1 := by simp [cplW]
    have e23 : (b - cplW c k).2.2 = b.2.2 := by simp [cplW]
    have hsnd : ‖(b - cplW c k).2.1‖ ≤ ‖b - cplW c k‖ :=
      (norm_fst_le (b - cplW c k).2).trans (norm_snd_le _)
    have hfst : ‖(b - cplW c k).1‖ ≤ ‖b - cplW c k‖ := norm_fst_le _
    have hsnd2 : ‖(b - cplW c k).2.2‖ ≤ ‖b - cplW c k‖ :=
      (norm_snd_le (b - cplW c k).2).trans (norm_snd_le _)
    have hR0' : 0 ≤ R := (norm_nonneg _).trans hn
    have hq0 : ‖b.2.1 + c * (k : ℝ)‖ ≤ R := by rw [← e21]; exact le_trans hsnd hn
    have hq : -R ≤ b.2.1 + c * (k : ℝ) ∧ b.2.1 + c * (k : ℝ) ≤ R :=
      abs_le.1 (by rwa [Real.norm_eq_abs] at hq0)
    have hkR : |(k : ℝ)| * c < R + c := by
      have habs : |(k : ℝ)| * c = |c * (k : ℝ)| := by
        rw [abs_mul, abs_of_pos hc, mul_comm]
      rw [habs]
      rw [abs_lt]
      constructor <;> linarith [hq.1, hq.2]
    have hK' : (R + c) / c ≤ (K : ℝ) := Nat.le_ceil _
    have habsK : (|k| : ℝ) ≤ (K : ℝ) := by
      by_contra hcon
      push_neg at hcon
      have h1 : (R + c) / c < (|k| : ℝ) := lt_of_le_of_lt hK' hcon
      rw [div_lt_iff₀ hc] at h1
      have h2 : |(k : ℝ)| = (|k| : ℝ) := by push_cast; rfl
      linarith
    refine ⟨?_, ?_⟩
    · have : |k| ≤ (K : ℤ) := by exact_mod_cast habsK
      exact this
    · rw [hBox, mem_closedBall_zero_iff]
      rw [Prod.norm_def, max_le_iff]
      refine ⟨?_, ?_⟩
      · have := hfst
        rw [e11] at this
        linarith
      · rw [Prod.norm_def, max_le_iff]
        have hb21 : ‖b.2.1‖ ≤ c / 2 := by
          rw [Real.norm_eq_abs, abs_le]
          constructor <;> linarith
        have hb22 : ‖b.2.2‖ ≤ R := by
          have := hsnd2
          rw [e23] at this
          linarith
        constructor <;> linarith
  -- pointwise bound for the periodized sum
  have hpt : ∀ b : Coord, b ∈ cplT c →
      ∑' k : ℤ, ‖((ψ (b - cplW c k) : ℝ) : ℂ)‖ₑ ≤ Box.indicator (fun _ => Cst) b := by
    intro b hb
    by_cases hbB : b ∈ Box
    · rw [Set.indicator_apply, if_pos hbB]
      have hzero : ∀ k : ℤ, k ∉ Finset.Icc (-(K : ℤ)) (K : ℤ) →
          ‖((ψ (b - cplW c k) : ℝ) : ℂ)‖ₑ = 0 := by
        intro k hk
        by_cases hψk : ψ (b - cplW c k) = 0
        · exact hψz _ hψk
        · exfalso
          obtain ⟨h1, _⟩ := hnz b hb k hψk
          exact hk (Finset.mem_Icc.2 (abs_le.1 h1))
      rw [tsum_eq_sum hzero]
      exact Finset.sum_le_sum (fun k _ => hψb _)
    · rw [Set.indicator_apply, if_neg hbB]
      have hz : ∀ k : ℤ, ‖((ψ (b - cplW c k) : ℝ) : ℂ)‖ₑ = 0 := by
        intro k
        by_cases hψk : ψ (b - cplW c k) = 0
        · exact hψz _ hψk
        · exfalso
          exact hbB (hnz b hb k hψk).2
      simp [hz]
  -- Box has finite measure for cylMeas
  have hBoxfin : cylMeas c Box ≠ ⊤ := by
    rw [cpl_cyl_apply c hBoxM]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (ne_top_of_le_ne_top (measure_closedBall_lt_top).ne
        (measure_mono inter_subset_left))
  have hs0 : 0 ≤ 1 / (1 : ℝ≥0∞).toReal - 1 / (ENNReal.ofReal r).toReal := by
    rw [ENNReal.toReal_one, ENNReal.toReal_ofReal (by linarith : (0 : ℝ) ≤ r)]
    have h1r : 1 / r ≤ 1 := by
      rw [div_le_one (by linarith)]
      linarith
    have : (1 : ℝ) / 1 = 1 := by norm_num
    linarith
  have hp1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal r := ENNReal.one_le_ofReal.2 hr.le
  refine ⟨Cst * ENNReal.ofReal c *
      (cylMeas c Box) ^ (1 / (1 : ℝ≥0∞).toReal - 1 / (ENNReal.ofReal r).toReal),
    ENNReal.mul_ne_top (ENNReal.mul_ne_top hCstT ENNReal.ofReal_ne_top)
      (ENNReal.rpow_ne_top_of_nonneg hs0 hBoxfin), ?_⟩
  intro e he hem
  have he_cyl : AEStronglyMeasurable e (cylMeas c) := hem.mono_ac (cpl_ac c)
  -- Hölder on the finite measure `cylMeas.restrict Box`
  have hfinB : IsFiniteMeasure ((cylMeas c).restrict Box) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact lt_top_iff_ne_top.2 hBoxfin⟩
  have hholder : eLpNorm e 1 ((cylMeas c).restrict Box) ≤
      cylNorm c r e * (cylMeas c Box) ^ (1 / (1 : ℝ≥0∞).toReal - 1 / (ENNReal.ofReal r).toReal) := by
    have h1 := eLpNorm_le_eLpNorm_mul_rpow_measure_univ (μ := (cylMeas c).restrict Box) hp1
      he_cyl.restrict
    have h2 : eLpNorm e (ENNReal.ofReal r) ((cylMeas c).restrict Box) ≤ cylNorm c r e :=
      eLpNorm_mono_measure e Measure.restrict_le_self
    rw [Measure.restrict_apply_univ] at h1
    exact h1.trans (mul_le_mul_of_nonneg_right h2 (by positivity))
  -- measurability of the summands
  have hψm : ∀ w : Coord, Measurable (fun y : Coord => ‖((ψ (y - w) : ℝ) : ℂ)‖ₑ) := fun w =>
    (Continuous.enorm (Complex.continuous_ofReal.comp (hψ.comp (continuous_sub_right w)))).measurable
  have hmeask : ∀ k : ℤ, AEMeasurable (fun y : Coord => ‖e y‖ₑ * ‖((ψ (y - cplW c k) : ℝ) : ℂ)‖ₑ)
      ((volume : Measure Coord).restrict (cplT c)) := fun k =>
    ((hem.enorm.mul (hψm _).aemeasurable)).restrict
  have hpre : ∀ k : ℤ, ∫⁻ x in cplA c k, ‖e x * (ψ x : ℂ)‖ₑ ∂volume =
      ∫⁻ y in cplT c, ‖e y‖ₑ * ‖((ψ (y - cplW c k) : ℝ) : ℂ)‖ₑ ∂volume := by
    intro k
    rw [cpl_lintegral_translate]
    apply lintegral_congr_ae
    filter_upwards [ae_restrict_of_ae (cpl_periodic_ae c e he k)] with y hy
    rw [enorm_mul, hy]
  calc ∫⁻ x, ‖e x * (ψ x : ℂ)‖ₑ ∂volume
      = ∑' k : ℤ, ∫⁻ x in cplA c k, ‖e x * (ψ x : ℂ)‖ₑ ∂volume := cpl_lintegral_split c hc _
    _ = ∑' k : ℤ, ∫⁻ y in cplT c, ‖e y‖ₑ * ‖((ψ (y - cplW c k) : ℝ) : ℂ)‖ₑ ∂volume :=
        tsum_congr hpre
    _ = ∫⁻ y in cplT c, ∑' k : ℤ, ‖e y‖ₑ * ‖((ψ (y - cplW c k) : ℝ) : ℂ)‖ₑ ∂volume :=
        (lintegral_tsum hmeask).symm
    _ = ∫⁻ y in cplT c, ‖e y‖ₑ * ∑' k : ℤ, ‖((ψ (y - cplW c k) : ℝ) : ℂ)‖ₑ ∂volume := by
        refine lintegral_congr (fun y => ?_)
        rw [ENNReal.tsum_mul_left]
    _ ≤ ∫⁻ y in cplT c, Box.indicator (fun y => ‖e y‖ₑ * Cst) y ∂volume := by
        apply lintegral_mono_ae
        filter_upwards [ae_restrict_mem (cplT_meas c)] with y hy
        calc ‖e y‖ₑ * ∑' k : ℤ, ‖((ψ (y - cplW c k) : ℝ) : ℂ)‖ₑ
            ≤ ‖e y‖ₑ * Box.indicator (fun _ => Cst) y :=
              mul_le_mul_of_nonneg_left (hpt y hy) (by positivity)
          _ = Box.indicator (fun y => ‖e y‖ₑ * Cst) y := by
              by_cases hyB : y ∈ Box
              · simp [Set.indicator_apply, hyB]
              · simp [Set.indicator_apply, hyB]
    _ = (∫⁻ y in Box, ‖e y‖ₑ ∂((volume : Measure Coord).restrict (cplT c))) * Cst := by
        rw [lintegral_indicator hBoxM, lintegral_mul_const' _ _ hCstT]
    _ = ENNReal.ofReal c * (∫⁻ y in Box, ‖e y‖ₑ ∂(cylMeas c)) * Cst := by
        rw [cpl_lint_T c hc Box]
    _ = ENNReal.ofReal c * eLpNorm e 1 ((cylMeas c).restrict Box) * Cst := by
        rw [eLpNorm_one_eq_lintegral_enorm]
    _ ≤ ENNReal.ofReal c * (cylNorm c r e *
          (cylMeas c Box) ^ (1 / (1 : ℝ≥0∞).toReal - 1 / (ENNReal.ofReal r).toReal)) * Cst :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hholder (by positivity))
          (by positivity)
    _ = Cst * ENNReal.ofReal c *
          (cylMeas c Box) ^ (1 / (1 : ℝ≥0∞).toReal - 1 / (ENNReal.ofReal r).toReal) *
            cylNorm c r e := by ring

theorem chmPairLim : ChmPairLim := by
  intro r c hr hc ψ hψ hψs g h hg hh hgm hhm hgn hhn hdiff
  obtain ⟨C, hC, hkey⟩ := cpl_key r c hr hc ψ hψ hψs
  have hone : (1 : ℝ≥0∞) ≤ ENNReal.ofReal r := ENNReal.one_le_ofReal.2 hr.le
  have hint : ∀ e : Coord → ℂ, QPeriodicS c e → AEStronglyMeasurable e volume →
      cylNorm c r e < ⊤ → Integrable (fun x => e x * (ψ x : ℂ)) := by
    intro e he hem hfin
    refine ⟨hem.mul (Complex.continuous_ofReal.comp hψ).aestronglyMeasurable, ?_⟩
    exact lt_of_le_of_lt (hkey e he hem) (ENNReal.mul_lt_top (lt_top_iff_ne_top.2 hC) hfin)
  have hgcyl : ∀ n, AEStronglyMeasurable (g n) (cylMeas c) := fun n =>
    (hgm n).mono_ac (cpl_ac c)
  have hhcyl : AEStronglyMeasurable h (cylMeas c) := hhm.mono_ac (cpl_ac c)
  have hfinD : ∀ n, cylNorm c r (fun x => g n x - h x) < ⊤ := fun n =>
    lt_of_le_of_lt (eLpNorm_sub_le (hgcyl n) hhcyl hone) (ENNReal.add_lt_top.2 ⟨hgn n, hhn⟩)
  have qdiff : ∀ n, QPeriodicS c (fun x => g n x - h x) := by
    intro n
    unfold QPeriodicS at hg hh ⊢
    filter_upwards [hg n, hh] with x h1 h2
    show g n (qShift c x) - h (qShift c x) = g n x - h x
    rw [h1, h2]
  have hbound : ∀ n, ∫⁻ x, ‖(g n x - h x) * (ψ x : ℂ)‖ₑ ∂volume ≤
      C * cylNorm c r (fun x => g n x - h x) := fun n =>
    hkey (fun x => g n x - h x) (qdiff n) ((hgm n).sub hhm)
  have hCt : Tendsto (fun n => C * cylNorm c r (fun x => g n x - h x)) atTop (𝓝 0) := by
    simpa using ENNReal.Tendsto.const_mul hdiff (Or.inr hC)
  have hreal : Tendsto (fun n => (C * cylNorm c r (fun x => g n x - h x)).toReal) atTop
      (𝓝 0) := by
    have h2 : Tendsto (fun n => (C * cylNorm c r (fun x => g n x - h x)).toReal) atTop
        (𝓝 (0 : ℝ≥0∞).toReal) := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hCt
    rwa [ENNReal.toReal_zero] at h2
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) hreal
  have hsplit : (∫ x, g n x * (ψ x : ℂ)) - (∫ x, h x * (ψ x : ℂ)) =
      ∫ x, (g n x - h x) * (ψ x : ℂ) := by
    rw [← integral_sub (hint (g n) (hg n) (hgm n) (hgn n)) (hint h hh hhm hhn)]
    congr 1
    funext x
    ring
  rw [hsplit]
  have hnl : ‖∫ x, (g n x - h x) * (ψ x : ℂ)‖ ≤
      (∫⁻ x, ‖(g n x - h x) * (ψ x : ℂ)‖ₑ ∂volume).toReal := by
    have := norm_integral_le_lintegral_norm (μ := (volume : Measure Coord))
      (fun x => (g n x - h x) * (ψ x : ℂ))
    simpa only [ofReal_norm] using this
  calc ‖∫ x, (g n x - h x) * (ψ x : ℂ)‖
      ≤ (∫⁻ x, ‖(g n x - h x) * (ψ x : ℂ)‖ₑ ∂volume).toReal := hnl
    _ ≤ (C * cylNorm c r (fun x => g n x - h x)).toReal :=
        ENNReal.toReal_mono (ENNReal.mul_ne_top hC (hfinD n).ne) (hbound n)

end UnforcedLeray.Short.IIb
