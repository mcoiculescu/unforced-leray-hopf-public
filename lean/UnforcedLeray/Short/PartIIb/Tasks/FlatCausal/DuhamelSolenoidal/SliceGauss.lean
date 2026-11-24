import UnforcedLeray.Short.PartIIb.Sub.T12_6
import UnforcedLeray.Short.PartIIb.Tasks.FlatUnique.CellStream.PeriodicUnfold
import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.DuhamelMeasurable.Periodic

/-!
# Part II-b, task `PartII-b:T12/6/5` (`DsolSliceGauss`): Gaussian integrability of a.e. slice

Source of record: `the November 2 reference manuscript`, SP 1924 (lines 1920-1930).
Target: `DsolSliceGauss` of `Sub/T12_6.lean`.

Proof outline (no Hoelder, no polynomial weights).
1. `exists_periodic_rep` gives a strongly measurable `G'` with `G = G'` a.e. on `{s > 0}`.
2. `hMeas c r = ageμ c (r/2-5/2)` has density `dens`, so the finiteness of `‖G‖_{H_r}` gives
   `∫⁻ dens · ‖G'‖ₑ^r < ∞`, which is the cell integral `M = ∫⁻_{strip 0} T < ∞` of
   `T x = c⁻¹ s^α ‖G'‖ₑ^r` (for `s > 0`).
3. On the `q`-strips `pucStrip c n` (Coord-level, from `PeriodicUnfold`), the Gaussian weight is
   bounded by `exp(-(a c²/4) n²)` and `T` is shift invariant a.e., so
   `∫⁻ T · E_a ≤ (∑_n exp(-(a c²/4) n²)) · M < ∞`.
4. Tonelli gives `∫⁻_{s} s^α J_a(s) < ∞`, hence `J_a(s) < ∞` for a.e. `s > 0`, where
   `J_a(s) = ∫⁻_y ‖G'(s,y)‖ₑ^r e^{-a|y|²}`. Only the countably many widths `a_k = 1/(k+1)` are
   needed, since `e^{-a|y|²} ≤ e^{-a_k |y|²}` for `a_k ≤ a`.
5. `x ≤ 1 + x^r` (for `r ≥ 1`) turns `J_a(s) < ∞` into Gaussian integrability of the slice.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal

namespace UnforcedLeray.Short.IIb

/-! ## Generic `q`-shift lemmas (the `PeriodicUnfold` versions are stated for `ℂ`-valued maps) -/

theorem dsl_ae_shift_add {β : Type*} {G : Coord → β} {s t : ℝ}
    (hs : ∀ᵐ x : Coord, G (qShift s x) = G x)
    (ht : ∀ᵐ x : Coord, G (qShift t x) = G x) : ∀ᵐ x : Coord, G (qShift (s + t) x) = G x := by
  have h : ∀ᵐ x : Coord, G (qShift s (qShift t x)) = G (qShift t x) :=
    (puc_measurePreserving_qShift t).quasiMeasurePreserving.ae hs
  filter_upwards [h, ht] with x hx1 hx2
  rw [← puc_qShift_qShift]
  exact hx1.trans hx2

theorem dsl_ae_shift_neg {β : Type*} {G : Coord → β} {s : ℝ}
    (hs : ∀ᵐ x : Coord, G (qShift s x) = G x) : ∀ᵐ x : Coord, G (qShift (-s) x) = G x := by
  have h : ∀ᵐ x : Coord, G (qShift s (qShift (-s) x)) = G (qShift (-s) x) :=
    (puc_measurePreserving_qShift (-s)).quasiMeasurePreserving.ae hs
  filter_upwards [h] with x hx
  rw [puc_qShift_inv] at hx
  exact hx.symm

theorem dsl_ae_shift_int {β : Type*} {G : Coord → β} {c : ℝ}
    (hper : ∀ᵐ x : Coord, G (qShift c x) = G x) (k : ℤ) :
    ∀ᵐ x : Coord, G (qShift ((k : ℝ) * c) x) = G x := by
  refine Int.induction_on k ?_ ?_ ?_
  · filter_upwards with x
    simp [qShift]
  · intro n ih
    have e : ((((n : ℤ) + 1 : ℤ)) : ℝ) * c = ((n : ℤ) : ℝ) * c + c := by
      push_cast
      ring
    rw [e]
    exact dsl_ae_shift_add ih hper
  · intro n ih
    have e : (((-(n : ℤ) - 1 : ℤ)) : ℝ) * c = ((-(n : ℤ) : ℤ) : ℝ) * c + -c := by
      push_cast
      ring
    rw [e]
    exact dsl_ae_shift_add ih (dsl_ae_shift_neg hper)

/-- Periodicity of the periodic representative on `{s > 0}`. -/
theorem dsl_periodic_rep {c : ℝ} (hc : 0 < c) {G G' : CProf} (hQ : QPeriodic c G)
    (hGG' : ∀ᵐ x : Coord, 0 < x.1 → G x = G' x) :
    ∀ k : ℤ, ∀ᵐ x : Coord, 0 < x.1 → G' (qShift ((k : ℝ) * c) x) = G' x := by
  intro k
  have hQ' : ∀ᵐ x : Coord, 0 < x.1 → G (qShift c x) = G x := by
    have := hQ
    unfold QPeriodic at this
    rwa [ae_restrict_iff' (measurableSet_lt measurable_const measurable_fst)] at this
  let G0 : CProf := fun x => if 0 < x.1 then G x else 0
  have hG0 : ∀ᵐ x : Coord, G0 (qShift c x) = G0 x := by
    filter_upwards [hQ'] with x hx
    by_cases hp : 0 < x.1
    · have hp' : 0 < (qShift c x).1 := hp
      simp only [G0, if_pos hp, if_pos hp', hx hp]
    · have hp' : ¬ 0 < (qShift c x).1 := hp
      simp only [G0, if_neg hp, if_neg hp']
  have h1 : ∀ᵐ x : Coord, G0 (qShift ((k : ℝ) * c) x) = G0 x := dsl_ae_shift_int hG0 k
  have h2 : ∀ᵐ x : Coord, (0 < (qShift ((k : ℝ) * c) x).1 →
      G (qShift ((k : ℝ) * c) x) = G' (qShift ((k : ℝ) * c) x)) :=
    (puc_measurePreserving_qShift ((k : ℝ) * c)).quasiMeasurePreserving.ae hGG'
  filter_upwards [h1, h2, hGG'] with x hx1 hx2 hx3 hxpos
  have hxpos' : 0 < (qShift ((k : ℝ) * c) x).1 := hxpos
  rw [← hx2 hxpos']
  simp only [G0, if_pos hxpos', if_pos hxpos] at hx1
  rw [hx1]
  exact hx3 hxpos

/-! ## Weights -/

/-- The cell weight `T(x) = c⁻¹ s^α 1_{s>0} ‖G'(x)‖ₑ^p`, invariant under `q`-shifts. -/
def dslT (c α p : ℝ) (G' : CProf) (x : Coord) : ℝ≥0∞ :=
  ENNReal.ofReal (c⁻¹ * x.1 ^ α) * (Ioi (0 : ℝ)).indicator 1 x.1 * ‖G' x‖ₑ ^ p

/-- The Gaussian weight at slice point `(q, η)`, `e^{-a(q²+η²)}`. -/
def dslE (a : ℝ) (x : Coord) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (-a * (x.2.1 ^ 2 + x.2.2 ^ 2)))

theorem dslT_measurable {c α p : ℝ} {G' : CProf} (hG' : Measurable G') :
    Measurable (dslT c α p G') := by
  unfold dslT
  have h1 : Measurable fun x : Coord => ENNReal.ofReal (c⁻¹ * x.1 ^ α) :=
    ENNReal.measurable_ofReal.comp ((measurable_fst.pow_const α).const_mul c⁻¹)
  have h2 : Measurable fun x : Coord => (Ioi (0 : ℝ)).indicator (1 : ℝ → ℝ≥0∞) x.1 :=
    (measurable_one.indicator measurableSet_Ioi).comp measurable_fst
  exact (h1.mul h2).mul (hG'.enorm.pow_const p)

theorem dslE_measurable (a : ℝ) : Measurable (dslE a) := by
  unfold dslE
  have h : Measurable fun x : Coord => Real.exp (-a * (x.2.1 ^ 2 + x.2.2 ^ 2)) := by fun_prop
  exact ENNReal.measurable_ofReal.comp h

/-- Shift invariance of `T` for a fixed shift, from the a.e. periodicity of `G'`. -/
theorem dsl_T_shift {c α p σ : ℝ} {G' : CProf}
    (hper : ∀ᵐ x : Coord, 0 < x.1 → G' (qShift σ x) = G' x) :
    ∀ᵐ x : Coord, dslT c α p G' (qShift σ x) = dslT c α p G' x := by
  filter_upwards [hper] with x hx
  have e : (qShift σ x).1 = x.1 := rfl
  by_cases hpos : 0 < x.1
  · unfold dslT
    rw [e, hx hpos]
  · unfold dslT
    rw [e, Set.indicator_of_notMem (fun h : x.1 ∈ Ioi (0 : ℝ) => hpos h)]
    simp

/-! ## The strips and the Gaussian bound on them -/

theorem dsl_sq_ge {c : ℝ} (hc : 0 < c) {n : ℤ} {x : Coord} (hx : x ∈ pucStrip c n) :
    ((n : ℝ) * c) ^ 2 / 4 ≤ x.2.1 ^ 2 := by
  obtain ⟨h1, h2⟩ := puc_mem_strip_iff.1 hx
  rcases lt_trichotomy n 0 with hn | hn | hn
  · have hn' : (n : ℝ) ≤ -1 := by exact_mod_cast (show n ≤ -1 by omega)
    have hk : (n : ℝ) * c ≤ -c := by nlinarith [mul_le_mul_of_nonneg_right hn' hc.le]
    have hA : -((n : ℝ) * c) / 2 ≤ -x.2.1 := by linarith
    have h0 : 0 ≤ -((n : ℝ) * c) / 2 := by linarith
    nlinarith [mul_self_le_mul_self h0 hA]
  · subst hn
    simp only [Int.cast_zero, zero_mul]
    nlinarith [sq_nonneg x.2.1]
  · have hn' : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
    have hk : c ≤ (n : ℝ) * c := by nlinarith [mul_le_mul_of_nonneg_right hn' hc.le]
    have hA : (n : ℝ) * c / 2 ≤ x.2.1 := by linarith
    have h0 : 0 ≤ (n : ℝ) * c / 2 := by linarith
    nlinarith [mul_self_le_mul_self h0 hA]

theorem dsl_summable {b : ℝ} (hb : 0 < b) :
    Summable (fun n : ℤ => Real.exp (-b * (n : ℝ) ^ 2)) := by
  have hnat : Summable (fun n : ℕ => Real.exp (-b * (n : ℝ) ^ 2)) := by
    refine Summable.of_nonneg_of_le (fun n => (Real.exp_pos _).le) (fun n => ?_)
      (summable_geometric_of_lt_one (Real.exp_pos (-b)).le (by
        have h := Real.exp_lt_exp.2 (show -b < 0 by linarith)
        simpa using h))
    rw [← Real.exp_nat_mul]
    apply Real.exp_le_exp.2
    have hn2 : (n : ℝ) ≤ (n : ℝ) ^ 2 := by
      rcases Nat.eq_zero_or_pos n with h | h
      · subst h; simp
      · have h1 : (1 : ℝ) ≤ n := by exact_mod_cast h
        nlinarith
    nlinarith [mul_le_mul_of_nonneg_left hn2 hb.le]
  refine Summable.of_nat_of_neg ?_ ?_
  · simpa using hnat
  · simpa using hnat

theorem dsl_sum_lt_top {c a : ℝ} (hc : 0 < c) (ha : 0 < a) :
    ∑' n : ℤ, ENNReal.ofReal (Real.exp (-(a * c ^ 2 / 4) * (n : ℝ) ^ 2)) < ⊤ := by
  have hb : 0 < a * c ^ 2 / 4 := div_pos (mul_pos ha (pow_pos hc 2)) (by norm_num)
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => (Real.exp_pos _).le) (dsl_summable hb)]
  exact ENNReal.ofReal_lt_top

theorem dsl_lintegral_strip (F : Coord → ℝ≥0∞) (c : ℝ) (n : ℤ) :
    ∫⁻ x in pucStrip c n, F x = ∫⁻ y in univ ×ˢ Cyl.cell c, F (qShift ((n : ℝ) * c) y) := by
  have h := (puc_measurePreserving_qShift (-((n : ℝ) * c))).setLIntegral_comp_preimage_emb
    (puc_qShift_measurableEmbedding (-((n : ℝ) * c)))
    (fun y => F (qShift ((n : ℝ) * c) y)) (univ ×ˢ Cyl.cell c)
  simp only [puc_qShift_inv, neg_neg] at h
  unfold pucStrip
  simpa only [neg_neg] using h

/-- Coordinate-level bound: the weighted integral is at most the sum of strip constants times
the cell integral of `T`. -/
theorem dsl_coord_bound {c α p a : ℝ} (hc : 0 < c) (ha : 0 < a) {G' : CProf}
    (hG' : Measurable G')
    (hper : ∀ k : ℤ, ∀ᵐ x : Coord, 0 < x.1 → G' (qShift ((k : ℝ) * c) x) = G' x) :
    ∫⁻ x, dslT c α p G' x * dslE a x ≤
      (∑' n : ℤ, ENNReal.ofReal (Real.exp (-(a * c ^ 2 / 4) * (n : ℝ) ^ 2))) *
        ∫⁻ x in pucStrip c 0, dslT c α p G' x := by
  have hstrip : ∀ n : ℤ, ∫⁻ x in pucStrip c n, dslT c α p G' x =
      ∫⁻ x in pucStrip c 0, dslT c α p G' x := by
    intro n
    rw [dsl_lintegral_strip, dsl_lintegral_strip]
    apply lintegral_congr_ae
    filter_upwards [ae_restrict_of_ae (dsl_T_shift (hper n)),
      ae_restrict_of_ae (dsl_T_shift (hper 0))] with y h1 h2
    rw [h1, h2]
  have hstripbd : ∀ n : ℤ, ∫⁻ x in pucStrip c n, dslT c α p G' x * dslE a x ≤
      ENNReal.ofReal (Real.exp (-(a * c ^ 2 / 4) * (n : ℝ) ^ 2)) *
        ∫⁻ x in pucStrip c 0, dslT c α p G' x := by
    intro n
    rw [← hstrip n, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    apply setLIntegral_mono' (puc_measurableSet_strip c n)
    intro x hx
    have hE : dslE a x ≤ ENNReal.ofReal (Real.exp (-(a * c ^ 2 / 4) * (n : ℝ) ^ 2)) := by
      unfold dslE
      apply ENNReal.ofReal_le_ofReal
      apply Real.exp_le_exp.2
      have hq := dsl_sq_ge hc hx
      nlinarith [mul_le_mul_of_nonneg_left hq ha.le, sq_nonneg x.2.2]
    calc dslT c α p G' x * dslE a x
        ≤ dslT c α p G' x * ENNReal.ofReal (Real.exp (-(a * c ^ 2 / 4) * (n : ℝ) ^ 2)) :=
          mul_le_mul_of_nonneg_left hE zero_le
      _ = ENNReal.ofReal (Real.exp (-(a * c ^ 2 / 4) * (n : ℝ) ^ 2)) * dslT c α p G' x :=
          mul_comm _ _
  have hU : ∫⁻ x, dslT c α p G' x * dslE a x =
      ∑' n : ℤ, ∫⁻ x in pucStrip c n, dslT c α p G' x * dslE a x := by
    rw [← lintegral_iUnion (fun n => puc_measurableSet_strip c n) (puc_pairwise_disjoint hc),
      puc_iUnion_strip hc, Measure.restrict_univ]
  rw [hU]
  calc ∑' n : ℤ, ∫⁻ x in pucStrip c n, dslT c α p G' x * dslE a x
      ≤ ∑' n : ℤ, ENNReal.ofReal (Real.exp (-(a * c ^ 2 / 4) * (n : ℝ) ^ 2)) *
          ∫⁻ x in pucStrip c 0, dslT c α p G' x := ENNReal.tsum_le_tsum hstripbd
    _ = (∑' n : ℤ, ENNReal.ofReal (Real.exp (-(a * c ^ 2 / 4) * (n : ℝ) ^ 2))) *
          ∫⁻ x in pucStrip c 0, dslT c α p G' x := ENNReal.tsum_mul_right

/-! ## Finiteness of the cell integral from `H_r` -/

theorem dsl_pointwise_strip {c r : ℝ} (hc : 0 < c) (G' : CProf) (x : Coord) :
    (pucStrip c 0).indicator (dslT c (r / 2 - 5 / 2) r G') x =
      dens c (r / 2 - 5 / 2) x * ‖G' x‖ₑ ^ r := by
  have hmem : x ∈ pucStrip c 0 ↔ x.2 ∈ Cyl.cell c := by
    rw [puc_mem_strip_iff, Cyl.mem_cell]
    simp
  by_cases h1 : 0 < x.1 <;> by_cases h2 : x.2 ∈ Cyl.cell c <;>
    simp [dslT, dens, Set.indicator_apply, hmem, Set.mem_prod, Axi.qCell_eq_cell, h1, h2]

theorem dsl_M_finite {c r : ℝ} (hc : 0 < c) (hr : 0 < r) {G G' : CProf} (hG : InHr c r G)
    (hG' : Measurable G') (hGG' : ∀ᵐ x : Coord, 0 < x.1 → G x = G' x) :
    ∫⁻ x in pucStrip c 0, dslT c (r / 2 - 5 / 2) r G' x < ⊤ := by
  have hfin : ∫⁻ z, ‖G z‖ₑ ^ r ∂(hMeas c r) < ⊤ := by
    have h : eLpNorm G (ENNReal.ofReal r) (hMeas c r) < ⊤ := hG.finite
    rw [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top
      (ENNReal.ofReal_pos.2 hr).ne' ENNReal.ofReal_ne_top,
      ENNReal.toReal_ofReal hr.le] at h
    exact h
  have hW : hMeas c r = (volume : Measure Coord).withDensity (dens c (r / 2 - 5 / 2)) :=
    ageμ_eq_withDensity hc _
  rw [hW] at hfin
  have hae : ∀ᵐ x ∂(volume : Measure Coord), dens c (r / 2 - 5 / 2) x ≠ 0 → G x = G' x := by
    filter_upwards [hGG'] with x hx hd
    apply hx
    by_contra hneg
    apply hd
    have hnot : x ∉ Ioi (0 : ℝ) ×ˢ Axi.qCell c := fun h => hneg h.1
    unfold dens
    rw [Set.indicator_of_notMem hnot]
    simp
  have hgood := (ae_withDensity_iff (measurable_dens c (r / 2 - 5 / 2))).2 hae
  have heq : ∫⁻ z, ‖G z‖ₑ ^ r ∂((volume : Measure Coord).withDensity (dens c (r / 2 - 5 / 2))) =
      ∫⁻ z, ‖G' z‖ₑ ^ r ∂((volume : Measure Coord).withDensity (dens c (r / 2 - 5 / 2))) := by
    apply lintegral_congr_ae
    filter_upwards [hgood] with z hz
    rw [hz]
  rw [heq, lintegral_withDensity_eq_lintegral_mul _ (measurable_dens c _)
    (hG'.enorm.pow_const r)] at hfin
  have hM : ∫⁻ x in pucStrip c 0, dslT c (r / 2 - 5 / 2) r G' x =
      ∫⁻ x, dens c (r / 2 - 5 / 2) x * ‖G' x‖ₑ ^ r := by
    rw [← lintegral_indicator (puc_measurableSet_strip c 0)]
    apply lintegral_congr
    intro x
    exact dsl_pointwise_strip hc G' x
  rw [hM]
  exact hfin

/-! ## Tonelli on the slices -/

theorem dsl_slice_finite {c α p a : ℝ} (hc : 0 < c) {G' : CProf} (hG' : Measurable G')
    (hLT : ∫⁻ x, dslT c α p G' x * dslE a x < ⊤) :
    ∀ᵐ s : ℝ, 0 < s → ∫⁻ y, ‖G' (s, y)‖ₑ ^ p * dslE a (s, y) < ⊤ := by
  have hTm := dslT_measurable (c := c) (α := α) (p := p) hG'
  have hF : Measurable fun x : Coord => dslT c α p G' x * dslE a x :=
    hTm.mul (dslE_measurable a)
  have hprod : ∫⁻ x, dslT c α p G' x * dslE a x =
      ∫⁻ s, ∫⁻ y, dslT c α p G' (s, y) * dslE a (s, y) := by
    rw [Measure.volume_eq_prod ℝ (ℝ × ℝ), lintegral_prod _ hF.aemeasurable]
  have hΦm : Measurable fun s : ℝ => ∫⁻ y, dslT c α p G' (s, y) * dslE a (s, y) :=
    hF.lintegral_prod_right'
  have hΦfin : ∫⁻ s, ∫⁻ y, dslT c α p G' (s, y) * dslE a (s, y) ≠ ⊤ := by
    rw [← hprod]
    exact hLT.ne
  filter_upwards [ae_lt_top hΦm hΦfin] with s hs hpos
  have hK : ENNReal.ofReal (c⁻¹ * s ^ α) ≠ 0 := by
    apply ENNReal.ofReal_ne_zero_iff.2
    have : 0 < c⁻¹ * s ^ α := mul_pos (inv_pos.2 hc) (Real.rpow_pos_of_pos hpos _)
    exact this
  have hKtop : ENNReal.ofReal (c⁻¹ * s ^ α) ≠ ⊤ := ENNReal.ofReal_ne_top
  have hsplit : ∫⁻ y, dslT c α p G' (s, y) * dslE a (s, y) =
      ENNReal.ofReal (c⁻¹ * s ^ α) * ∫⁻ y, ‖G' (s, y)‖ₑ ^ p * dslE a (s, y) := by
    rw [← lintegral_const_mul]
    · apply lintegral_congr
      intro y
      unfold dslT
      rw [Set.indicator_of_mem (show s ∈ Ioi (0 : ℝ) from hpos)]
      simp [mul_assoc, mul_comm, mul_left_comm]
    · exact (hG'.comp (measurable_const.prodMk measurable_id)).enorm.pow_const p |>.mul
        (dslE_measurable a |>.comp (measurable_const.prodMk measurable_id))
  rw [hsplit] at hs
  have hJ : ∫⁻ y, ‖G' (s, y)‖ₑ ^ p * dslE a (s, y) =
      (ENNReal.ofReal (c⁻¹ * s ^ α))⁻¹ * (ENNReal.ofReal (c⁻¹ * s ^ α) *
        ∫⁻ y, ‖G' (s, y)‖ₑ ^ p * dslE a (s, y)) := by
    rw [← mul_assoc, ENNReal.inv_mul_cancel hK hKtop, one_mul]
  rw [hJ, lt_top_iff_ne_top]
  exact ENNReal.mul_ne_top (ENNReal.inv_ne_top.2 hK) hs.ne

/-! ## The slice Gaussian integrability from the lintegral bound -/

theorem dsl_enorm_le (x : ℝ≥0∞) {r : ℝ} (hr : 1 ≤ r) : x ≤ 1 + x ^ r := by
  rcases le_total x 1 with h | h
  · exact h.trans (le_add_right le_rfl)
  · have : x ^ (1 : ℝ) ≤ x ^ r := ENNReal.rpow_le_rpow_of_exponent_le h hr
    rw [ENNReal.rpow_one] at this
    exact this.trans le_add_self

theorem dsl_gauss_fin {a : ℝ} (ha : 0 < a) :
    ∫⁻ y : ℝ × ℝ, ENNReal.ofReal (Real.exp (-a * (y.1 ^ 2 + y.2 ^ 2))) < ⊤ := by
  have hfac : ∀ y : ℝ × ℝ, Real.exp (-a * (y.1 ^ 2 + y.2 ^ 2)) =
      Real.exp (-a * y.1 ^ 2) * Real.exp (-a * y.2 ^ 2) := fun y => by
    rw [← Real.exp_add]
    congr 1
    ring
  have hI : Integrable (fun y : ℝ × ℝ => Real.exp (-a * y.1 ^ 2) * Real.exp (-a * y.2 ^ 2))
      (volume.prod volume) :=
    Integrable.mul_prod (integrable_exp_neg_mul_sq ha) (integrable_exp_neg_mul_sq ha)
  have h := hI.2
  unfold HasFiniteIntegral at h
  refine lt_of_eq_of_lt ?_ h
  apply lintegral_congr
  intro y
  dsimp only
  rw [hfac y, Real.enorm_eq_ofReal (by positivity)]

theorem dsl_slice_integrable {a r : ℝ} (ha : 0 < a) (hr : 1 ≤ r) {g0 : ℝ × ℝ → CMerid}
    (hg : Measurable g0)
    (hJ : ∫⁻ y, ‖g0 y‖ₑ ^ r * ENNReal.ofReal (Real.exp (-a * (y.1 ^ 2 + y.2 ^ 2))) < ⊤) :
    Integrable (fun y : ℝ × ℝ => Real.exp (-a * (y.1 ^ 2 + y.2 ^ 2)) • g0 y) := by
  have hEm : Measurable fun y : ℝ × ℝ => Real.exp (-a * (y.1 ^ 2 + y.2 ^ 2)) := by
    fun_prop
  have hlin := dsl_gauss_fin ha
  have hsm : AEStronglyMeasurable (fun y : ℝ × ℝ => Real.exp (-a * (y.1 ^ 2 + y.2 ^ 2)) • g0 y) volume :=
    (hEm.smul hg).aestronglyMeasurable
  refine ⟨hsm, ?_⟩
  unfold HasFiniteIntegral
  have hpt : ∀ y : ℝ × ℝ, ‖Real.exp (-a * (y.1 ^ 2 + y.2 ^ 2)) • g0 y‖ₑ ≤
      ENNReal.ofReal (Real.exp (-a * (y.1 ^ 2 + y.2 ^ 2))) +
        ‖g0 y‖ₑ ^ r * ENNReal.ofReal (Real.exp (-a * (y.1 ^ 2 + y.2 ^ 2))) := by
    intro y
    rw [enorm_smul, Real.enorm_eq_ofReal (Real.exp_pos _).le]
    calc ENNReal.ofReal (Real.exp (-a * (y.1 ^ 2 + y.2 ^ 2))) * ‖g0 y‖ₑ
        ≤ ENNReal.ofReal (Real.exp (-a * (y.1 ^ 2 + y.2 ^ 2))) * (1 + ‖g0 y‖ₑ ^ r) := by
          gcongr
          exact dsl_enorm_le _ hr
      _ = ENNReal.ofReal (Real.exp (-a * (y.1 ^ 2 + y.2 ^ 2))) +
          ‖g0 y‖ₑ ^ r * ENNReal.ofReal (Real.exp (-a * (y.1 ^ 2 + y.2 ^ 2))) := by
          rw [mul_add, mul_one, mul_comm (‖g0 y‖ₑ ^ r)]
  have hEm' : Measurable fun y : ℝ × ℝ =>
      ENNReal.ofReal (Real.exp (-a * (y.1 ^ 2 + y.2 ^ 2))) :=
    ENNReal.measurable_ofReal.comp hEm
  have hsum : ∫⁻ y, (ENNReal.ofReal (Real.exp (-a * (y.1 ^ 2 + y.2 ^ 2))) +
          ‖g0 y‖ₑ ^ r * ENNReal.ofReal (Real.exp (-a * (y.1 ^ 2 + y.2 ^ 2)))) < ⊤ := by
    rw [lintegral_add_left hEm']
    exact ENNReal.add_lt_top.2 ⟨hlin, hJ⟩
  exact lt_of_le_of_lt (lintegral_mono hpt) hsum

/-! ## Main theorem -/

/-- **Leaf `PartII-b:T12/6/5`** (`DsolSliceGauss`, Gaussian integrability of a.e. slice). -/
theorem dsolSliceGauss : UnforcedLeray.Short.IIb.DsolSliceGauss := by
  intro c r G hc hr1 hr3 hG
  obtain ⟨G', hG'm, hGG'⟩ := exists_periodic_rep (a := r / 2 - 5 / 2) hc hG.periodic hG.meas
  have hG'meas : Measurable G' := hG'm.measurable
  have hper := dsl_periodic_rep hc hG.periodic hGG'
  have hM := dsl_M_finite hc (by linarith) hG hG'meas hGG'
  -- finiteness of the Coord-level weighted integral for the width `a`
  have hLTk : ∀ a : ℝ, 0 < a → ∫⁻ x, dslT c (r / 2 - 5 / 2) r G' x * dslE a x < ⊤ := by
    intro a ha
    refine lt_of_le_of_lt (dsl_coord_bound (α := r / 2 - 5 / 2) (p := r) hc ha hG'meas hper) ?_
    exact ENNReal.mul_lt_top (dsl_sum_lt_top hc ha) hM
  have hk : ∀ k : ℕ, ∀ᵐ s : ℝ, 0 < s →
      ∫⁻ y, ‖G' (s, y)‖ₑ ^ r * dslE (1 / ((k : ℝ) + 1)) (s, y) < ⊤ := fun k =>
    dsl_slice_finite hc hG'meas (hLTk _ (by positivity))
  have hall := ae_all_iff.2 hk
  have h2 : ∀ᵐ z ∂((volume : Measure ℝ).prod (volume : Measure (ℝ × ℝ))),
      (0 < z.1 → G z = G' z) := hGG'
  have hsl := Measure.ae_ae_of_ae_prod h2
  filter_upwards [hall, hsl] with t hkt hst ht
  unfold DsolGaussInt
  intro a ha
  obtain ⟨k, hk'⟩ := exists_nat_one_div_lt ha
  have hJa : ∫⁻ y, ‖G' (t, y)‖ₑ ^ r * ENNReal.ofReal (Real.exp (-a * (y.1 ^ 2 + y.2 ^ 2))) < ⊤ := by
    refine lt_of_le_of_lt ?_ (hkt k ht)
    apply lintegral_mono
    intro y
    refine mul_le_mul_of_nonneg_left ?_ zero_le
    show ENNReal.ofReal (Real.exp (-a * (y.1 ^ 2 + y.2 ^ 2))) ≤
      ENNReal.ofReal (Real.exp (-(1 / ((k : ℝ) + 1)) * (y.1 ^ 2 + y.2 ^ 2)))
    apply ENNReal.ofReal_le_ofReal
    apply Real.exp_le_exp.2
    have hq : 0 ≤ y.1 ^ 2 + y.2 ^ 2 := by positivity
    nlinarith [mul_le_mul_of_nonneg_right hk'.le hq]
  have hGm : Measurable fun y : ℝ × ℝ => G' (t, y) :=
    hG'meas.comp (measurable_const.prodMk measurable_id)
  have hint := dsl_slice_integrable ha (by linarith : (1 : ℝ) ≤ r) hGm hJa
  refine hint.congr ?_
  filter_upwards [hst] with y hy
  rw [hy ht]

end UnforcedLeray.Short.IIb
