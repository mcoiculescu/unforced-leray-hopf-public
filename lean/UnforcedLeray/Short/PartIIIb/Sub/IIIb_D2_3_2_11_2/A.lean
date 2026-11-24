import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_2_11_2

/-!
# `smoothOldSource_proved` (PartIII-b:IIIb-D2/3/2/11/2/1)

Source of record: `the November 2 reference manuscript` 4155-4166.
Smooth old data gives a separated source `oldPhys R c g` (period `2c/R`, radial support
`ϱ ≤ R√(5ν/6)`, bounded and compactly supported in `z`), hence `IsSepSource` and `SepMoment`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- Entries of a cylindrical frame are bounded by one. -/
lemma cylFrame_abs_le (z : Space) (i k : Fin 3) : |NearInst.cylFrame z i k| ≤ 1 := by
  have hz0 : |z 0 / NearInst.hRad z| ≤ 1 ∧ |z 1 / NearInst.hRad z| ≤ 1 := by
    unfold NearInst.hRad
    by_cases h0 : Real.sqrt (z 0 ^ 2 + z 1 ^ 2) = 0
    · simp [h0]
    · have hpos : 0 < Real.sqrt (z 0 ^ 2 + z 1 ^ 2) :=
        lt_of_le_of_ne (Real.sqrt_nonneg _) (Ne.symm h0)
      constructor
      · rw [abs_div, abs_of_pos hpos]
        exact div_le_one_of_le₀ (Real.abs_le_sqrt (by nlinarith [sq_nonneg (z 1)])) hpos.le
      · rw [abs_div, abs_of_pos hpos]
        exact div_le_one_of_le₀ (Real.abs_le_sqrt (by nlinarith [sq_nonneg (z 0)])) hpos.le
  fin_cases i <;> fin_cases k <;> simp [NearInst.cylFrame, hz0.1, hz0.2]


lemma nsSym_zero : NearInst.nsSym 0 = 0 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [NearInst.nsSym, NearInst.symRZ]

/-- Off the old disk `ϱ > R√(5ν/6)` the physical source of smooth old data vanishes. -/
lemma oldPhys_eq_zero_of_far {R c ν : ℝ} {g : Chart → Ten3} (hR : 0 < R) (hν : 0 < ν)
    (hg : IsSmoothOld c ν g) (τ : ℝ) (z : Space)
    (hz : R * Real.sqrt (5 * ν / 6) < NearInst.hRad z) : oldPhys R c g τ z = 0 := by
  have hρ : 0 ≤ R * Real.sqrt (5 * ν / 6) := by positivity
  have hh : 0 < NearInst.hRad z := lt_of_le_of_lt hρ hz
  have h1 : (R * Real.sqrt (5 * ν / 6)) ^ 2 < NearInst.hRad z ^ 2 :=
    pow_lt_pow_left₀ hz hρ (by norm_num)
  have h2 : (R * Real.sqrt (5 * ν / 6)) ^ 2 = R ^ 2 * (5 * ν / 6) := by
    rw [mul_pow, Real.sq_sqrt (by positivity)]
  rw [h2] at h1
  have hs : ν * (NearInst.chartOf R c z τ).1 ≤ 6 / 5 := by
    show ν * (R ^ 2 / NearInst.hRad z ^ 2) ≤ 6 / 5
    rw [← mul_div_assoc, div_le_iff₀ (by positivity)]
    nlinarith
  have hg0 : g (NearInst.chartOf R c z τ) = 0 := hg.old _ hs
  simp [oldPhys, NearInst.cartLift, hg0, nsSym_zero]

/-- Bound for a chart tensor entry `s • nsSym X` in terms of the sup bounds. -/
lemma nsSym_abs_le (X : Ten3) (a b : Fin 3) : |NearInst.nsSym X a b| ≤ ‖X‖ := by
  have hx : ∀ p, |X p| ≤ ‖X‖ := fun p => by
    rw [← Real.norm_eq_abs]; exact PiLp.norm_apply_le X p
  have h0 : 0 ≤ ‖X‖ := norm_nonneg _
  have hs : |NearInst.symRZ X| ≤ ‖X‖ := by
    unfold NearInst.symRZ
    rw [abs_le]
    constructor <;> linarith [abs_le.mp (hx (0, 2)), abs_le.mp (hx (2, 0))]
  fin_cases a <;> fin_cases b <;> simp [NearInst.nsSym, hs, hx, h0]

/-- Entry bound for a triple product `Q * A * Qᵀ`. -/
lemma triple_entry_bound (Q A : Matrix (Fin 3) (Fin 3) ℝ) (b : ℝ) (hb : 0 ≤ b)
    (hQ : ∀ i k, |Q i k| ≤ 1) (hA : ∀ k l, |A k l| ≤ b) (i j : Fin 3) :
    |(Q * A * Q.transpose) i j| ≤ 9 * b := by
  have hQA : ∀ i k, |(Q * A) i k| ≤ 3 * b := by
    intro i k
    rw [Matrix.mul_apply]
    calc |∑ l, Q i l * A l k| ≤ ∑ l, |Q i l * A l k| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _l : Fin 3, b := Finset.sum_le_sum fun l _ => by
          rw [abs_mul]
          nlinarith [abs_nonneg (Q i l), abs_nonneg (A l k), hQ i l, hA l k]
      _ = 3 * b := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
  rw [Matrix.mul_apply]
  calc |∑ k, (Q * A) i k * Q.transpose k j| ≤ ∑ k, |(Q * A) i k * Q.transpose k j| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _k : Fin 3, 3 * b := Finset.sum_le_sum fun k _ => by
        rw [abs_mul, Matrix.transpose_apply]
        nlinarith [abs_nonneg ((Q * A) i k), hQA i k, hQ j k, abs_nonneg (Q j k)]
    _ = 9 * b := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring

/-- Frobenius norm bound from entrywise bounds. -/
lemma tensorNorm_le_of_entries (M : Matrix (Fin 3) (Fin 3) ℝ) (e : ℝ) (he : 0 ≤ e)
    (h : ∀ i j, |M i j| ≤ e) : IIIa.tensorNorm M ≤ 3 * e := by
  unfold IIIa.tensorNorm
  have key : ∀ i j, M i j ^ 2 ≤ e ^ 2 := fun i j => by
    nlinarith [abs_nonneg (M i j), sq_abs (M i j), h i j]
  have hsum : ∑ i, ∑ j, M i j ^ 2 ≤ (3 * e) ^ 2 := by
    simp only [Fin.sum_univ_three]
    have : (3 * e) ^ 2 = 9 * e ^ 2 := by ring
    rw [this]
    linarith [key 0 0, key 0 1, key 0 2, key 1 0, key 1 1, key 1 2, key 2 0, key 2 1, key 2 2]
  calc Real.sqrt (∑ i, ∑ j, M i j ^ 2) ≤ Real.sqrt ((3 * e) ^ 2) := Real.sqrt_le_sqrt hsum
    _ = 3 * e := Real.sqrt_sq (by positivity)

lemma tensorNorm_zero : IIIa.tensorNorm 0 = 0 := by
  simp [IIIa.tensorNorm]

/-- The chart support is bounded: `|q₁|` and `|q₃|` are bounded on `tsupport g`. -/
lemma chart_support_bound {c : ℝ} {g : Chart → Ten3} (hg : IsSmoothChart c g) :
    ∃ B, 0 ≤ B ∧ ∀ q ∈ tsupport g, |q.1| ≤ B ∧ |q.2.2| ≤ B := by
  obtain ⟨r, hr⟩ := (Metric.isBounded_iff_subset_closedBall (0 : Chart)).1
    hg.compact.isCompact.isBounded
  refine ⟨max r 0, le_max_right _ _, fun q hq => ?_⟩
  have hn : ‖q‖ ≤ r := by simpa using hr hq
  have h1 : |q.1| ≤ r := by
    rw [← Real.norm_eq_abs]; exact le_trans (norm_fst_le q) hn
  have h2 : |q.2.2| ≤ r := by
    rw [← Real.norm_eq_abs]
    exact le_trans (norm_snd_le q.2) (le_trans (norm_snd_le q) hn)
  exact ⟨le_trans h1 (le_max_left _ _), le_trans h2 (le_max_left _ _)⟩

/-- Entrywise bound for the physical source with a bound `B` on the first and third chart
coordinates and `G` on the chart tensor. -/
lemma oldPhys_entry_bound {R c : ℝ} {g : Chart → Ten3} (B G : ℝ) (hB0 : 0 ≤ B) (hG0 : 0 ≤ G)
    (hG : ∀ x, ‖g x‖ ≤ G) (hB : ∀ q ∈ tsupport g, |q.1| ≤ B) (τ : ℝ) (z : Space) (i j : Fin 3) :
    |oldPhys R c g τ z i j| ≤ 9 * (B * G) := by
  have hA : ∀ k l, |((NearInst.chartOf R c z τ).1 • NearInst.nsSym (g (NearInst.chartOf R c z τ))) k l|
      ≤ B * G := by
    intro k l
    by_cases hq : NearInst.chartOf R c z τ ∈ tsupport g
    · rw [Matrix.smul_apply, smul_eq_mul, abs_mul]
      exact mul_le_mul (hB _ hq) (le_trans (nsSym_abs_le _ _ _) (hG _)) (abs_nonneg _) hB0
    · have h0 : g (NearInst.chartOf R c z τ) = 0 := image_eq_zero_of_notMem_tsupport hq
      rw [Matrix.smul_apply, smul_eq_mul, h0, nsSym_zero]
      simp [mul_nonneg hB0 hG0]
  have hQ : ∀ i k, |NearInst.cylFrame z i k| ≤ 1 := cylFrame_abs_le z
  simp only [oldPhys, NearInst.cartLift]
  exact triple_entry_bound _ _ (B * G) (mul_nonneg hB0 hG0) hQ hA i j


/-- Off the old disk, `ϱ ≤ ρ` for the source to be nonzero, and the `z₃` coordinate is controlled
by the compact chart support. -/
lemma oldPhys_ne_zero_bound {R c ν : ℝ} {g : Chart → Ten3} (hR : 0 < R) (hν : 0 < ν)
    (hg : IsSmoothOld c ν g) (B : ℝ) (hB0 : 0 ≤ B)
    (hB : ∀ q ∈ tsupport g, |q.1| ≤ B ∧ |q.2.2| ≤ B) (τ : ℝ) (z : Space)
    (hne : oldPhys R c g τ z ≠ 0) :
    ‖z‖ ≤ R * Real.sqrt (5 * ν / 6) + B * (R * Real.sqrt (5 * ν / 6)) / R := by
  have hρ0 : 0 ≤ R * Real.sqrt (5 * ν / 6) := by positivity
  have hq : NearInst.chartOf R c z τ ∈ tsupport g := by
    by_contra hq
    apply hne
    have h0 : g (NearInst.chartOf R c z τ) = 0 := image_eq_zero_of_notMem_tsupport hq
    simp [oldPhys, NearInst.cartLift, h0, nsSym_zero]
  have hs : 0 < (NearInst.chartOf R c z τ).1 := (hg.chart.inChart hq).1
  have hh : 0 < NearInst.hRad z := by
    by_contra hcon
    have h0 : NearInst.hRad z = 0 := le_antisymm (not_lt.mp hcon) (Real.sqrt_nonneg _)
    simp [NearInst.chartOf, h0] at hs
  have hρle : NearInst.hRad z ≤ R * Real.sqrt (5 * ν / 6) := by
    by_contra hcon
    push_neg at hcon
    exact hne (oldPhys_eq_zero_of_far hR hν hg τ z hcon)
  have hz2 : |z 2| ≤ B * (R * Real.sqrt (5 * ν / 6)) / R := by
    have e : |R * z 2 / NearInst.hRad z| ≤ B := by
      simpa [NearInst.chartOf] using (hB _ hq).2
    rw [abs_div, abs_mul, abs_of_pos hR, abs_of_pos hh, div_le_iff₀ hh] at e
    rw [le_div_iff₀ hR]
    have := mul_le_mul_of_nonneg_left hρle hB0
    nlinarith [this, e]
  have hnorm : ‖z‖ ^ 2 = z 0 ^ 2 + z 1 ^ 2 + z 2 ^ 2 := by
    rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]
    simp [Fin.sum_univ_three, Real.norm_eq_abs, sq_abs]
  have hh2 : NearInst.hRad z ^ 2 = z 0 ^ 2 + z 1 ^ 2 := by
    unfold NearInst.hRad; rw [Real.sq_sqrt (by positivity)]
  have hA : NearInst.hRad z ^ 2 ≤ (R * Real.sqrt (5 * ν / 6)) ^ 2 :=
    pow_le_pow_left₀ (Real.sqrt_nonneg _ |>.trans' (by positivity)) hρle 2
  have hb0 : 0 ≤ B * (R * Real.sqrt (5 * ν / 6)) / R := by positivity
  have hB2 : z 2 ^ 2 ≤ (B * (R * Real.sqrt (5 * ν / 6)) / R) ^ 2 := by
    have := pow_le_pow_left₀ (abs_nonneg (z 2)) hz2 2
    rwa [sq_abs] at this
  have hsq : ‖z‖ ^ 2 ≤ (R * Real.sqrt (5 * ν / 6) + B * (R * Real.sqrt (5 * ν / 6)) / R) ^ 2 := by
    rw [hnorm]
    nlinarith [mul_nonneg hρ0 hb0]
  exact abs_le_of_sq_le_sq' hsq (by positivity) |>.2

/-- The chart map is measurable in the (phase, point) variables. -/
lemma chartOf_measurable (R c : ℝ) :
    Measurable fun p : ℝ × Space => NearInst.chartOf R c p.2 p.1 := by
  have hcont : Continuous (fun z : Space => NearInst.hRad z) := by
    unfold NearInst.hRad; fun_prop
  have hh : Measurable fun p : ℝ × Space => NearInst.hRad p.2 :=
    hcont.measurable.comp measurable_snd
  have hz2 : Measurable fun p : ℝ × Space => p.2 2 := by
    fun_prop
  have hA : Measurable fun p : ℝ × Space =>
      R * Real.log (NearInst.hRad p.2 / R) + R * p.1 / 2 :=
    ((measurable_const.mul (Real.measurable_log.comp (hh.div_const R))).add
      ((measurable_const.mul measurable_fst).div_const 2))
  have hF : Measurable fun p : ℝ × Space =>
      ((⌊(R * Real.log (NearInst.hRad p.2 / R) + R * p.1 / 2) / c + 1 / 2⌋ : ℤ) : ℝ) :=
    (Measurable.of_discrete (f := fun n : ℤ => (n : ℝ))).comp
      (Int.measurable_floor.comp ((hA.div_const c).add_const (1 / 2)))
  unfold NearInst.chartOf
  refine Measurable.prodMk ?_ (Measurable.prodMk ?_ ?_)
  · exact measurable_const.div (hh.pow_const 2)
  · exact hA.sub (measurable_const.mul hF)
  · exact (measurable_const.mul hz2).div hh

/-- Entries of the chart tensor composed with the chart map are measurable. -/
lemma chartTensor_entry_measurable {R c : ℝ} {g : Chart → Ten3} (hgc : Continuous g) (a b : Fin 3) :
    Measurable fun p : ℝ × Space => g (NearInst.chartOf R c p.2 p.1) (a, b) := by
  have hX : Measurable fun p : ℝ × Space => g (NearInst.chartOf R c p.2 p.1) :=
    hgc.measurable.comp (chartOf_measurable R c)
  have hco : Measurable fun X : Ten3 => X (a, b) := by
    fun_prop
  exact hco.comp hX

lemma oldPhys_entry_measurable {R c : ℝ} {g : Chart → Ten3} (hgc : Continuous g) (i j : Fin 3) :
    Measurable fun p : ℝ × Space => oldPhys R c g p.1 p.2 i j := by
  have hs : Measurable fun p : ℝ × Space => (NearInst.chartOf R c p.2 p.1).1 :=
    measurable_fst.comp (chartOf_measurable R c)
  have hcyl : ∀ i k, Measurable fun p : ℝ × Space => NearInst.cylFrame p.2 i k := by
    intro i k
    fin_cases i <;> fin_cases k <;> simp [NearInst.cylFrame, NearInst.hRad] <;> fun_prop
  have hn : ∀ a b, Measurable fun p : ℝ × Space =>
      NearInst.nsSym (g (NearInst.chartOf R c p.2 p.1)) a b := by
    intro a b
    fin_cases a <;> fin_cases b <;> simp [NearInst.nsSym, NearInst.symRZ]
    all_goals first
      | exact measurable_const
      | exact chartTensor_entry_measurable hgc _ _
      | exact (((chartTensor_entry_measurable hgc _ _).add
          (chartTensor_entry_measurable hgc _ _)).div_const 2)
  unfold oldPhys NearInst.cartLift
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.smul_apply, smul_eq_mul]
  exact Finset.measurable_sum _ fun k _ => Measurable.mul
    (Finset.measurable_sum _ fun l _ => (hcyl i l).mul (hs.mul (hn l k))) (hcyl j k)

/-- The `Y₂` moment of the physical source of smooth old data is finite. -/
lemma sepMoment_oldPhys {R c ν : ℝ} {g : Chart → Ten3} (hR : 0 < R) (hν : 0 < ν) (hc : 0 < c)
    (hg : IsSmoothOld c ν g) : SepMoment (2 * c / R) (oldPhys R c g) := by
  obtain ⟨B, hB0, hB⟩ := chart_support_bound hg.chart
  obtain ⟨G0, hG0⟩ := hg.chart.smooth.continuous.bounded_above_of_compact_support hg.chart.compact
  have hG : ∀ x, ‖g x‖ ≤ max G0 0 := fun x => le_trans (hG0 x) (le_max_left _ _)
  have hG0' : 0 ≤ max G0 0 := le_max_right _ _
  have he0 : 0 ≤ 9 * (B * max G0 0) := mul_nonneg (by norm_num) (mul_nonneg hB0 hG0')
  have hball : ∀ τ z, IIIa.srcNorm (oldPhys R c g) τ z ^ (2 : ℝ) ≤
      Set.indicator (Metric.closedBall (0 : Space)
        (R * Real.sqrt (5 * ν / 6) + B * (R * Real.sqrt (5 * ν / 6)) / R))
        (fun _ => ENNReal.ofReal ((3 * (9 * (B * max G0 0))) ^ 2)) z := by
    intro τ z
    by_cases hz : z ∈ Metric.closedBall (0 : Space)
        (R * Real.sqrt (5 * ν / 6) + B * (R * Real.sqrt (5 * ν / 6)) / R)
    · rw [Set.indicator_of_mem hz]
      have hT := tensorNorm_le_of_entries (oldPhys R c g τ z) (9 * (B * max G0 0)) he0
        (fun i j => oldPhys_entry_bound B (max G0 0) hB0 hG0' hG (fun q hq => (hB q hq).1) τ z i j)
      have ht0 : 0 ≤ IIIa.tensorNorm (oldPhys R c g τ z) := by
        unfold IIIa.tensorNorm; exact Real.sqrt_nonneg _
      unfold IIIa.srcNorm
      rw [ENNReal.ofReal_rpow_of_nonneg ht0 (by norm_num), Real.rpow_two]
      exact ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ ht0 hT 2)
    · rw [Set.indicator_of_notMem hz]
      have h0 : oldPhys R c g τ z = 0 := by
        by_contra hne
        exact hz (mem_closedBall_zero_iff.2 (oldPhys_ne_zero_bound hR hν hg B hB0
          (fun q hq => hB q hq) τ z hne))
      unfold IIIa.srcNorm
      rw [h0, tensorNorm_zero]
      simp
  have hinner : ∀ τ, (∫⁻ z, IIIa.srcNorm (oldPhys R c g) τ z ^ (2 : ℝ)) ≤
      ENNReal.ofReal ((3 * (9 * (B * max G0 0))) ^ 2) *
        volume (Metric.closedBall (0 : Space)
          (R * Real.sqrt (5 * ν / 6) + B * (R * Real.sqrt (5 * ν / 6)) / R)) := by
    intro τ
    calc (∫⁻ z, IIIa.srcNorm (oldPhys R c g) τ z ^ (2 : ℝ))
        ≤ ∫⁻ z, Set.indicator (Metric.closedBall (0 : Space)
            (R * Real.sqrt (5 * ν / 6) + B * (R * Real.sqrt (5 * ν / 6)) / R))
            (fun _ => ENNReal.ofReal ((3 * (9 * (B * max G0 0))) ^ 2)) z := lintegral_mono (hball τ)
      _ = _ := lintegral_indicator_const measurableSet_closedBall _
  have hK : ENNReal.ofReal ((3 * (9 * (B * max G0 0))) ^ 2) *
      volume (Metric.closedBall (0 : Space)
        (R * Real.sqrt (5 * ν / 6) + B * (R * Real.sqrt (5 * ν / 6)) / R)) < ⊤ :=
    ENNReal.mul_lt_top ENNReal.ofReal_lt_top measure_closedBall_lt_top
  have hP : 0 < 2 * c / R := by positivity
  unfold SepMoment IIIa.ltauLq
  have hτ : ∫⁻ τ in Set.Ioc 0 (2 * c / R),
      (∫⁻ z, IIIa.srcNorm (oldPhys R c g) τ z ^ (2 : ℝ)) ^ ((2 : ℝ) / 2) ≤
      ∫⁻ _τ in Set.Ioc 0 (2 * c / R), ENNReal.ofReal ((3 * (9 * (B * max G0 0))) ^ 2) *
        volume (Metric.closedBall (0 : Space)
          (R * Real.sqrt (5 * ν / 6) + B * (R * Real.sqrt (5 * ν / 6)) / R)) :=
    lintegral_mono (fun τ => by
      rw [show (2 : ℝ) / 2 = 1 by norm_num, ENNReal.rpow_one]
      exact hinner τ)
  have hI : ∫⁻ _τ in Set.Ioc 0 (2 * c / R), ENNReal.ofReal ((3 * (9 * (B * max G0 0))) ^ 2) *
        volume (Metric.closedBall (0 : Space)
          (R * Real.sqrt (5 * ν / 6) + B * (R * Real.sqrt (5 * ν / 6)) / R)) < ⊤ := by
    rw [setLIntegral_const, Real.volume_Ioc]
    exact ENNReal.mul_lt_top hK ENNReal.ofReal_lt_top
  have hJ : (ENNReal.ofReal (2 * c / R))⁻¹ * ∫⁻ τ in Set.Ioc 0 (2 * c / R),
      (∫⁻ z, IIIa.srcNorm (oldPhys R c g) τ z ^ (2 : ℝ)) ^ ((2 : ℝ) / 2) < ⊤ :=
    ENNReal.mul_lt_top (ENNReal.inv_lt_top.2 (ENNReal.ofReal_pos.2 hP))
      (lt_of_le_of_lt hτ hI)
  exact ENNReal.rpow_lt_top_of_nonneg (by norm_num) hJ.ne

/-- The physical source of smooth old data is a separated source (`IsSepSource`). -/
lemma isSepSource_oldPhys {R c ν : ℝ} {g : Chart → Ten3} (hR : 0 < R) (hν : 0 < ν)
    (hg : IsSmoothOld c ν g) :
    IIIa.IsSepSource (2 * c / R) (R * Real.sqrt (5 * ν / 6)) (oldPhys R c g) :=
  { measurable := fun i j => oldPhys_entry_measurable hg.chart.smooth.continuous i j
    periodic := fun τ z => oldPhysPeriodic R c g τ z
    support := fun τ z hz => oldPhys_eq_zero_of_far hR hν hg τ z hz }

/-- **`smoothOldSource_proved`** (source 4155-4166). -/
theorem smoothOldSource_proved : SmoothOldSource := by
  intro ν R c g hν hR hc hg
  exact ⟨isSepSource_oldPhys hR hν hg, sepMoment_oldPhys hR hν hc hg⟩

end UnforcedLeray.Short.PartIIIb.Concrete
