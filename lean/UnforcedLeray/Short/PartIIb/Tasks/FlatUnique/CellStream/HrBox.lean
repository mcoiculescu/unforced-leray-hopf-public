import UnforcedLeray.Short.PartIIb.Sub.T11_1
import UnforcedLeray.Short.PartIIb.Org.QPeriodicHalfSpace.Basic

/-!
# Part II-b, leaf `PartII-b:T11/1/4` (`HrBoxIntegrable`): box integrability of `H_r` profiles

Source of record: `the November 2 reference manuscript`, SP 1900-1903 (the space
`H_r` with measure `s^{r/2-5/2} ds dq/c dη`; `Defs.lean`: `hMeas`, `hNorm`, `InHr`, `qShift`).
Statement: `HrBoxIntegrable` of `Sub/T11_1.lean`.

Proof, self-contained (it does not use `PeriodicRepresentative` of `Sub/T07.lean`):
1. `b' := (InHr.meas).mk b` is strongly measurable and `b = b'` `hMeas`-a.e.
2. Lebesgue measure on `(0,∞) × cell` is absolutely continuous with respect to `ageμ` (`hrBox_ac`),
   so `b = b'` Lebesgue-a.e. on `(0,∞) × cell`. With `c`-periodicity for all integer shifts this
   gives `b x = b' (hrBoxRed c x)` for a.e. `x` with `s > 0`, where `hrBoxRed` is the measurable
   `q`-reduction of `x` into the cell.
3. On the box `B`, `‖b' ∘ hrBoxRed‖ₑ^r` is bounded by a finite sum of translates of
   `1_{[σ,H] × cell} ‖b'‖ₑ^r`, whose Lebesgue integral is finite by the density lower bound
   `s^{r/2-5/2} ≥ m > 0` on `[σ, H]` (`hrBox_lintegral_G_bound`).
4. `L^r(B) ⊆ L^1(B)` on the finite measure set `B`, and `|b_i| ≤ ‖b‖`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal

namespace UnforcedLeray.Short.IIb

/-! ## Translations in the `q` variable -/

theorem hrBox_qShift_qShift (a b : ℝ) (x : Coord) :
    qShift a (qShift b x) = qShift (a + b) x := by
  show (x.1, ((x.2.1 + b) + a, x.2.2)) = (x.1, (x.2.1 + (a + b), x.2.2))
  rw [show x.2.1 + b + a = x.2.1 + (a + b) by ring]

theorem hrBox_qShift_mp (a : ℝ) : MeasurePreserving (qShift a) volume volume := by
  have h1 : MeasurePreserving (fun t : ℝ => t + a) volume volume :=
    measurePreserving_add_right volume a
  exact (MeasurePreserving.id (volume : Measure ℝ)).prod
    (h1.prod (MeasurePreserving.id (volume : Measure ℝ)))

/-! ## Periodicity for all integer shifts -/

/-- `b` is invariant under the integer `q`-shift `m c`, almost everywhere on `s > 0`. -/
def hrBoxShiftPer (c : ℝ) (b : CProf) (m : ℤ) : Prop :=
  ∀ᵐ x : Coord, 0 < x.1 → b (qShift ((m : ℝ) * c) x) = b x

theorem hrBox_shiftPer_zero (c : ℝ) (b : CProf) : hrBoxShiftPer c b 0 := by
  unfold hrBoxShiftPer
  exact ae_of_all _ (fun x _ => by simp [qShift])

theorem hrBox_shiftPer_succ {c : ℝ} {b : CProf} (hper : QPeriodic c b) (m : ℤ)
    (h : hrBoxShiftPer c b m) : hrBoxShiftPer c b (m + 1) := by
  have hper' : ∀ᵐ x : Coord, 0 < x.1 → b (qShift c x) = b x := QPerHalf.ae_imp hper
  have h2 : ∀ᵐ x : Coord, 0 < (qShift ((m : ℝ) * c) x).1 →
      b (qShift c (qShift ((m : ℝ) * c) x)) = b (qShift ((m : ℝ) * c) x) :=
    ((hrBox_qShift_mp ((m : ℝ) * c)).quasiMeasurePreserving).ae hper'
  unfold hrBoxShiftPer at h ⊢
  filter_upwards [h2, h] with x hx1 hx2 hx0
  have e : qShift (((m + 1 : ℤ) : ℝ) * c) x = qShift c (qShift ((m : ℝ) * c) x) := by
    rw [hrBox_qShift_qShift]
    congr 1
    push_cast
    ring
  rw [e, hx1 hx0, hx2 hx0]

theorem hrBox_shiftPer_pred {c : ℝ} {b : CProf} (hper : QPeriodic c b) (m : ℤ)
    (h : hrBoxShiftPer c b (m + 1)) : hrBoxShiftPer c b m := by
  have hper' : ∀ᵐ x : Coord, 0 < x.1 → b (qShift c x) = b x := QPerHalf.ae_imp hper
  have h2 : ∀ᵐ x : Coord, 0 < (qShift ((m : ℝ) * c) x).1 →
      b (qShift c (qShift ((m : ℝ) * c) x)) = b (qShift ((m : ℝ) * c) x) :=
    ((hrBox_qShift_mp ((m : ℝ) * c)).quasiMeasurePreserving).ae hper'
  unfold hrBoxShiftPer at h ⊢
  filter_upwards [h2, h] with x hx1 hx2 hx0
  have e : qShift (((m + 1 : ℤ) : ℝ) * c) x = qShift c (qShift ((m : ℝ) * c) x) := by
    rw [hrBox_qShift_qShift]
    congr 1
    push_cast
    ring
  rw [e] at hx2
  exact (hx1 hx0).symm.trans (hx2 hx0)

theorem hrBox_shiftPer_all {c : ℝ} {b : CProf} (hper : QPeriodic c b) (m : ℤ) :
    hrBoxShiftPer c b m := by
  induction m using Int.induction_on with
  | zero => exact hrBox_shiftPer_zero c b
  | succ k ih => exact hrBox_shiftPer_succ hper (k : ℤ) ih
  | pred k ih =>
    exact hrBox_shiftPer_pred hper (-(k : ℤ) - 1) (by rw [sub_add_cancel]; exact ih)

/-! ## Absolute continuity of Lebesgue measure on `(0,∞) × cell` with respect to `ageμ` -/

theorem hrBox_ac {c : ℝ} (hc : 0 < c) (a : ℝ) :
    volume.restrict (Ioi (0 : ℝ) ×ˢ Cyl.cell c) ≪ Axi.ageμ c a := by
  intro t ht
  have hmt : MeasurableSet (toMeasurable (Axi.ageμ c a) t) := measurableSet_toMeasurable _ _
  have h0 : Axi.ageμ c a (toMeasurable (Axi.ageμ c a) t) = 0 := by
    rw [measure_toMeasurable]
    exact ht
  refine measure_mono_null (subset_toMeasurable (Axi.ageμ c a) t) ?_
  have h := Axi.lintegral_ageμ hc a (f := (toMeasurable (Axi.ageμ c a) t).indicator 1)
    (measurable_one.indicator hmt)
  rw [lintegral_indicator_one hmt, h0, Axi.qCell_eq_cell] at h
  have hmeas : Measurable (fun p : Coord => ENNReal.ofReal (c⁻¹ * p.1 ^ a) *
      (toMeasurable (Axi.ageμ c a) t).indicator 1 p) :=
    (ENNReal.measurable_ofReal.comp (measurable_const.mul (measurable_fst.pow_const a))).mul
      (measurable_one.indicator hmt)
  have h' := (lintegral_eq_zero_iff' hmeas.aemeasurable).1 h.symm
  have hnot : ∀ᵐ p ∂(volume.restrict (Ioi (0 : ℝ) ×ˢ Cyl.cell c)),
      p ∉ toMeasurable (Axi.ageμ c a) t := by
    filter_upwards [h', ae_restrict_mem (measurableSet_Ioi.prod
      (measurableSet_Ico.prod MeasurableSet.univ))] with p hp hpS hpT
    have hp' : ENNReal.ofReal (c⁻¹ * p.1 ^ a) *
        (toMeasurable (Axi.ageμ c a) t).indicator 1 p = 0 := hp
    rw [Set.indicator_of_mem hpT, Pi.one_apply, mul_one] at hp'
    have hpos : 0 < c⁻¹ * p.1 ^ a :=
      mul_pos (inv_pos.2 hc) (Real.rpow_pos_of_pos (Set.mem_prod.1 hpS).1 a)
    exact (ENNReal.ofReal_pos.2 hpos).ne' hp'
  exact measure_eq_zero_iff_ae_notMem.2 hnot

/-! ## Density lower bound on `[σ, H]` -/

theorem hrBox_density_lower {σ H a : ℝ} (hσ : 0 < σ) :
    ∃ m : ℝ, 0 < m ∧ ∀ s ∈ Icc σ H, m ≤ s ^ a := by
  refine ⟨min (σ ^ a) ((max H σ) ^ a), lt_min (Real.rpow_pos_of_pos hσ a)
    (Real.rpow_pos_of_pos (lt_of_lt_of_le hσ (le_max_right _ _)) a), fun s hs => ?_⟩
  obtain ⟨h1, h2⟩ := hs
  have hs0 : 0 < s := lt_of_lt_of_le hσ h1
  have hM : s ≤ max H σ := le_trans h2 (le_max_left _ _)
  rcases le_total 0 a with ha | ha
  · exact le_trans (min_le_left _ _) (Real.rpow_le_rpow hσ.le h1 ha)
  · exact le_trans (min_le_right _ _) (Real.rpow_le_rpow_of_nonpos hs0 hM ha)

/-! ## The `q`-reduction into the cell -/

/-- The integer `k(x) = ⌊(q + c/2)/c⌋` with `q = x.2.1`. -/
def hrBoxK (c : ℝ) (x : Coord) : ℤ := ⌊(x.2.1 + c / 2) / c⌋

/-- The `q`-reduction `x ↦ (s, q - k(x) c, η)`, a shift by the integer multiple `-k(x) c`. -/
def hrBoxRed (c : ℝ) (x : Coord) : Coord :=
  qShift (((-(hrBoxK c x) : ℤ) : ℝ) * c) x

theorem hrBox_floor_bounds {c : ℝ} (hc : 0 < c) (x : Coord) :
    (hrBoxK c x : ℝ) * c ≤ x.2.1 + c / 2 ∧ x.2.1 + c / 2 < (hrBoxK c x : ℝ) * c + c := by
  have h1 : (hrBoxK c x : ℝ) ≤ (x.2.1 + c / 2) / c := Int.floor_le _
  have h2 : (x.2.1 + c / 2) / c < (hrBoxK c x : ℝ) + 1 := Int.lt_floor_add_one _
  constructor
  · exact (le_div_iff₀ hc).1 h1
  · have h3 := (div_lt_iff₀ hc).1 h2
    have e : ((hrBoxK c x : ℝ) + 1) * c = (hrBoxK c x : ℝ) * c + c := by ring
    linarith

theorem hrBox_red_q (c : ℝ) (x : Coord) :
    (hrBoxRed c x).2.1 = x.2.1 - (hrBoxK c x : ℝ) * c := by
  simp only [hrBoxRed, qShift, Int.cast_neg]
  ring

theorem hrBox_red_mem {c : ℝ} (hc : 0 < c) (T : Set ℝ) (x : Coord) (hx : x.1 ∈ T) :
    hrBoxRed c x ∈ T ×ˢ Cyl.cell c := by
  obtain ⟨k1, k2⟩ := hrBox_floor_bounds hc x
  refine Set.mem_prod.2 ⟨hx, Set.mem_prod.2 ⟨?_, Set.mem_univ _⟩⟩
  rw [Set.mem_Ico, hrBox_red_q]
  constructor <;> linarith

theorem hrBox_red_measurable (c : ℝ) : Measurable (hrBoxRed c) := by
  have hq : Measurable (fun x : Coord => x.2.1) := measurable_fst.comp measurable_snd
  have hk : Measurable (fun x : Coord => hrBoxK c x) :=
    Int.measurable_floor.comp ((hq.add_const (c / 2)).div_const c)
  have hf : Measurable (fun x : Coord => ((-(hrBoxK c x) : ℤ) : ℝ) * c) :=
    (Measurable.of_discrete (f := fun n : ℤ => ((-n : ℤ) : ℝ) * c)).comp hk
  unfold hrBoxRed qShift
  exact measurable_fst.prodMk ((hq.add hf).prodMk (measurable_snd.comp measurable_snd))

theorem hrBox_cell_measurable (c : ℝ) : MeasurableSet (Cyl.cell c) :=
  measurableSet_Ico.prod MeasurableSet.univ

/-! ## The truncated `H_r` mass -/

/-- `1_{[σ,H] × cell} ‖b'‖ₑ^r`. -/
def hrBoxG (c r σ H : ℝ) (b' : CProf) : Coord → ℝ≥0∞ :=
  (Icc σ H ×ˢ Cyl.cell c).indicator (fun y => ‖b' y‖ₑ ^ r)

theorem hrBoxG_measurable {c r σ H : ℝ} {b' : CProf} (hb' : Measurable b') :
    Measurable (hrBoxG c r σ H b') := by
  unfold hrBoxG
  exact ((hb'.enorm).pow_const r).indicator
    (MeasurableSet.prod measurableSet_Icc (hrBox_cell_measurable c))

/-- The Lebesgue integral of `1_{[σ,H] × cell} ‖b'‖ₑ^r` is finite when the `H_r` integral is. -/
theorem hrBox_lintegral_G_bound {c r σ H : ℝ} {b b' : CProf} (hc : 0 < c) (hσ : 0 < σ)
    (hb'm : Measurable b') (hbb' : ∀ᵐ y ∂(hMeas c r), b y = b' y)
    (hfin : ∫⁻ y, ‖b y‖ₑ ^ r ∂(hMeas c r) < ⊤) :
    ∫⁻ y, hrBoxG c r σ H b' y ∂volume < ⊤ := by
  unfold hMeas at hbb' hfin
  obtain ⟨m, hm, hmle⟩ := hrBox_density_lower (H := H) (a := r / 2 - 5 / 2) hσ
  have hGm : Measurable (hrBoxG c r σ H b') := hrBoxG_measurable hb'm
  have hK0 : ENNReal.ofReal (c⁻¹ * m) ≠ 0 :=
    (ENNReal.ofReal_pos.2 (mul_pos (inv_pos.2 hc) hm)).ne'
  have hKt : ENNReal.ofReal (c⁻¹ * m) ≠ ⊤ := ENNReal.ofReal_ne_top
  have hpt : ∀ y : Coord, ENNReal.ofReal (c⁻¹ * m) * hrBoxG c r σ H b' y ≤
      ENNReal.ofReal (c⁻¹ * y.1 ^ (r / 2 - 5 / 2)) * hrBoxG c r σ H b' y := by
    intro y
    by_cases hy : y ∈ Icc σ H ×ˢ Cyl.cell c
    · have hyI : y.1 ∈ Icc σ H := (Set.mem_prod.1 hy).1
      have hle : c⁻¹ * m ≤ c⁻¹ * y.1 ^ (r / 2 - 5 / 2) :=
        mul_le_mul_of_nonneg_left (hmle y.1 hyI) (inv_nonneg.2 hc.le)
      exact mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal hle) zero_le
    · have h0 : hrBoxG c r σ H b' y = 0 := by
        unfold hrBoxG
        exact Set.indicator_of_notMem hy _
      rw [h0, mul_zero, mul_zero]
  have hsupp : Function.support
      (fun y => ENNReal.ofReal (c⁻¹ * m) * hrBoxG c r σ H b' y) ⊆
      Ioi (0 : ℝ) ×ˢ Cyl.cell c := by
    intro y hy
    have hy' : ENNReal.ofReal (c⁻¹ * m) * hrBoxG c r σ H b' y ≠ 0 := hy
    have hyS : y ∈ Icc σ H ×ˢ Cyl.cell c := by
      by_contra hn
      apply hy'
      have h0 : hrBoxG c r σ H b' y = 0 := by
        unfold hrBoxG
        exact Set.indicator_of_notMem hn _
      rw [h0, mul_zero]
    exact Set.mem_prod.2 ⟨lt_of_lt_of_le hσ (Set.mem_prod.1 hyS).1.1, (Set.mem_prod.1 hyS).2⟩
  have hlow : ENNReal.ofReal (c⁻¹ * m) * ∫⁻ y, hrBoxG c r σ H b' y ∂volume ≤
      ∫⁻ y, hrBoxG c r σ H b' y ∂(Axi.ageμ c (r / 2 - 5 / 2)) := by
    calc ENNReal.ofReal (c⁻¹ * m) * ∫⁻ y, hrBoxG c r σ H b' y ∂volume
        = ∫⁻ y, ENNReal.ofReal (c⁻¹ * m) * hrBoxG c r σ H b' y ∂volume :=
          (lintegral_const_mul' _ _ hKt).symm
      _ = ∫⁻ y in Ioi (0 : ℝ) ×ˢ Cyl.cell c,
            ENNReal.ofReal (c⁻¹ * m) * hrBoxG c r σ H b' y ∂volume :=
          (setLIntegral_eq_of_support_subset hsupp).symm
      _ ≤ ∫⁻ y in Ioi (0 : ℝ) ×ˢ Cyl.cell c,
            ENNReal.ofReal (c⁻¹ * y.1 ^ (r / 2 - 5 / 2)) * hrBoxG c r σ H b' y ∂volume :=
          lintegral_mono (fun y => hpt y)
      _ = ∫⁻ y, hrBoxG c r σ H b' y ∂(Axi.ageμ c (r / 2 - 5 / 2)) := by
          rw [Axi.lintegral_ageμ hc (r / 2 - 5 / 2) hGm, Axi.qCell_eq_cell]
  have hG_le : ∫⁻ y, hrBoxG c r σ H b' y ∂(Axi.ageμ c (r / 2 - 5 / 2)) ≤
      ∫⁻ y, ‖b y‖ₑ ^ r ∂(Axi.ageμ c (r / 2 - 5 / 2)) := by
    apply lintegral_mono_ae
    filter_upwards [hbb'] with y hy
    by_cases hyS : y ∈ Icc σ H ×ˢ Cyl.cell c
    · have h1 : hrBoxG c r σ H b' y = ‖b' y‖ₑ ^ r := by
        unfold hrBoxG
        exact Set.indicator_of_mem hyS _
      rw [h1, hy]
    · have h1 : hrBoxG c r σ H b' y = 0 := by
        unfold hrBoxG
        exact Set.indicator_of_notMem hyS _
      rw [h1]
      exact zero_le
  have hY : ENNReal.ofReal (c⁻¹ * m) * ∫⁻ y, hrBoxG c r σ H b' y ∂volume < ⊤ :=
    lt_of_le_of_lt hlow (lt_of_le_of_lt hG_le hfin)
  rcases ENNReal.mul_lt_top_iff.1 hY with ⟨_, h2⟩ | h1 | h2
  · exact h2
  · exact absurd h1 hK0
  · rw [h2]
    exact ENNReal.zero_lt_top

/-! ## The leaf `PartII-b:T11/1/4` -/

/-- **Leaf `PartII-b:T11/1/4`** (`H_r` box integrability), proved from scratch. -/
theorem hrBoxIntegrable : HrBoxIntegrable := by
  intro c r b hc hr hb σ H R L hσ i
  have hr0 : 0 < r := by linarith
  obtain ⟨b', hb'sm, hbb'⟩ : ∃ b' : CProf, StronglyMeasurable b' ∧
      ∀ᵐ y ∂(hMeas c r), b y = b' y :=
    ⟨hb.meas.mk b, hb.meas.stronglyMeasurable_mk, hb.meas.ae_eq_mk⟩
  have hb'm : Measurable b' := hb'sm.measurable
  have hfin : ∫⁻ y, ‖b y‖ₑ ^ r ∂(hMeas c r) < ⊤ := by
    have h0 : eLpNorm b (ENNReal.ofReal r) (hMeas c r) < ⊤ := hb.finite
    have h1 := (eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top
      (ENNReal.ofReal_pos.2 hr0).ne' ENNReal.ofReal_ne_top).1 h0
    rwa [ENNReal.toReal_ofReal hr0.le] at h1
  have hX : ∫⁻ y, hrBoxG c r σ H b' y ∂volume < ⊤ :=
    hrBox_lintegral_G_bound (H := H) hc hσ hb'm hbb' hfin
  -- periodicity for all integer shifts, and the Lebesgue a.e. identity on the cell
  have hper : QPeriodic c b := hb.periodic
  have hper' : ∀ n : ℤ, ∀ᵐ x : Coord, 0 < x.1 → b (qShift ((n : ℝ) * c) x) = b x :=
    fun n => hrBox_shiftPer_all hper n
  have hAll : ∀ᵐ x : Coord, ∀ n : ℤ, 0 < x.1 → b (qShift ((n : ℝ) * c) x) = b x :=
    ae_all_iff.2 hper'
  have hS0ae : ∀ᵐ y ∂(volume.restrict (Ioi (0 : ℝ) ×ˢ Cyl.cell c)), b y = b' y :=
    (hrBox_ac hc (r / 2 - 5 / 2)).ae_le hbb'
  have hS0 : ∀ᵐ y : Coord, y ∈ Ioi (0 : ℝ) ×ˢ Cyl.cell c → b y = b' y :=
    (ae_restrict_iff' (MeasurableSet.prod measurableSet_Ioi (hrBox_cell_measurable c))).1 hS0ae
  have hE : ∀ n : ℤ, ∀ᵐ x : Coord, qShift ((n : ℝ) * c) x ∈ Ioi (0 : ℝ) ×ˢ Cyl.cell c →
      b (qShift ((n : ℝ) * c) x) = b' (qShift ((n : ℝ) * c) x) :=
    fun n => ((hrBox_qShift_mp ((n : ℝ) * c)).quasiMeasurePreserving).ae hS0
  have hEall : ∀ᵐ x : Coord, ∀ n : ℤ, qShift ((n : ℝ) * c) x ∈ Ioi (0 : ℝ) ×ˢ Cyl.cell c →
      b (qShift ((n : ℝ) * c) x) = b' (qShift ((n : ℝ) * c) x) :=
    ae_all_iff.2 hE
  -- the pointwise identity `b x = b' (hrBoxRed c x)` for a.e. `x` with `s > 0`
  have hpt : ∀ᵐ x : Coord, 0 < x.1 → b x = b' (hrBoxRed c x) := by
    filter_upwards [hAll, hEall] with x hA hE' hx
    have hmem : qShift (((-(hrBoxK c x) : ℤ) : ℝ) * c) x ∈ Ioi (0 : ℝ) ×ˢ Cyl.cell c :=
      hrBox_red_mem hc (Ioi 0) x hx
    exact (hA (-(hrBoxK c x)) hx).symm.trans (hE' (-(hrBoxK c x)) hmem)
  have hgm : Measurable (fun x : Coord => b' (hrBoxRed c x)) :=
    hb'm.comp (hrBox_red_measurable c)
  -- the finite index set of translates
  obtain ⟨N, hN⟩ : ∃ N : ℤ, |R| + c ≤ (N : ℝ) * c :=
    ⟨⌈(|R| + c) / c⌉, (div_le_iff₀ hc).1 (Int.le_ceil _)⟩
  have hkF : ∀ x ∈ Icc σ H ×ˢ (Icc (-R) R ×ˢ Icc (-L) L), -(hrBoxK c x) ∈ Finset.Icc (-N) N := by
    intro x hx
    have hq : x.2.1 ∈ Icc (-R) R := (Set.mem_prod.1 (Set.mem_prod.1 hx).2).1
    have hq1 : -|R| ≤ x.2.1 := le_trans (neg_le_neg (le_abs_self R)) hq.1
    have hq2 : x.2.1 ≤ |R| := le_trans hq.2 (le_abs_self R)
    obtain ⟨k1, k2⟩ := hrBox_floor_bounds hc x
    have hkN : (hrBoxK c x : ℝ) < N := by
      have h : (hrBoxK c x : ℝ) * c < (N : ℝ) * c := by linarith
      exact lt_of_mul_lt_mul_right h hc.le
    have hNk : -(N : ℝ) < (hrBoxK c x : ℝ) := by
      have h : -(N : ℝ) * c < (hrBoxK c x : ℝ) * c := by
        have e : -(N : ℝ) * c = -((N : ℝ) * c) := by ring
        rw [e]
        linarith
      exact lt_of_mul_lt_mul_right h hc.le
    have hkN' : hrBoxK c x < N := by exact_mod_cast hkN
    have hNk' : -N < hrBoxK c x := by exact_mod_cast hNk
    exact Finset.mem_Icc.2 ⟨by omega, by omega⟩
  -- the box mass is bounded by a finite sum of translates of `hrBoxG`
  have hsum : ∫⁻ x in Icc σ H ×ˢ (Icc (-R) R ×ˢ Icc (-L) L), ‖b' (hrBoxRed c x)‖ₑ ^ r ∂volume ≤
      ∑ m ∈ Finset.Icc (-N) N, ∫⁻ x, hrBoxG c r σ H b' (qShift ((m : ℝ) * c) x) ∂volume := by
    rw [← lintegral_finsetSum (f := fun (m : ℤ) (x : Coord) =>
      hrBoxG c r σ H b' (qShift ((m : ℝ) * c) x))
      _ (fun m _ => (hrBoxG_measurable hb'm).comp (hrBox_qShift_mp ((m : ℝ) * c)).measurable)]
    have hBm : MeasurableSet (Icc σ H ×ˢ (Icc (-R) R ×ˢ Icc (-L) L)) :=
      MeasurableSet.prod measurableSet_Icc
        (MeasurableSet.prod measurableSet_Icc measurableSet_Icc)
    rw [← lintegral_indicator hBm]
    apply lintegral_mono
    intro x
    by_cases hx : x ∈ Icc σ H ×ˢ (Icc (-R) R ×ˢ Icc (-L) L)
    · rw [Set.indicator_of_mem hx]
      have hredS : hrBoxRed c x ∈ Icc σ H ×ˢ Cyl.cell c :=
        hrBox_red_mem hc (Icc σ H) x (Set.mem_prod.1 hx).1
      have hG1 : hrBoxG c r σ H b' (hrBoxRed c x) = ‖b' (hrBoxRed c x)‖ₑ ^ r := by
        unfold hrBoxG
        exact Set.indicator_of_mem hredS _
      calc ‖b' (hrBoxRed c x)‖ₑ ^ r = hrBoxG c r σ H b' (hrBoxRed c x) := hG1.symm
        _ ≤ ∑ m ∈ Finset.Icc (-N) N, hrBoxG c r σ H b' (qShift ((m : ℝ) * c) x) :=
          Finset.single_le_sum (f := fun m : ℤ => hrBoxG c r σ H b' (qShift ((m : ℝ) * c) x))
            (fun _ _ => zero_le) (hkF x hx)
    · rw [Set.indicator_of_notMem hx]
      exact zero_le
  have hterm : ∀ m : ℤ, ∫⁻ x, hrBoxG c r σ H b' (qShift ((m : ℝ) * c) x) ∂volume < ⊤ := by
    intro m
    rw [(hrBox_qShift_mp ((m : ℝ) * c)).lintegral_comp (hrBoxG_measurable hb'm)]
    exact hX
  have hXB : ∫⁻ x in Icc σ H ×ˢ (Icc (-R) R ×ˢ Icc (-L) L), ‖b' (hrBoxRed c x)‖ₑ ^ r ∂volume < ⊤ :=
    lt_of_le_of_lt hsum (ENNReal.sum_lt_top.2 (fun m _ => hterm m))
  -- `g = b' ∘ hrBoxRed` is in `L^r(B)`, hence in `L^1(B)` on the finite measure set `B`
  have hBfin : volume (Icc σ H ×ˢ (Icc (-R) R ×ˢ Icc (-L) L)) < ⊤ :=
    (isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)).measure_lt_top
  have : IsFiniteMeasure (volume.restrict (Icc σ H ×ˢ (Icc (-R) R ×ˢ Icc (-L) L))) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact hBfin⟩
  have hLp : MemLp (fun x : Coord => b' (hrBoxRed c x)) (ENNReal.ofReal r)
      (volume.restrict (Icc σ H ×ˢ (Icc (-R) R ×ˢ Icc (-L) L))) := by
    refine ⟨hgm.aestronglyMeasurable, ?_⟩
    rw [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top (ENNReal.ofReal_pos.2 hr0).ne'
      ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal hr0.le]
    exact hXB
  have hI1 : Integrable (fun x : Coord => b' (hrBoxRed c x))
      (volume.restrict (Icc σ H ×ˢ (Icc (-R) R ×ˢ Icc (-L) L))) :=
    hLp.integrable (ENNReal.one_le_ofReal.2 hr.le)
  -- the component `i` is dominated by the norm
  have hcont : Measurable (fun v : CMerid => v i) :=
    ((continuous_apply i).comp (PiLp.continuous_ofLp 2 (fun _ : Fin 2 => ℂ))).measurable
  have hIc : Integrable (fun x : Coord => b' (hrBoxRed c x) i)
      (volume.restrict (Icc σ H ×ˢ (Icc (-R) R ×ˢ Icc (-L) L))) :=
    Integrable.mono' hI1.norm (hcont.comp hgm).aestronglyMeasurable
      (ae_of_all _ (fun x => PiLp.norm_apply_le _ i))
  have hBm : MeasurableSet (Icc σ H ×ˢ (Icc (-R) R ×ˢ Icc (-L) L)) :=
    MeasurableSet.prod measurableSet_Icc
      (MeasurableSet.prod measurableSet_Icc measurableSet_Icc)
  have hae : (fun x : Coord => b' (hrBoxRed c x) i) =ᵐ[volume.restrict
      (Icc σ H ×ˢ (Icc (-R) R ×ˢ Icc (-L) L))] (fun x : Coord => b x i) := by
    filter_upwards [ae_restrict_of_ae hpt, ae_restrict_mem hBm] with x hx hxB
    have hxs : 0 < x.1 := lt_of_lt_of_le hσ (Set.mem_prod.1 hxB).1.1
    rw [hx hxs]
  exact hIc.congr hae

end UnforcedLeray.Short.IIb
