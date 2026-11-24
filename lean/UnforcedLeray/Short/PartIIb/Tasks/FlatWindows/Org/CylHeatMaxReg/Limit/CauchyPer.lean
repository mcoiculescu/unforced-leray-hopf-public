import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T13_1_4_4

/-!
# Part II-b, task `PartII-b:T13/1/4/4/3` (`ChmCauchyPer`): completeness of periodic `L^r(cylMeas c)`

Source of record: `the November 2 reference manuscript` (SP) lines 1933-1935.

Proof. The cylinder measure `cylMeas c = c⁻¹ • volume.restrict T` with `T = ℝ × cell c`, so
the strip `T` carries all the mass. The sequence `g n` is Cauchy in `L^r(cylMeas c)` (the
modulus `a` tends to `0`), hence converges in the complete space `Lp` to some `L`. The
periodic extension `x ↦ L (red x)` of `L` through the reduction `red` of `q` into the centred
cell is `qShift c`-invariant everywhere and volume-measurable (the translations generating the
fibres of `red` preserve volume and `map red volume ≪ cylMeas c`). On the cell `red` is the
identity, so the norms of `g n - L ∘ red` and `g n - L` agree.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.IIb

open MeasureTheory Set Filter Topology
open scoped ENNReal ContDiff

/-- The reduction of `x` into the centred cell: `q ↦ q - c ⌊(q + c/2)/c⌋`. -/
def chmCpRed (c : ℝ) (x : Coord) : Coord :=
  (x.1, (x.2.1 - c * ((⌊(x.2.1 + c / 2) / c⌋ : ℤ) : ℝ), x.2.2))

/-- The translation undoing the reduction at level `k`. -/
def chmCpW (c : ℝ) (k : ℤ) : Coord := (0, (-(c * (k : ℝ)), 0))

/-- The strip `T = ℝ × cell c` in `Coord`. -/
def chmCpT (c : ℝ) : Set Coord := univ ×ˢ UnforcedLeray.Cyl.cell c

/-- The tail supremum `N ↦ sup_{k ≥ N} a k`. -/
def chmCpTail (a : ℕ → ℝ≥0∞) (N : ℕ) : ℝ≥0∞ := ⨆ k, ⨆ (_ : N ≤ k), a k

theorem chmCp_measurableSet (c : ℝ) : MeasurableSet (chmCpT c) :=
  MeasurableSet.univ.prod (measurableSet_Ico.prod MeasurableSet.univ)

theorem chmCp_mem_iff (c : ℝ) (x : Coord) : x ∈ chmCpT c ↔ x.2.1 ∈ Ico (-c / 2) (c / 2) := by
  unfold chmCpT UnforcedLeray.Cyl.cell
  simp only [Set.mem_prod, Set.mem_univ, true_and, and_true]

theorem chmCp_cylMeas (c : ℝ) :
    cylMeas c = ENNReal.ofReal c⁻¹ • (volume : Measure Coord).restrict (chmCpT c) := by
  unfold cylMeas UnforcedLeray.Cyl.avgμ UnforcedLeray.Cyl.cellμ chmCpT
  rw [Measure.prod_smul_right]
  have h := Measure.prod_restrict (univ : Set ℝ) (UnforcedLeray.Cyl.cell c)
    (μ := (volume : Measure ℝ)) (ν := (volume : Measure (ℝ × ℝ)))
  rw [Measure.restrict_univ] at h
  rw [h]
  rfl

theorem chmCp_cylMeas_apply (c : ℝ) {t : Set Coord} (ht : MeasurableSet t) :
    cylMeas c t = ENNReal.ofReal c⁻¹ * volume (t ∩ chmCpT c) := by
  rw [chmCp_cylMeas, Measure.smul_apply, Measure.restrict_apply ht, smul_eq_mul]

theorem chmCp_null_of (c : ℝ) (hc : 0 < c) {t : Set Coord} (ht : MeasurableSet t)
    (h0 : cylMeas c t = 0) : volume (t ∩ chmCpT c) = 0 := by
  rw [chmCp_cylMeas_apply c ht] at h0
  rcases mul_eq_zero.1 h0 with h1 | h1
  · exact absurd h1 (ENNReal.ofReal_pos.2 (inv_pos.2 hc)).ne'
  · exact h1

theorem chmCp_ae_mem (c : ℝ) : ∀ᵐ x ∂(cylMeas c), x ∈ chmCpT c := by
  rw [ae_iff]
  have hcompl : {x : Coord | ¬ x ∈ chmCpT c} = (chmCpT c)ᶜ := rfl
  rw [hcompl, chmCp_cylMeas_apply c (chmCp_measurableSet c).compl, Set.compl_inter_self,
    measure_empty, mul_zero]

theorem chmCp_red_add (c : ℝ) (x : Coord) :
    chmCpRed c x = x + chmCpW c ⌊(x.2.1 + c / 2) / c⌋ := by
  unfold chmCpRed chmCpW
  exact Prod.ext (by simp) (Prod.ext (by simp [sub_eq_add_neg]) (by simp))

theorem chmCp_red_mem (c : ℝ) (hc : 0 < c) (x : Coord) : chmCpRed c x ∈ chmCpT c := by
  have hc' : c ≠ 0 := hc.ne'
  rw [chmCp_mem_iff]
  have h1 : ((⌊(x.2.1 + c / 2) / c⌋ : ℤ) : ℝ) ≤ (x.2.1 + c / 2) / c := Int.floor_le _
  have h2 : (x.2.1 + c / 2) / c < ((⌊(x.2.1 + c / 2) / c⌋ : ℤ) : ℝ) + 1 :=
    Int.lt_floor_add_one _
  have hu : c * ((x.2.1 + c / 2) / c) = x.2.1 + c / 2 := by field_simp
  have h3 : c * ((⌊(x.2.1 + c / 2) / c⌋ : ℤ) : ℝ) ≤ c * ((x.2.1 + c / 2) / c) :=
    mul_le_mul_of_nonneg_left h1 hc.le
  have h4 : c * ((x.2.1 + c / 2) / c) < c * (((⌊(x.2.1 + c / 2) / c⌋ : ℤ) : ℝ) + 1) :=
    mul_lt_mul_of_pos_left h2 hc
  rw [mul_add, mul_one] at h4
  show x.2.1 - c * ((⌊(x.2.1 + c / 2) / c⌋ : ℤ) : ℝ) ∈ Ico (-c / 2) (c / 2)
  rw [Set.mem_Ico]
  constructor <;> linarith

theorem chmCp_red_eq (c : ℝ) (hc : 0 < c) (x : Coord) (hx : x ∈ chmCpT c) :
    chmCpRed c x = x := by
  rw [chmCp_mem_iff] at hx
  obtain ⟨hx1, hx2⟩ := Set.mem_Ico.1 hx
  have hfl : ⌊(x.2.1 + c / 2) / c⌋ = 0 := by
    rw [Int.floor_eq_zero_iff, Set.mem_Ico]
    constructor
    · exact div_nonneg (by linarith) hc.le
    · rw [div_lt_one hc]; linarith
  unfold chmCpRed
  rw [hfl]
  simp

theorem chmCp_ae_red (c : ℝ) (hc : 0 < c) : ∀ᵐ x ∂(cylMeas c), chmCpRed c x = x := by
  filter_upwards [chmCp_ae_mem c] with x hx
  exact chmCp_red_eq c hc x hx

theorem chmCp_red_qShift (c : ℝ) (hc : 0 < c) (x : Coord) :
    chmCpRed c (qShift c x) = chmCpRed c x := by
  have hc' : c ≠ 0 := hc.ne'
  have hfl : ⌊((x.2.1 + c) + c / 2) / c⌋ = ⌊(x.2.1 + c / 2) / c⌋ + 1 := by
    rw [← Int.floor_add_one]
    congr 1
    rw [div_add_one hc']
    congr 1
    ring
  unfold chmCpRed qShift
  simp only [hfl, Int.cast_add, Int.cast_one]
  exact Prod.ext rfl (Prod.ext (by ring) rfl)

theorem chmCp_red_measurable (c : ℝ) : Measurable (chmCpRed c) := by
  have hf : Measurable (fun x : Coord => (x.2.1 + c / 2) / c) :=
    ((measurable_fst.comp measurable_snd).add_const _).div_const _
  have hk : Measurable (fun x : Coord => ((⌊(x.2.1 + c / 2) / c⌋ : ℤ) : ℝ)) :=
    (measurable_of_countable (fun n : ℤ => (n : ℝ))).comp hf.floor
  unfold chmCpRed
  exact measurable_fst.prodMk
    (((measurable_fst.comp measurable_snd).sub (measurable_const.mul hk)).prodMk
      (measurable_snd.comp measurable_snd))

theorem chmCp_map_null (c : ℝ) (hc : 0 < c) (t : Set Coord) (ht : MeasurableSet t)
    (h0 : cylMeas c t = 0) : Measure.map (chmCpRed c) volume t = 0 := by
  rw [Measure.map_apply (chmCp_red_measurable c) ht]
  have hsub : chmCpRed c ⁻¹' t ⊆
      ⋃ k : ℤ, (fun x : Coord => x + chmCpW c k) ⁻¹' (t ∩ chmCpT c) := by
    intro x hx
    refine Set.mem_iUnion.2 ⟨⌊(x.2.1 + c / 2) / c⌋, ?_⟩
    show x + chmCpW c ⌊(x.2.1 + c / 2) / c⌋ ∈ t ∩ chmCpT c
    rw [← chmCp_red_add c x]
    exact ⟨hx, chmCp_red_mem c hc x⟩
  refine measure_mono_null hsub ?_
  refine measure_iUnion_null_iff.2 (fun k => ?_)
  rw [measure_preimage_add_right]
  exact chmCp_null_of c hc ht h0

theorem chmCp_ac (c : ℝ) (hc : 0 < c) : Measure.map (chmCpRed c) volume ≪ cylMeas c := by
  intro s hs
  refine measure_mono_null (subset_toMeasurable (cylMeas c) s) ?_
  apply chmCp_map_null c hc _ (measurableSet_toMeasurable _ _)
  rw [measure_toMeasurable]
  exact hs

theorem chmCp_tail_ge (a : ℕ → ℝ≥0∞) (N n : ℕ) (hn : N ≤ n) : a n ≤ chmCpTail a N := by
  unfold chmCpTail
  exact le_iSup₂_of_le n hn le_rfl

theorem chmCp_tail_antitone (a : ℕ → ℝ≥0∞) : Antitone (chmCpTail a) := by
  intro N M hNM
  unfold chmCpTail
  refine iSup_le fun k => iSup_le fun hk => ?_
  exact le_iSup₂_of_le k (le_trans hNM hk) le_rfl

theorem chmCp_tail_tendsto (a : ℕ → ℝ≥0∞) (ha : Tendsto a atTop (𝓝 0)) :
    Tendsto (chmCpTail a) atTop (𝓝 0) := by
  have h2 : (⨅ N, chmCpTail a N) = limsup a atTop :=
    (Filter.limsup_eq_iInf_iSup_of_nat (u := a)).symm
  have hinf : (⨅ N, chmCpTail a N) = 0 := by
    rw [h2, ha.limsup_eq]
  have := tendsto_atTop_iInf (chmCp_tail_antitone a)
  rwa [hinf] at this

theorem chmCauchyPer : ChmCauchyPer := by
  intro r c hr hc g hg a ha hcau
  have hp1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal r := ENNReal.one_le_ofReal.2 hr.le
  have : Fact (1 ≤ ENNReal.ofReal r) := ⟨hp1⟩
  have hmem : ∀ n, MemLp (g n) (ENNReal.ofReal r) (cylMeas c) := fun n =>
    ⟨(hg n).1.aestronglyMeasurable, (hg n).2.2⟩
  let F : ℕ → Lp ℂ (ENNReal.ofReal r) (cylMeas c) := fun n => (hmem n).toLp (g n)
  have hedist : ∀ n m, edist (F n) (F m) =
      eLpNorm (fun x => g n x - g m x) (ENNReal.ofReal r) (cylMeas c) :=
    fun n m => Lp.edist_toLp_toLp (g n) (g m) (hmem n) (hmem m)
  have hcauchy : CauchySeq F := by
    rw [EMetric.cauchySeq_iff_le_tendsto_0]
    refine ⟨fun N => chmCpTail a N + chmCpTail a N, ?_, ?_⟩
    · intro n m N hn hm
      rw [hedist]
      refine (hcau n m).trans ?_
      exact add_le_add (chmCp_tail_ge a N n hn) (chmCp_tail_ge a N m hm)
    · have := (chmCp_tail_tendsto a ha).add (chmCp_tail_tendsto a ha)
      rwa [add_zero] at this
  obtain ⟨L, hL⟩ := cauchySeq_tendsto_of_complete hcauchy
  have hLn := (MeasureTheory.Lp.tendsto_Lp_iff_tendsto_eLpNorm' F L).1 hL
  have hconv : ∀ n, eLpNorm (⇑(F n) - ⇑L) (ENNReal.ofReal r) (cylMeas c) =
      eLpNorm (fun x => g n x - ⇑L x) (ENNReal.ofReal r) (cylMeas c) := fun n =>
    eLpNorm_congr_ae ((MemLp.coeFn_toLp (hmem n)).sub EventuallyEq.rfl)
  have hset : ∀ n, eLpNorm (fun x => g n x - L (chmCpRed c x)) (ENNReal.ofReal r) (cylMeas c) =
      eLpNorm (fun x => g n x - L x) (ENNReal.ofReal r) (cylMeas c) := by
    intro n
    apply eLpNorm_congr_ae
    filter_upwards [chmCp_ae_red c hc] with x hx
    rw [hx]
  have hq : Measure.QuasiMeasurePreserving (chmCpRed c) volume (cylMeas c) :=
    ⟨chmCp_red_measurable c, chmCp_ac c hc⟩
  refine ⟨fun x => L (chmCpRed c x), ?_, ?_, ?_⟩
  · unfold QPeriodicS
    exact Filter.Eventually.of_forall (fun x => by
      show L (chmCpRed c (qShift c x)) = L (chmCpRed c x)
      rw [chmCp_red_qShift c hc x])
  · exact (Lp.aestronglyMeasurable L).comp_quasiMeasurePreserving hq
  · refine Tendsto.congr (fun n => ?_) hLn
    rw [hconv n]
    exact (hset n).symm

end UnforcedLeray.Short.IIb
