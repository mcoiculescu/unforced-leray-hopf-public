import UnforcedLeray.Short.PartIIb.Tasks.FlatWindows.Org.FlatGraphOrg

/-!
Helpers for `PartII-b:T13/1/9` (`dyadicSummation`, finite overlap of the dyadic windows, SP 1930-1931).
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.IIb

open MeasureTheory Set Filter
open scoped ENNReal ContDiff

/-- `‖f‖^r` over a measure is the lintegral of `‖f‖ₑ^r`, for `r ≥ 1`. -/
theorem dys_pow_eLpNorm {α : Type*} [MeasurableSpace α] {F : Type*} [NormedAddCommGroup F]
    {r : ℝ} (hr : 1 ≤ r) (ν : Measure α) (f : α → F) :
    eLpNorm f (ENNReal.ofReal r) ν ^ r = ∫⁻ x, ‖f x‖ₑ ^ r ∂ν := by
  have hr0 : 0 < r := by linarith
  have hp0 : ENNReal.ofReal r ≠ 0 := (ENNReal.ofReal_pos.2 hr0).ne'
  have hpt : ENNReal.ofReal r ≠ ⊤ := ENNReal.ofReal_ne_top
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hpt, ENNReal.toReal_ofReal hr0.le,
    ← ENNReal.rpow_mul, one_div_mul_cancel hr0.ne', ENNReal.rpow_one]

/-- Scaling through an outer `ℓ^r` norm. -/
theorem dys_scale {r : ℝ} (hr : 0 < r) (c : ENNReal) (B : ℤ → ENNReal) :
    (∑' k, (c * B k) ^ r) ^ (1 / r) = c * (∑' k, B k ^ r) ^ (1 / r) := by
  simp only [ENNReal.mul_rpow_of_nonneg _ _ hr.le]
  rw [ENNReal.tsum_mul_left, ENNReal.mul_rpow_of_nonneg _ _ (one_div_nonneg.2 hr.le),
    one_div, ENNReal.rpow_rpow_inv hr.ne']

/-- Minkowski inequality in `ℓ^r(ℤ)` for pointwise-dominated sequences. -/
theorem dys_mink {r : ℝ} (hr : 1 ≤ r) (A Y Z : ℤ → ENNReal) (h : ∀ k, A k ≤ Y k + Z k) :
    (∑' k, A k ^ r) ^ (1 / r) ≤ (∑' k, Y k ^ r) ^ (1 / r) + (∑' k, Z k ^ r) ^ (1 / r) := by
  rw [← lintegral_count (fun k => A k ^ r), ← lintegral_count (fun k => Y k ^ r),
    ← lintegral_count (fun k => Z k ^ r)]
  have hle : (∫⁻ k, A k ^ r ∂Measure.count) ≤ ∫⁻ k, (Y + Z) k ^ r ∂Measure.count := by
    apply lintegral_mono
    intro k
    exact ENNReal.rpow_le_rpow (h k) (by linarith)
  calc (∫⁻ k, A k ^ r ∂Measure.count) ^ (1 / r)
      ≤ (∫⁻ k, (Y + Z) k ^ r ∂Measure.count) ^ (1 / r) :=
        ENNReal.rpow_le_rpow hle (one_div_nonneg.2 (by linarith))
    _ ≤ _ := ENNReal.lintegral_Lp_add_le (measurable_of_countable Y).aemeasurable
        (measurable_of_countable Z).aemeasurable hr

/-- The `r`-th power of a bound: `(∑ b_k^r)^{1/r} ≤ 4 G` from `∑ b_k^r ≤ 4 G^r`. -/
theorem dys_bound_one {r : ℝ} (hr : 1 ≤ r) (B : ℤ → ENNReal) (G : ENNReal)
    (hB : ∑' k, B k ^ r ≤ 4 * G ^ r) : (∑' k, B k ^ r) ^ (1 / r) ≤ 4 * G := by
  have hr0 : 0 < r := by linarith
  calc (∑' k, B k ^ r) ^ (1 / r) ≤ (4 * G ^ r) ^ (1 / r) :=
        ENNReal.rpow_le_rpow hB (one_div_nonneg.2 hr0.le)
    _ = (4 : ENNReal) ^ (1 / r) * G := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ (one_div_nonneg.2 hr0.le), one_div,
          ENNReal.rpow_rpow_inv hr0.ne']
    _ ≤ 4 * G := by
        have h4 : (4 : ENNReal) ^ (1 / r) ≤ 4 := by
          calc (4 : ENNReal) ^ (1 / r) ≤ (4 : ENNReal) ^ (1 : ℝ) :=
                ENNReal.rpow_le_rpow_of_exponent_le (by norm_num) ((div_le_one hr0).2 hr)
            _ = 4 := ENNReal.rpow_one 4
        gcongr

/-- Dyadic windows `(2^k, 2^{k+1})` are pairwise disjoint. -/
theorem dys_pair (i j : ℤ) (h : i < j) : 2 * (2 : ℝ) ^ i ≤ (2 : ℝ) ^ j := by
  have h1 : (2 : ℝ) ^ (i + 1) ≤ (2 : ℝ) ^ j := zpow_le_zpow_right₀ (by norm_num) (by omega)
  rwa [zpow_add_one₀ (by norm_num : (2 : ℝ) ≠ 0), mul_comm] at h1

theorem dys_disj_lt (i j : ℤ) (h : i < j) :
    Disjoint (winOpen ((2 : ℝ) ^ i)) (winOpen ((2 : ℝ) ^ j)) := by
  refine Set.disjoint_left.2 fun x hx hx' => ?_
  have h2 := dys_pair i j h
  have hx1 := hx.1
  have hx2 := hx'.1
  simp only [mem_Ioo] at hx1 hx2
  linarith [hx1.2, hx2.1]

theorem dys_disjoint : Pairwise fun i j : ℤ => Disjoint (winOpen ((2 : ℝ) ^ i)) (winOpen ((2 : ℝ) ^ j)) := by
  intro i j hij
  rcases lt_or_gt_of_ne hij with h | h
  · exact dys_disj_lt i j h
  · exact (dys_disj_lt j i h).symm

theorem dys_meas_winSet2 (a : ℝ) : MeasurableSet (winSet2 a) :=
  measurableSet_Icc.prod MeasurableSet.univ

/-- Copy of `ageμ_ae_pos` (`Sub/PartII-b_T10_2.lean`): the measure `ageμ` lives on `s > 0`. -/
theorem dys_ae_pos (c a : ℝ) : ∀ᵐ x ∂(Axi.ageμ c a), 0 < x.1 := by
  rw [ae_iff]
  have h : {x : Coord | ¬ 0 < x.1} = Iic (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ)) := by
    ext x; simp
  haveI : SFinite (UnforcedLeray.Cyl.avgμ c) := by unfold UnforcedLeray.Cyl.avgμ; infer_instance
  have hI : Iic (0 : ℝ) ∩ Ioi 0 = ∅ := by
    ext x; simp only [mem_inter_iff, mem_Iic, mem_Ioi, mem_empty_iff_false, iff_false, not_and,
      not_lt]; exact id
  rw [h, Axi.ageμ, Measure.prod_prod, withDensity_apply _ measurableSet_Iic,
    Measure.restrict_restrict measurableSet_Iic, hI]
  simp

/-- The dyadic windows cover `hMeas`-almost every point. -/
theorem dys_cover_ae (c r : ℝ) : ∀ᵐ x ∂(hMeas c r), x ∈ ⋃ k : ℤ, winOpen ((2 : ℝ) ^ k) := by
  have h1 : hMeas c r {x : Coord | ¬ 0 < x.1} = 0 := by
    unfold hMeas
    exact ae_iff.1 (dys_ae_pos c (r / 2 - 5 / 2))
  have h2 : ∀ k : ℤ, hMeas c r {x : Coord | x.1 = (2 : ℝ) ^ k} = 0 := by
    intro k
    have hvol : (volume : Measure Coord) {x : Coord | x.1 = (2 : ℝ) ^ k} = 0 := by
      have e : {x : Coord | x.1 = (2 : ℝ) ^ k} = ({(2 : ℝ) ^ k} : Set ℝ) ×ˢ (univ : Set (ℝ × ℝ)) := by
        ext x
        simp
      rw [e, Measure.volume_eq_prod, Measure.prod_prod, Real.volume_singleton, zero_mul]
    exact fw_hMeas_ac c r hvol
  rw [ae_iff]
  refine measure_mono_null ?_ (measure_union_null h1 (measure_iUnion_null h2))
  intro x hx
  simp only [mem_setOf_eq, mem_iUnion, mem_union] at hx ⊢
  by_cases hpos : 0 < x.1
  · obtain ⟨j, hj1, hj2⟩ := exists_mem_Ico_zpow hpos one_lt_two
    by_cases heq : x.1 = (2 : ℝ) ^ j
    · exact Or.inr ⟨j, heq⟩
    · exfalso
      have hlt : x.1 < 2 * (2 : ℝ) ^ j := by
        rw [zpow_add_one₀ (by norm_num : (2 : ℝ) ≠ 0), mul_comm] at hj2
        exact hj2
      exact hx ⟨j, ⟨lt_of_le_of_ne hj1 (Ne.symm heq), hlt⟩, mem_univ _⟩
  · exact Or.inl hpos

/-- Covering identity for the dyadic windows: `∑_k ‖f‖_{W_k}^r = ‖f‖^r`. -/
theorem dys_cover {c r : ℝ} (hr : 1 ≤ r) (f : CProf) :
    ∑' k : ℤ, hNormOn c r (winOpen ((2 : ℝ) ^ k)) f ^ r = hNorm c r f ^ r := by
  simp only [hNormOn, hNorm, dys_pow_eLpNorm hr]
  rw [← lintegral_iUnion (s := fun k : ℤ => winOpen ((2 : ℝ) ^ k))
    (fun k => fw_measurableSet_winOpen _) dys_disjoint,
    Measure.restrict_eq_self_of_ae_mem (dys_cover_ae c r)]

/-- `ℓ^r` norm of the window norms is the global norm. -/
theorem dys_norm_eq {c r : ℝ} (hr : 1 ≤ r) (f : CProf) :
    (∑' k : ℤ, hNormOn c r (winOpen ((2 : ℝ) ^ k)) f ^ r) ^ (1 / r) = hNorm c r f := by
  have hr0 : 0 < r := by linarith
  rw [dys_cover hr f, one_div, ENNReal.rpow_rpow_inv hr0.ne']

/-- Pointwise finite overlap: at most four enlarged windows `[2^{k-1}, 2^{k+2}]` contain a point. -/
theorem dys_window_index (x : Coord) :
    ∃ j : ℤ, ∀ k : ℤ, x ∈ winSet2 ((2 : ℝ) ^ k) → j - 2 ≤ k ∧ k ≤ j + 1 := by
  by_cases hpos : 0 < x.1
  · obtain ⟨j, hj1, hj2⟩ := exists_mem_Ico_zpow hpos one_lt_two
    refine ⟨j, fun k hk => ?_⟩
    obtain ⟨h1, h2⟩ := hk.1
    have ht : (2 : ℝ) ^ (j + 1) = 2 * (2 : ℝ) ^ j := by
      rw [zpow_add_one₀ (by norm_num : (2 : ℝ) ≠ 0), mul_comm]
    have ht2 : (2 : ℝ) ^ (j + 2) = 4 * (2 : ℝ) ^ j := by
      rw [zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0), zpow_two]
      ring
    have ht3 : (2 : ℝ) ^ (k + 3) = 8 * (2 : ℝ) ^ k := by
      rw [zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0), show (3 : ℤ) = 3 from rfl]
      norm_num
      ring
    constructor
    · by_contra hcon
      have hk3 : k + 3 ≤ j := by omega
      have hm : (2 : ℝ) ^ (k + 3) ≤ (2 : ℝ) ^ j := zpow_le_zpow_right₀ (by norm_num) hk3
      have hkpos : (0 : ℝ) < (2 : ℝ) ^ k := zpow_pos (by norm_num) k
      linarith
    · by_contra hcon
      have hk2 : j + 2 ≤ k := by omega
      have hm : (2 : ℝ) ^ (j + 2) ≤ (2 : ℝ) ^ k := zpow_le_zpow_right₀ (by norm_num) hk2
      have hjpos : (0 : ℝ) < (2 : ℝ) ^ j := zpow_pos (by norm_num) j
      linarith
  · refine ⟨0, fun k hk => ?_⟩
    have hkpos : (0 : ℝ) < (2 : ℝ) ^ k := zpow_pos (by norm_num) k
    exfalso
    have h1 : (2 : ℝ) ^ k / 2 ≤ x.1 := hk.1.1
    have : x.1 ≤ 0 := not_lt.1 hpos
    linarith

/-- Pointwise bound on the window sum. -/
theorem dys_pt (h : Coord → ENNReal) (x : Coord) :
    ∑' k : ℤ, (winSet2 ((2 : ℝ) ^ k)).indicator h x ≤ 4 * h x := by
  obtain ⟨j, hj⟩ := dys_window_index x
  have hsub : ∀ k : ℤ, k ∉ Finset.Icc (j - 2) (j + 1) →
      (winSet2 ((2 : ℝ) ^ k)).indicator h x = 0 := by
    intro k hk
    have hnot : x ∉ winSet2 ((2 : ℝ) ^ k) := by
      intro hx
      apply hk
      obtain ⟨h1, h2⟩ := hj k hx
      rw [Finset.mem_Icc]
      exact ⟨h1, h2⟩
    unfold Set.indicator
    exact if_neg hnot
  rw [tsum_eq_sum (s := Finset.Icc (j - 2) (j + 1)) (fun k hk => hsub k hk)]
  calc ∑ k ∈ Finset.Icc (j - 2) (j + 1), (winSet2 ((2 : ℝ) ^ k)).indicator h x
      ≤ ∑ _k ∈ Finset.Icc (j - 2) (j + 1), h x :=
        Finset.sum_le_sum (fun k _ => by unfold Set.indicator; split_ifs <;> simp)
    _ = 4 * h x := by
        rw [Finset.sum_const, Int.card_Icc, show (j + 1 + 1 - (j - 2)).toNat = 4 by omega,
          nsmul_eq_mul]
        norm_num

/-- The enlarged windows have summable `r`-th powers, bounded by the global norm (`4` overlap). -/
theorem dys_W2 {c r : ℝ} (hr : 1 ≤ r) (g : CProf) (hg : AEStronglyMeasurable g (hMeas c r)) :
    ∑' k : ℤ, hNormOn c r (winSet2 ((2 : ℝ) ^ k)) g ^ r ≤ 4 * hNorm c r g ^ r := by
  have hmeas : AEMeasurable (fun x : Coord => ‖g x‖ₑ ^ r) (hMeas c r) :=
    (ENNReal.continuous_rpow_const (y := r)).measurable.comp_aemeasurable hg.aemeasurable.enorm
  have hk : ∀ k : ℤ, hNormOn c r (winSet2 ((2 : ℝ) ^ k)) g ^ r =
      ∫⁻ x, (winSet2 ((2 : ℝ) ^ k)).indicator (fun x => ‖g x‖ₑ ^ r) x ∂(hMeas c r) := by
    intro k
    unfold hNormOn
    rw [dys_pow_eLpNorm hr, lintegral_indicator (dys_meas_winSet2 _)]
  calc ∑' k : ℤ, hNormOn c r (winSet2 ((2 : ℝ) ^ k)) g ^ r
      = ∑' k : ℤ, ∫⁻ x, (winSet2 ((2 : ℝ) ^ k)).indicator (fun x => ‖g x‖ₑ ^ r) x ∂(hMeas c r) :=
        tsum_congr hk
    _ = ∫⁻ x, ∑' k : ℤ, (winSet2 ((2 : ℝ) ^ k)).indicator (fun x => ‖g x‖ₑ ^ r) x ∂(hMeas c r) :=
        (lintegral_tsum (fun k => hmeas.indicator (dys_meas_winSet2 _))).symm
    _ ≤ ∫⁻ x, 4 * (‖g x‖ₑ ^ r) ∂(hMeas c r) :=
        lintegral_mono (fun x => dys_pt (fun y => ‖g y‖ₑ ^ r) x)
    _ = 4 * ∫⁻ x, ‖g x‖ₑ ^ r ∂(hMeas c r) := lintegral_const_mul' 4 _ (by norm_num)
    _ = 4 * hNorm c r g ^ r := by
        unfold hNorm
        rw [dys_pow_eLpNorm hr]

end UnforcedLeray.Short.IIb
