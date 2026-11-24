import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T12_1_4_1

/-!

Source: `the November 2 reference manuscript` lines 1933-1935.
Route: pointwise Hoelder over the `2N+1` translates, translation of the window integrals,
overlap count `≤ 2M` of the shifted windows, then the whole-plane `L^p` bound on `G`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology Function
open scoped ENNReal

namespace UnforcedLeray.Short.IIb

theorem ppl_window_measurable (c : ℝ) (M : ℕ) : MeasurableSet (ppWindow c M) := by
  have h : ppWindow c M = Ico (-(M : ℝ) * c) ((M : ℝ) * c) ×ˢ (univ : Set ℝ) := by
    ext z
    simp [ppWindow]
  rw [h]
  exact measurableSet_Ico.prod MeasurableSet.univ

/-- Overlap count: each point lies in at most `2M` of the shifted windows `W + j c e_q`. -/
theorem ppl_window_count {c : ℝ} (hc : 0 < c) (M N : ℕ) (z : ℝ × ℝ) :
    ∑ j ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
      (ppWindow c M).indicator (1 : ℝ × ℝ → ℝ≥0∞) (z - ((j : ℝ) * c, 0)) ≤ 2 * (M : ℝ≥0∞) := by
  classical
  set x : ℝ := z.1 / c with hxdef
  have hx : x * c = z.1 := div_mul_cancel₀ _ hc.ne'
  set m : ℤ := ⌊x⌋ with hmdef
  have hm1 : (m : ℝ) ≤ x := Int.floor_le x
  have hm2 : x < (m : ℝ) + 1 := Int.lt_floor_add_one x
  have hsub : (Finset.Icc (-(N : ℤ)) (N : ℤ)).filter
      (fun j : ℤ => z - ((j : ℝ) * c, 0) ∈ ppWindow c M) ⊆ Finset.Icc (m - M + 1) (m + M) := by
    intro j hj
    rw [Finset.mem_filter] at hj
    obtain ⟨-, hW⟩ := hj
    simp only [ppWindow, mem_setOf_eq, Prod.fst_sub] at hW
    obtain ⟨hW1, hW2⟩ := hW
    have hjc1 : (j : ℝ) * c ≤ (x + M) * c := by rw [add_mul, hx]; linarith
    have hjc2 : (x - M) * c < (j : ℝ) * c := by rw [sub_mul, hx]; linarith
    have hj1 : (j : ℝ) ≤ x + M := le_of_mul_le_mul_right hjc1 hc
    have hj2 : x - M < (j : ℝ) := lt_of_mul_lt_mul_right hjc2 hc.le
    have hj3 : j < m + M + 1 := by
      have : (j : ℝ) < ((m + M + 1 : ℤ) : ℝ) := by push_cast; linarith
      exact_mod_cast this
    have hj4 : m - M < j := by
      have : ((m - M : ℤ) : ℝ) < (j : ℝ) := by push_cast; linarith
      exact_mod_cast this
    exact Finset.mem_Icc.2 ⟨by omega, by omega⟩
  have hcardI : (Finset.Icc (m - M + 1) (m + M)).card = 2 * M := by
    rw [Int.card_Icc]; omega
  have hsum : ∑ j ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
      (ppWindow c M).indicator (1 : ℝ × ℝ → ℝ≥0∞) (z - ((j : ℝ) * c, 0)) =
      (((Finset.Icc (-(N : ℤ)) (N : ℤ)).filter
        (fun j : ℤ => z - ((j : ℝ) * c, 0) ∈ ppWindow c M)).card : ℝ≥0∞) := by
    simp only [Set.indicator_apply, Pi.one_apply]
    rw [Finset.sum_boole]
  rw [hsum]
  calc (((Finset.Icc (-(N : ℤ)) (N : ℤ)).filter
        (fun j : ℤ => z - ((j : ℝ) * c, 0) ∈ ppWindow c M)).card : ℝ≥0∞)
      ≤ ((Finset.Icc (m - M + 1) (m + M)).card : ℝ≥0∞) := by
        exact_mod_cast Finset.card_le_card hsub
    _ = 2 * (M : ℝ≥0∞) := by rw [hcardI]; push_cast; ring

/-- Translation of a window integral: `∫_W g(· + (a,0)) = ∫ 1_{W}(z - (a,0)) g(z)`. -/
theorem ppl_shift_window {c : ℝ} (M : ℕ) (a : ℝ) (g : ℝ × ℝ → ℝ≥0∞) :
    ∫⁻ z in ppWindow c M, g (z.1 + a, z.2) =
      ∫⁻ z, (ppWindow c M).indicator (1 : ℝ × ℝ → ℝ≥0∞) (z - (a, 0)) * g z := by
  have hW := ppl_window_measurable c M
  have h := lintegral_sub_right_eq_self (μ := (volume : Measure (ℝ × ℝ)))
    (fun z => (ppWindow c M).indicator (fun w => g (w.1 + a, w.2)) z) (a, (0 : ℝ))
  rw [← lintegral_indicator hW (fun w => g (w.1 + a, w.2)), ← h]
  apply lintegral_congr
  intro z
  by_cases hz : z - (a, (0:ℝ)) ∈ ppWindow c M
  · simp only [Set.indicator_of_mem hz, Pi.one_apply, one_mul]
    congr 1
    simp
  · simp only [Set.indicator_of_notMem hz, zero_mul]

/-- Translations of the plane in the `q`-direction preserve Lebesgue measure. -/
theorem ppl_mp_shift (a : ℝ) :
    MeasurePreserving (fun z : ℝ × ℝ => (z.1 + a, z.2)) volume volume := by
  rw [Measure.volume_eq_prod]
  exact (measurePreserving_add_right (volume : Measure ℝ) a).prod (MeasurePreserving.id volume)

/-- Pure power identities for `1/p`. -/
theorem ppl_rpow_inv_rpow {p : ℝ} (hp : 0 < p) (x : ℝ≥0∞) : (x ^ p) ^ (1 / p) = x := by
  rw [← ENNReal.rpow_mul, mul_one_div_cancel hp.ne', ENNReal.rpow_one]

theorem ppl_rpow_rpow_inv {p : ℝ} (hp : 0 < p) (x : ℝ≥0∞) : (x ^ (1 / p)) ^ p = x := by
  rw [← ENNReal.rpow_mul, one_div_mul_cancel hp.ne', ENNReal.rpow_one]

/-- Real scalar inequality behind the constant `3`. -/
theorem ppl_real_scalar {p : ℝ} (hp : 1 ≤ p) {N : ℕ} (hN : 1 ≤ N) {c : ℝ} (hc : 0 < c) :
    ((N : ℝ)⁻¹) ^ p * (2 * (N : ℝ) + 1) ^ (p - 1) * ((N : ℝ) * c) ≤ 3 ^ p * c := by
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := by linarith
  have hA : (2 * (N : ℝ) + 1) ^ (p - 1) ≤ (3 * (N : ℝ)) ^ (p - 1) :=
    Real.rpow_le_rpow (by positivity) (by linarith) (by linarith)
  have hB : (3 * (N : ℝ)) ^ (p - 1) = 3 ^ (p - 1) * (N : ℝ) ^ (p - 1) :=
    Real.mul_rpow (by norm_num) hN0.le
  have hA' : (2 * (N : ℝ) + 1) ^ (p - 1) ≤ 3 ^ (p - 1) * (N : ℝ) ^ (p - 1) := hB ▸ hA
  have hC : ((N : ℝ)⁻¹) ^ p * (N : ℝ) ^ (p - 1) * N = 1 := by
    have hNp : (N : ℝ) ^ p ≠ 0 := by positivity
    rw [Real.inv_rpow hN0.le, Real.rpow_sub_one hN0.ne']
    field_simp
  have hD : (3 : ℝ) ^ (p - 1) ≤ 3 ^ p := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
  have hNonneg : (0 : ℝ) ≤ ((N : ℝ)⁻¹) ^ p := by positivity
  calc ((N : ℝ)⁻¹) ^ p * (2 * (N : ℝ) + 1) ^ (p - 1) * ((N : ℝ) * c)
      ≤ ((N : ℝ)⁻¹) ^ p * (3 ^ (p - 1) * (N : ℝ) ^ (p - 1)) * ((N : ℝ) * c) := by
        gcongr
    _ = 3 ^ (p - 1) * c * (((N : ℝ)⁻¹) ^ p * (N : ℝ) ^ (p - 1) * N) := by ring
    _ = 3 ^ (p - 1) * c := by rw [hC, mul_one]
    _ ≤ 3 ^ p * c := by gcongr


/-- **Task `PartII-b:T12/1/4/1/2`** (`PPLAvgBound`). -/
theorem ppl_avg_bound : UnforcedLeray.Short.IIb.PPLAvgBound := by
  intro c hc p hp1 G N M A hG hGn
  have hp0 : (0 : ℝ) < p := by linarith
  have hW := ppl_window_measurable c M
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · have h0 : ppAvg c 0 G = 0 := by
      funext z
      simp [ppAvg]
    rw [h0]
    simp
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := by linarith
  have hGm : AEStronglyMeasurable G volume := hG.aestronglyMeasurable
  have hTr : ∀ j : ℤ, AEStronglyMeasurable (fun z : ℝ × ℝ => G (z.1 + (j : ℝ) * c, z.2)) volume :=
    fun j => hGm.comp_measurePreserving (ppl_mp_shift ((j : ℝ) * c))
  have hcardN : (Finset.Icc (-(N : ℤ)) (N : ℤ)).card = 2 * N + 1 := by
    rw [Int.card_Icc]; omega
  have hcardE : (((Finset.Icc (-(N : ℤ)) (N : ℤ)).card : ℕ) : ℝ≥0∞) =
      ENNReal.ofReal (2 * (N : ℝ) + 1) := by
    have h' : ((2 * N + 1 : ℕ) : ℝ) = 2 * (N : ℝ) + 1 := by push_cast; ring
    rw [hcardN, ← h', ENNReal.ofReal_natCast]
  have hKne : ENNReal.ofReal ((N : ℝ)⁻¹) ^ p * (((Finset.Icc (-(N : ℤ)) (N : ℤ)).card : ℕ) : ℝ≥0∞) ^ (p - 1) ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg (by linarith) ENNReal.ofReal_ne_top)
      (ENNReal.rpow_ne_top_of_nonneg (by linarith) (ENNReal.natCast_ne_top _))
  -- pointwise Hoelder bound
  have hnorm : ∀ z : ℝ × ℝ, ‖ppAvg c N G z‖ₑ ^ p ≤
      ENNReal.ofReal ((N : ℝ)⁻¹) ^ p * (((Finset.Icc (-(N : ℤ)) (N : ℤ)).card : ℕ) : ℝ≥0∞) ^ (p - 1) *
        ∑ j ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), ‖G (z.1 + (j : ℝ) * c, z.2)‖ₑ ^ p := by
    intro z
    have hK : ‖((N : ℂ))⁻¹‖ₑ = ENNReal.ofReal ((N : ℝ)⁻¹) := by
      rw [← ofReal_norm_eq_enorm]
      congr 1
      simp
    have h1 : ‖ppAvg c N G z‖ₑ ≤ ENNReal.ofReal ((N : ℝ)⁻¹) *
        ∑ j ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), ‖G (z.1 + (j : ℝ) * c, z.2)‖ₑ := by
      unfold ppAvg
      rw [enorm_smul, hK]
      exact mul_le_mul' le_rfl (enorm_sum_le _ _)
    calc ‖ppAvg c N G z‖ₑ ^ p
        ≤ (ENNReal.ofReal ((N : ℝ)⁻¹) *
            ∑ j ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), ‖G (z.1 + (j : ℝ) * c, z.2)‖ₑ) ^ p :=
          ENNReal.rpow_le_rpow h1 hp0.le
      _ = ENNReal.ofReal ((N : ℝ)⁻¹) ^ p *
            (∑ j ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), ‖G (z.1 + (j : ℝ) * c, z.2)‖ₑ) ^ p :=
          ENNReal.mul_rpow_of_nonneg _ _ hp0.le
      _ ≤ ENNReal.ofReal ((N : ℝ)⁻¹) ^ p *
            ((((Finset.Icc (-(N : ℤ)) (N : ℤ)).card : ℕ) : ℝ≥0∞) ^ (p - 1) *
              ∑ j ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), ‖G (z.1 + (j : ℝ) * c, z.2)‖ₑ ^ p) :=
          mul_le_mul' le_rfl (ENNReal.rpow_sum_le_const_mul_sum_rpow _ _ hp1)
      _ = _ := by ring
  -- integrability / measurability bookkeeping
  have hgm : AEMeasurable (fun w : ℝ × ℝ => ‖G w‖ₑ ^ p) volume :=
    (hGm.enorm).pow_const p
  have hint_tr : ∀ j : ℤ, AEMeasurable (fun z : ℝ × ℝ => ‖G (z.1 + (j : ℝ) * c, z.2)‖ₑ ^ p)
      (volume.restrict (ppWindow c M)) :=
    fun j => (((hTr j).enorm).pow_const p).mono_measure Measure.restrict_le_self
  have hsumG : ∫⁻ z in ppWindow c M, ∑ j ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
      ‖G (z.1 + (j : ℝ) * c, z.2)‖ₑ ^ p =
      ∑ j ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), ∫⁻ z in ppWindow c M, ‖G (z.1 + (j : ℝ) * c, z.2)‖ₑ ^ p :=
    lintegral_finsetSum' _ (fun j _ => hint_tr j)
  have hshift : ∀ j : ℤ, ∫⁻ z in ppWindow c M, ‖G (z.1 + (j : ℝ) * c, z.2)‖ₑ ^ p =
      ∫⁻ z, (ppWindow c M).indicator (1 : ℝ × ℝ → ℝ≥0∞) (z - ((j : ℝ) * c, 0)) * ‖G z‖ₑ ^ p :=
    fun j => ppl_shift_window M ((j : ℝ) * c) (fun w => ‖G w‖ₑ ^ p)
  have hsumI : ∑ j ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
      ∫⁻ z, (ppWindow c M).indicator (1 : ℝ × ℝ → ℝ≥0∞) (z - ((j : ℝ) * c, 0)) * ‖G z‖ₑ ^ p =
      ∫⁻ z, ∑ j ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
        (ppWindow c M).indicator (1 : ℝ × ℝ → ℝ≥0∞) (z - ((j : ℝ) * c, 0)) * ‖G z‖ₑ ^ p := by
    refine (lintegral_finsetSum' _ (fun j _ => ?_)).symm
    exact (((measurable_one.indicator hW).comp (measurable_id.sub_const _)).aemeasurable).mul hgm
  have hpt : ∀ z : ℝ × ℝ, ∑ j ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
      (ppWindow c M).indicator (1 : ℝ × ℝ → ℝ≥0∞) (z - ((j : ℝ) * c, 0)) * ‖G z‖ₑ ^ p ≤
      2 * (M : ℝ≥0∞) * ‖G z‖ₑ ^ p := by
    intro z
    rw [← Finset.sum_mul]
    exact mul_le_mul' (ppl_window_count hc M N z) le_rfl
  have hbound_int : ∫⁻ z, ∑ j ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
      (ppWindow c M).indicator (1 : ℝ × ℝ → ℝ≥0∞) (z - ((j : ℝ) * c, 0)) * ‖G z‖ₑ ^ p ≤
      2 * (M : ℝ≥0∞) * ∫⁻ z, ‖G z‖ₑ ^ p := by
    calc _ ≤ ∫⁻ z, 2 * (M : ℝ≥0∞) * ‖G z‖ₑ ^ p := lintegral_mono hpt
      _ = _ := lintegral_const_mul' _ _ (ENNReal.mul_ne_top (by simp) (ENNReal.natCast_ne_top _))
  -- the whole-plane norm of G
  have hGfin : ∫⁻ z, ‖G z‖ₑ ^ p < ⊤ := by
    have h1 : (∫⁻ z, ‖G z‖ₑ ^ p) ^ (1 / p) < ⊤ := by
      have h2 := hG.eLpNorm_lt_top
      rw [eLpNorm_eq_lintegral_rpow_enorm (ENNReal.ofReal_pos.2 hp0).ne' ENNReal.ofReal_ne_top,
        ENNReal.toReal_ofReal hp0.le] at h2
      exact h2
    rw [← ppl_rpow_rpow_inv hp0 (∫⁻ z, ‖G z‖ₑ ^ p)]
    exact ENNReal.rpow_lt_top_of_nonneg (by positivity) h1.ne
  have hGint : ∫⁻ z, ‖G z‖ₑ ^ p ≤ ENNReal.ofReal ((N : ℝ) * c) * A ^ p := by
    have h1 : eLpNorm G (ENNReal.ofReal p) volume = (∫⁻ z, ‖G z‖ₑ ^ p) ^ (1 / p) := by
      rw [eLpNorm_eq_lintegral_rpow_enorm (ENNReal.ofReal_pos.2 hp0).ne' ENNReal.ofReal_ne_top,
        ENNReal.toReal_ofReal hp0.le]
    have h2 : (∫⁻ z, ‖G z‖ₑ ^ p) ^ (1 / p) ≤ ENNReal.ofReal ((N : ℝ) * c) ^ (1 / p) * A := by
      rw [← h1]; exact hGn
    have h3 := ENNReal.rpow_le_rpow h2 hp0.le
    rw [ppl_rpow_rpow_inv hp0] at h3
    calc ∫⁻ z, ‖G z‖ₑ ^ p ≤ (ENNReal.ofReal ((N : ℝ) * c) ^ (1 / p) * A) ^ p := h3
      _ = ENNReal.ofReal ((N : ℝ) * c) * A ^ p := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ hp0.le, ppl_rpow_rpow_inv hp0]
  -- the averaged integral over the window
  have hQ' : ∫⁻ z in ppWindow c M, ‖ppAvg c N G z‖ₑ ^ p ≤
      (ENNReal.ofReal ((N : ℝ)⁻¹) ^ p * (((Finset.Icc (-(N : ℤ)) (N : ℤ)).card : ℕ) : ℝ≥0∞) ^ (p - 1)) *
        (2 * (M : ℝ≥0∞) * ∫⁻ z, ‖G z‖ₑ ^ p) := by
    calc ∫⁻ z in ppWindow c M, ‖ppAvg c N G z‖ₑ ^ p
        ≤ ∫⁻ z in ppWindow c M, (ENNReal.ofReal ((N : ℝ)⁻¹) ^ p *
            (((Finset.Icc (-(N : ℤ)) (N : ℤ)).card : ℕ) : ℝ≥0∞) ^ (p - 1)) *
              ∑ j ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), ‖G (z.1 + (j : ℝ) * c, z.2)‖ₑ ^ p :=
          lintegral_mono (fun z => hnorm z)
      _ = (ENNReal.ofReal ((N : ℝ)⁻¹) ^ p * (((Finset.Icc (-(N : ℤ)) (N : ℤ)).card : ℕ) : ℝ≥0∞) ^ (p - 1)) *
            ∫⁻ z in ppWindow c M, ∑ j ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), ‖G (z.1 + (j : ℝ) * c, z.2)‖ₑ ^ p :=
          lintegral_const_mul' _ _ hKne
      _ = (ENNReal.ofReal ((N : ℝ)⁻¹) ^ p * (((Finset.Icc (-(N : ℤ)) (N : ℤ)).card : ℕ) : ℝ≥0∞) ^ (p - 1)) *
            ∫⁻ z, ∑ j ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
              (ppWindow c M).indicator (1 : ℝ × ℝ → ℝ≥0∞) (z - ((j : ℝ) * c, 0)) * ‖G z‖ₑ ^ p := by
          rw [hsumG, ← hsumI]
          exact congrArg _ (Finset.sum_congr rfl (fun j _ => hshift j))
      _ ≤ (ENNReal.ofReal ((N : ℝ)⁻¹) ^ p * (((Finset.Icc (-(N : ℤ)) (N : ℤ)).card : ℕ) : ℝ≥0∞) ^ (p - 1)) *
            (2 * (M : ℝ≥0∞) * ∫⁻ z, ‖G z‖ₑ ^ p) := mul_le_mul' le_rfl hbound_int
  -- the scalar constant
  have hscalE : ENNReal.ofReal ((N : ℝ)⁻¹) ^ p * (((Finset.Icc (-(N : ℤ)) (N : ℤ)).card : ℕ) : ℝ≥0∞) ^ (p - 1) *
      ENNReal.ofReal ((N : ℝ) * c) ≤ (3 : ℝ≥0∞) ^ p * ENNReal.ofReal c := by
    have hnn1 : (0 : ℝ) ≤ ((N : ℝ)⁻¹) ^ p := by positivity
    have hnn2 : (0 : ℝ) ≤ (2 * (N : ℝ) + 1) ^ (p - 1) := by positivity
    have hnn3 : (0 : ℝ) ≤ 3 ^ p := by positivity
    rw [hcardE, show (3 : ℝ≥0∞) = ENNReal.ofReal 3 by norm_num,
      ENNReal.ofReal_rpow_of_nonneg (by positivity) hp0.le,
      ENNReal.ofReal_rpow_of_nonneg (by positivity) (by linarith),
      ENNReal.ofReal_rpow_of_nonneg (by norm_num) hp0.le,
      ← ENNReal.ofReal_mul hnn1, ← ENNReal.ofReal_mul (mul_nonneg hnn1 hnn2),
      ← ENNReal.ofReal_mul hnn3]
    exact ENNReal.ofReal_le_ofReal (ppl_real_scalar hp1 hN hc)
  have hR : (3 * ENNReal.ofReal (2 * (M : ℝ) * c) ^ (1 / p) * A) ^ p =
      (3 : ℝ≥0∞) ^ p * ENNReal.ofReal (2 * (M : ℝ) * c) * A ^ p := by
    rw [ENNReal.mul_rpow_of_nonneg _ _ hp0.le, ENNReal.mul_rpow_of_nonneg _ _ hp0.le,
      ppl_rpow_rpow_inv hp0]
  have h2M : ENNReal.ofReal (2 * (M : ℝ) * c) = 2 * (M : ℝ≥0∞) * ENNReal.ofReal c := by
    rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity)]
    simp
  have hT : ∫⁻ z in ppWindow c M, ‖ppAvg c N G z‖ₑ ^ p ≤
      (3 * ENNReal.ofReal (2 * (M : ℝ) * c) ^ (1 / p) * A) ^ p := by
    rw [hR, h2M]
    calc ∫⁻ z in ppWindow c M, ‖ppAvg c N G z‖ₑ ^ p
        ≤ (ENNReal.ofReal ((N : ℝ)⁻¹) ^ p * (((Finset.Icc (-(N : ℤ)) (N : ℤ)).card : ℕ) : ℝ≥0∞) ^ (p - 1)) *
            (2 * (M : ℝ≥0∞) * ∫⁻ z, ‖G z‖ₑ ^ p) := hQ'
      _ ≤ (ENNReal.ofReal ((N : ℝ)⁻¹) ^ p * (((Finset.Icc (-(N : ℤ)) (N : ℤ)).card : ℕ) : ℝ≥0∞) ^ (p - 1)) *
            (2 * (M : ℝ≥0∞) * (ENNReal.ofReal ((N : ℝ) * c) * A ^ p)) :=
          mul_le_mul' le_rfl (mul_le_mul' le_rfl hGint)
      _ = (ENNReal.ofReal ((N : ℝ)⁻¹) ^ p * (((Finset.Icc (-(N : ℤ)) (N : ℤ)).card : ℕ) : ℝ≥0∞) ^ (p - 1) *
            ENNReal.ofReal ((N : ℝ) * c)) * (2 * (M : ℝ≥0∞)) * A ^ p := by ring
      _ ≤ ((3 : ℝ≥0∞) ^ p * ENNReal.ofReal c) * (2 * (M : ℝ≥0∞)) * A ^ p :=
          mul_le_mul' (mul_le_mul' hscalE le_rfl) le_rfl
      _ = (3 : ℝ≥0∞) ^ p * (2 * (M : ℝ≥0∞) * ENNReal.ofReal c) * A ^ p := by ring
  -- conclusion
  have hE : eLpNorm (ppAvg c N G) (ENNReal.ofReal p) (volume.restrict (ppWindow c M)) =
      (∫⁻ z in ppWindow c M, ‖ppAvg c N G z‖ₑ ^ p) ^ (1 / p) := by
    rw [eLpNorm_eq_lintegral_rpow_enorm (ENNReal.ofReal_pos.2 hp0).ne' ENNReal.ofReal_ne_top,
      ENNReal.toReal_ofReal hp0.le]
  have hEle : eLpNorm (ppAvg c N G) (ENNReal.ofReal p) (volume.restrict (ppWindow c M)) ≤
      3 * ENNReal.ofReal (2 * (M : ℝ) * c) ^ (1 / p) * A := by
    rw [hE]
    calc (∫⁻ z in ppWindow c M, ‖ppAvg c N G z‖ₑ ^ p) ^ (1 / p)
        ≤ ((3 * ENNReal.ofReal (2 * (M : ℝ) * c) ^ (1 / p) * A) ^ p) ^ (1 / p) :=
          ENNReal.rpow_le_rpow hT (by positivity)
      _ = _ := ppl_rpow_inv_rpow hp0 _
  have hAE : AEStronglyMeasurable (ppAvg c N G) (volume.restrict (ppWindow c M)) := by
    unfold ppAvg
    exact (((Finset.aestronglyMeasurable_fun_sum _ (fun j _ => hTr j)).const_smul ((N : ℂ)⁻¹)).restrict)
  have hfinQ : (ENNReal.ofReal ((N : ℝ)⁻¹) ^ p * (((Finset.Icc (-(N : ℤ)) (N : ℤ)).card : ℕ) : ℝ≥0∞) ^ (p - 1)) *
      (2 * (M : ℝ≥0∞) * ∫⁻ z, ‖G z‖ₑ ^ p) < ⊤ :=
    ENNReal.mul_lt_top (lt_top_iff_ne_top.2 hKne)
      (ENNReal.mul_lt_top (lt_top_iff_ne_top.2 (ENNReal.mul_ne_top (by norm_num) (ENNReal.natCast_ne_top M))) hGfin)
  have hEfin : eLpNorm (ppAvg c N G) (ENNReal.ofReal p) (volume.restrict (ppWindow c M)) < ⊤ := by
    rw [hE]
    refine ENNReal.rpow_lt_top_of_nonneg (by positivity) ?_
    exact (lt_of_le_of_lt hQ' hfinQ).ne
  exact ⟨⟨hAE, hEfin⟩, hEle⟩

#print axioms UnforcedLeray.Short.IIb.ppl_avg_bound
