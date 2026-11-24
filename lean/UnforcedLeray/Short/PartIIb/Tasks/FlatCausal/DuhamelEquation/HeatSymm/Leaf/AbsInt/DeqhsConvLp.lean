import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T12_7_3_1
import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.FlatHeatContraction

/-!
# Part II-b, leaf `DeqhsConvLp` (SP 1923-1927): `L^r(cell)` bound for `convAbs`

Source of record: `the November 2 reference manuscript`, lines 1923-1927.
Route.
* `g'` is the floor-shifted, everywhere `c`-periodic strongly measurable copy of a representative of `g`;
  `convAbs θ g = convAbs θ g'` pointwise (quasi measure preserving `w ↦ z - w`).
* Jensen/Hölder with the unit-mass kernel: `(∫⁻ K a)^r ≤ ∫⁻ K a^r` for `∫⁻ K = 1`, `r > 1`.
* Tonelli on the cell and translation invariance of the periodic function `‖g'‖^r` on the cell.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

/-- Jensen for a unit-mass weight: `(∫⁻ K a)^r ≤ ∫⁻ K a^r` for `r > 1`. -/
theorem holder_power_lint {α : Type*} [MeasurableSpace α] (μ : Measure α) {r : ℝ} (hr : 1 < r)
    (K a : α → ℝ≥0∞) (hKm : Measurable K) (ha : Measurable a) (hK : ∫⁻ x, K x ∂μ = 1) :
    (∫⁻ x, K x * a x ∂μ) ^ r ≤ ∫⁻ x, K x * a x ^ r ∂μ := by
  have hpq : r.HolderConjugate (Real.conjExponent r) := Real.HolderConjugate.conjExponent hr
  have hinv := (Real.holderConjugate_iff.1 hpq).2
  have hr0 : 0 < r := by linarith
  have hri : r⁻¹ < 1 := inv_lt_one_of_one_lt₀ hr
  have hsi : 0 < (Real.conjExponent r)⁻¹ := by linarith
  have hs0 : 0 < Real.conjExponent r := inv_pos.1 hsi
  have e1 : ∀ x, K x ^ (1 / r) * a x * K x ^ (1 / Real.conjExponent r) = K x * a x := by
    intro x
    have hadd : K x ^ (1 / r + 1 / Real.conjExponent r) =
        K x ^ (1 / r) * K x ^ (1 / Real.conjExponent r) :=
      ENNReal.rpow_add_of_nonneg (1 / r) (1 / Real.conjExponent r)
        (one_div_nonneg.2 hr0.le) (one_div_nonneg.2 hs0.le)
    have h1 : (1 / r + 1 / Real.conjExponent r) = 1 := by
      rw [one_div, one_div]; exact hinv
    rw [h1, ENNReal.rpow_one] at hadd
    calc K x ^ (1 / r) * a x * K x ^ (1 / Real.conjExponent r)
        = (K x ^ (1 / r) * K x ^ (1 / Real.conjExponent r)) * a x := by ring
      _ = K x * a x := by rw [← hadd]
  have e2 : ∀ x, (K x ^ (1 / r) * a x) ^ r = K x * a x ^ r := by
    intro x
    rw [ENNReal.mul_rpow_of_nonneg _ _ hr0.le, ← ENNReal.rpow_mul, one_div,
      inv_mul_cancel₀ hr0.ne', ENNReal.rpow_one]
  have e3 : ∀ x, (K x ^ (1 / Real.conjExponent r)) ^ Real.conjExponent r = K x := by
    intro x
    rw [← ENNReal.rpow_mul, one_div, inv_mul_cancel₀ hs0.ne', ENNReal.rpow_one]
  have hfm : AEMeasurable (fun x => K x ^ (1 / r) * a x) μ :=
    ((hKm.pow_const _).mul ha).aemeasurable
  have hgm : AEMeasurable (fun x => K x ^ (1 / Real.conjExponent r)) μ :=
    (hKm.pow_const _).aemeasurable
  have hH := ENNReal.lintegral_mul_le_Lp_mul_Lq μ hpq hfm hgm
  simp only [Pi.mul_apply, e1, e2, e3, hK, ENNReal.one_rpow, mul_one] at hH
  have hL : ∫⁻ x, K x * a x ∂μ ≤ (∫⁻ x, K x * a x ^ r ∂μ) ^ (1 / r) := by
    simpa using hH
  have hfin : (∫⁻ x, K x * a x ∂μ) ^ r ≤ ((∫⁻ x, K x * a x ^ r ∂μ) ^ (1 / r)) ^ r :=
    ENNReal.rpow_le_rpow hL hr0.le
  rw [← ENNReal.rpow_mul, one_div, inv_mul_cancel₀ hr0.ne', ENNReal.rpow_one] at hfin
  exact hfin

/-- **Leaf `PartII-b:T12/7/3/1/3`** (SP 1923-1927): `convAbs θ g` has finite `L^r` norm on the cell. -/
theorem deqhsConvLp : UnforcedLeray.Short.IIb.DeqhsConvLp := by
  intro c r g hc hr hg θ hθ
  have hr1 : 1 < r := hr
  have hr0 : 0 < r := by linarith
  obtain ⟨hper, hgm, hfin⟩ := hg
  -- (1) a strongly measurable representative `g₀` of `g`
  obtain ⟨g₀, hg₀m, hg₀⟩ : ∃ g₀ : ℝ × ℝ → CMerid, StronglyMeasurable g₀ ∧
      ∀ᵐ z : ℝ × ℝ, g₀ z = g z :=
    ⟨hgm.mk g, hgm.stronglyMeasurable_mk, hgm.ae_eq_mk.symm⟩
  -- (2) the floor-shifted, everywhere `c`-periodic copy `g'`
  have hc0 : c ≠ 0 := hc.ne'
  have hfl : Measurable (fun z : ℝ × ℝ => ((⌊z.1 / c⌋ : ℤ) : ℝ)) :=
    (measurable_of_countable (fun n : ℤ => (n : ℝ))).comp
      (Int.measurable_floor.comp (measurable_fst.div_const c))
  have hS : Measurable (fun z : ℝ × ℝ => (z.1 - ((⌊z.1 / c⌋ : ℤ) : ℝ) * c, z.2)) :=
    (measurable_fst.sub (hfl.mul_const c)).prodMk measurable_snd
  obtain ⟨g', hg'def⟩ : ∃ g' : ℝ × ℝ → CMerid, ∀ z : ℝ × ℝ,
      g' z = g₀ (z.1 - ((⌊z.1 / c⌋ : ℤ) : ℝ) * c, z.2) :=
    ⟨fun z => g₀ (z.1 - ((⌊z.1 / c⌋ : ℤ) : ℝ) * c, z.2), fun _ => rfl⟩
  have hper' : ∀ z : ℝ × ℝ, g' (z.1 + c, z.2) = g' z := by
    intro z
    rw [hg'def, hg'def]
    dsimp only
    have hfl1 : ⌊(z.1 + c) / c⌋ = ⌊z.1 / c⌋ + 1 := by
      rw [add_div, div_self hc0]
      exact Int.floor_add_one _
    rw [hfl1]
    have e : z.1 + c - ((⌊z.1 / c⌋ + 1 : ℤ) : ℝ) * c =
        z.1 - ((⌊z.1 / c⌋ : ℤ) : ℝ) * c := by
      push_cast; ring
    rw [e]
  have hg'm : StronglyMeasurable g' := by
    have hfun : g' = fun z : ℝ × ℝ => g₀ (z.1 - ((⌊z.1 / c⌋ : ℤ) : ℝ) * c, z.2) :=
      funext hg'def
    rw [hfun]
    exact hg₀m.comp_measurable hS
  have hA : ∀ k : ℤ, ∀ᵐ z : ℝ × ℝ, g₀ (z.1 - (k : ℝ) * c, z.2) = g z := by
    intro k
    have h1 : ∀ᵐ z : ℝ × ℝ, g₀ (z.1 + ((-k : ℤ) : ℝ) * c, z.2) =
        g (z.1 + ((-k : ℤ) : ℝ) * c, z.2) :=
      (UnforcedLeray.Cyl.measurePreserving_shift (((-k : ℤ) : ℝ) * c)).quasiMeasurePreserving.ae
        hg₀
    filter_upwards [h1, flatHeat_ae_intShift hper (-k)] with z h1z h2z
    have e : z.1 - (k : ℝ) * c = z.1 + ((-k : ℤ) : ℝ) * c := by
      push_cast; ring
    rw [e, h1z, h2z]
  have hall : ∀ᵐ z : ℝ × ℝ, ∀ k : ℤ, g₀ (z.1 - (k : ℝ) * c, z.2) = g z :=
    (ae_all_iff (p := fun (z : ℝ × ℝ) (k : ℤ) => g₀ (z.1 - (k : ℝ) * c, z.2) = g z)).2 hA
  have hgg' : ∀ᵐ z : ℝ × ℝ, g' z = g z := by
    filter_upwards [hall] with z hz
    rw [hg'def]
    exact hz ⌊z.1 / c⌋
  have hgg2 : ∀ᵐ z : ℝ × ℝ, g z = g' z := hgg'.mono fun z hz => hz.symm
  -- (3) `convAbs θ g` equals `convAbs θ g'` at every point
  have hrep : ∀ z : ℝ × ℝ, convAbs θ g z = convAbs θ g' z := by
    intro z
    unfold convAbs
    refine lintegral_congr_ae ?_
    have hq := quasiMeasurePreserving_sub_left_of_right_invariant (volume : Measure (ℝ × ℝ)) z
    filter_upwards [hq.ae hgg'] with w hw
    simp only [hw]
  -- (4) the unit-mass kernel
  have hKc : Continuous (flatHeatKernel θ) := by
    unfold flatHeatKernel
    fun_prop
  have hKnn : ∀ w : ℝ × ℝ, 0 ≤ flatHeatKernel θ w := by
    intro w
    unfold flatHeatKernel
    have h1 : (0 : ℝ) ≤ (4 * Real.pi * θ)⁻¹ := by
      apply inv_nonneg.2
      exact mul_nonneg (mul_nonneg (by norm_num) Real.pi_pos.le) hθ.le
    exact mul_nonneg h1 (Real.exp_pos _).le
  have hK1 : ∫⁻ w, ENNReal.ofReal (flatHeatKernel θ w) = 1 := by
    have h := flatHeat_eLpNorm_kernel_one hθ
    rw [eLpNorm_one_eq_lintegral_enorm] at h
    have hcongr : ∫⁻ w, ‖flatHeatKernel θ w‖ₑ = ∫⁻ w, ENNReal.ofReal (flatHeatKernel θ w) :=
      lintegral_congr fun w => Real.enorm_of_nonneg (hKnn w)
    rw [← hcongr]
    exact h
  have hKm : Measurable (fun w : ℝ × ℝ => ENNReal.ofReal (flatHeatKernel θ w)) :=
    ENNReal.measurable_ofReal.comp hKc.measurable
  have hg'meas : Measurable g' := hg'm.measurable
  -- (5) Jensen pointwise
  have hJ : ∀ z : ℝ × ℝ, (convAbs θ g' z) ^ r ≤
      ∫⁻ w, ENNReal.ofReal (flatHeatKernel θ w) * ‖g' (z - w)‖ₑ ^ r := by
    intro z
    have ha : Measurable (fun w : ℝ × ℝ => ‖g' (z - w)‖ₑ) :=
      (hg'meas.comp (measurable_const.sub measurable_id)).enorm
    unfold convAbs
    exact holder_power_lint volume hr1 (fun w => ENNReal.ofReal (flatHeatKernel θ w))
      (fun w => ‖g' (z - w)‖ₑ) hKm ha hK1
  -- (6) the periodic function `‖g'‖^r`
  have hPer2 : UnforcedLeray.Cyl.IsPeriodic c (fun z => ‖g' z‖ₑ ^ r) := fun z => by
    simp only [hper' z]
  have hmeasJ : Measurable (fun p : (ℝ × ℝ) × (ℝ × ℝ) =>
      ENNReal.ofReal (flatHeatKernel θ p.2) * ‖g' (p.1 - p.2)‖ₑ ^ r) :=
    (hKm.comp measurable_snd).mul
      (((hg'meas.comp (measurable_fst.sub measurable_snd)).enorm).pow_const r)
  have hcellJ : ∫⁻ z in UnforcedLeray.Cyl.cell c, (convAbs θ g' z) ^ r ≤
      ∫⁻ z in UnforcedLeray.Cyl.cell c,
        ∫⁻ w, ENNReal.ofReal (flatHeatKernel θ w) * ‖g' (z - w)‖ₑ ^ r :=
    lintegral_mono fun z => hJ z
  have hswap : ∫⁻ z in UnforcedLeray.Cyl.cell c,
        ∫⁻ w, ENNReal.ofReal (flatHeatKernel θ w) * ‖g' (z - w)‖ₑ ^ r =
      ∫⁻ w, ∫⁻ z in UnforcedLeray.Cyl.cell c,
        ENNReal.ofReal (flatHeatKernel θ w) * ‖g' (z - w)‖ₑ ^ r :=
    lintegral_lintegral_swap hmeasJ.aemeasurable
  have hinner : ∀ w : ℝ × ℝ, ∫⁻ z in UnforcedLeray.Cyl.cell c,
        ENNReal.ofReal (flatHeatKernel θ w) * ‖g' (z - w)‖ₑ ^ r =
      ENNReal.ofReal (flatHeatKernel θ w) *
        ∫⁻ z in UnforcedLeray.Cyl.cell c, ‖g' z‖ₑ ^ r := by
    intro w
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    congr 1
    have key := UnforcedLeray.Cyl.lintegral_cell_comp_add hc hPer2 (-w)
    simpa only [sub_eq_add_neg] using key
  have hbound : ∫⁻ z in UnforcedLeray.Cyl.cell c, (convAbs θ g' z) ^ r ≤
      ∫⁻ z in UnforcedLeray.Cyl.cell c, ‖g' z‖ₑ ^ r := by
    calc ∫⁻ z in UnforcedLeray.Cyl.cell c, (convAbs θ g' z) ^ r
        ≤ _ := hcellJ
      _ = ∫⁻ w, ∫⁻ z in UnforcedLeray.Cyl.cell c,
          ENNReal.ofReal (flatHeatKernel θ w) * ‖g' (z - w)‖ₑ ^ r := hswap
      _ = ∫⁻ w, ENNReal.ofReal (flatHeatKernel θ w) *
          ∫⁻ z in UnforcedLeray.Cyl.cell c, ‖g' z‖ₑ ^ r := lintegral_congr fun w => hinner w
      _ = (∫⁻ w, ENNReal.ofReal (flatHeatKernel θ w)) *
          ∫⁻ z in UnforcedLeray.Cyl.cell c, ‖g' z‖ₑ ^ r := lintegral_mul_const _ hKm
      _ = ∫⁻ z in UnforcedLeray.Cyl.cell c, ‖g' z‖ₑ ^ r := by rw [hK1, one_mul]
  -- (7) finiteness of the periodic cell integral of `‖g'‖^r`
  have hgeq : eLpNorm g' (ENNReal.ofReal r) (UnforcedLeray.Cyl.avgμ c) < ⊤ := by
    have hgeq' : eLpNorm g (ENNReal.ofReal r) (UnforcedLeray.Cyl.avgμ c) =
        eLpNorm g' (ENNReal.ofReal r) (UnforcedLeray.Cyl.avgμ c) := by
      refine eLpNorm_congr_ae ?_
      unfold UnforcedLeray.Cyl.avgμ UnforcedLeray.Cyl.cellμ
      exact Measure.ae_smul_measure (ae_restrict_of_ae hgg2) _
    rw [← hgeq']
    exact hfin
  have hAvg : ∫⁻ z, ‖g' z‖ₑ ^ r ∂(UnforcedLeray.Cyl.avgμ c) < ⊤ := by
    have h := hgeq
    rw [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top
      (ENNReal.ofReal_pos.2 hr0).ne' ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal hr0.le] at h
    exact h
  have hCell : ∫⁻ z in UnforcedLeray.Cyl.cell c, ‖g' z‖ₑ ^ r < ⊤ := by
    unfold UnforcedLeray.Cyl.avgμ UnforcedLeray.Cyl.cellμ at hAvg
    rw [lintegral_smul_measure] at hAvg
    have hpos : 0 < ENNReal.ofReal c⁻¹ := ENNReal.ofReal_pos.2 (inv_pos.2 hc)
    have hc0' : ENNReal.ofReal c⁻¹ ≠ 0 := hpos.ne'
    have hct : ENNReal.ofReal c⁻¹ ≠ ⊤ := ENNReal.ofReal_ne_top
    calc ∫⁻ z in UnforcedLeray.Cyl.cell c, ‖g' z‖ₑ ^ r
        = (ENNReal.ofReal c⁻¹)⁻¹ * (ENNReal.ofReal c⁻¹ *
            ∫⁻ z in UnforcedLeray.Cyl.cell c, ‖g' z‖ₑ ^ r) := by
          rw [← mul_assoc, ENNReal.inv_mul_cancel hc0' hct, one_mul]
      _ < ⊤ := ENNReal.mul_lt_top (ENNReal.inv_lt_top.2 hpos) hAvg
  -- (8) conclusion
  unfold UnforcedLeray.Cyl.cellμ
  rw [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top (ENNReal.ofReal_pos.2 hr0).ne'
    ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal hr0.le]
  simp only [hrep, enorm_eq_self]
  exact lt_of_le_of_lt hbound hCell

end UnforcedLeray.Short.IIb
