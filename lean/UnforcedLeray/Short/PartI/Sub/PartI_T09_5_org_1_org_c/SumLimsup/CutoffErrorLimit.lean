import UnforcedLeray.Short.PartI.Sub.PartI_T09_5_org_1_org_c.SumLimsup
import UnforcedLeray.Short.PartI.Sub.PartI_T04_5
import UnforcedLeray.Short.PartI.Tasks.TrainCutoffEnergyProof.CellToolkit
import UnforcedLeray.Short.PartI.Tasks.ClassicalOdd.EtaCutoffFacts
import UnforcedLeray.Short.PartI.Tasks.ClassicalOdd.ClassicalEnergyBound.StripBound

/-!
# `PartI:T09/5/org/1/org/c/1/2`: the limit `R → ∞` in a cutoff identity with a boundary error

Source: `the November 2 reference manuscript`, lines 283-286.  Proves the leaf
`CutoffErrorLimit` of `Sub/PartI_T09_5_org_1_org_c/SumLimsup.lean`.

Route.  Write `I_X(R) = ∫_cell χ_R X` and `E(R) = ∫_cell χ_R' a b`.  The identity gives
`I_F = I_G - 2 E`, and `|E| ≤ K₀ c M²` uniformly (`ebStripBound`).

* If `F` and `G` are both integrable, then `E(R) → 0` (`cel_decay`: the strip estimate with
  `|χ_R'| ≤ (C₀/R) √χ_R`, `b² ≤ F` and the Young bound `|b| ≤ (√R F + 1/√R)/2`), so
  `∫F = ∫G` by `tendsto_cutoff_integral` and uniqueness of limits.
* If one of them is not integrable, the uniform bound and monotone truncation
  (`cel_mc_upper`) force the other one to be non-integrable too; then both `lintegral`s are `⊤`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartI

open UnforcedLeray.Cyl (Plane)

/-- Integrability on the cell of a cutoff times a continuous function. -/
theorem cel_cut_integrable (c R : ℝ) (hc : 0 < c) (hR : 0 < R) (χ : ℝ → ℝ) (hχ : Continuous χ)
    (hχz : ∀ η : ℝ, 2 * R ≤ |η| → χ η = 0) (X : Plane → ℝ) (hX : Continuous X) :
    IntegrableOn (fun z : Plane => χ z.2 * X z) (Cyl.cell c) :=
  cellIntegrable_of_support c R hc hR _ ((hχ.comp continuous_snd).mul hX)
    (fun z hz => by simp only [hχz z.2 hz, zero_mul])

/-- For a continuous nonnegative function, integrability on the cell is finiteness of the
`lintegral` of its positive part. -/
theorem cel_integrable_iff (c : ℝ) (X : Plane → ℝ) (hX : Continuous X) (hX0 : ∀ z, 0 ≤ X z) :
    IntegrableOn X (Cyl.cell c) ↔ ∫⁻ z in Cyl.cell c, ENNReal.ofReal (X z) < ⊤ := by
  have hae : 0 ≤ᵐ[volume.restrict (Cyl.cell c)] X := Filter.Eventually.of_forall hX0
  constructor
  · intro h
    exact (hasFiniteIntegral_iff_ofReal hae).1 h.2
  · intro h
    exact ⟨hX.aestronglyMeasurable, (hasFiniteIntegral_iff_ofReal hae).2 h⟩

/-- Truncations `n ↦ 1_{|η| ≤ n} ofReal f` of a nonnegative function. -/
def celTrunc (f : Plane → ℝ) (n : ℕ) : Plane → ℝ≥0∞ :=
  {z : Plane | |z.2| ≤ (n : ℝ)}.indicator (fun z => ENNReal.ofReal (f z))

theorem celTrunc_measurable (f : Plane → ℝ) (hf : Continuous f) (n : ℕ) :
    Measurable (celTrunc f n) := by
  have hS : MeasurableSet {z : Plane | |z.2| ≤ (n : ℝ)} :=
    (isClosed_le (continuous_abs.comp continuous_snd) continuous_const).measurableSet
  exact (hf.measurable.ennreal_ofReal).indicator hS

theorem celTrunc_mono (f : Plane → ℝ) (hf0 : ∀ z, 0 ≤ f z) : Monotone (celTrunc f) := by
  intro n m hnm z
  unfold celTrunc
  apply Set.indicator_le_indicator_of_subset _ (fun _ => zero_le)
  intro w hw
  have h1 : (n : ℝ) ≤ m := by exact_mod_cast hnm
  exact le_trans (show |w.2| ≤ (n : ℝ) from hw) h1

theorem celTrunc_sup (f : Plane → ℝ) (hf0 : ∀ z, 0 ≤ f z) (z : Plane) :
    ⨆ n, celTrunc f n z = ENNReal.ofReal (f z) := by
  apply le_antisymm
  · exact iSup_le fun n => by
      unfold celTrunc
      by_cases hz : z ∈ {z : Plane | |z.2| ≤ (n : ℝ)}
      · rw [Set.indicator_of_mem hz]
      · rw [Set.indicator_of_notMem hz]
        exact zero_le
  · obtain ⟨n, hn⟩ := exists_nat_ge |z.2|
    refine le_iSup_of_le n (le_of_eq ?_)
    unfold celTrunc
    rw [Set.indicator_of_mem (show z ∈ {z : Plane | |z.2| ≤ (n : ℝ)} from hn)]

/-- **Monotone truncation.** If `∫_cell χ_R f ≤ B` for all large `R`, then `∫_cell ofReal f ≤ ofReal B`. -/
theorem cel_mc_upper (c : ℝ) (hc : 0 < c) (hη : EtaCutoffFacts) (f : Plane → ℝ)
    (hf : Continuous f) (hf0 : ∀ z, 0 ≤ f z) (R0 B : ℝ) (hR0 : 1 ≤ R0)
    (hB : ∀ R : ℝ, R0 ≤ R → ∫ z in Cyl.cell c, etaCutoff R z.2 * f z ≤ B) :
    ∫⁻ z in Cyl.cell c, ENNReal.ofReal (f z) ≤ ENNReal.ofReal B := by
  obtain ⟨C₀, hC₀, hfac⟩ := hη
  have hbound : ∀ n : ℕ, ∫⁻ z in Cyl.cell c, celTrunc f n z ≤ ENNReal.ofReal B := by
    intro n
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have hR1 : 1 ≤ R0 + n := by linarith
    obtain ⟨hsm, h01, h1, hz, -⟩ := hfac (R0 + n) hR1
    have hle : ∀ z : Plane, celTrunc f n z ≤ ENNReal.ofReal (etaCutoff (R0 + n) z.2 * f z) := by
      intro z
      unfold celTrunc
      by_cases hzn : z ∈ {z : Plane | |z.2| ≤ (n : ℝ)}
      · have hχ1 : etaCutoff (R0 + n) z.2 = 1 := by
          apply h1 z.2
          have hzn' : |z.2| ≤ (n : ℝ) := hzn
          linarith
        rw [Set.indicator_of_mem hzn, hχ1, one_mul]
      · rw [Set.indicator_of_notMem hzn]
        exact zero_le
    have hint : Integrable (fun z : Plane => etaCutoff (R0 + n) z.2 * f z)
        (volume.restrict (Cyl.cell c)) :=
      cel_cut_integrable c (R0 + n) hc (by linarith) _ hsm.continuous hz f hf
    have hnn : 0 ≤ᵐ[volume.restrict (Cyl.cell c)] (fun z : Plane => etaCutoff (R0 + n) z.2 * f z) :=
      Filter.Eventually.of_forall fun z => mul_nonneg (h01 z.2).1 (hf0 z)
    calc ∫⁻ z in Cyl.cell c, celTrunc f n z
        ≤ ∫⁻ z in Cyl.cell c, ENNReal.ofReal (etaCutoff (R0 + n) z.2 * f z) :=
          lintegral_mono fun z => hle z
      _ = ENNReal.ofReal (∫ z in Cyl.cell c, etaCutoff (R0 + n) z.2 * f z) :=
          (ofReal_integral_eq_lintegral_ofReal hint hnn).symm
      _ ≤ ENNReal.ofReal B := ENNReal.ofReal_le_ofReal (hB (R0 + n) (by linarith))
  calc ∫⁻ z in Cyl.cell c, ENNReal.ofReal (f z)
      = ∫⁻ z in Cyl.cell c, ⨆ n, celTrunc f n z :=
        lintegral_congr fun z => (celTrunc_sup f hf0 z).symm
    _ = ⨆ n, ∫⁻ z in Cyl.cell c, celTrunc f n z :=
        lintegral_iSup (celTrunc_measurable f hf) (celTrunc_mono f hf0)
    _ ≤ ENNReal.ofReal B := iSup_le hbound


/-- A continuous nonnegative `X` is integrable on the cell when `∫χ_R X ≤ ∫χ_R Y + K` for `R ≥ 1` and
`Y` is integrable. -/
theorem cel_integrable_of_bound (c : ℝ) (hc : 0 < c) (hη : EtaCutoffFacts) (X Y : Plane → ℝ)
    (hX : Continuous X) (hX0 : ∀ z, 0 ≤ X z) (hY : IntegrableOn Y (Cyl.cell c)) (K : ℝ)
    (hrel : ∀ R : ℝ, 1 ≤ R →
      (∫ z in Cyl.cell c, etaCutoff R z.2 * X z) ≤ (∫ z in Cyl.cell c, etaCutoff R z.2 * Y z) + K) :
    IntegrableOn X (Cyl.cell c) := by
  have hT := tendsto_cutoff_integral hη c Y hY
  have hev : ∀ᶠ R in atTop, (∫ z in Cyl.cell c, etaCutoff R z.2 * Y z) <
      (∫ z in Cyl.cell c, Y z) + 1 :=
    hT.eventually (gt_mem_nhds (lt_add_one _))
  obtain ⟨R0, hR0⟩ := eventually_atTop.1 hev
  have hB : ∀ R : ℝ, max R0 1 ≤ R →
      ∫ z in Cyl.cell c, etaCutoff R z.2 * X z ≤ (∫ z in Cyl.cell c, Y z) + 1 + K := by
    intro R hR
    have h1 : 1 ≤ R := le_trans (le_max_right _ _) hR
    have h2 : R0 ≤ R := le_trans (le_max_left _ _) hR
    linarith [hrel R h1, hR0 R h2]
  have hmc := cel_mc_upper c hc hη X hX hX0 (max R0 1) _ (le_max_right _ _) hB
  exact (cel_integrable_iff c X hX hX0).2 (lt_of_le_of_lt hmc ENNReal.ofReal_lt_top)

/-- Young's inequality on the box: `|b| ≤ (√R F + 1/√R)/2` when `b² ≤ F`. -/
theorem cel_young (R : ℝ) (hR : 0 < R) (F b : ℝ) (hb : b ^ 2 ≤ F) :
    |b| ≤ (Real.sqrt R * F + 1 / Real.sqrt R) / 2 := by
  have hs : 0 < Real.sqrt R := Real.sqrt_pos.2 hR
  have hs2 : Real.sqrt R ^ 2 = R := Real.sq_sqrt hR.le
  have hu : Real.sqrt R * (1 / Real.sqrt R) = 1 := by field_simp
  have h1 : Real.sqrt R ^ 2 * b ^ 2 ≤ Real.sqrt R ^ 2 * F :=
    mul_le_mul_of_nonneg_left hb (sq_nonneg _)
  have hab2 : Real.sqrt R ^ 2 * |b| ^ 2 = Real.sqrt R ^ 2 * b ^ 2 := by rw [sq_abs]
  have key : 2 * Real.sqrt R * |b| ≤ Real.sqrt R ^ 2 * F + 1 := by
    nlinarith [sq_nonneg (Real.sqrt R * |b| - 1), hab2, h1]
  have h2 : Real.sqrt R * (2 * |b|) ≤ Real.sqrt R * (Real.sqrt R * F + 1 / Real.sqrt R) := by
    nlinarith [key, hu]
  have h3 := le_of_mul_le_mul_left h2 hs
  linarith

/-- The algebra of the strip bound. -/
theorem cel_identity (C₀ M I c R s : ℝ) (hs : 0 < s) (hR : s ^ 2 = R) :
    C₀ * M / (2 * R) * (s * I) + C₀ * M / (2 * R) / s * (c * (4 * R)) =
      C₀ * M * (I + 4 * c) / 2 / s := by
  subst hR
  have hs0 : s ≠ 0 := hs.ne'
  field_simp

/-- **Decay of the boundary error.** If `F` is integrable on the cell, the cutoff error tends to `0`. -/
theorem cel_decay (c : ℝ) (hc : 0 < c) (hη : EtaCutoffFacts) (M : ℝ) (F a b : Plane → ℝ)
    (hF0 : ∀ z, 0 ≤ F z) (hFi : IntegrableOn F (Cyl.cell c)) (hbF : ∀ z, b z ^ 2 ≤ F z)
    (haM : ∀ z, |a z| ≤ M) :
    Tendsto (fun R : ℝ => ∫ z in Cyl.cell c, deriv (etaCutoff R) z.2 * (a z * b z))
      atTop (𝓝 0) := by
  obtain ⟨C₀, hC₀, hfac⟩ := hη
  have hM0 : 0 ≤ M := le_trans (abs_nonneg _) (haM 0)
  have hbound : ∀ R : ℝ, 1 ≤ R →
      |∫ z in Cyl.cell c, deriv (etaCutoff R) z.2 * (a z * b z)| ≤
        C₀ * M * ((∫ z in Cyl.cell c, F z) + 4 * c) / 2 / Real.sqrt R := by
    intro R hR
    obtain ⟨-, h01, -, hz, hd⟩ := hfac R hR
    have hR0 : 0 < R := by linarith
    have hsq : 0 < Real.sqrt R := Real.sqrt_pos.2 hR0
    have hsq2 : Real.sqrt R ^ 2 = R := Real.sq_sqrt hR0.le
    have hBm : MeasurableSet (Ico (-c / 2) (c / 2) ×ˢ Icc (-(2 * R)) (2 * R)) :=
      measurableSet_Ico.prod measurableSet_Icc
    have hBsub : Ico (-c / 2) (c / 2) ×ˢ Icc (-(2 * R)) (2 * R) ⊆ Cyl.cell c :=
      Set.prod_mono subset_rfl (subset_univ _)
    -- the pointwise bound on the cell
    have hpt : ∀ z : Plane, z ∈ Cyl.cell c →
        |deriv (etaCutoff R) z.2 * (a z * b z)| ≤
          C₀ * M / (2 * R) * (Real.sqrt R * F z) +
            C₀ * M / (2 * R) / Real.sqrt R *
              (Ico (-c / 2) (c / 2) ×ˢ Icc (-(2 * R)) (2 * R)).indicator (fun _ => (1 : ℝ)) z := by
      intro z hzc
      by_cases hzB : z ∈ Ico (-c / 2) (c / 2) ×ˢ Icc (-(2 * R)) (2 * R)
      · have hzI := (Set.mem_prod.1 hzB).2
        have hd' : |deriv (etaCutoff R) z.2| ≤ C₀ / R := by
          have h2 := hd z.2
          have hsq1 : Real.sqrt (etaCutoff R z.2) ≤ 1 := Real.sqrt_le_one.2 (h01 z.2).2
          calc |deriv (etaCutoff R) z.2|
              ≤ C₀ / R * Real.sqrt (etaCutoff R z.2) := h2
            _ ≤ C₀ / R * 1 := mul_le_mul_of_nonneg_left hsq1 (div_nonneg hC₀ hR0.le)
            _ = C₀ / R := mul_one _
        have hb' := cel_young R hR0 (F z) (b z) (hbF z)
        have hind1 : (Ico (-c / 2) (c / 2) ×ˢ Icc (-(2 * R)) (2 * R)).indicator
            (fun _ => (1 : ℝ)) z = 1 := Set.indicator_of_mem hzB _
        rw [hind1, mul_one, abs_mul, abs_mul]
        have hmain : |deriv (etaCutoff R) z.2| * (|a z| * |b z|) ≤
            C₀ / R * (M * ((Real.sqrt R * F z + 1 / Real.sqrt R) / 2)) :=
          mul_le_mul hd' (mul_le_mul (haM z) hb' (abs_nonneg _) hM0)
            (by positivity) (by positivity)
        calc |deriv (etaCutoff R) z.2| * (|a z| * |b z|)
            ≤ C₀ / R * (M * ((Real.sqrt R * F z + 1 / Real.sqrt R) / 2)) := hmain
          _ = C₀ * M / (2 * R) * (Real.sqrt R * F z) +
              C₀ * M / (2 * R) / Real.sqrt R := by ring
      · have h2R : 2 * R ≤ |z.2| := by
          by_contra hlt
          push Not at hlt
          exact hzB (Set.mem_prod.2 ⟨(Set.mem_prod.1 hzc).1, abs_le.1 hlt.le⟩)
        have hd0 : deriv (etaCutoff R) z.2 = 0 := by
          have h2 := hd z.2
          rw [hz z.2 h2R, Real.sqrt_zero, mul_zero] at h2
          exact abs_nonpos_iff.1 h2
        rw [hd0, zero_mul, abs_zero, Set.indicator_of_notMem hzB, mul_zero, add_zero]
        apply mul_nonneg
        · exact div_nonneg (mul_nonneg hC₀ hM0) (by linarith)
        · exact mul_nonneg hsq.le (hF0 z)
    -- integrability of the dominating function
    have hfin : (volume.restrict (Cyl.cell c)) (Ico (-c / 2) (c / 2) ×ˢ Icc (-(2 * R)) (2 * R)) ≠ ⊤ := by
      rw [Measure.restrict_apply hBm]
      exact ne_top_of_le_ne_top (ebStripBox_ne_top c R) (measure_mono Set.inter_subset_left)
    have hind : Integrable ((Ico (-c / 2) (c / 2) ×ˢ Icc (-(2 * R)) (2 * R)).indicator
        (fun _ => (1 : ℝ))) (volume.restrict (Cyl.cell c)) :=
      (integrable_indicator_iff hBm).2 (integrableOn_const hfin)
    have hgi : Integrable (fun z : Plane => C₀ * M / (2 * R) * (Real.sqrt R * F z) +
        C₀ * M / (2 * R) / Real.sqrt R *
          (Ico (-c / 2) (c / 2) ×ˢ Icc (-(2 * R)) (2 * R)).indicator (fun _ => (1 : ℝ)) z)
        (volume.restrict (Cyl.cell c)) :=
      ((hFi.const_mul (Real.sqrt R)).const_mul (C₀ * M / (2 * R))).add
        (hind.const_mul (C₀ * M / (2 * R) / Real.sqrt R))
    have hnorm := norm_integral_le_of_norm_le (f := fun z : Plane =>
        deriv (etaCutoff R) z.2 * (a z * b z)) hgi
      (by
        filter_upwards [ae_restrict_mem (Cyl.measurableSet_cell c)] with z hz
        rw [Real.norm_eq_abs]
        exact hpt z hz)
    have hI1 : ∫ z in Cyl.cell c, (Ico (-c / 2) (c / 2) ×ˢ Icc (-(2 * R)) (2 * R)).indicator
        (fun _ => (1 : ℝ)) z = c * (4 * R) := by
      have h := integral_indicator_one (μ := volume.restrict (Cyl.cell c)) hBm
      rw [measureReal_restrict_apply hBm, Set.inter_eq_left.2 hBsub,
        ebStripBox_real c R hc.le hR0.le] at h
      exact h
    have hcomp : ∫ z in Cyl.cell c, (C₀ * M / (2 * R) * (Real.sqrt R * F z) +
        C₀ * M / (2 * R) / Real.sqrt R *
          (Ico (-c / 2) (c / 2) ×ˢ Icc (-(2 * R)) (2 * R)).indicator (fun _ => (1 : ℝ)) z) =
        C₀ * M / (2 * R) * (Real.sqrt R * ∫ z in Cyl.cell c, F z) +
          C₀ * M / (2 * R) / Real.sqrt R * (c * (4 * R)) := by
      rw [integral_add ((hFi.const_mul (Real.sqrt R)).const_mul (C₀ * M / (2 * R)))
        (hind.const_mul (C₀ * M / (2 * R) / Real.sqrt R))]
      simp only [integral_const_mul]
      rw [hI1]
    rw [← Real.norm_eq_abs]
    calc ‖∫ z in Cyl.cell c, deriv (etaCutoff R) z.2 * (a z * b z)‖
        ≤ ∫ z in Cyl.cell c, (C₀ * M / (2 * R) * (Real.sqrt R * F z) +
          C₀ * M / (2 * R) / Real.sqrt R *
            (Ico (-c / 2) (c / 2) ×ˢ Icc (-(2 * R)) (2 * R)).indicator (fun _ => (1 : ℝ)) z) :=
          hnorm
      _ = C₀ * M / (2 * R) * (Real.sqrt R * ∫ z in Cyl.cell c, F z) +
          C₀ * M / (2 * R) / Real.sqrt R * (c * (4 * R)) := hcomp
      _ = C₀ * M * ((∫ z in Cyl.cell c, F z) + 4 * c) / 2 / Real.sqrt R :=
          cel_identity C₀ M (∫ z in Cyl.cell c, F z) c R (Real.sqrt R) hsq hsq2
  have hlim : Tendsto (fun R : ℝ => C₀ * M * ((∫ z in Cyl.cell c, F z) + 4 * c) / 2 / Real.sqrt R)
      atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop Real.tendsto_sqrt_atTop
  refine squeeze_zero_norm' ?_ hlim
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with R hR
  rw [Real.norm_eq_abs]
  exact hbound R hR

/-- **`CutoffErrorLimit`** (proved). -/
theorem cutoffErrorLimit_proof : CutoffErrorLimit := by
  intro c M F G a b hc hF hG hac hbc hG0 hGF hbF hab hid
  have hη := etaCutoffFacts
  obtain ⟨K₀, hK₀, hK⟩ := ebStripBound etaCutoffFacts
  have hF0 : ∀ z, 0 ≤ F z := fun z => le_trans (sq_nonneg _) (hbF z)
  have hM0 : 0 ≤ M := le_trans (abs_nonneg _) (hab 0).1
  -- uniform bound on the error
  have hunif : ∀ R : ℝ, 1 ≤ R →
      |∫ z in Cyl.cell c, deriv (etaCutoff R) z.2 * (a z * b z)| ≤ K₀ * c * (M * M) := by
    intro R hR
    refine hK c R hc hR (fun z => a z * b z) (M * M) (hac.mul hbc) (fun z => ?_)
    show |a z * b z| ≤ M * M
    rw [abs_mul]
    exact mul_le_mul (hab z).1 (hab z).2 (abs_nonneg _) hM0
  have hrel1 : ∀ R : ℝ, 1 ≤ R →
      (∫ z in Cyl.cell c, etaCutoff R z.2 * F z) ≤
        (∫ z in Cyl.cell c, etaCutoff R z.2 * G z) + 2 * (K₀ * c * (M * M)) := by
    intro R hR
    have h1 := abs_le.1 (hunif R hR)
    have h2 := hid R hR
    linarith [h1.1, h1.2]
  have hrel2 : ∀ R : ℝ, 1 ≤ R →
      (∫ z in Cyl.cell c, etaCutoff R z.2 * G z) ≤
        (∫ z in Cyl.cell c, etaCutoff R z.2 * F z) + 2 * (K₀ * c * (M * M)) := by
    intro R hR
    have h1 := abs_le.1 (hunif R hR)
    have h2 := hid R hR
    linarith [h1.1, h1.2]
  by_cases hFi : IntegrableOn F (Cyl.cell c)
  · by_cases hGi : IntegrableOn G (Cyl.cell c)
    · -- both integrable: the error vanishes in the limit
      have hdec := cel_decay c hc hη M F a b hF0 hFi hbF (fun z => (hab z).1)
      have hI := tendsto_cutoff_integral hη c F hFi
      have hJ := tendsto_cutoff_integral hη c G hGi
      have hdiff : Tendsto (fun R : ℝ => (∫ z in Cyl.cell c, etaCutoff R z.2 * F z) -
          (∫ z in Cyl.cell c, etaCutoff R z.2 * G z)) atTop
          (𝓝 ((∫ z in Cyl.cell c, F z) - ∫ z in Cyl.cell c, G z)) := hI.sub hJ
      have hdiff0 : Tendsto (fun R : ℝ => (∫ z in Cyl.cell c, etaCutoff R z.2 * F z) -
          (∫ z in Cyl.cell c, etaCutoff R z.2 * G z)) atTop (𝓝 0) := by
        have h := hdec.const_mul (-2)
        rw [mul_zero] at h
        apply h.congr'
        filter_upwards [eventually_ge_atTop (1 : ℝ)] with R hR
        rw [hid R hR]
        ring
      have heq := tendsto_nhds_unique hdiff hdiff0
      have hint : ∫ z in Cyl.cell c, F z = ∫ z in Cyl.cell c, G z := by linarith
      rw [← ofReal_integral_eq_lintegral_ofReal hFi (Filter.Eventually.of_forall hF0),
        ← ofReal_integral_eq_lintegral_ofReal hGi (Filter.Eventually.of_forall hG0), hint]
    · exfalso
      apply hGi
      exact cel_integrable_of_bound c hc hη G F hG hG0 hFi (2 * (K₀ * c * (M * M))) hrel2
  · by_cases hGi : IntegrableOn G (Cyl.cell c)
    · exfalso
      apply hFi
      exact cel_integrable_of_bound c hc hη F G hF hF0 hGi (2 * (K₀ * c * (M * M))) hrel1
    · -- neither integrable: both `lintegral`s are infinite
      have h1 : ∫⁻ z in Cyl.cell c, ENNReal.ofReal (F z) = ⊤ :=
        top_le_iff.1 (not_lt.1 fun h => hFi ((cel_integrable_iff c F hF hF0).2 h))
      have h2 : ∫⁻ z in Cyl.cell c, ENNReal.ofReal (G z) = ⊤ :=
        top_le_iff.1 (not_lt.1 fun h => hGi ((cel_integrable_iff c G hG hG0).2 h))
      rw [h1, h2]

end UnforcedLeray.Short.PartI
