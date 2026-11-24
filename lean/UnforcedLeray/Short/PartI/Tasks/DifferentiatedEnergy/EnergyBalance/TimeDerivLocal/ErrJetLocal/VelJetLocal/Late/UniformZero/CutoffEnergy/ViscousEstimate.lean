import UnforcedLeray.Short.PartI.Sub.PartI_T08_4_1_1_1_2_2_1_3_2

/-!
# Part I, task `PartI:T08/4/1/1/1/2/2/1/3/2/3`: leaf `VelViscousEstimate`

Source of record: `the November 2 reference manuscript`, lines 273-288.
Target: `velViscousEstimate_proof : VelViscousEstimate` (`Short/PartI/Sub/PartI_T08_4_1_1_1_2_2_1_3_2.lean`).

Single-train analogue (`v' = 0`) of `Tasks/TrainCutoffEnergyProof/ViscousEstimate.lean`.
Let `v = tr.v s`, `φ = etaCutoff R`, `D = ∫_cell φ |∇v|²`, `C₀` from `EtaCutoffFacts`.

1. Pointwise Young inequality (`viscEst_young`, imported): `-2ν φ'⟨v, ∂_η v⟩ ≤ (ν/2) φ |∇v|² +
   2ν (C₀/R)² |v|²`, where `|v|² ≤ M²` on the strip `|η| < 2R`. Off the strip `φ = φ' = 0`, so
   the left side is `0`. Hence, on the cell, the left side is bounded by `(ν/2) φ |∇v|² +
   2ν (C₀/R)² M² 1_{Box}` with `Box = [-c/2, c/2] × [-2R, 2R]`.
2. Integrate over the cell. `vol(Box) = 4Rc`, so `2ν (C₀/R)² M² · 4Rc = 8ν C₀² c M² / R ≤ 8ν C₀² c M²`.
3. `viscousRhs = -2νD - 2ν ∫ φ'⟨v, ∂_η v⟩ ≤ -(3/2) ν D + K` with `K = 8 ν C₀² c M²`.

Helpers are prefixed `ve`, and the imported `viscEst_*` lemmas come from the model module.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.PartI

open UnforcedLeray.Cyl (Plane)
open UnforcedLeray.Train (Vec)

/-- The box `[-c/2, c/2] × [-2R, 2R]` containing the strip of the cell where `φ_R` is not zero. -/
def veBox (c R : ℝ) : Set Plane := Icc (-c / 2) (c / 2) ×ˢ Icc (-(2 * R)) (2 * R)

/-- The volume of the box is `c · 4R`. -/
theorem veBox_volume {c R : ℝ} (hc : 0 < c) : volume (veBox c R) = ENNReal.ofReal (c * (4 * R)) := by
  unfold veBox
  rw [Measure.volume_eq_prod, Measure.prod_prod, Real.volume_Icc, Real.volume_Icc,
    ← ENNReal.ofReal_mul (show (0 : ℝ) ≤ c / 2 - -c / 2 by linarith)]
  congr 1
  ring

/-- **Leaf `VelViscousEstimate`** (source lines 276-288, Young inequality for the viscous cross
term). -/
theorem velViscousEstimate_proof : UnforcedLeray.Short.PartI.VelViscousEstimate := by
  intro ν c hν hc tr S M hS0 hb
  have hcutF : EtaCutoffFacts := etaCutoffFacts
  unfold EtaCutoffFacts at hcutF
  obtain ⟨C₀, hC₀, hcut⟩ := hcutF
  have hM : 0 ≤ M := le_trans (norm_nonneg _) (hb 0 ⟨le_refl 0, hS0⟩ 0)
  have hK0 : 0 ≤ 8 * ν * C₀ ^ 2 * c * M ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hν.le) (sq_nonneg _)) hc.le)
      (sq_nonneg _)
  refine ⟨8 * ν * C₀ ^ 2 * c * M ^ 2, hK0, ?_⟩
  intro R hR s hs
  have hR0 : 0 < R := by linarith
  have hRne : R ≠ 0 := hR0.ne'
  have hs0 : 0 ≤ s := hs.1
  obtain ⟨hsm, -, -, hφz, hφd⟩ := hcut R hR
  -- smoothness of the difference-free train slice
  have hw1 : ContDiff ℝ ∞ (tr.v s) := (trainSliceSmooth ν c tr s hs0).1
  have hw1' : ContDiff ℝ 1 (tr.v s) := hw1.of_le (by simp)
  have hwc : Continuous (tr.v s) := hw1'.continuous
  have hwd : Differentiable ℝ (tr.v s) := hw1'.differentiable (by simp)
  have hpe : Continuous (Cyl.partialEta (tr.v s)) := (Cyl.C1_partial_of_contDiff hw1').2
  have hsm1 : ContDiff ℝ 1 (etaCutoff R) := hsm.of_le (by simp)
  have hφc : Continuous (fun z : Plane => etaCutoff R z.2) :=
    hsm1.continuous.comp continuous_snd
  have hdc : Continuous (fun z : Plane => deriv (etaCutoff R) z.2) :=
    hsm1.continuous_deriv_one.comp continuous_snd
  have hdz : ∀ η : ℝ, 2 * R ≤ |η| → deriv (etaCutoff R) η = 0 := by
    intro η hη
    have h := hφd η
    rw [hφz η hη, Real.sqrt_zero, mul_zero] at h
    exact abs_nonpos_iff.mp h
  have hf_zero : ∀ z : Plane, 2 * R ≤ |z.2| →
      deriv (etaCutoff R) z.2 * inner ℝ (tr.v s z) (Cyl.partialEta (tr.v s) z) = 0 := by
    intro z hz
    rw [hdz z.2 hz, zero_mul]
  have hD_zero : ∀ z : Plane, 2 * R ≤ |z.2| → etaCutoff R z.2 * gradNormSq (tr.v s) z = 0 := by
    intro z hz
    rw [hφz z.2 hz, zero_mul]
  -- continuity and support, hence integrability on the cell
  have hG_cont : Continuous (gradNormSq (tr.v s)) := viscEst_gradNormSq_cont hw1'
  have hfcont : Continuous (fun z : Plane =>
      deriv (etaCutoff R) z.2 * inner ℝ (tr.v s z) (Cyl.partialEta (tr.v s) z)) :=
    hdc.mul (hwc.inner hpe)
  have hDcont : Continuous (fun z : Plane => etaCutoff R z.2 * gradNormSq (tr.v s) z) :=
    hφc.mul hG_cont
  have hfI : IntegrableOn (fun z : Plane =>
      deriv (etaCutoff R) z.2 * inner ℝ (tr.v s z) (Cyl.partialEta (tr.v s) z)) (Cyl.cell c) :=
    cellIntegrable_of_support c R hc hR0 _ hfcont hf_zero
  have hDI : IntegrableOn (fun z : Plane => etaCutoff R z.2 * gradNormSq (tr.v s) z)
      (Cyl.cell c) :=
    cellIntegrable_of_support c R hc hR0 _ hDcont hD_zero
  -- the box and the cell
  have hcellmeas : MeasurableSet (Cyl.cell c) := by
    unfold Cyl.cell
    exact measurableSet_Ico.prod MeasurableSet.univ
  have hBmeas : MeasurableSet (veBox c R) := measurableSet_Icc.prod measurableSet_Icc
  have hBvol : volume (veBox c R) ≠ ⊤ := by
    rw [veBox_volume hc]
    exact ENNReal.ofReal_ne_top
  have hBfin : (volume.restrict (Cyl.cell c)) (veBox c R) ≠ ⊤ :=
    ne_top_of_le_ne_top hBvol (Measure.restrict_apply_le _ _)
  have hBI : IntegrableOn ((veBox c R).indicator (fun _ : Plane => M ^ 2)) (Cyl.cell c) :=
    (integrable_indicator_iff hBmeas).2 (integrableOn_const hBfin)
  -- the pointwise Young bound on the cell
  have hpt : ∀ z : Plane, z ∈ Cyl.cell c →
      -2 * ν * (deriv (etaCutoff R) z.2 * inner ℝ (tr.v s z) (Cyl.partialEta (tr.v s) z)) ≤
        ν / 2 * (etaCutoff R z.2 * gradNormSq (tr.v s) z) +
          2 * ν * (C₀ / R) ^ 2 * ((veBox c R).indicator (fun _ : Plane => M ^ 2) z) := by
    intro z hzc
    have hind0 : 0 ≤ (veBox c R).indicator (fun _ : Plane => M ^ 2) z :=
      Set.indicator_nonneg (fun _ _ => sq_nonneg M) z
    have hk : 0 ≤ 2 * ν * (C₀ / R) ^ 2 :=
      mul_nonneg (mul_nonneg (by norm_num) hν.le) (sq_nonneg _)
    by_cases hz : 2 * R ≤ |z.2|
    · rw [hdz z.2 hz, zero_mul, mul_zero, hφz z.2 hz]
      have h0 := mul_nonneg hk hind0
      linarith
    · have hz' : |z.2| < 2 * R := not_le.mp hz
      have hzB : z ∈ veBox c R := by
        have h1 : z.1 ∈ Icc (-c / 2) (c / 2) := Ico_subset_Icc_self (Set.mem_prod.1 hzc).1
        have h2 : z.2 ∈ Icc (-(2 * R)) (2 * R) :=
          ⟨by linarith [neg_abs_le z.2], by linarith [le_abs_self z.2]⟩
        exact Set.mk_mem_prod h1 h2
      have hind : (veBox c R).indicator (fun _ : Plane => M ^ 2) z = M ^ 2 :=
        Set.indicator_of_mem hzB _
      have hyM : ‖tr.v s z‖ ^ 2 ≤ M ^ 2 := by
        nlinarith [norm_nonneg (tr.v s z), hb s hs z]
      have hY := viscEst_young ν (C₀ / R) (Real.sqrt (etaCutoff R z.2))
        (deriv (etaCutoff R) z.2)
        (inner ℝ (tr.v s z) (Cyl.partialEta (tr.v s) z))
        ‖Cyl.partialEta (tr.v s) z‖ ‖tr.v s z‖
        (gradNormSq (tr.v s) z) (etaCutoff R z.2)
        hν.le (div_nonneg hC₀ hR0.le) (Real.sqrt_nonneg _)
        (Real.sq_sqrt (etaCutoff_nonneg R z.2)) (etaCutoff_nonneg R z.2) (hφd z.2)
        (abs_real_inner_le_norm _ _) (viscEst_norm_sq_le hwd z)
      have hk2 : 2 * ν * (C₀ / R) ^ 2 * ‖tr.v s z‖ ^ 2 ≤ 2 * ν * (C₀ / R) ^ 2 * M ^ 2 :=
        mul_le_mul_of_nonneg_left hyM hk
      rw [hind]
      linarith [hY, hk2]
  -- integrate the pointwise bound over the cell
  have hgI : IntegrableOn (fun z : Plane => ν / 2 * (etaCutoff R z.2 * gradNormSq (tr.v s) z) +
      2 * ν * (C₀ / R) ^ 2 * ((veBox c R).indicator (fun _ : Plane => M ^ 2) z))
      (Cyl.cell c) :=
    (hDI.const_mul (ν / 2)).add (hBI.const_mul (2 * ν * (C₀ / R) ^ 2))
  have hLmono : ∫ z in Cyl.cell c, -2 * ν * (deriv (etaCutoff R) z.2 *
        inner ℝ (tr.v s z) (Cyl.partialEta (tr.v s) z)) ≤
      ∫ z in Cyl.cell c, (ν / 2 * (etaCutoff R z.2 * gradNormSq (tr.v s) z) +
        2 * ν * (C₀ / R) ^ 2 * ((veBox c R).indicator (fun _ : Plane => M ^ 2) z)) :=
    integral_mono_ae (hfI.const_mul (-2 * ν)) hgI (by
      filter_upwards [ae_restrict_mem hcellmeas] with z hz
      exact hpt z hz)
  have hL : ∫ z in Cyl.cell c, -2 * ν * (deriv (etaCutoff R) z.2 *
        inner ℝ (tr.v s z) (Cyl.partialEta (tr.v s) z)) =
      -2 * ν * ∫ z in Cyl.cell c, deriv (etaCutoff R) z.2 *
        inner ℝ (tr.v s z) (Cyl.partialEta (tr.v s) z) := by
    rw [integral_const_mul]
  have hsplit : ∫ z in Cyl.cell c, (ν / 2 * (etaCutoff R z.2 * gradNormSq (tr.v s) z) +
        2 * ν * (C₀ / R) ^ 2 * ((veBox c R).indicator (fun _ : Plane => M ^ 2) z)) =
      ν / 2 * (∫ z in Cyl.cell c, etaCutoff R z.2 * gradNormSq (tr.v s) z) +
        2 * ν * (C₀ / R) ^ 2 *
          ∫ z in Cyl.cell c, (veBox c R).indicator (fun _ : Plane => M ^ 2) z := by
    rw [integral_add (hDI.const_mul (ν / 2)) (hBI.const_mul (2 * ν * (C₀ / R) ^ 2)),
      integral_const_mul, integral_const_mul]
  have hInd : ∫ z in Cyl.cell c, (veBox c R).indicator (fun _ : Plane => M ^ 2) z =
      (volume.restrict (Cyl.cell c)).real (veBox c R) * M ^ 2 := by
    rw [integral_indicator_const _ hBmeas, smul_eq_mul]
  -- the measure of the box is at most `4 R c`
  have hXle : (volume.restrict (Cyl.cell c)).real (veBox c R) ≤ c * (4 * R) := by
    rw [measureReal_def]
    apply ENNReal.toReal_le_of_le_ofReal (mul_nonneg hc.le (by linarith))
    calc (volume.restrict (Cyl.cell c)) (veBox c R) ≤ volume (veBox c R) :=
          Measure.restrict_apply_le _ _
      _ = ENNReal.ofReal (c * (4 * R)) := veBox_volume hc
  have hX0 : 0 ≤ (volume.restrict (Cyl.cell c)).real (veBox c R) := by
    rw [measureReal_def]
    exact ENNReal.toReal_nonneg
  -- the constant: `2ν (C₀/R)² · M² · 4Rc = 8 ν C₀² c M² / R ≤ 8 ν C₀² c M²`
  have hA : 2 * ν * (C₀ / R) ^ 2 *
      ((volume.restrict (Cyl.cell c)).real (veBox c R) * M ^ 2) ≤
        8 * ν * C₀ ^ 2 * c * M ^ 2 := by
    have h1 : (volume.restrict (Cyl.cell c)).real (veBox c R) * M ^ 2 ≤
        (c * (4 * R)) * M ^ 2 := mul_le_mul_of_nonneg_right hXle (sq_nonneg M)
    have hk : 0 ≤ 2 * ν * (C₀ / R) ^ 2 :=
      mul_nonneg (mul_nonneg (by norm_num) hν.le) (sq_nonneg _)
    have h2 : 2 * ν * (C₀ / R) ^ 2 * ((c * (4 * R)) * M ^ 2) =
        8 * ν * C₀ ^ 2 * c * M ^ 2 / R := by
      field_simp
      ring
    have h3 : 8 * ν * C₀ ^ 2 * c * M ^ 2 / R ≤ 8 * ν * C₀ ^ 2 * c * M ^ 2 :=
      div_le_self hK0 hR
    have h4 := mul_le_mul_of_nonneg_left h1 hk
    linarith
  -- assemble
  unfold velViscousRhs velCutoffDissipation
  rw [hL, hsplit, hInd] at hLmono
  linarith [hLmono, hA]

end UnforcedLeray.Short.PartI
