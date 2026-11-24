import UnforcedLeray.Short.PartI.Sub.PartI_T08_4_1_1_1_2_2_1_3_2
import UnforcedLeray.Short.PartI.Tasks.ClassicalOdd.EtaCutoffFacts
import UnforcedLeray.Short.PartI.Tasks.TrainCutoffEnergyProof.CellToolkit
import UnforcedLeray.Short.PartI.Tasks.TrainCutoffEnergyProof.SliceSmooth

/-!
# Part I, task `PartI:T08/4/1/1/1/2/2/1/3/2/7`: leaf `VelPressureEstimate`

Source of record: `the November 2 reference manuscript` lines 273-288.
Target: `velPressureEstimate_proof : VelPressureEstimate` (`Sub/PartI_T08_4_1_1_1_2_2_1_3_2.lean`).

Route. The integrand `f = φ' p v₁` of `velPressureRhs / 2` is continuous and vanishes for
`2R ≤ |η|`, so it is integrable on the cell. On the strip `|η| ≤ 2R` we have
`|f| ≤ (C₀/R) · P · M`, and `f = 0` off the strip. Hence `∫_cell f ≤ K₀ · cellμ(strip)` with
`cellμ(strip) = c · 4R`, so `velPressureRhs = 2 ∫ f ≤ 8 C₀ c P M`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.PartI

open UnforcedLeray.Cyl (Plane)
open UnforcedLeray.Train (Vec)

/-- The cell measure of the strip `univ ×ˢ [-2R, 2R]` is `c · 4R`. -/
theorem vpe_strip_measure (c R : ℝ) (hc : 0 < c) (hR : 0 < R) :
    (UnforcedLeray.Cyl.cellμ c (univ ×ˢ Icc (-(2 * R)) (2 * R))).toReal = c * (4 * R) := by
  rw [UnforcedLeray.Cyl.cellμ_prod, Real.volume_Icc,
    ENNReal.toReal_mul, ENNReal.toReal_ofReal hc.le,
    ENNReal.toReal_ofReal (show (0 : ℝ) ≤ 2 * R - -(2 * R) by linarith)]
  ring

/-- The strip indicator with constant value is integrable on the cell. -/
theorem vpe_indicator_integrable (c R K0 : ℝ) :
    IntegrableOn ((univ ×ˢ Icc (-(2 * R)) (2 * R) : Set Plane).indicator (fun _ : Plane => K0))
      (UnforcedLeray.Cyl.cell c) := by
  have hT : MeasurableSet (univ ×ˢ Icc (-(2 * R)) (2 * R) : Set Plane) :=
    MeasurableSet.univ.prod measurableSet_Icc
  refine (integrable_indicator_iff hT).2 ?_
  have hfin : UnforcedLeray.Cyl.cellμ c (univ ×ˢ Icc (-(2 * R)) (2 * R)) ≠ ⊤ := by
    rw [UnforcedLeray.Cyl.cellμ_prod, Real.volume_Icc]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
  exact integrableOn_const (C := K0) hfin (by finiteness)

/-- **`PartI:T08/4/1/1/1/2/2/1/3/2/7`, target `VelPressureEstimate`.** -/
theorem velPressureEstimate_proof : UnforcedLeray.Short.PartI.VelPressureEstimate := by
  have hη := etaCutoffFacts
  unfold EtaCutoffFacts at hη
  obtain ⟨C₀, hC₀, hφ⟩ := hη
  unfold VelPressureEstimate
  intro ν c hν hc tr S M P hS0 hb hpb
  have hM0 : 0 ≤ M := le_trans (norm_nonneg _) (hb 0 ⟨le_rfl, hS0⟩ 0)
  have hP0 : 0 ≤ P := le_trans (abs_nonneg _) (hpb 0 ⟨le_rfl, hS0⟩ 0)
  refine ⟨8 * C₀ * c * P * M,
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hC₀) hc.le) hP0) hM0, ?_⟩
  intro R hR s hs
  have hRpos : 0 < R := by linarith
  have hRne : R ≠ 0 := hRpos.ne'
  have hs0 : 0 ≤ s := hs.1
  obtain ⟨hφS, hφ01, -, hφ0, hφd⟩ := hφ R hR
  have hSm : TrainSliceSmooth := trainSliceSmooth
  obtain ⟨hv, hp⟩ := hSm ν c tr s hs0
  have hvC : Continuous (tr.v s) := hv.continuous
  have hpC : Continuous (tr.p s) := hp.continuous
  have hV1 : Continuous fun z : Plane => tr.v s z 1 :=
    (EuclideanSpace.proj (1 : Fin 2) : Vec →L[ℝ] ℝ).continuous.comp hvC
  have hD : Continuous fun z : Plane => deriv (etaCutoff R) z.2 :=
    (hφS.continuous_deriv (by simp)).comp continuous_snd
  have hfc : Continuous fun z : Plane =>
      deriv (etaCutoff R) z.2 * tr.p s z * tr.v s z 1 :=
    (hD.mul hpC).mul hV1
  have hfz : ∀ z : Plane, 2 * R ≤ |z.2| →
      deriv (etaCutoff R) z.2 * tr.p s z * tr.v s z 1 = 0 := by
    intro z hz
    have h0 : deriv (etaCutoff R) z.2 = 0 := by
      have h := hφd z.2
      rw [hφ0 z.2 hz, Real.sqrt_zero, mul_zero] at h
      exact abs_nonpos_iff.mp h
    rw [h0, zero_mul, zero_mul]
  have hfI : IntegrableOn (fun z : Plane =>
      deriv (etaCutoff R) z.2 * tr.p s z * tr.v s z 1) (UnforcedLeray.Cyl.cell c) :=
    cellToolkit.1 c R hc hRpos _ hfc hfz
  -- the pointwise majorant: the constant `K₀` on the strip, `0` off it
  have hT : MeasurableSet (univ ×ˢ Icc (-(2 * R)) (2 * R) : Set Plane) :=
    MeasurableSet.univ.prod measurableSet_Icc
  have hpt : ∀ z : Plane,
      deriv (etaCutoff R) z.2 * tr.p s z * tr.v s z 1 ≤
        (univ ×ˢ Icc (-(2 * R)) (2 * R) : Set Plane).indicator
          (fun _ : Plane => C₀ / R * P * M) z := by
    intro z
    by_cases hz : z.2 ∈ Icc (-(2 * R)) (2 * R)
    · have hzT : z ∈ (univ ×ˢ Icc (-(2 * R)) (2 * R) : Set Plane) :=
        mem_prod.2 ⟨mem_univ _, hz⟩
      rw [Set.indicator_of_mem hzT]
      have hp1 : |tr.p s z| ≤ P := hpb s hs z
      have hv1 : |tr.v s z 1| ≤ M := by
        have h1' : ‖tr.v s z 1‖ ≤ ‖tr.v s z‖ := PiLp.norm_apply_le (tr.v s z) 1
        rw [Real.norm_eq_abs] at h1'
        exact h1'.trans (hb s hs z)
      have hs1 : Real.sqrt (etaCutoff R z.2) ≤ 1 := by
        have h := Real.sqrt_le_sqrt (hφ01 z.2).2
        rwa [Real.sqrt_one] at h
      have hd1 : |deriv (etaCutoff R) z.2| ≤ C₀ / R :=
        (hφd z.2).trans (mul_le_of_le_one_right (div_nonneg hC₀ hRpos.le) hs1)
      calc deriv (etaCutoff R) z.2 * tr.p s z * tr.v s z 1
          ≤ |deriv (etaCutoff R) z.2 * tr.p s z * tr.v s z 1| := le_abs_self _
        _ = |deriv (etaCutoff R) z.2| * |tr.p s z| * |tr.v s z 1| := by
            rw [abs_mul, abs_mul]
        _ ≤ C₀ / R * P * M :=
            mul_le_mul (mul_le_mul hd1 hp1 (abs_nonneg _) (div_nonneg hC₀ hRpos.le)) hv1
              (abs_nonneg _) (mul_nonneg (div_nonneg hC₀ hRpos.le) hP0)
    · have hzT : z ∉ (univ ×ˢ Icc (-(2 * R)) (2 * R) : Set Plane) := fun h =>
        hz (mem_prod.1 h).2
      rw [Set.indicator_apply, if_neg hzT]
      have hz2 : 2 * R ≤ |z.2| := by
        by_contra h
        push_neg at h
        obtain ⟨h1, h2⟩ := abs_lt.mp h
        exact hz ⟨by linarith, by linarith⟩
      rw [hfz z hz2]
  have hintI := vpe_indicator_integrable c R (C₀ / R * P * M)
  have hmono := integral_mono hfI hintI (fun z => hpt z)
  have hval : ∫ z in UnforcedLeray.Cyl.cell c,
      (univ ×ˢ Icc (-(2 * R)) (2 * R) : Set Plane).indicator
        (fun _ : Plane => C₀ / R * P * M) z =
      c * (4 * R) * (C₀ / R * P * M) := by
    rw [integral_indicator_const (C₀ / R * P * M) hT]
    show ((UnforcedLeray.Cyl.cellμ c) (univ ×ˢ Icc (-(2 * R)) (2 * R))).toReal • _ = _
    rw [vpe_strip_measure c R hc hRpos, smul_eq_mul]
  unfold velPressureRhs
  have hEq : 2 * (c * (4 * R) * (C₀ / R * P * M)) = 8 * C₀ * c * P * M := by
    rw [show 2 * (c * (4 * R) * (C₀ / R * P * M)) = 8 * C₀ * c * P * M * (R / R) by ring,
      div_self hRne, mul_one]
  calc 2 * ∫ z in UnforcedLeray.Cyl.cell c,
        deriv (etaCutoff R) z.2 * tr.p s z * tr.v s z 1
      ≤ 2 * ∫ z in UnforcedLeray.Cyl.cell c,
          (univ ×ˢ Icc (-(2 * R)) (2 * R) : Set Plane).indicator
            (fun _ : Plane => C₀ / R * P * M) z :=
        mul_le_mul_of_nonneg_left hmono (by norm_num)
    _ = 2 * (c * (4 * R) * (C₀ / R * P * M)) := by rw [hval]
    _ = 8 * C₀ * c * P * M := hEq

end UnforcedLeray.Short.PartI
