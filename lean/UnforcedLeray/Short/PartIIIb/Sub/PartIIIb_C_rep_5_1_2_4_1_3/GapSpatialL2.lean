import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_5_1_2_4_1_3.Kernel
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_5_1_2_4_1.GapL2

/-!
# `PartIII-b:C/rep/5/1/2/4/1/3/3/14`: the spatial `L²` norm across the radial gap

Source `the November 2 reference manuscript` 5588-5591.  Put `D = (1-θ)R/√s₀`.
On the set `{age R y ≤ s₀, ϱ z < θ ϱ y}` one has `‖y - l z‖ ≥ D`: indeed
`‖y - l z‖ ≥ ϱ y - l ϱ z ≥ (1-θ) ϱ y ≥ D` (planar reverse triangle inequality, `l < 1`).
Translating by `l z` and using `gapKernel_sq_lintegral_le` gives the bound `4π/5 · D⁻⁵ = gapA`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete.WYCore

/-- **Spatial `L²` norm across the gap** (source 5588-5591). -/
theorem gapSpatialL2 : GapSpatialL2 := by
  intro R θ s0 l z hR hθ hθ1 hs0 hl0 hl1
  have hsq : 0 < Real.sqrt s0 := Real.sqrt_pos.2 hs0
  have hs2 : Real.sqrt s0 ^ 2 = s0 := Real.sq_sqrt hs0.le
  have hD : 0 < (1 - θ) * R / Real.sqrt s0 :=
    div_pos (mul_pos (by linarith) hR) hsq
  -- geometric inclusion: the gap set lies in the preimage of `{‖x‖ ≥ D}`
  have hsub : ∀ y : Space, (age R y ≤ s0 ∧ ϱ z < θ * ϱ y) →
      (1 - θ) * R / Real.sqrt s0 ≤ ‖y - l • z‖ := by
    rintro y ⟨hage, hzy⟩
    have hϱ0 : 0 ≤ ϱ y := ϱ_nonneg y
    have hz0 : 0 ≤ ϱ z := ϱ_nonneg z
    have ha : 0 < ϱ y := by nlinarith
    have hy2 : 0 < ϱ y ^ 2 := pow_pos ha 2
    have hage' : R ^ 2 ≤ s0 * ϱ y ^ 2 := by
      unfold age at hage
      exact (div_le_iff₀ hy2).1 hage
    have hRa2 : R ^ 2 ≤ (ϱ y * Real.sqrt s0) ^ 2 := by
      rw [mul_pow, hs2]
      nlinarith [hage']
    have hRa : R ≤ ϱ y * Real.sqrt s0 := by
      nlinarith [hRa2, mul_nonneg ha.le hsq.le]
    have hD_le : (1 - θ) * R / Real.sqrt s0 ≤ (1 - θ) * ϱ y := by
      rw [div_le_iff₀ hsq]
      nlinarith [mul_le_mul_of_nonneg_left hRa (by linarith : (0 : ℝ) ≤ 1 - θ)]
    -- planar Cauchy-Schwarz and the reverse triangle inequality for the norm
    have hϱy : ϱ y ^ 2 = y 0 ^ 2 + y 1 ^ 2 := by
      unfold ϱ
      rw [Real.sq_sqrt]
      positivity
    have hϱz : ϱ z ^ 2 = z 0 ^ 2 + z 1 ^ 2 := by
      unfold ϱ
      rw [Real.sq_sqrt]
      positivity
    have hcs : y 0 * z 0 + y 1 * z 1 ≤ ϱ y * ϱ z := by
      have hab2 : (ϱ y * ϱ z) ^ 2 = (y 0 ^ 2 + y 1 ^ 2) * (z 0 ^ 2 + z 1 ^ 2) := by
        rw [mul_pow, hϱy, hϱz]
      nlinarith [mul_self_nonneg (y 0 * z 1 - y 1 * z 0), mul_nonneg hϱ0 hz0]
    have hN2 : ‖y - l • z‖ ^ 2 =
        (y 0 - l * z 0) ^ 2 + (y 1 - l * z 1) ^ 2 + (y 2 - l * z 2) ^ 2 := by
      rw [EuclideanSpace.norm_eq, Real.sq_sqrt, Fin.sum_univ_three]
      · simp [Real.norm_eq_abs, sq_abs]
      · positivity
    have hQ : (ϱ y - l * ϱ z) ^ 2 ≤ ‖y - l • z‖ ^ 2 := by
      have e : (ϱ y - l * ϱ z) ^ 2 = ϱ y ^ 2 - 2 * l * (ϱ y * ϱ z) + l ^ 2 * ϱ z ^ 2 := by
        ring
      rw [e, hϱy, hϱz, hN2]
      nlinarith [mul_nonneg hl0.le (sub_nonneg.2 hcs), sq_nonneg (y 2 - l * z 2)]
    have hN : ϱ y - l * ϱ z ≤ ‖y - l • z‖ := by
      have hN0 : 0 ≤ ‖y - l • z‖ := norm_nonneg _
      nlinarith [hQ, hN0]
    have hlz : l * ϱ z ≤ ϱ z := by
      nlinarith [mul_nonneg (sub_nonneg.2 hl1.le) hz0]
    calc (1 - θ) * R / Real.sqrt s0 ≤ (1 - θ) * ϱ y := hD_le
      _ ≤ ϱ y - l * ϱ z := by
        rw [sub_mul, one_mul]
        linarith [hzy, hlz]
      _ ≤ ‖y - l • z‖ := hN
  have hT : MeasurableSet {x : Space | (1 - θ) * R / Real.sqrt s0 ≤ ‖x‖} :=
    measurableSet_le measurable_const measurable_norm
  have hP : MeasurableSet
      ((fun y : Space => y - l • z) ⁻¹' {x : Space | (1 - θ) * R / Real.sqrt s0 ≤ ‖x‖}) :=
    hT.preimage (measurable_id.sub_const (l • z))
  calc ∫⁻ y in {y : Space | age R y ≤ s0 ∧ ϱ z < θ * ϱ y},
          ENNReal.ofReal ((‖y - l • z‖ ^ 4)⁻¹) ^ (2 : ℝ)
      ≤ ∫⁻ y in (fun y : Space => y - l • z) ⁻¹' {x : Space | (1 - θ) * R / Real.sqrt s0 ≤ ‖x‖},
          ENNReal.ofReal ((‖y - l • z‖ ^ 4)⁻¹) ^ (2 : ℝ) := by
        apply lintegral_mono_set
        intro y hy
        exact hsub y hy
    _ = ∫⁻ y, Set.indicator
          ((fun y : Space => y - l • z) ⁻¹' {x : Space | (1 - θ) * R / Real.sqrt s0 ≤ ‖x‖})
          (fun y => ENNReal.ofReal ((‖y - l • z‖ ^ 4)⁻¹) ^ (2 : ℝ)) y :=
        (lintegral_indicator hP _).symm
    _ = ∫⁻ y, Set.indicator {x : Space | (1 - θ) * R / Real.sqrt s0 ≤ ‖x‖}
          (fun x => ENNReal.ofReal ((‖x‖ ^ 4)⁻¹) ^ (2 : ℝ)) (y - l • z) := by
        refine lintegral_congr fun y => ?_
        by_cases hy : y - l • z ∈ {x : Space | (1 - θ) * R / Real.sqrt s0 ≤ ‖x‖}
        · have hy' : y ∈ (fun y : Space => y - l • z) ⁻¹'
              {x : Space | (1 - θ) * R / Real.sqrt s0 ≤ ‖x‖} := hy
          rw [Set.indicator_of_mem hy', Set.indicator_of_mem hy]
        · have hy' : y ∉ (fun y : Space => y - l • z) ⁻¹'
              {x : Space | (1 - θ) * R / Real.sqrt s0 ≤ ‖x‖} := hy
          rw [Set.indicator_of_notMem hy', Set.indicator_of_notMem hy]
    _ = ∫⁻ x, Set.indicator {x : Space | (1 - θ) * R / Real.sqrt s0 ≤ ‖x‖}
          (fun x => ENNReal.ofReal ((‖x‖ ^ 4)⁻¹) ^ (2 : ℝ)) x :=
        lintegral_sub_right_eq_self _ (l • z)
    _ = ∫⁻ x in {x : Space | (1 - θ) * R / Real.sqrt s0 ≤ ‖x‖},
          ENNReal.ofReal ((‖x‖ ^ 4)⁻¹) ^ (2 : ℝ) :=
        lintegral_indicator hT _
    _ ≤ ENNReal.ofReal (4 * Real.pi / 5 * (((1 - θ) * R / Real.sqrt s0)⁻¹) ^ 5) :=
        gapKernel_sq_lintegral_le hD
    _ = ENNReal.ofReal (gapA θ R s0) := rfl

end UnforcedLeray.Short.PartIIIb.Concrete.WYCore

end
