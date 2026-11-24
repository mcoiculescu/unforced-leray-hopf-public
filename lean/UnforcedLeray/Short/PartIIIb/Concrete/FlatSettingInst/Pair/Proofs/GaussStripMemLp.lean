import UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst.Pair.Defs
import UnforcedLeray.Lib.Gaussian.Absorb
import UnforcedLeray.Lib.Gaussian.GammaToolkit
import UnforcedLeray.Units.B0579

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal ComplexConjugate

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst.Pair

/-- Polynomial weight against a Gaussian: `(1+y)^M e^{-y/24}` is bounded for `y ≥ 0`, `M ≥ 0`. -/
theorem gs_absorb {M : ℝ} (hM : 0 ≤ M) :
    ∃ K : ℝ, ∀ y : ℝ, 0 ≤ y → (1 + y) ^ M * Real.exp (-(y / 24)) ≤ K := by
  obtain ⟨C, hC0, hC⟩ := UnforcedLeray.Gaussian.rpow_mul_exp_neg_le hM
  refine ⟨2 ^ M * (1 + 24 ^ M * C), fun y hy => ?_⟩
  have h1 : (1 + y) ^ M ≤ 2 ^ M * (1 + y ^ M) := UnforcedLeray.Gaussian.one_add_rpow_le hM hy
  have he0 : 0 ≤ Real.exp (-(y / 24)) := (Real.exp_pos _).le
  have he : Real.exp (-(y / 24)) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
  have hy24 : y ^ M = 24 ^ M * (y / 24) ^ M := by
    rw [← Real.mul_rpow (by norm_num) (by positivity)]
    congr 1
    ring
  have hC' : (y / 24) ^ M * Real.exp (-(y / 24)) ≤ C := hC (y / 24) (by positivity)
  have hP : (0 : ℝ) ≤ 2 ^ M := by positivity
  have h24 : (0 : ℝ) ≤ 24 ^ M := by positivity
  calc (1 + y) ^ M * Real.exp (-(y / 24)) ≤ (2 ^ M * (1 + y ^ M)) * Real.exp (-(y / 24)) :=
        mul_le_mul_of_nonneg_right h1 he0
    _ = 2 ^ M * (Real.exp (-(y / 24)) + 24 ^ M * ((y / 24) ^ M * Real.exp (-(y / 24)))) := by
        rw [hy24]; ring
    _ ≤ 2 ^ M * (1 + 24 ^ M * C) := by
        apply mul_le_mul_of_nonneg_left _ hP
        linarith [mul_le_mul_of_nonneg_left hC' h24]

/-- The cell weight is dominated: `⟨x⟩^{2m} ≤ (1+c²)^M (1+x₂²)^M` on the cell, `M = max m 0`. -/
theorem gs_jb {c m : ℝ} (x : ℝ × ℝ) (hx : x ∈ B0579.cell c) :
    B0579.jb x ^ m ≤ (1 + c ^ 2) ^ (max m 0) * (1 + x.2 ^ 2) ^ (max m 0) := by
  obtain ⟨hlo, hhi⟩ := Set.mem_Ico.1 (Set.mem_prod.1 hx).1
  have hx1 : x.1 ^ 2 ≤ c ^ 2 := by
    nlinarith [mul_nonneg (show (0 : ℝ) ≤ x.1 + c / 2 by linarith)
      (show (0 : ℝ) ≤ c / 2 - x.1 by linarith), sq_nonneg c]
  have hjb : B0579.jb x ≤ (1 + c ^ 2) * (1 + x.2 ^ 2) := by
    unfold B0579.jb
    nlinarith [mul_nonneg (sq_nonneg c) (sq_nonneg x.2)]
  have hjb1 : 1 ≤ B0579.jb x := by
    unfold B0579.jb
    nlinarith [sq_nonneg x.1, sq_nonneg x.2]
  rcases le_total 0 m with hm | hm
  · rw [max_eq_left hm]
    calc B0579.jb x ^ m ≤ ((1 + c ^ 2) * (1 + x.2 ^ 2)) ^ m :=
          Real.rpow_le_rpow (B0579.jb_pos x).le hjb hm
      _ = (1 + c ^ 2) ^ m * (1 + x.2 ^ 2) ^ m :=
          Real.mul_rpow (by positivity) (by positivity)
  · rw [max_eq_right hm, Real.rpow_zero, Real.rpow_zero, mul_one]
    exact Real.rpow_le_one_of_one_le_of_nonpos hjb1 hm

/-- The majorant `1_{Ico}(x₁) · e^{-x₂²/24}` is integrable on the plane. -/
theorem gs_integrable (c K : ℝ) :
    Integrable (fun z : ℝ × ℝ =>
      (Set.Ico (-(c / 2)) (c / 2)).indicator (fun _ : ℝ => K) z.1 *
        Real.exp (-(z.2 ^ 2 / 24))) := by
  have hf : Integrable ((Set.Ico (-(c / 2)) (c / 2)).indicator (fun _ : ℝ => K)) := by
    rw [integrable_indicator_iff measurableSet_Ico]
    exact integrableOn_const measure_Ico_lt_top.ne
  have hg : Integrable (fun y : ℝ => Real.exp (-(y ^ 2 / 24))) := by
    have h := integrable_exp_neg_mul_sq (b := 1 / 24) (by norm_num)
    refine h.congr (Filter.Eventually.of_forall fun y => ?_)
    dsimp only
    congr 1
    ring
  have hprod := hf.mul_prod hg
  rw [← MeasureTheory.Measure.volume_eq_prod] at hprod
  exact hprod

theorem gaussStripMemLp :
    UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst.Pair.GaussStripMemLp := by
  intro c m A
  have hcont : Continuous (fun x : ℝ × ℝ => A * Real.exp (-(x.2 ^ 2) / 24)) := by
    fun_prop
  refine (memLp_two_iff_integrable_sq hcont.aestronglyMeasurable).2 ?_
  rw [B0579.integrable_cellMeasure_iff]
  obtain ⟨K3, hK3⟩ := gs_absorb (M := max m 0) (le_max_right m 0)
  have hG := gs_integrable c ((1 + c ^ 2) ^ (max m 0) * A ^ 2 * K3)
  have hFc : Continuous (fun x : ℝ × ℝ =>
      ((B0579.density m x : NNReal) : ℝ) * (A * Real.exp (-(x.2 ^ 2) / 24)) ^ 2) :=
    (NNReal.continuous_coe.comp (B0579.continuous_density m)).mul (hcont.pow 2)
  have key : ∀ x ∈ B0579.cell c,
      ((B0579.density m x : NNReal) : ℝ) * (A * Real.exp (-(x.2 ^ 2) / 24)) ^ 2 ≤
        (1 + c ^ 2) ^ (max m 0) * A ^ 2 * K3 * Real.exp (-(x.2 ^ 2 / 24)) := by
    intro x hx
    rw [B0579.coe_density, neg_div]
    have hjb := gs_jb (c := c) (m := m) x hx
    have habs := hK3 (x.2 ^ 2) (sq_nonneg _)
    have he0 : 0 ≤ Real.exp (-(x.2 ^ 2 / 24)) := (Real.exp_pos _).le
    have hpos : (0 : ℝ) ≤ (1 + c ^ 2) ^ (max m 0) * A ^ 2 := by positivity
    have step1 : B0579.jb x ^ m * (A * Real.exp (-(x.2 ^ 2 / 24))) ^ 2 ≤
        ((1 + c ^ 2) ^ (max m 0) * (1 + x.2 ^ 2) ^ (max m 0)) *
          (A * Real.exp (-(x.2 ^ 2 / 24))) ^ 2 :=
      mul_le_mul_of_nonneg_right hjb (sq_nonneg _)
    have step2 : ((1 + c ^ 2) ^ (max m 0) * (1 + x.2 ^ 2) ^ (max m 0)) *
          (A * Real.exp (-(x.2 ^ 2 / 24))) ^ 2 =
        ((1 + c ^ 2) ^ (max m 0) * A ^ 2) * ((1 + x.2 ^ 2) ^ (max m 0) *
          Real.exp (-(x.2 ^ 2 / 24))) * Real.exp (-(x.2 ^ 2 / 24)) := by
      ring
    have step3 : ((1 + c ^ 2) ^ (max m 0) * A ^ 2) * ((1 + x.2 ^ 2) ^ (max m 0) *
          Real.exp (-(x.2 ^ 2 / 24))) * Real.exp (-(x.2 ^ 2 / 24)) ≤
        ((1 + c ^ 2) ^ (max m 0) * A ^ 2) * K3 * Real.exp (-(x.2 ^ 2 / 24)) := by
      apply mul_le_mul_of_nonneg_right _ he0
      exact mul_le_mul_of_nonneg_left habs hpos
    have step4 : ((1 + c ^ 2) ^ (max m 0) * A ^ 2) * K3 * Real.exp (-(x.2 ^ 2 / 24)) =
        (1 + c ^ 2) ^ (max m 0) * A ^ 2 * K3 * Real.exp (-(x.2 ^ 2 / 24)) := by
      ring
    linarith [step1, step2, step3, step4]
  simp only [NNReal.smul_def, smul_eq_mul]
  refine Integrable.mono' hG.integrableOn hFc.aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem (B0579.measurableSet_cell c)] with x hx
  have hmem : x.1 ∈ Set.Ico (-(c / 2)) (c / 2) := (Set.mem_prod.1 hx).1
  rw [Real.norm_of_nonneg (mul_nonneg (NNReal.coe_nonneg _) (sq_nonneg _)),
    Set.indicator_of_mem hmem]
  exact key x hx

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst.Pair
