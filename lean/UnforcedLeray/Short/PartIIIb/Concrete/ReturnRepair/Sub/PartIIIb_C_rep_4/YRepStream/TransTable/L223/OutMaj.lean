import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_5_2_2TransOrg
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_4.YRepStream.TransTable.L223.VertYoung
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_2_4_2
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_2_4_3
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_2_4_4
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_2_4_7

/-!
# `L223/OutMaj`: the outward primitive in `L²_τL^{22/3}` (source 4181-4192, 3651-3656)

Mirror of `outMajAnnulusL2` with `q = 22/3`: annulus Fubini with the power `3/22`
(`outAnn7_int`), vertical Young `vertYoungL223`, the old-disk Hölder `vprofHolder`, and the scalar
identity `outAnn7_alg`.
-/

set_option autoImplicit false

noncomputable section

open Filter Set MeasureTheory UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- **Annulus Fubini in `L²_τL^{22/3}`** (source 4164-4167). -/
theorem annulusFubiniL223 (ν R P : ℝ) (hν : 0 < ν) (hR : 0 < R) (_hP : 0 < P)
    (F : ℝ → ℝ → ℝ≥0∞) (hF : Measurable (Function.uncurry F)) :
    IIIa.ltauLq P (22 / 3) (fun τ => (streamAnn ν R).indicator (fun y => F τ (y 2))) =
      ENNReal.ofReal ((Real.pi * ν * R ^ 2 / 4) ^ (3 / 22 : ℝ)) * ltauLq1 P (22 / 3) F := by
  have hmeas : MeasurableSet (streamAnn ν R) := by
    have : streamAnn ν R = ϱ ⁻¹' Icc (R * Real.sqrt ν) (R * Real.sqrt (5 * ν / 4)) := by
      ext y; simp [streamAnn]
    rw [this]
    exact measurable_ϱ measurableSet_Icc
  have hcnn : (0 : ℝ) ≤ Real.pi * ν * R ^ 2 / 4 := by positivity
  have hpt : ∀ τ, (∫⁻ y, (streamAnn ν R).indicator (fun y => F τ (y 2)) y ^ (22 / 3 : ℝ)) ^
        (2 / (22 / 3) : ℝ) =
      ENNReal.ofReal (Real.pi * ν * R ^ 2 / 4) ^ (2 / (22 / 3) : ℝ) *
        (∫⁻ s, F τ s ^ (22 / 3 : ℝ)) ^ (2 / (22 / 3) : ℝ) := by
    intro τ
    have hsec : Measurable fun s : ℝ => F τ s :=
      hF.comp (measurable_const.prodMk measurable_id)
    have hind : ∀ y, (streamAnn ν R).indicator (fun y => F τ (y 2)) y ^ (22 / 3 : ℝ) =
        (streamAnn ν R).indicator (fun y => F τ (y 2) ^ (22 / 3 : ℝ)) y := by
      intro y
      by_cases hy : y ∈ streamAnn ν R
      · simp [Set.indicator_of_mem hy]
      · simp [Set.indicator_of_notMem hy]
    simp_rw [hind]
    rw [lintegral_indicator hmeas, outAnn7_int ν R hν hR (fun s => F τ s) hsec,
      ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)]
  simp only [IIIa.ltauLq, ltauLq1]
  simp only [hpt]
  rw [lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_nonneg (by norm_num)
    ENNReal.ofReal_ne_top)]
  rw [show (ENNReal.ofReal P)⁻¹ * (ENNReal.ofReal (Real.pi * ν * R ^ 2 / 4) ^ (2 / (22 / 3) : ℝ) *
      ∫⁻ τ in Ioc 0 P, (∫⁻ s, F τ s ^ (22 / 3 : ℝ)) ^ (2 / (22 / 3) : ℝ)) =
      ENNReal.ofReal (Real.pi * ν * R ^ 2 / 4) ^ (2 / (22 / 3) : ℝ) *
      ((ENNReal.ofReal P)⁻¹ * ∫⁻ τ in Ioc 0 P, (∫⁻ s, F τ s ^ (22 / 3 : ℝ)) ^ (2 / (22 / 3) : ℝ))
      by ring]
  rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), ← ENNReal.rpow_mul,
    ← ENNReal.ofReal_rpow_of_nonneg hcnn (by norm_num)]
  congr 2
  norm_num

/-- **The outward primitive majorant in `L²_τL^{22/3}`** (source 4181-4192; any `a ≥ 0`, any
period): `‖1_ann outMaj a D g‖_{L²_τL^{22/3}} ≤ C (R√ν)^{-13/11}‖g‖_{L²_τL^{22/19}}`. -/
theorem outMajAnnulusL223 : ∃ C : ℝ, 0 ≤ C ∧ ∀ (ν R P a : ℝ), 0 < ν → 0 < R → 0 < P → 0 ≤ a →
    ∀ g : ℝ → Space → ℝ≥0∞, Measurable (Function.uncurry g) → (∀ τ z, g (τ + P) z = g τ z) →
      (∀ τ z, R * Real.sqrt (5 * ν / 6) < ϱ z → g τ z = 0) →
        IIIa.ltauLq P (22 / 3) (fun τ => (streamAnn ν R).indicator
            (fun y => outMaj a (R * Real.sqrt ν - R * Real.sqrt (5 * ν / 6)) g τ (ϱ y) (y 2))) ≤
          ENNReal.ofReal (C * (R * Real.sqrt ν) ^ (-(13 / 11 : ℝ))) * IIIa.ltauLq P (22 / 19) g := by
  obtain ⟨Cy, hCy, hY⟩ := vertYoungL223
  have hF := annulusFubiniL223
  have hs1 : Real.sqrt (5 / 6 : ℝ) < 1 := by
    have h := Real.sqrt_lt_sqrt (by norm_num : (0 : ℝ) ≤ 5 / 6) (by norm_num : (5 / 6 : ℝ) < 1)
    rwa [Real.sqrt_one] at h
  have hs0 : 0 ≤ Real.sqrt (5 / 6 : ℝ) := Real.sqrt_nonneg _
  have hd0 : 0 < 1 - Real.sqrt (5 / 6 : ℝ) := by linarith
  refine ⟨Cy * ((Real.pi / 4) ^ (3 / 22 : ℝ) * (Real.pi * (5 / 6)) ^ (3 / 22 : ℝ) *
      (1 - Real.sqrt (5 / 6 : ℝ)) ^ (-2 + 3 / 11 : ℝ) * (1 - Real.sqrt (5 / 6 : ℝ))⁻¹),
    mul_nonneg hCy (mul_nonneg (mul_nonneg (mul_nonneg (by positivity) (by positivity))
      (Real.rpow_nonneg hd0.le _)) (inv_nonneg.2 hd0.le)), ?_⟩
  intro ν R P a hν hR hP0 ha g hg hper hsupp
  have hsν : 0 < Real.sqrt ν := Real.sqrt_pos.2 hν
  have hrIn0 : 0 < R * Real.sqrt ν := mul_pos hR hsν
  have hsq : Real.sqrt (5 * ν / 6) = Real.sqrt (5 / 6 : ℝ) * Real.sqrt ν := by
    rw [← Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 5 / 6)]
    congr 1; ring
  have hrO : R * Real.sqrt (5 * ν / 6) = Real.sqrt (5 / 6 : ℝ) * (R * Real.sqrt ν) := by
    rw [hsq]; ring
  have hD : R * Real.sqrt ν - R * Real.sqrt (5 * ν / 6) =
      (1 - Real.sqrt (5 / 6 : ℝ)) * (R * Real.sqrt ν) := by
    rw [hrO]; ring
  have hD0 : 0 < R * Real.sqrt ν - R * Real.sqrt (5 * ν / 6) := by
    rw [hD]; exact mul_pos hd0 hrIn0
  have hrO0 : 0 ≤ R * Real.sqrt (5 * ν / 6) := by
    rw [hrO]; exact mul_nonneg hs0 hrIn0.le
  have hrOlt : R * Real.sqrt (5 * ν / 6) < R * Real.sqrt ν := by
    have := mul_lt_mul_of_pos_right hs1 hrIn0
    rw [hrO]; linarith
  have hVM := vertMeasurable g hg
  have hvm : Measurable (Function.uncurry (vprof g)) := hVM.1
  have hunc : Measurable (Function.uncurry (vertRed a (R * Real.sqrt ν)
      (R * Real.sqrt ν - R * Real.sqrt (5 * ν / 6)) g)) :=
    hVM.2 a (R * Real.sqrt ν) (R * Real.sqrt ν - R * Real.sqrt (5 * ν / 6))
  have hvper : ∀ τ' s, vprof g (τ' + P) s = vprof g τ' s := by
    intro τ' s
    simp only [vprof, hper]
  -- step 1: `outMaj` is dominated by `vertRed` on the annulus
  have stepA : IIIa.ltauLq P (22 / 3) (fun τ => (streamAnn ν R).indicator
      (fun y => outMaj a (R * Real.sqrt ν - R * Real.sqrt (5 * ν / 6)) g τ (ϱ y) (y 2))) ≤
      IIIa.ltauLq P (22 / 3) (fun τ => (streamAnn ν R).indicator
      (fun y => vertRed a (R * Real.sqrt ν) (R * Real.sqrt ν - R * Real.sqrt (5 * ν / 6)) g τ
        (y 2))) := by
    refine IIIa.ltauLq_mono P (22 / 3) (by norm_num) (fun τ y => ?_)
    dsimp only
    by_cases hy : y ∈ streamAnn ν R
    · rw [Set.indicator_of_mem hy, Set.indicator_of_mem hy]
      exact outMajReduce a (R * Real.sqrt (5 * ν / 6)) (R * Real.sqrt ν) hrO0 hrOlt g hg hsupp τ
        (ϱ y) (y 2) hy.1
    · rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hy]
  -- step 2: annulus Fubiniin `L²`
  have stepB := hF ν R P hν hR hP0 (vertRed a (R * Real.sqrt ν)
      (R * Real.sqrt ν - R * Real.sqrt (5 * ν / 6)) g) hunc
  -- step 3: vertical Young in `L²`
  have stepC := hY a (R * Real.sqrt ν) (R * Real.sqrt ν - R * Real.sqrt (5 * ν / 6)) P ha hD0
    hrIn0 hP0 (vprof g) hvm hvper
  -- step 4: old-disk Hölder
  have stepD := vprofHolder (R * Real.sqrt (5 * ν / 6)) P hrO0 hP0 g hg hsupp
  have hA0 : (0 : ℝ) ≤ (Real.pi * ν * R ^ 2 / 4) ^ (3 / 22 : ℝ) :=
    Real.rpow_nonneg (div_nonneg (mul_nonneg (mul_nonneg Real.pi_pos.le hν.le) (sq_nonneg R))
      (by norm_num)) _
  have hA0 : (0 : ℝ) ≤ (Real.pi * ν * R ^ 2 / 4) ^ (3 / 22 : ℝ) :=
    Real.rpow_nonneg (div_nonneg (mul_nonneg (mul_nonneg Real.pi_pos.le hν.le) (sq_nonneg R))
      (by norm_num)) _
  have hB0 : (0 : ℝ) ≤ Cy * ((R * Real.sqrt ν) / (R * Real.sqrt ν - R * Real.sqrt (5 * ν / 6))) *
      (R * Real.sqrt ν - R * Real.sqrt (5 * ν / 6)) ^ (-2 + 3 / 11 : ℝ) :=
    mul_nonneg (mul_nonneg hCy (div_nonneg hrIn0.le hD0.le)) (Real.rpow_nonneg hD0.le _)
  have hC0 : (0 : ℝ) ≤ (Real.pi * (R * Real.sqrt (5 * ν / 6)) ^ 2) ^ (3 / 22 : ℝ) :=
    Real.rpow_nonneg (mul_nonneg Real.pi_pos.le (sq_nonneg _)) _
  -- the stepC statement is the same as `vertRed` (definitional unfolding)
  have stepC2 : ltauLq1 P (22 / 3) (vertRed a (R * Real.sqrt ν) (R * Real.sqrt ν - R * Real.sqrt (5 * ν / 6)) g)
      ≤ ENNReal.ofReal (Cy * ((R * Real.sqrt ν) / (R * Real.sqrt ν - R * Real.sqrt (5 * ν / 6))) *
          (R * Real.sqrt ν - R * Real.sqrt (5 * ν / 6)) ^ (-2 + 3 / 11 : ℝ)) *
        ltauLq1 P (22 / 19) (vprof g) := stepC
  have key : ENNReal.ofReal ((Real.pi * ν * R ^ 2 / 4) ^ (3 / 22 : ℝ)) *
      (ENNReal.ofReal (Cy * ((R * Real.sqrt ν) / (R * Real.sqrt ν - R * Real.sqrt (5 * ν / 6))) *
          (R * Real.sqrt ν - R * Real.sqrt (5 * ν / 6)) ^ (-2 + 3 / 11 : ℝ)) *
        ENNReal.ofReal ((Real.pi * (R * Real.sqrt (5 * ν / 6)) ^ 2) ^ (3 / 22 : ℝ))) =
      ENNReal.ofReal ((Cy * ((Real.pi / 4) ^ (3 / 22 : ℝ) * (Real.pi * (5 / 6)) ^ (3 / 22 : ℝ) *
        (1 - Real.sqrt (5 / 6 : ℝ)) ^ (-2 + 3 / 11 : ℝ) * (1 - Real.sqrt (5 / 6 : ℝ))⁻¹)) *
        (R * Real.sqrt ν) ^ (-(13 / 11 : ℝ))) := by
    rw [← ENNReal.ofReal_mul hB0, ← ENNReal.ofReal_mul hA0, ← mul_assoc]
    congr 1
    exact outAnn7_alg Cy R ν hν hR
  calc IIIa.ltauLq P (22 / 3) (fun τ => (streamAnn ν R).indicator
        (fun y => outMaj a (R * Real.sqrt ν - R * Real.sqrt (5 * ν / 6)) g τ (ϱ y) (y 2)))
      ≤ IIIa.ltauLq P (22 / 3) (fun τ => (streamAnn ν R).indicator
        (fun y => vertRed a (R * Real.sqrt ν) (R * Real.sqrt ν - R * Real.sqrt (5 * ν / 6)) g τ
          (y 2))) := stepA
    _ = ENNReal.ofReal ((Real.pi * ν * R ^ 2 / 4) ^ (3 / 22 : ℝ)) *
        ltauLq1 P (22 / 3) (vertRed a (R * Real.sqrt ν) (R * Real.sqrt ν - R * Real.sqrt (5 * ν / 6)) g) :=
        stepB
    _ ≤ ENNReal.ofReal ((Real.pi * ν * R ^ 2 / 4) ^ (3 / 22 : ℝ)) *
        (ENNReal.ofReal (Cy * ((R * Real.sqrt ν) / (R * Real.sqrt ν - R * Real.sqrt (5 * ν / 6))) *
          (R * Real.sqrt ν - R * Real.sqrt (5 * ν / 6)) ^ (-2 + 3 / 11 : ℝ)) *
          ltauLq1 P (22 / 19) (vprof g)) :=
        mul_le_mul_of_nonneg_left stepC2 (by positivity)
    _ ≤ ENNReal.ofReal ((Real.pi * ν * R ^ 2 / 4) ^ (3 / 22 : ℝ)) *
        (ENNReal.ofReal (Cy * ((R * Real.sqrt ν) / (R * Real.sqrt ν - R * Real.sqrt (5 * ν / 6))) *
          (R * Real.sqrt ν - R * Real.sqrt (5 * ν / 6)) ^ (-2 + 3 / 11 : ℝ)) *
          (ENNReal.ofReal ((Real.pi * (R * Real.sqrt (5 * ν / 6)) ^ 2) ^ (3 / 22 : ℝ)) *
            IIIa.ltauLq P (22 / 19) g)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left stepD (by positivity))
          (by positivity)
    _ = ENNReal.ofReal ((Cy * ((Real.pi / 4) ^ (3 / 22 : ℝ) * (Real.pi * (5 / 6)) ^ (3 / 22 : ℝ) *
        (1 - Real.sqrt (5 / 6 : ℝ)) ^ (-2 + 3 / 11 : ℝ) * (1 - Real.sqrt (5 / 6 : ℝ))⁻¹)) *
        (R * Real.sqrt ν) ^ (-(13 / 11 : ℝ))) * IIIa.ltauLq P (22 / 19) g := by
        rw [show ∀ a b c x : ℝ≥0∞, a * (b * (c * x)) = a * (b * c) * x from fun a b c x => by ring,
          key]

end UnforcedLeray.Short.PartIIIb.Concrete

end
