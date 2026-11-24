import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_5_2_2TransOrg
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_5_2_2.AnnulusFubiniL2
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_5_2_2.VertYoungL2
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_2_4_2
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_2_4_3
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_2_4_4

/-!
# `PartIII-b:C/rep/5/2/2/10`: `OutMajAnnulusL2` (the outward primitive majorant in `L²_τL²`)

Source `the November 2 reference manuscript` 4181-4192, 3651-3656, 5590-5592.

Composition, mirroring `outMajAnnulus` (`Sub/PartIII-b_C_rep_2_4_7.lean`) with `L²` in place of
`L^{22/3}`:
1. on `streamAnn`, `ϱ y ≥ rIn`, so `outMaj` is bounded by `vertRed` (`outMajReduce`);
2. the annulus Fubini identity `annulusFubiniL2` (energy form) turns `L²_τL²` on the annulus into
   the constant `(πνR²/4)^{1/2} = (π/4)^{1/2} R√ν` times the one-dimensional `L²_τ L²_s` norm
   of `vertRed`;
3. vertical Young `vertYoungL2` with `h = vprof g`;
4. the old-disk Hölder `vprofHolder` with `rOut = R√(5ν/6)`;
5. the scalar identity: the powers of `R√ν` add up to `(R√ν)^{-1/11}`, with the constant
   `(π/4)^{1/2}(π·5/6)^{3/22}(1-√(5/6))^{-26/11}` (`D = (1-√(5/6))R√ν`).
-/

set_option autoImplicit false

noncomputable section

open Filter Set MeasureTheory UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- The scalar identity of the composition: with `s = R√ν`, `d = 1 - √(5/6)`. -/
theorem outMajL2_alg (Cy R ν : ℝ) (hν : 0 < ν) (hR : 0 < R) :
    (Real.pi * ν * R ^ 2 / 4) ^ (1 / 2 : ℝ) *
        (Cy * ((R * Real.sqrt ν) / (R * Real.sqrt ν - R * Real.sqrt (5 * ν / 6))) *
          (R * Real.sqrt ν - R * Real.sqrt (5 * ν / 6)) ^ (-2 + 7 / 11 : ℝ)) *
        (Real.pi * (R * Real.sqrt (5 * ν / 6)) ^ 2) ^ (3 / 22 : ℝ) =
      Cy * ((Real.pi / 4) ^ (1 / 2 : ℝ) * (Real.pi * (5 / 6)) ^ (3 / 22 : ℝ) *
        (1 - Real.sqrt (5 / 6 : ℝ))⁻¹ * (1 - Real.sqrt (5 / 6 : ℝ)) ^ (-2 + 7 / 11 : ℝ)) *
        (R * Real.sqrt ν) ^ (-(1 / 11 : ℝ)) := by
  have hs1 : Real.sqrt (5 / 6 : ℝ) < 1 := by
    have h := Real.sqrt_lt_sqrt (by norm_num : (0 : ℝ) ≤ 5 / 6) (by norm_num : (5 / 6 : ℝ) < 1)
    rwa [Real.sqrt_one] at h
  have hs0 : 0 ≤ Real.sqrt (5 / 6 : ℝ) := Real.sqrt_nonneg _
  have hd0 : 0 < 1 - Real.sqrt (5 / 6 : ℝ) := by linarith
  have hsq56 : Real.sqrt (5 / 6 : ℝ) ^ 2 = 5 / 6 := Real.sq_sqrt (by norm_num)
  have hsν : 0 < Real.sqrt ν := Real.sqrt_pos.2 hν
  have hrIn0 : 0 < R * Real.sqrt ν := mul_pos hR hsν
  have hsq : Real.sqrt (5 * ν / 6) = Real.sqrt (5 / 6 : ℝ) * Real.sqrt ν := by
    rw [← Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 5 / 6)]
    congr 1; ring
  have hrO : R * Real.sqrt (5 * ν / 6) = Real.sqrt (5 / 6 : ℝ) * (R * Real.sqrt ν) := by
    rw [hsq]; ring
  have hc : Real.pi * ν * R ^ 2 / 4 = (Real.pi / 4) * (R * Real.sqrt ν) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hν.le]; ring
  have hG : Real.pi * (R * Real.sqrt (5 * ν / 6)) ^ 2 =
      (Real.pi * (5 / 6)) * (R * Real.sqrt ν) ^ 2 := by
    rw [hrO, mul_pow (Real.sqrt (5 / 6 : ℝ)), hsq56]; ring
  have hD : R * Real.sqrt ν - R * Real.sqrt (5 * ν / 6) =
      (1 - Real.sqrt (5 / 6 : ℝ)) * (R * Real.sqrt ν) := by
    rw [hrO]; ring
  have hA : (Real.pi * ν * R ^ 2 / 4) ^ (1 / 2 : ℝ) =
      (Real.pi / 4) ^ (1 / 2 : ℝ) * (R * Real.sqrt ν) ^ (1 : ℝ) := by
    rw [hc, Real.mul_rpow (show (0 : ℝ) ≤ Real.pi / 4 by positivity) (sq_nonneg _),
      ← Real.rpow_natCast, ← Real.rpow_mul hrIn0.le]
    norm_num
  have hGp : (Real.pi * (R * Real.sqrt (5 * ν / 6)) ^ 2) ^ (3 / 22 : ℝ) =
      (Real.pi * (5 / 6)) ^ (3 / 22 : ℝ) * (R * Real.sqrt ν) ^ (3 / 11 : ℝ) := by
    rw [hG, Real.mul_rpow (show (0 : ℝ) ≤ Real.pi * (5 / 6) by positivity) (sq_nonneg _),
      ← Real.rpow_natCast, ← Real.rpow_mul hrIn0.le]
    norm_num
  have hB : (R * Real.sqrt ν) / (R * Real.sqrt ν - R * Real.sqrt (5 * ν / 6)) =
      (1 - Real.sqrt (5 / 6 : ℝ))⁻¹ := by
    have h1 : (1 - Real.sqrt (5 / 6 : ℝ)) ≠ 0 := hd0.ne'
    have h2 : R * Real.sqrt ν ≠ 0 := hrIn0.ne'
    rw [hD]
    field_simp
  have hE : (R * Real.sqrt ν - R * Real.sqrt (5 * ν / 6)) ^ (-2 + 7 / 11 : ℝ) =
      (1 - Real.sqrt (5 / 6 : ℝ)) ^ (-2 + 7 / 11 : ℝ) * (R * Real.sqrt ν) ^ (-2 + 7 / 11 : ℝ) := by
    rw [hD, Real.mul_rpow hd0.le hrIn0.le]
  have hpow : (R * Real.sqrt ν) ^ (1 : ℝ) * (R * Real.sqrt ν) ^ (-2 + 7 / 11 : ℝ) *
      (R * Real.sqrt ν) ^ (3 / 11 : ℝ) = (R * Real.sqrt ν) ^ (-(1 / 11 : ℝ)) := by
    rw [← Real.rpow_add hrIn0, ← Real.rpow_add hrIn0]
    norm_num
  rw [hA, hGp, hB, hE]
  linear_combination (Cy * (Real.pi / 4) ^ (1 / 2 : ℝ) * (Real.pi * (5 / 6)) ^ (3 / 22 : ℝ) *
    (1 - Real.sqrt (5 / 6 : ℝ)) ^ (-2 + 7 / 11 : ℝ) * (1 - Real.sqrt (5 / 6 : ℝ))⁻¹) * hpow

/-- **The outward primitive majorant in `L²_τL²`** (`OutMajAnnulusL2`, source 4181-4192). -/
theorem outMajAnnulusL2 : OutMajAnnulusL2 := by
  have hYP := vertYoungL2
  unfold VertYoungL2 at hYP
  obtain ⟨Cy, hCy, hY⟩ := hYP
  have hF := annulusFubiniL2
  unfold AnnulusFubiniL2 at hF
  have hs1 : Real.sqrt (5 / 6 : ℝ) < 1 := by
    have h := Real.sqrt_lt_sqrt (by norm_num : (0 : ℝ) ≤ 5 / 6) (by norm_num : (5 / 6 : ℝ) < 1)
    rwa [Real.sqrt_one] at h
  have hs0 : 0 ≤ Real.sqrt (5 / 6 : ℝ) := Real.sqrt_nonneg _
  have hd0 : 0 < 1 - Real.sqrt (5 / 6 : ℝ) := by linarith
  refine ⟨Cy * ((Real.pi / 4) ^ (1 / 2 : ℝ) * (Real.pi * (5 / 6)) ^ (3 / 22 : ℝ) *
      (1 - Real.sqrt (5 / 6 : ℝ))⁻¹ * (1 - Real.sqrt (5 / 6 : ℝ)) ^ (-2 + 7 / 11 : ℝ)),
    mul_nonneg hCy (mul_nonneg (mul_nonneg (mul_nonneg (by positivity) (by positivity))
      (inv_nonneg.2 hd0.le)) (Real.rpow_nonneg hd0.le _)), ?_⟩
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
  have stepA : IIIa.ltauLq P 2 (fun τ => (streamAnn ν R).indicator
      (fun y => outMaj a (R * Real.sqrt ν - R * Real.sqrt (5 * ν / 6)) g τ (ϱ y) (y 2))) ≤
      IIIa.ltauLq P 2 (fun τ => (streamAnn ν R).indicator
      (fun y => vertRed a (R * Real.sqrt ν) (R * Real.sqrt ν - R * Real.sqrt (5 * ν / 6)) g τ
        (y 2))) := by
    refine IIIa.ltauLq_mono P 2 (by norm_num) (fun τ y => ?_)
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
  have hA0 : (0 : ℝ) ≤ (Real.pi * ν * R ^ 2 / 4) ^ (1 / 2 : ℝ) :=
    Real.rpow_nonneg (div_nonneg (mul_nonneg (mul_nonneg Real.pi_pos.le hν.le) (sq_nonneg R))
      (by norm_num)) _
  have hA0 : (0 : ℝ) ≤ (Real.pi * ν * R ^ 2 / 4) ^ (1 / 2 : ℝ) :=
    Real.rpow_nonneg (div_nonneg (mul_nonneg (mul_nonneg Real.pi_pos.le hν.le) (sq_nonneg R))
      (by norm_num)) _
  have hB0 : (0 : ℝ) ≤ Cy * ((R * Real.sqrt ν) / (R * Real.sqrt ν - R * Real.sqrt (5 * ν / 6))) *
      (R * Real.sqrt ν - R * Real.sqrt (5 * ν / 6)) ^ (-2 + 7 / 11 : ℝ) :=
    mul_nonneg (mul_nonneg hCy (div_nonneg hrIn0.le hD0.le)) (Real.rpow_nonneg hD0.le _)
  have hC0 : (0 : ℝ) ≤ (Real.pi * (R * Real.sqrt (5 * ν / 6)) ^ 2) ^ (3 / 22 : ℝ) :=
    Real.rpow_nonneg (mul_nonneg Real.pi_pos.le (sq_nonneg _)) _
  -- the stepC statement is the same as `vertRed` (definitional unfolding)
  have stepC2 : ltauLq1 P 2 (vertRed a (R * Real.sqrt ν) (R * Real.sqrt ν - R * Real.sqrt (5 * ν / 6)) g)
      ≤ ENNReal.ofReal (Cy * ((R * Real.sqrt ν) / (R * Real.sqrt ν - R * Real.sqrt (5 * ν / 6))) *
          (R * Real.sqrt ν - R * Real.sqrt (5 * ν / 6)) ^ (-2 + 7 / 11 : ℝ)) *
        ltauLq1 P (22 / 19) (vprof g) := stepC
  have key : ENNReal.ofReal ((Real.pi * ν * R ^ 2 / 4) ^ (1 / 2 : ℝ)) *
      (ENNReal.ofReal (Cy * ((R * Real.sqrt ν) / (R * Real.sqrt ν - R * Real.sqrt (5 * ν / 6))) *
          (R * Real.sqrt ν - R * Real.sqrt (5 * ν / 6)) ^ (-2 + 7 / 11 : ℝ)) *
        ENNReal.ofReal ((Real.pi * (R * Real.sqrt (5 * ν / 6)) ^ 2) ^ (3 / 22 : ℝ))) =
      ENNReal.ofReal ((Cy * ((Real.pi / 4) ^ (1 / 2 : ℝ) * (Real.pi * (5 / 6)) ^ (3 / 22 : ℝ) *
        (1 - Real.sqrt (5 / 6 : ℝ))⁻¹ * (1 - Real.sqrt (5 / 6 : ℝ)) ^ (-2 + 7 / 11 : ℝ))) *
        (R * Real.sqrt ν) ^ (-(1 / 11 : ℝ))) := by
    rw [← ENNReal.ofReal_mul hB0, ← ENNReal.ofReal_mul hA0, ← mul_assoc]
    congr 1
    exact outMajL2_alg Cy R ν hν hR
  calc IIIa.ltauLq P 2 (fun τ => (streamAnn ν R).indicator
        (fun y => outMaj a (R * Real.sqrt ν - R * Real.sqrt (5 * ν / 6)) g τ (ϱ y) (y 2)))
      ≤ IIIa.ltauLq P 2 (fun τ => (streamAnn ν R).indicator
        (fun y => vertRed a (R * Real.sqrt ν) (R * Real.sqrt ν - R * Real.sqrt (5 * ν / 6)) g τ
          (y 2))) := stepA
    _ = ENNReal.ofReal ((Real.pi * ν * R ^ 2 / 4) ^ (1 / 2 : ℝ)) *
        ltauLq1 P 2 (vertRed a (R * Real.sqrt ν) (R * Real.sqrt ν - R * Real.sqrt (5 * ν / 6)) g) :=
        stepB
    _ ≤ ENNReal.ofReal ((Real.pi * ν * R ^ 2 / 4) ^ (1 / 2 : ℝ)) *
        (ENNReal.ofReal (Cy * ((R * Real.sqrt ν) / (R * Real.sqrt ν - R * Real.sqrt (5 * ν / 6))) *
          (R * Real.sqrt ν - R * Real.sqrt (5 * ν / 6)) ^ (-2 + 7 / 11 : ℝ)) *
          ltauLq1 P (22 / 19) (vprof g)) :=
        mul_le_mul_of_nonneg_left stepC2 (by positivity)
    _ ≤ ENNReal.ofReal ((Real.pi * ν * R ^ 2 / 4) ^ (1 / 2 : ℝ)) *
        (ENNReal.ofReal (Cy * ((R * Real.sqrt ν) / (R * Real.sqrt ν - R * Real.sqrt (5 * ν / 6))) *
          (R * Real.sqrt ν - R * Real.sqrt (5 * ν / 6)) ^ (-2 + 7 / 11 : ℝ)) *
          (ENNReal.ofReal ((Real.pi * (R * Real.sqrt (5 * ν / 6)) ^ 2) ^ (3 / 22 : ℝ)) *
            IIIa.ltauLq P (22 / 19) g)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left stepD (by positivity))
          (by positivity)
    _ = ENNReal.ofReal ((Cy * ((Real.pi / 4) ^ (1 / 2 : ℝ) * (Real.pi * (5 / 6)) ^ (3 / 22 : ℝ) *
        (1 - Real.sqrt (5 / 6 : ℝ))⁻¹ * (1 - Real.sqrt (5 / 6 : ℝ)) ^ (-2 + 7 / 11 : ℝ))) *
        (R * Real.sqrt ν) ^ (-(1 / 11 : ℝ))) * IIIa.ltauLq P (22 / 19) g := by
        rw [show ∀ a b c x : ℝ≥0∞, a * (b * (c * x)) = a * (b * c) * x from fun a b c x => by ring,
          key]

end UnforcedLeray.Short.PartIIIb.Concrete

end
