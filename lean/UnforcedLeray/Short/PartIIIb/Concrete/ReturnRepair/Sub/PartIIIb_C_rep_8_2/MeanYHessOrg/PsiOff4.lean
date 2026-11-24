import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_2.MeanYHessOrg.Props
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_2.Pres.MeanGrad.PsiOff

/-!
# `scPsiBoundOff4`: the fourth derivative of the outward stream primitive off the ray

Source `the November 2 reference manuscript`
4180-4182, 5400-5413. This is the `m = 4` case of `scPsiBoundOff` (`Pres/MeanGrad/PsiOff.lean`),
with the same proof: the Leibniz sum runs over `i ≤ 4`, the bound `2^m ≤ 16` replaces `2^m ≤ 8`,
and the constant `512` is kept (it dominates `16 · 4 = 64`).
The helpers `PsiOffAux.psiI_bound_off` and `PsiOffAux.term_off` are valid for all `j ≤ 7`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Metric Filter Topology UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

open PsiOffAux PsiBoundAux in
/-- **`scPsiBoundOff4`** (source 4180-4182, 5400-5413): the `m = 4` case of `scPsiBoundOff`. -/
theorem scPsiBoundOff4 : SCPsiBoundOff4 := by
  refine ⟨512, ?_⟩
  intro ν B Z hν hB hZ m hm y hy
  have hcyl_sq := cylR_sq_eq' y
  have hr2 : 0 < cylR y ^ 2 := lt_of_lt_of_le hν hy
  have hr0 : 0 ≤ cylR y := by unfold cylR; positivity
  have hr : 0 < cylR y :=
    lt_of_le_of_ne hr0 (fun h => by rw [← h] at hr2; norm_num at hr2)
  have hyU : y ∈ psiU ν := by
    show ν * (11 / 12) < eucSq y ∧ 0 < cylR y
    refine ⟨?_, hr⟩
    rw [psiFdom_eucSq]
    nlinarith [sq_nonneg (y 2), sq_nonneg (y 0), sq_nonneg (y 1)]
  have hEpos : 0 < eucSq y := by
    rw [psiFdom_eucSq]; nlinarith [sq_nonneg (y 2), sq_nonneg (y 0), sq_nonneg (y 1)]
  have hEq : streamPsi Z =ᶠ[𝓝 y]
      (fun z => -(z 0 ^ 2 + z 1 ^ 2) * ∫ t in Ioi (1 : ℝ), psiF Z t z) :=
    Filter.eventually_of_mem ((psiU_isOpen ν).mem_nhds hyU) (fun z hz =>
      scPsiSubst Z z (show ν * (11 / 12) < eucSq z ∧ 0 < cylR z from hz).2)
  rw [(hEq.iteratedFDeriv (𝕜 := ℝ) m).self_of_nhds]
  have hIc : ContDiffOn ℝ 7 (fun z => ∫ t in Ioi (1 : ℝ), psiF Z t z) (psiU ν) :=
    scParamInt7 (psiU ν) (psiF Z) (psiU_isOpen ν)
      (fun t ht => scPsiF_smooth ν B Z hν hB hZ t ht)
      (fun k hk x hx => scPsiF_meas ν B Z hν hB hZ k hk x hx)
      (fun x₀ hx₀ => scPsiF_dom ν B Z hν hB hZ x₀ hx₀)
  have hqc : ContDiffOn ℝ 7 (fun z : Vec3 => -(z 0 ^ 2 + z 1 ^ 2)) (psiU ν) :=
    (by fun_prop : ContDiff ℝ 7 (fun z : Vec3 => -(z 0 ^ 2 + z 1 ^ 2))).contDiffOn
  have hm7 : m ≤ 7 := by omega
  have hmle : (m : WithTop ℕ∞) ≤ 7 := by exact_mod_cast hm7
  have hL := norm_iteratedFDerivWithin_mul_le (𝕜 := ℝ) hqc hIc
    (psiU_isOpen ν).uniqueDiffOn hyU hmle
  have hsum : (∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ) *
      ‖iteratedFDerivWithin ℝ i (fun z : Vec3 => -(z 0 ^ 2 + z 1 ^ 2)) (psiU ν) y‖ *
      ‖iteratedFDerivWithin ℝ (m - i) (fun z => ∫ t in Ioi (1 : ℝ), psiF Z t z) (psiU ν) y‖)
      = ∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ) *
      ‖iteratedFDeriv ℝ i (fun z : Vec3 => -(z 0 ^ 2 + z 1 ^ 2)) y‖ *
      ‖iteratedFDeriv ℝ (m - i) (fun z => ∫ t in Ioi (1 : ℝ), psiF Z t z) y‖ :=
    Finset.sum_congr rfl (fun i _ => by
      rw [(iteratedFDerivWithin_of_isOpen i (psiU_isOpen ν)) hyU,
        (iteratedFDerivWithin_of_isOpen (m - i) (psiU_isOpen ν)) hyU])
  have hL2 : ‖iteratedFDeriv ℝ m (fun z => -(z 0 ^ 2 + z 1 ^ 2) *
      ∫ t in Ioi (1 : ℝ), psiF Z t z) y‖
      ≤ ∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ) *
        ‖iteratedFDeriv ℝ i (fun z : Vec3 => -(z 0 ^ 2 + z 1 ^ 2)) y‖ *
        ‖iteratedFDeriv ℝ (m - i) (fun z => ∫ t in Ioi (1 : ℝ), psiF Z t z) y‖ := by
    rw [← (iteratedFDerivWithin_of_isOpen m (psiU_isOpen ν)) hyU]
    exact hL.trans (le_of_eq hsum)
  have hbound : ∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ) *
        ‖iteratedFDeriv ℝ i (fun z : Vec3 => -(z 0 ^ 2 + z 1 ^ 2)) y‖ *
        ‖iteratedFDeriv ℝ (m - i) (fun z => ∫ t in Ioi (1 : ℝ), psiF Z t z) y‖
      ≤ ∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ) *
        (4 * B * (eucSq y)⁻¹ * (cylR y ^ m)⁻¹) := by
    apply Finset.sum_le_sum
    intro i hi
    have hi' : i ≤ m := by
      have := Finset.mem_range.mp hi
      omega
    have t := term_off (cylR y) B (eucSq y)⁻¹ _ _ i (m - i) m hr hB (inv_nonneg.mpr hEpos.le)
      (norm_nonneg _) (norm_nonneg _)
      (by omega) (qPoly_iter y i) (psiI_bound_off ν B Z hν hB hZ y hyU (m - i) (by omega))
    have hc : (0 : ℝ) ≤ (m.choose i : ℝ) := Nat.cast_nonneg _
    calc (m.choose i : ℝ) * ‖iteratedFDeriv ℝ i (fun z : Vec3 => -(z 0 ^ 2 + z 1 ^ 2)) y‖ *
          ‖iteratedFDeriv ℝ (m - i) (fun z => ∫ t in Ioi (1 : ℝ), psiF Z t z) y‖
        = (m.choose i : ℝ) * (‖iteratedFDeriv ℝ i (fun z : Vec3 => -(z 0 ^ 2 + z 1 ^ 2)) y‖ *
          ‖iteratedFDeriv ℝ (m - i) (fun z => ∫ t in Ioi (1 : ℝ), psiF Z t z) y‖) := by ring
      _ ≤ (m.choose i : ℝ) * (4 * B * (eucSq y)⁻¹ * (cylR y ^ m)⁻¹) :=
          mul_le_mul_of_nonneg_left t hc
  have hpow : (2 : ℝ) ^ m ≤ 16 := by
    rw [hm]; norm_num
  have hsc : ∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ) = 2 ^ m := by
    rw [← Nat.cast_sum, Nat.sum_range_choose]
    push_cast
    rfl
  have hconv : cylR y ^ (-(m : ℝ)) = (cylR y ^ m)⁻¹ := by
    rw [Real.rpow_neg hr.le, Real.rpow_natCast]
  have hK : 0 ≤ 4 * B * (eucSq y)⁻¹ * (cylR y ^ m)⁻¹ := by
    have := inv_nonneg.mpr (pow_nonneg hr.le m)
    have := inv_nonneg.mpr hEpos.le
    positivity
  have hX : 0 ≤ B * (eucSq y)⁻¹ * (cylR y ^ m)⁻¹ := by
    have := inv_nonneg.mpr (pow_nonneg hr.le m)
    have := inv_nonneg.mpr hEpos.le
    positivity
  calc ‖iteratedFDeriv ℝ m (fun z => -(z 0 ^ 2 + z 1 ^ 2) *
          ∫ t in Ioi (1 : ℝ), psiF Z t z) y‖
      ≤ _ := hL2
    _ ≤ _ := hbound
    _ = (∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ)) * (4 * B * (eucSq y)⁻¹ * (cylR y ^ m)⁻¹) := by
        rw [Finset.sum_mul]
    _ = 2 ^ m * (4 * B * (eucSq y)⁻¹ * (cylR y ^ m)⁻¹) := by rw [hsc]
    _ ≤ 16 * (4 * B * (eucSq y)⁻¹ * (cylR y ^ m)⁻¹) := mul_le_mul_of_nonneg_right hpow hK
    _ ≤ 512 * B * cylR y ^ (-(m : ℝ)) * (eucSq y)⁻¹ := by
        rw [hconv]; nlinarith [hX]

end UnforcedLeray.Short.PartIIIb.Concrete
