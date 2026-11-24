import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_2.MeanYHessOrg.Props
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_2.MeanYHessOrg.PsiOff4
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_2.Pres.MeanGrad.XJetOff
import UnforcedLeray.Short.PartIIIb.Concrete.SourceL.Ambient.StreamCut.ChiJet

/-!
# `SCXJetOff4`: the fourth derivative of the stream-cut field off the ray

Source `the November 2 reference manuscript`
lines 4178-4186 (`𝒞_yZ = χ_yZ + (χ_y'/r)Ψ_Z e_z`) and 5400-5413.

This is the `m = 4` case of `scXJetOff` (`Pres/MeanGrad/XJetOff.lean`), with the same proof.
The only change is the Ψ-term: `scPsiBoundOff` covers orders `≤ 3`, and `scPsiBoundOff4` covers
order `4`. For every `j ≤ 4`, the Ψ-bound `‖∂^jΨ_Z(y)‖ ≤ (|C1| + |C1'|) B r^{-j}|y|^{-2}` holds
(case split `j ≤ 3` or `j = 4`). The Leibniz constant is `2^4 (|C2| + |C2|(|C1| + |C1'|)) ≤ 128(...)`.
The helpers `xjo_abs` and `xjo_zJetE` come from `XJetOff`; the χ-jet bound `scChiJet` is used at
orders `≤ 4 ≤ 7`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- **`scXJetOff4`** (source 4178-4186, 5400-5413): the `m = 4` case of `scXJetOff`. -/
theorem scXJetOff4 (χy : ℝ → ℝ) : SCXJetOff4 χy := by
  obtain ⟨C1, hC1⟩ := scPsiBoundOff
  obtain ⟨C1', hC1'⟩ := scPsiBoundOff4
  obtain ⟨C2, hC2⟩ := scChiJet χy
  refine ⟨128 * (|C2| + |C2| * (|C1| + |C1'|)), ?_⟩
  intro ν B hν hB Z hZ hχ y hge m hm
  have hr : 0 < cylR y := by
    have h0 := xj_cylR_nonneg y
    nlinarith
  have he0 : 0 < eucSq y := lt_of_lt_of_le (pow_pos hr 2) (xj_sq_le_eucSq y)
  have hyW : y ∈ xjWReg ν :=
    ⟨lt_of_lt_of_le (by linarith) (le_trans hge (xj_sq_le_eucSq y)), hr⟩
  obtain ⟨hZc, hZb⟩ := id hZ
  have hopen := xjWReg_isOpen ν
  have huniq : UniqueDiffOn ℝ (xjWReg ν) := hopen.uniqueDiffOn
  have hφW : ContDiffOn ℝ 7 (xjPhi ν χy) (xjWReg ν) := fun w hw =>
    ((hC2 ν hν hχ w hw.2).1).contDiffWithinAt
  have hgW : ContDiffOn ℝ 7 (xjG ν χy) (xjWReg ν) := fun w hw =>
    ((hC2 ν hν hχ w hw.2).2.1).contDiffWithinAt
  have hZW : ContDiffOn ℝ 7 Z (xjWReg ν) := hZc.mono (fun w hw => hw.1)
  have hΨW : ContDiffOn ℝ 7 (streamPsi Z) (xjWReg ν) := scPsiSmooth ν B Z hν hB hZ
  have hφY : ContDiffWithinAt ℝ 7 (xjPhi ν χy) (xjWReg ν) y := hφW y hyW
  have hZY : ContDiffWithinAt ℝ 7 Z (xjWReg ν) y := hZW y hyW
  have hgY : ContDiffWithinAt ℝ 7 (xjG ν χy) (xjWReg ν) y := hgW y hyW
  have hΨY : ContDiffWithinAt ℝ 7 (streamPsi Z) (xjWReg ν) y := hΨW y hyW
  have hA0 : ContDiffWithinAt ℝ 7 (fun w => xjPhi ν χy w • Z w) (xjWReg ν) y :=
    hφY.smul hZY
  have hgΨY : ContDiffWithinAt ℝ 7 (fun w => xjG ν χy w * streamPsi Z w) (xjWReg ν) y :=
    hgY.mul hΨY
  have hB0 : ContDiffWithinAt ℝ 7 (fun w => (xjG ν χy w * streamPsi Z w) • xjEz)
      (xjWReg ν) y :=
    hgΨY.smul (contDiffWithinAt_const (c := xjEz))
  have hm7n : m ≤ 7 := by omega
  have hm7 : (m : WithTop ℕ∞) ≤ 7 := by exact_mod_cast hm7n
  have hA1 : ContDiffWithinAt ℝ (m : WithTop ℕ∞) (fun w => xjPhi ν χy w • Z w)
      (xjWReg ν) y := hA0.of_le hm7
  have hB1 : ContDiffWithinAt ℝ (m : WithTop ℕ∞) (fun w => (xjG ν χy w * streamPsi Z w) • xjEz)
      (xjWReg ν) y := hB0.of_le hm7
  -- Ψ-bound for every order `j ≤ 4`, with the constant `|C1| + |C1'|`
  have hψall : ∀ j : ℕ, j ≤ 4 →
      ‖iteratedFDeriv ℝ j (streamPsi Z) y‖ ≤
        (|C1| + |C1'|) * B * cylR y ^ (-(j : ℝ)) * (eucSq y)⁻¹ := by
    intro j hj
    have hK : 0 ≤ B * cylR y ^ (-(j : ℝ)) * (eucSq y)⁻¹ :=
      mul_nonneg (mul_nonneg hB (Real.rpow_nonneg (xj_cylR_nonneg y) _))
        (inv_nonneg.mpr he0.le)
    have hC : |C1| ≤ |C1| + |C1'| := by linarith [abs_nonneg C1']
    have hC' : |C1'| ≤ |C1| + |C1'| := by linarith [abs_nonneg C1]
    by_cases hj3 : j ≤ 3
    · have h1 := xjo_abs hB (xj_cylR_nonneg y) (inv_nonneg.mpr he0.le)
        (hC1 ν B Z hν hB hZ j hj3 y hge)
      calc _ ≤ |C1| * B * cylR y ^ (-(j : ℝ)) * (eucSq y)⁻¹ := h1
        _ = |C1| * (B * cylR y ^ (-(j : ℝ)) * (eucSq y)⁻¹) := by ring
        _ ≤ (|C1| + |C1'|) * (B * cylR y ^ (-(j : ℝ)) * (eucSq y)⁻¹) :=
            mul_le_mul_of_nonneg_right hC hK
        _ = (|C1| + |C1'|) * B * cylR y ^ (-(j : ℝ)) * (eucSq y)⁻¹ := by ring
    · have hj4 : j = 4 := by omega
      have h1 := xjo_abs hB (xj_cylR_nonneg y) (inv_nonneg.mpr he0.le)
        (hC1' ν B Z hν hB hZ j hj4 y hge)
      calc _ ≤ |C1'| * B * cylR y ^ (-(j : ℝ)) * (eucSq y)⁻¹ := h1
        _ = |C1'| * (B * cylR y ^ (-(j : ℝ)) * (eucSq y)⁻¹) := by ring
        _ ≤ (|C1| + |C1'|) * (B * cylR y ^ (-(j : ℝ)) * (eucSq y)⁻¹) :=
            mul_le_mul_of_nonneg_right hC' hK
        _ = (|C1| + |C1'|) * B * cylR y ^ (-(j : ℝ)) * (eucSq y)⁻¹ := by ring
  -- term bounds for the first Leibniz sum (`χ_y(ν/r²) · Z`)
  have termA : ∀ i ∈ Finset.range (m + 1),
      (m.choose i : ℝ) * ‖iteratedFDerivWithin ℝ i (xjPhi ν χy) (xjWReg ν) y‖ *
          ‖iteratedFDerivWithin ℝ (m - i) Z (xjWReg ν) y‖ ≤
        (m.choose i : ℝ) * (|C2| * B * (eucSq y)⁻¹ * cylR y ^ (-(2 : ℝ) - (m : ℝ))) := by
    intro i hi
    have hi' : i ≤ m := by
      rw [Finset.mem_range] at hi
      omega
    rw [xj_iterWithin_eq hopen hyW, xj_iterWithin_eq hopen hyW]
    have hφb : ‖iteratedFDeriv ℝ i (xjPhi ν χy) y‖ ≤ |C2| * cylR y ^ (-(i : ℝ)) :=
      xj_le_abs_mul_rpow (xj_cylR_nonneg y) ((hC2 ν hν hχ y hr).2.2 i (by omega)).1
    have hZb' : ‖iteratedFDeriv ℝ (m - i) Z y‖ ≤
        B * (eucSq y)⁻¹ * cylR y ^ (-(2 : ℝ) - ((m - i : ℕ) : ℝ)) :=
      xjo_zJetE hB hZb hyW.1 hyW.2 (m - i) (by omega)
    have hexp : cylR y ^ (-(i : ℝ)) * cylR y ^ (-(2 : ℝ) - ((m - i : ℕ) : ℝ)) =
        cylR y ^ (-(2 : ℝ) - (m : ℝ)) := by
      rw [← Real.rpow_add hyW.2]
      congr 1
      rw [Nat.cast_sub hi']
      ring
    have hprod : ‖iteratedFDeriv ℝ i (xjPhi ν χy) y‖ * ‖iteratedFDeriv ℝ (m - i) Z y‖ ≤
        |C2| * B * (eucSq y)⁻¹ * cylR y ^ (-(2 : ℝ) - (m : ℝ)) := by
      have h1' := mul_le_mul hφb hZb' (norm_nonneg _)
        (mul_nonneg (abs_nonneg _) (Real.rpow_nonneg (xj_cylR_nonneg y) _))
      calc _ ≤ _ := h1'
        _ = (|C2| * B * (eucSq y)⁻¹) *
            (cylR y ^ (-(i : ℝ)) * cylR y ^ (-(2 : ℝ) - ((m - i : ℕ) : ℝ))) := by ring
        _ = _ := by rw [hexp]
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left hprod (Nat.cast_nonneg _)
  -- term bounds for the second Leibniz sum (`(χ_y'/r) · Ψ_Z`)
  have termB : ∀ i ∈ Finset.range (m + 1),
      (m.choose i : ℝ) * ‖iteratedFDerivWithin ℝ i (xjG ν χy) (xjWReg ν) y‖ *
          ‖iteratedFDerivWithin ℝ (m - i) (streamPsi Z) (xjWReg ν) y‖ ≤
        (m.choose i : ℝ) * (|C2| * ((|C1| + |C1'|) * B * (eucSq y)⁻¹) *
          cylR y ^ (-(2 : ℝ) - (m : ℝ))) := by
    intro i hi
    have hi' : i ≤ m := by
      rw [Finset.mem_range] at hi
      omega
    rw [xj_iterWithin_eq hopen hyW, xj_iterWithin_eq hopen hyW]
    have hgb : ‖iteratedFDeriv ℝ i (xjG ν χy) y‖ ≤ |C2| * cylR y ^ (-(2 : ℝ) - (i : ℝ)) :=
      xj_le_abs_mul_rpow (xj_cylR_nonneg y) ((hC2 ν hν hχ y hr).2.2 i (by omega)).2
    have hψb : ‖iteratedFDeriv ℝ (m - i) (streamPsi Z) y‖ ≤
        (|C1| + |C1'|) * B * cylR y ^ (-((m - i : ℕ) : ℝ)) * (eucSq y)⁻¹ :=
      hψall (m - i) (by omega)
    have hexpB : cylR y ^ (-(2 : ℝ) - (i : ℝ)) * cylR y ^ (-((m - i : ℕ) : ℝ)) =
        cylR y ^ (-(2 : ℝ) - (m : ℝ)) := by
      rw [← Real.rpow_add hyW.2]
      congr 1
      rw [Nat.cast_sub hi']
      ring
    have hprod : ‖iteratedFDeriv ℝ i (xjG ν χy) y‖ * ‖iteratedFDeriv ℝ (m - i) (streamPsi Z) y‖ ≤
        |C2| * ((|C1| + |C1'|) * B * (eucSq y)⁻¹) * cylR y ^ (-(2 : ℝ) - (m : ℝ)) := by
      have h1' := mul_le_mul hgb hψb (norm_nonneg _)
        (mul_nonneg (abs_nonneg _) (Real.rpow_nonneg (xj_cylR_nonneg y) _))
      calc _ ≤ _ := h1'
        _ = (|C2| * ((|C1| + |C1'|) * B * (eucSq y)⁻¹)) *
            (cylR y ^ (-(2 : ℝ) - (i : ℝ)) * cylR y ^ (-((m - i : ℕ) : ℝ))) := by ring
        _ = _ := by rw [hexpB]
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left hprod (Nat.cast_nonneg _)
  -- the two Leibniz bounds
  have hXb : ‖iteratedFDerivWithin ℝ m (fun w => xjPhi ν χy w • Z w) (xjWReg ν) y‖ ≤
      2 ^ m * (|C2| * B * (eucSq y)⁻¹ * cylR y ^ (-(2 : ℝ) - (m : ℝ))) := by
    have hL := norm_iteratedFDerivWithin_smul_le hφW hZW huniq hyW (n := m)
      (by exact_mod_cast hm7n)
    exact (hL.trans (Finset.sum_le_sum termA)).trans
      (le_of_eq (xj_sum_choose_mul m _))
  have hYb : ‖iteratedFDerivWithin ℝ m (fun w => (xjG ν χy w * streamPsi Z w) • xjEz)
      (xjWReg ν) y‖ ≤
      2 ^ m * (|C2| * ((|C1| + |C1'|) * B * (eucSq y)⁻¹) * cylR y ^ (-(2 : ℝ) - (m : ℝ))) := by
    have hcomp : (fun w => (xjG ν χy w * streamPsi Z w) • xjEz) =
        (ContinuousLinearMap.toSpanSingleton ℝ xjEz) ∘
          (fun w => xjG ν χy w * streamPsi Z w) := by
      funext w
      simp [ContinuousLinearMap.toSpanSingleton_apply]
    have hcomp' := ContinuousLinearMap.norm_iteratedFDerivWithin_comp_left
      (ContinuousLinearMap.toSpanSingleton ℝ xjEz) hgΨY huniq hyW (n := m)
      (by exact_mod_cast hm7n)
    rw [ContinuousLinearMap.norm_toSpanSingleton] at hcomp'
    have hG1 : ‖iteratedFDerivWithin ℝ m (fun w => (xjG ν χy w * streamPsi Z w) • xjEz)
        (xjWReg ν) y‖ ≤ ‖iteratedFDerivWithin ℝ m (fun w => xjG ν χy w * streamPsi Z w)
        (xjWReg ν) y‖ := by
      rw [hcomp]
      exact hcomp'.trans (mul_le_of_le_one_left (norm_nonneg _) xj_norm_xjEz_le)
    have hL := norm_iteratedFDerivWithin_mul_le hgW hΨW huniq hyW (n := m)
      (by exact_mod_cast hm7n)
    exact hG1.trans ((hL.trans (Finset.sum_le_sum termB)).trans
      (le_of_eq (xj_sum_choose_mul m _)))
  -- assemble
  have hD : iteratedFDeriv ℝ m (streamCut ν 1 χy Z) y =
      iteratedFDerivWithin ℝ m (streamCut ν 1 χy Z) (xjWReg ν) y :=
    (xj_iterWithin_eq hopen hyW (streamCut ν 1 χy Z) m).symm
  rw [hD, xj_stream_eq, iteratedFDerivWithin_add_apply hA1 hB1 huniq hyW]
  have h2m : (2 : ℝ) ^ m ≤ 128 := by
    calc (2 : ℝ) ^ m ≤ 2 ^ 7 := pow_le_pow_right₀ (by norm_num) hm7n
      _ = 128 := by norm_num
  have hKnn : 0 ≤ (|C2| + |C2| * (|C1| + |C1'|)) * B * (eucSq y)⁻¹ *
      cylR y ^ (-(2 : ℝ) - (m : ℝ)) :=
    mul_nonneg (mul_nonneg (mul_nonneg (by positivity) hB) (inv_nonneg.mpr he0.le))
      (Real.rpow_nonneg (xj_cylR_nonneg y) _)
  refine (norm_add_le _ _).trans ?_
  refine (add_le_add hXb hYb).trans ?_
  calc 2 ^ m * (|C2| * B * (eucSq y)⁻¹ * cylR y ^ (-(2 : ℝ) - (m : ℝ))) +
        2 ^ m * (|C2| * ((|C1| + |C1'|) * B * (eucSq y)⁻¹) * cylR y ^ (-(2 : ℝ) - (m : ℝ)))
      = 2 ^ m * ((|C2| + |C2| * (|C1| + |C1'|)) * B * (eucSq y)⁻¹ *
          cylR y ^ (-(2 : ℝ) - (m : ℝ))) := by ring
    _ ≤ 128 * ((|C2| + |C2| * (|C1| + |C1'|)) * B * (eucSq y)⁻¹ *
          cylR y ^ (-(2 : ℝ) - (m : ℝ))) :=
        mul_le_mul_of_nonneg_right h2m hKnn
    _ = 128 * (|C2| + |C2| * (|C1| + |C1'|)) * B * cylR y ^ (-(2 : ℝ) - (m : ℝ)) *
          (eucSq y)⁻¹ := by
        ring

end UnforcedLeray.Short.PartIIIb.Concrete
