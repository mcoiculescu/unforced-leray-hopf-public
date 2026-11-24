import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_2_3_6
import UnforcedLeray.Short.PartIIIa.Clock.WeakSmoothing.TerminalBound

/-!
# `PartIII-a:T21/2/2/3/6`, leaf `AdjPhiMemLp`: the weighted `L²` bound of the adjoint (SP 3044-3047)

Source of record: `the November 2 reference manuscript` lines 3040-3047 (the
periodic weight `p_d` is equivalent to `⟨y⟩^{2m}`).

The periodic weight `periodicWeight (-m) d y = P(y)^{-m}` with `P(y) = 1 + y₂² + (d/π)² sin²(πy₁/d)`.
Since `|sin u| ≤ |u|`, `P(y) ≤ 1 + y₁² + y₂² = jb y` on the whole plane, and for `m ≥ 0` the map
`x ↦ x^{-m}` is antitone, so `jb^{-m} ≤ P^{-m} = periodicWeight (-m) d` pointwise. Hence a continuous
`Φ` with `∫_{C_d} p_d⁻¹|Φ|² < ∞` is in `L²(C_d, jb^{-m})` and its weighted norm squared is at most
`E_0`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal

namespace UnforcedLeray.Short.IIIa.AdjE1

/-- The weight comparison `⟨y⟩^{-2m} ≤ p_d⁻¹` for `m ≥ 0`, pointwise on the plane, from
`P(y) ≤ jb y` (`|sin u| ≤ |u|`). -/
theorem adjPhi_jb_rpow_le {m d : ℝ} (hm : 0 ≤ m) (hd : 0 < d) (y : ℝ × ℝ) :
    B0579.jb y ^ (-m) ≤ periodicWeight (-m) d y := by
  have hdne : d ≠ 0 := hd.ne'
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  have hsin : Real.sin (Real.pi * y.1 / d) ^ 2 ≤ (Real.pi * y.1 / d) ^ 2 := Real.sin_sq_le_sq
  have hkey : (d / Real.pi) ^ 2 * (Real.pi * y.1 / d) ^ 2 = y.1 ^ 2 := by
    field_simp
  have hP : 1 + y.2 ^ 2 + (d / Real.pi) ^ 2 * Real.sin (Real.pi * y.1 / d) ^ 2 ≤
      B0579.jb y := by
    have h2 : (d / Real.pi) ^ 2 * Real.sin (Real.pi * y.1 / d) ^ 2 ≤
        (d / Real.pi) ^ 2 * (Real.pi * y.1 / d) ^ 2 :=
      mul_le_mul_of_nonneg_left hsin (sq_nonneg _)
    rw [hkey] at h2
    unfold B0579.jb
    linarith
  have hpos : 0 < 1 + y.2 ^ 2 + (d / Real.pi) ^ 2 * Real.sin (Real.pi * y.1 / d) ^ 2 := by
    positivity
  unfold periodicWeight
  exact Real.rpow_le_rpow_of_nonpos hpos hP (neg_nonpos.2 hm)

/-- **Leaf `AdjPhiMemLp`** (SP 3044-3047): for `m ≥ 0`, a continuous `Φ` with
`∫_{C_d} p_d⁻¹|Φ|² < ∞` lies in `L²(C_d, ⟨y⟩^{-2m})` and `‖Φ‖_{X_{-m,d}} ≤ √E_0`. -/
theorem adjPhiMemLp (m : ℝ) : UnforcedLeray.Short.IIIa.AdjE1.AdjPhiMemLp m := by
  unfold AdjPhiMemLp
  intro hm d Φ hd hΦc hΦi
  have hcont : Continuous (fun y => B0579.jb y ^ (-m) * ‖Φ y‖ ^ 2) :=
    (B0579.continuous_jb_rpow (-m)).mul (hΦc.norm.pow 2)
  have hint : Integrable (fun y => B0579.jb y ^ (-m) * ‖Φ y‖ ^ 2)
      (volume.restrict (B0579.cell d)) := by
    refine Integrable.mono' hΦi hcont.aestronglyMeasurable (Eventually.of_forall fun y => ?_)
    rw [Real.norm_of_nonneg (mul_nonneg (Real.rpow_nonneg (B0579.jb_pos y).le _) (sq_nonneg _))]
    exact mul_le_mul_of_nonneg_right (adjPhi_jb_rpow_le hm hd y) (sq_nonneg _)
  have hmem : MemLp Φ 2 (B0579.cellMeasure d (-m)) := by
    refine (memLp_two_iff_integrable_sq_norm hΦc.aestronglyMeasurable).2 ?_
    unfold B0579.cellMeasure
    rw [integrable_withDensity_iff_integrable_smul (B0579.measurable_density (-m))]
    refine hint.congr (Eventually.of_forall fun y => ?_)
    simp only [NNReal.smul_def, B0579.coe_density, smul_eq_mul]
  refine ⟨hmem, ?_⟩
  have hfin : xNorm d (-m) Φ ≠ ⊤ := hmem.eLpNorm_lt_top.ne
  have hsq := tb_sq_xNorm hmem
  have hle : (xNorm d (-m) Φ).toReal ^ 2 ≤ adjE0 d m Φ := by
    rw [hsq]
    unfold adjE0
    exact integral_mono (tb_integrable hmem) hΦi
      (fun y => mul_le_mul_of_nonneg_right (adjPhi_jb_rpow_le hm hd y) (sq_nonneg _))
  have hnn : 0 ≤ (xNorm d (-m) Φ).toReal := ENNReal.toReal_nonneg
  have habs : (xNorm d (-m) Φ).toReal ≤ Real.sqrt (adjE0 d m Φ) := by
    have h := Real.abs_le_sqrt hle
    rwa [abs_of_nonneg hnn] at h
  exact (ENNReal.le_ofReal_iff_toReal_le hfin (Real.sqrt_nonneg _)).2 habs

end UnforcedLeray.Short.IIIa.AdjE1
