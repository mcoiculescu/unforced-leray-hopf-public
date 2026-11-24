import UnforcedLeray.Short.PartI.Sub.PartI_T04_5_1_3
import UnforcedLeray.Short.PartI.Sub.T02_3
import UnforcedLeray.Short.PartI.Tasks.ClassicalOdd.EtaCutoffFacts

/-!
# Part I, task `PartI:T04/5/1/3/3`: transport term of the cutoff energy identity

Target: `apEnergyTransportEstimate : APEnergyTransportEstimate` (`Short/PartI/Sub/PartI_T04_5_1_3.lean`).
Source of record: `the November 2 reference manuscript`, lines 278-286.

Route. `|v| ≤ M` on `[0,T]` (`exists_sup_bound_of_hasBoundedDerivsOn`), so `|v_η| ≤ M`;
`|χ_R'| ≤ C₀/R` (`EtaCutoffFacts`); hence the integrand is bounded pointwise by
`(M C₀/R) |v|²`, and `jet_l2` at `j = 0` gives `∫_cell |v|² ≤ K₀`.  Thus
`|∫| ≤ M C₀ |K₀| / R ≤ M C₀ |K₀| / √R`.  No integrability of the integrand is needed.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter
open scoped ContDiff

namespace UnforcedLeray.Short.PartI

open UnforcedLeray.Cyl (Plane)
open UnforcedLeray.Train (Vec)

/-- **Leaf 3 (transport term)**: `|∫ |v|² v_η χ_R'| ≤ C/√R`. -/
theorem apEnergyTransportEstimate : APEnergyTransportEstimate := by
  intro ν c T v p hν hc hcls
  have hF : EtaCutoffFacts := etaCutoffFacts
  unfold EtaCutoffFacts at hF
  obtain ⟨C0, hC0, hcut⟩ := hF
  obtain ⟨M, hM⟩ := exists_sup_bound_of_hasBoundedDerivsOn hcls.bounded
  have hM0 : 0 ≤ M := le_trans (norm_nonneg _) (hM 0 ⟨le_refl 0, hcls.pos.le⟩ 0)
  obtain ⟨K0, hK0⟩ := hcls.jet_l2 0
  refine ⟨M * C0 * |K0|, mul_nonneg (mul_nonneg hM0 hC0) (abs_nonneg _), ?_⟩
  intro R hR s hs
  have hR0 : 0 < R := by linarith
  obtain ⟨-, hbd, -, -, hd⟩ := hcut R hR
  -- `|χ_R'| ≤ C₀ / R` everywhere
  have hdbd : ∀ η : ℝ, |deriv (etaCutoff R) η| ≤ C0 / R := by
    intro η
    have h1 := hd η
    have hs1 : Real.sqrt (etaCutoff R η) ≤ 1 :=
      (Real.sqrt_le_sqrt (hbd η).2).trans_eq Real.sqrt_one
    have hk : 0 ≤ C0 / R := div_nonneg hC0 hR0.le
    calc |deriv (etaCutoff R) η| ≤ C0 / R * Real.sqrt (etaCutoff R η) := h1
      _ ≤ C0 / R * 1 := mul_le_mul_of_nonneg_left hs1 hk
      _ = C0 / R := mul_one _
  -- `1 ≤ √R ≤ R` and `1/R ≤ 1/√R`
  have hsR : 0 < Real.sqrt R := Real.sqrt_pos.2 hR0
  have hs1 : 1 ≤ Real.sqrt R := by
    have := Real.sqrt_le_sqrt hR
    rwa [Real.sqrt_one] at this
  have hsqle : Real.sqrt R ≤ R := by
    nlinarith [Real.sq_sqrt hR0.le, Real.sqrt_nonneg R,
      mul_nonneg (sub_nonneg.2 hs1) (Real.sqrt_nonneg R)]
  have h1R : 1 / R ≤ 1 / Real.sqrt R := one_div_le_one_div_of_le hsR hsqle
  obtain ⟨hI0, hV0⟩ := hK0 s (Ioo_subset_Icc_self hs)
  have hV0' : ∫ z in Cyl.cell c, ‖iteratedFDeriv ℝ 0 (v s) z‖ ^ 2 ≤ K0 := hV0
  have hMs : ∀ z : Plane, ‖v s z‖ ≤ M := fun z => hM s (Ioo_subset_Icc_self hs) z
  -- pointwise majorant `(M C₀ / R) |v|²`
  have hpt : ∀ z : Plane,
      ‖‖v s z‖ ^ 2 * v s z 1 * deriv (etaCutoff R) z.2‖ ≤
        M * C0 / R * ‖iteratedFDeriv ℝ 0 (v s) z‖ ^ 2 := by
    intro z
    have e : ‖‖v s z‖ ^ 2 * v s z 1 * deriv (etaCutoff R) z.2‖ =
        ‖v s z‖ ^ 2 * ‖v s z 1‖ * ‖deriv (etaCutoff R) z.2‖ := by
      simp [norm_mul, norm_pow]
    have hA : ‖v s z 1‖ ≤ M := (PiLp.norm_apply_le (v s z) 1).trans (hMs z)
    have hD : ‖deriv (etaCutoff R) z.2‖ ≤ C0 / R := by
      rw [Real.norm_eq_abs]
      exact hdbd z.2
    have hsq : 0 ≤ ‖v s z‖ ^ 2 := by positivity
    calc ‖‖v s z‖ ^ 2 * v s z 1 * deriv (etaCutoff R) z.2‖
        = ‖v s z‖ ^ 2 * ‖v s z 1‖ * ‖deriv (etaCutoff R) z.2‖ := e
      _ ≤ ‖v s z‖ ^ 2 * M * (C0 / R) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hA hsq) hD (norm_nonneg _)
            (mul_nonneg hsq hM0)
      _ = M * C0 / R * ‖iteratedFDeriv ℝ 0 (v s) z‖ ^ 2 := by
          rw [norm_iteratedFDeriv_zero]
          ring
  have hint : ∫ z in Cyl.cell c, ‖‖v s z‖ ^ 2 * v s z 1 * deriv (etaCutoff R) z.2‖ ≤
      ∫ z in Cyl.cell c, M * C0 / R * ‖iteratedFDeriv ℝ 0 (v s) z‖ ^ 2 :=
    integral_mono_of_nonneg (Filter.Eventually.of_forall fun z => norm_nonneg _)
      (hI0.const_mul _) (Filter.Eventually.of_forall hpt)
  have hsplit : ∫ z in Cyl.cell c, M * C0 / R * ‖iteratedFDeriv ℝ 0 (v s) z‖ ^ 2 =
      M * C0 / R * ∫ z in Cyl.cell c, ‖iteratedFDeriv ℝ 0 (v s) z‖ ^ 2 :=
    integral_const_mul _ _
  have hfin : M * C0 / R * ∫ z in Cyl.cell c, ‖iteratedFDeriv ℝ 0 (v s) z‖ ^ 2 ≤
      M * C0 / R * |K0| :=
    mul_le_mul_of_nonneg_left (le_trans hV0' (le_abs_self K0))
      (div_nonneg (mul_nonneg hM0 hC0) hR0.le)
  have hfin2 : M * C0 / R * |K0| ≤ M * C0 * |K0| / Real.sqrt R := by
    have e1 : M * C0 / R * |K0| = (M * C0 * |K0|) * (1 / R) := by ring
    have e2 : M * C0 * |K0| / Real.sqrt R = (M * C0 * |K0|) * (1 / Real.sqrt R) := by ring
    rw [e1, e2]
    exact mul_le_mul_of_nonneg_left h1R (mul_nonneg (mul_nonneg hM0 hC0) (abs_nonneg _))
  calc |∫ z in Cyl.cell c, ‖v s z‖ ^ 2 * v s z 1 * deriv (etaCutoff R) z.2|
      = ‖∫ z in Cyl.cell c, ‖v s z‖ ^ 2 * v s z 1 * deriv (etaCutoff R) z.2‖ :=
        (Real.norm_eq_abs _).symm
    _ ≤ ∫ z in Cyl.cell c, ‖‖v s z‖ ^ 2 * v s z 1 * deriv (etaCutoff R) z.2‖ :=
        norm_integral_le_integral_norm _
    _ ≤ _ := hint
    _ = M * C0 / R * ∫ z in Cyl.cell c, ‖iteratedFDeriv ℝ 0 (v s) z‖ ^ 2 := hsplit
    _ ≤ M * C0 / R * |K0| := hfin
    _ ≤ M * C0 * |K0| / Real.sqrt R := hfin2

end UnforcedLeray.Short.PartI
