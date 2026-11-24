import UnforcedLeray.Short.PartIIa.Sub.N02_5.Cond

/-!


Source of record: `the November 2 reference manuscript`, lines 1738-1750
(`H = L²(s^{-3/2} ds dq dη)`).

Proof. `measureH c` is the density `s^{-3/2}` on the cell `(0,∞) × (0,c] × ℝ`. Put
`D := B - A` (continuous, supported in the same band), so `∫ A ≤ ∫ B` is `0 ≤ ∫ D`.
Writing `∫ D dμ` as `∫_{cell} s^{-3/2} D` and applying Fubini with the `q`-variable innermost,
the innermost `q`-integral is `∫_0^c D(s,·,η) ≥ 0` for `s > 0` by the hypothesis.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace UnforcedLeray.Short.PartIIa

open UnforcedLeray.B0220 UnforcedLeray.B0223 UnforcedLeray.B0226

/-- The cell measure splits as `ds ⊗ (dq ⊗ dη)` on `(0,∞) × (0,c] × ℝ`. -/
theorem asmCellSplit (c : ℝ) :
    (volume : Measure Profile).restrict (cell c) =
      (volume.restrict (Ioi (0 : ℝ))).prod
        ((volume.restrict (Ioc (0 : ℝ) c)).prod (volume.restrict (univ : Set ℝ))) := by
  unfold cell
  rw [Measure.volume_eq_prod ℝ (ℝ × ℝ), Measure.volume_eq_prod ℝ ℝ,
    ← Measure.prod_restrict, ← Measure.prod_restrict]

/-- For `s > 0` and `η`, the `q`-integral over `(0,c]` of the weighted difference is nonnegative. -/
theorem asmSliceNonneg {c : ℝ} (hc : 0 < c) {A B : Profile → ℝ} (hA : Continuous A)
    (hB : Continuous B)
    (hyp : ∀ s η : ℝ, 0 < s →
      ∫ q in (0 : ℝ)..c, A (s, q, η) ≤ ∫ q in (0 : ℝ)..c, B (s, q, η))
    {s : ℝ} (hs : 0 < s) (η : ℝ) :
    0 ≤ ∫ q in Ioc (0 : ℝ) c, s ^ (-(3 / 2 : ℝ)) * (B (s, q, η) - A (s, q, η)) := by
  have hAc : Continuous fun q : ℝ => A (s, q, η) := hA.comp (by fun_prop)
  have hBc : Continuous fun q : ℝ => B (s, q, η) := hB.comp (by fun_prop)
  have hAi : IntervalIntegrable (fun q : ℝ => A (s, q, η)) volume 0 c :=
    hAc.intervalIntegrable 0 c
  have hBi : IntervalIntegrable (fun q : ℝ => B (s, q, η)) volume 0 c :=
    hBc.intervalIntegrable 0 c
  rw [integral_const_mul, ← intervalIntegral.integral_of_le hc.le,
    intervalIntegral.integral_sub hBi hAi]
  exact mul_nonneg (Real.rpow_nonneg hs.le _) (sub_nonneg.2 (hyp s η hs))

/-- **`AvgSliceMono`** (task `PartII-a:N02/5/3`, leaf). -/
theorem avgSliceMono_proof : AvgSliceMono := by
  intro c hc A B hA hB ⟨s0, s1, L, hs0, hband⟩ hyp
  -- `A`, `B`, `D := B - A` are integrable for `measureH c`
  have hAi : Integrable A (measureH c) :=
    avgIntegrable_of_band hs0 hA fun p hp => hband p (Or.inl hp)
  have hBi : Integrable B (measureH c) :=
    avgIntegrable_of_band hs0 hB fun p hp => hband p (Or.inr hp)
  have hDc : Continuous fun p => B p - A p := hB.sub hA
  have hDi : Integrable (fun p => B p - A p) (measureH c) := by
    refine avgIntegrable_of_band hs0 hDc fun p hp => hband p ?_
    by_contra h
    apply hp
    simp only [not_or, ne_eq, not_not] at h
    simp [h.1, h.2]
  -- the real version of `integralMeasureHCell`
  have hcell : ∫ p, (B p - A p) ∂(measureH c) =
      ∫ p in cell c, p.1 ^ (-(3 / 2 : ℝ)) * (B p - A p) := by
    rw [measureH, integral_withDensity_eq_integral_toReal_smul measurable_weightH
      (ae_weightH_lt_top c), cellMeasure]
    refine setIntegral_congr_fun (measurableSet_cell c) fun p hp => ?_
    have hp1 : 0 < p.1 := hp.1
    simp only [weightH, smul_eq_mul, ENNReal.toReal_ofReal (Real.rpow_nonneg hp1.le _)]
  -- integrability of the weighted difference on the cell
  have hint : Integrable (fun p : Profile => p.1 ^ (-(3 / 2 : ℝ)) * (B p - A p))
      (volume.restrict (cell c)) := by
    have h2 := (integrable_withDensity_iff_integrable_smul' measurable_weightH
      (ae_weightH_lt_top c)).1 hDi
    refine h2.congr ?_
    filter_upwards [ae_restrict_mem (measurableSet_cell c)] with p hp
    have hp1 : 0 < p.1 := hp.1
    simp only [weightH, smul_eq_mul, ENNReal.toReal_ofReal (Real.rpow_nonneg hp1.le _)]
  have hint' : Integrable (fun p : Profile => p.1 ^ (-(3 / 2 : ℝ)) * (B p - A p))
      ((volume.restrict (Ioi (0 : ℝ))).prod
        ((volume.restrict (Ioc (0 : ℝ) c)).prod (volume.restrict (univ : Set ℝ)))) := by
    rw [← asmCellSplit c]
    exact hint
  -- Fubini on the cell with `q` innermost, and nonnegativity of the iterated integral
  have h0 : 0 ≤ ∫ p in cell c, p.1 ^ (-(3 / 2 : ℝ)) * (B p - A p) := by
    rw [asmCellSplit c, integral_prod _ hint']
    refine integral_nonneg_of_ae ?_
    filter_upwards [hint'.prod_right_ae,
      (ae_restrict_mem (measurableSet_Ioi : MeasurableSet (Ioi (0 : ℝ))))] with s hsI hs
    have hs' : 0 < s := hs
    rw [integral_prod_symm _ hsI]
    refine integral_nonneg fun η => ?_
    exact asmSliceNonneg hc hA hB hyp hs' η
  have hD : 0 ≤ ∫ p, (B p - A p) ∂(measureH c) := by
    rw [hcell]
    exact h0
  have hsub : ∫ p, (B p - A p) ∂(measureH c) =
      ∫ p, B p ∂(measureH c) - ∫ p, A p ∂(measureH c) :=
    integral_sub hBi hAi
  linarith

end UnforcedLeray.Short.PartIIa
