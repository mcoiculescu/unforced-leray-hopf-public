import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_5_1_2_4_1_4
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_5_1_2_4_1_4.StreamFiber

/-!
# `PartIII-b:C/rep/5/1/2/4/1/4/4/spatial`: the spatial `L²` norm of the stream kernel

Source `the November 2 reference manuscript` 5588-5591, 5592.  For `a ∈ ℝ`,
the stream kernel `ϱ(y)^{-2}(ϱ(y)²+(y₂-a)²)^{-1}` has `∫_{0<age≤s₀} (kernel)² dy ≤ gapS R s₀`.
Route: the set lies in `{ϱ ≥ R/√s₀}`; the axisymmetric integral (`Axi.lintegral_axisymm`) turns
the `y`-integral into `2π ∫_{ρ ≥ r₀} ρ ∫_h (ρ²(ρ²+(h-a)²))^{-2} dh dρ`; the fibre integral is
`π/(2ρ⁷)` (`StreamFiber`), and `∫_{ρ ≥ r₀} π/(2ρ⁶) dρ = π r₀^{-5}/10`.
-/

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete.WYStream

/-- The fibre integrand on the half-plane `{ρ ≥ r₀}`. -/
def spG (r0 a : ℝ) (p : ℝ × ℝ) : ℝ≥0∞ :=
  ({p : ℝ × ℝ | r0 ≤ p.1}).indicator (fun p => ENNReal.ofReal (sfPhi p.1 (p.2 - a))) p

theorem sp_subset (R s0 : ℝ) (hR : 0 < R) (hs0 : 0 < s0) (y : Space)
    (h0 : 0 < age R y) (hs : age R y ≤ s0) : R / Real.sqrt s0 ≤ ϱ y := by
  have hsq : 0 < Real.sqrt s0 := Real.sqrt_pos.2 hs0
  have hs2 : Real.sqrt s0 ^ 2 = s0 := Real.sq_sqrt hs0.le
  have hϱ0 : 0 ≤ ϱ y := ϱ_nonneg y
  have hy2 : 0 < ϱ y ^ 2 := by
    by_contra hneg
    have h0' : ϱ y ^ 2 = 0 := le_antisymm (not_lt.1 hneg) (sq_nonneg _)
    unfold age at h0
    rw [h0', div_zero] at h0
    exact lt_irrefl _ h0
  have ha : 0 < ϱ y := by nlinarith
  unfold age at hs
  have hR2 : R ^ 2 ≤ s0 * ϱ y ^ 2 := by
    have := (div_le_iff₀ hy2).1 hs
    linarith
  rw [div_le_iff₀ hsq]
  nlinarith [mul_nonneg ha.le hsq.le]

theorem sp_G_meas (r0 a : ℝ) : Measurable (spG r0 a) := by
  unfold spG
  apply Measurable.indicator
  · exact ENNReal.measurable_ofReal.comp (by unfold sfPhi; fun_prop)
  · exact measurableSet_le measurable_const measurable_fst

theorem sp_fibre (r0 ρ a : ℝ) (hρ : 0 < ρ) :
    ∫⁻ h, spG r0 a (ρ, h) = if r0 ≤ ρ then ENNReal.ofReal (Real.pi / (2 * ρ ^ 7)) else 0 := by
  by_cases hr : r0 ≤ ρ
  · rw [if_pos hr]
    have hfun : ∀ h : ℝ, spG r0 a (ρ, h) = ENNReal.ofReal (sfPhi ρ (h - a)) := by
      intro h
      simp [spG, Set.indicator_apply, hr]
    simp only [hfun]
    have hnn : 0 ≤ᵐ[volume] (fun h : ℝ => sfPhi ρ (h - a)) :=
      Eventually.of_forall (fun h => by unfold sfPhi; positivity)
    rw [← ofReal_integral_eq_lintegral_ofReal ((sfPhi_integrable ρ hρ).comp_sub_right a) hnn,
      sfPhi_shift_integral ρ a hρ]
  · rw [if_neg hr]
    have hfun : ∀ h : ℝ, spG r0 a (ρ, h) = 0 := by
      intro h
      simp [spG, Set.indicator_apply, hr]
    simp only [hfun, lintegral_zero]

theorem sp_rpow6 (ρ : ℝ) (hρ : 0 < ρ) : ρ ^ (-6 : ℝ) = (ρ ^ 6)⁻¹ := by
  rw [show (-6 : ℝ) = -((6 : ℕ) : ℝ) by norm_num, Real.rpow_neg hρ.le, Real.rpow_natCast]

theorem sp_outer_integral (r0 : ℝ) (hr0 : 0 < r0) :
    ∫⁻ ρ in Ici r0, ENNReal.ofReal (Real.pi / 2 * ρ ^ (-6 : ℝ)) =
      ENNReal.ofReal (Real.pi / 2 * (r0 ^ (-5 : ℝ) / 5)) := by
  have hint : IntegrableOn (fun ρ : ℝ => Real.pi / 2 * ρ ^ (-6 : ℝ)) (Ici r0) := by
    rw [integrableOn_Ici_iff_integrableOn_Ioi]
    exact (integrableOn_Ioi_rpow_of_lt (by norm_num) hr0).const_mul _
  have hnn : 0 ≤ᵐ[volume.restrict (Ici r0)] (fun ρ : ℝ => Real.pi / 2 * ρ ^ (-6 : ℝ)) := by
    refine ae_restrict_of_forall_mem measurableSet_Ici (fun ρ hρ => ?_)
    have hρ0 : 0 ≤ ρ := le_trans hr0.le hρ
    exact mul_nonneg (by positivity) (Real.rpow_nonneg hρ0 _)
  rw [← ofReal_integral_eq_lintegral_ofReal hint hnn]
  congr 1
  rw [integral_const_mul, integral_Ici_eq_integral_Ioi,
    integral_Ioi_rpow_of_lt (by norm_num : (-6 : ℝ) < -1) hr0]
  norm_num

theorem sp_pointwise (r0 ρ : ℝ) (hρ : 0 < ρ) :
    ENNReal.ofReal ρ * (if r0 ≤ ρ then ENNReal.ofReal (Real.pi / (2 * ρ ^ 7)) else 0) =
      (Ici r0).indicator (fun ρ : ℝ => ENNReal.ofReal (Real.pi / 2 * ρ ^ (-6 : ℝ))) ρ := by
  by_cases hr : r0 ≤ ρ
  · have hmem : ρ ∈ Ici r0 := hr
    rw [if_pos hr, Set.indicator_of_mem hmem, ← ENNReal.ofReal_mul hρ.le, sp_rpow6 ρ hρ]
    congr 1
    field_simp
  · have hnmem : ρ ∉ Ici r0 := hr
    rw [if_neg hr, Set.indicator_of_notMem hnmem, mul_zero]

theorem sp_rpow5 (x : ℝ) (hx : 0 ≤ x) : x ^ (-5 : ℝ) = (x⁻¹) ^ 5 := by
  rw [show (-5 : ℝ) = -((5 : ℕ) : ℝ) by norm_num, Real.rpow_neg hx, Real.rpow_natCast, inv_pow]

theorem streamSpatial (R s0 a : ℝ) (hR : 0 < R) (hs0 : 0 < s0) :
    ∫⁻ y in {y : Space | 0 < age R y ∧ age R y ≤ s0}, ENNReal.ofReal (sfPhi (ϱ y) (y 2 - a))
      ≤ ENNReal.ofReal (gapS R s0) := by
  have hr0 : 0 < R / Real.sqrt s0 := div_pos hR (Real.sqrt_pos.2 hs0)
  have hBm : MeasurableSet {y : Space | R / Real.sqrt s0 ≤ ϱ y} :=
    measurableSet_le measurable_const measurable_ϱ
  have hsub : {y : Space | 0 < age R y ∧ age R y ≤ s0} ⊆ {y : Space | R / Real.sqrt s0 ≤ ϱ y} :=
    fun y hy => sp_subset R s0 hR hs0 y hy.1 hy.2
  have hstep1 := lintegral_mono_set (μ := volume)
    (f := fun y : Space => ENNReal.ofReal (sfPhi (ϱ y) (y 2 - a))) hsub
  have hstep2 : ∫⁻ y in {y : Space | R / Real.sqrt s0 ≤ ϱ y},
      ENNReal.ofReal (sfPhi (ϱ y) (y 2 - a)) = ∫⁻ y, spG (R / Real.sqrt s0) a (ϱ y, y 2) := by
    rw [← lintegral_indicator hBm]
    refine lintegral_congr fun y => ?_
    by_cases hy : R / Real.sqrt s0 ≤ ϱ y
    · have hmem : y ∈ {y : Space | R / Real.sqrt s0 ≤ ϱ y} := hy
      rw [Set.indicator_of_mem hmem]
      simp [spG, Set.indicator_apply, hy]
    · have hnmem : y ∉ {y : Space | R / Real.sqrt s0 ≤ ϱ y} := hy
      rw [Set.indicator_of_notMem hnmem]
      simp [spG, Set.indicator_apply, hy]
  have hH : Measurable (fun p : ℝ × ℝ => ENNReal.ofReal p.1 * spG (R / Real.sqrt s0) a p) :=
    (ENNReal.measurable_ofReal.comp measurable_fst).mul (sp_G_meas _ a)
  calc ∫⁻ y in {y : Space | 0 < age R y ∧ age R y ≤ s0}, ENNReal.ofReal (sfPhi (ϱ y) (y 2 - a))
      ≤ ∫⁻ y in {y : Space | R / Real.sqrt s0 ≤ ϱ y}, ENNReal.ofReal (sfPhi (ϱ y) (y 2 - a)) :=
        hstep1
    _ = ∫⁻ y, spG (R / Real.sqrt s0) a (ϱ y, y 2) := hstep2
    _ = ENNReal.ofReal (2 * Real.pi) * ∫⁻ p in Ioi (0 : ℝ) ×ˢ (univ : Set ℝ),
          ENNReal.ofReal p.1 * spG (R / Real.sqrt s0) a p :=
        lintegral_axisymm _ (sp_G_meas _ a)
    _ = ENNReal.ofReal (2 * Real.pi) * ∫⁻ ρ in Ioi (0 : ℝ),
          ∫⁻ h, ENNReal.ofReal ρ * spG (R / Real.sqrt s0) a (ρ, h) := by
        congr 1
        rw [Measure.volume_eq_prod ℝ ℝ, setLIntegral_prod_univ _ hH]
    _ = ENNReal.ofReal (2 * Real.pi) * ∫⁻ ρ in Ioi (0 : ℝ),
          (Ici (R / Real.sqrt s0)).indicator
            (fun ρ : ℝ => ENNReal.ofReal (Real.pi / 2 * ρ ^ (-6 : ℝ))) ρ := by
        congr 1
        refine setLIntegral_congr_fun measurableSet_Ioi (fun ρ hρ => ?_)
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, sp_fibre _ ρ a hρ]
        exact sp_pointwise _ ρ hρ
    _ = ENNReal.ofReal (2 * Real.pi) * ∫⁻ ρ in Ici (R / Real.sqrt s0),
          ENNReal.ofReal (Real.pi / 2 * ρ ^ (-6 : ℝ)) := by
        congr 1
        rw [setLIntegral_indicator measurableSet_Ici,
          Set.inter_eq_left.2
            (show Ici (R / Real.sqrt s0) ⊆ Ioi (0 : ℝ) from fun x hx => lt_of_lt_of_le hr0 hx)]
    _ = ENNReal.ofReal (2 * Real.pi) *
          ENNReal.ofReal (Real.pi / 2 * ((R / Real.sqrt s0) ^ (-5 : ℝ) / 5)) := by
        rw [sp_outer_integral _ hr0]
    _ = ENNReal.ofReal (gapS R s0) := by
        rw [← ENNReal.ofReal_mul (by positivity)]
        congr 1
        unfold gapS
        rw [sp_rpow5 _ hr0.le]
        ring

end UnforcedLeray.Short.PartIIIb.Concrete.WYStream

end
