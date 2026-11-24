import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_4

/-!
# `EnergyLocOfSlice` (leaf 4 of `PartIII-b:C/flatset/col/4`)

Source of record `the November 2 reference manuscript` 3426-3430.
Tonelli on the compact age band `[s₁,s₂]`: the slice bound `KcSliceBound` gives a uniform bound on
the cell integral for every `s ∈ [s₁,s₂] ⊂ (0,∞)`, `n` is bounded there by continuity, and the
product measure of the band times the finite-volume cell is finite.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal ComplexConjugate

open UnforcedLeray.Short.IIIa (vnorm2 tnorm2)

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

/-- **(4) Local energy from the slice bound** (Tonelli on the compact age band `[s₁,s₂]`). -/
theorem energyLocOfSlice : EnergyLocOfSlice := by
  unfold EnergyLocOfSlice
  intro c b G n hc hb hG hn hK s₁ s₂ hs₁ hs₁₂
  obtain ⟨K, hK⟩ := hK
  have hsub : Icc s₁ s₂ ⊆ Ioi (0 : ℝ) := fun s hs => lt_of_lt_of_le hs₁ hs.1
  have hcpt : IsCompact ((fun x => ‖n x‖) '' Icc s₁ s₂) :=
    isCompact_Icc.image_of_continuousOn ((hn.mono hsub).norm)
  obtain ⟨M, hM⟩ := hcpt.bddAbove
  have key : ∀ s ∈ Icc s₁ s₂,
      ∫⁻ x in B0579.cell c, ENNReal.ofReal (vnorm2 (b (s, x)) ^ 2 + tnorm2 (G (s, x)) ^ 2)
        ≤ ENNReal.ofReal (|K| * M ^ 2) := by
    intro s hs
    refine (hK s (lt_of_lt_of_le hs₁ hs.1)).trans (ENNReal.ofReal_le_ofReal ?_)
    have hnM : |n s| ≤ M := by
      have h := hM ⟨s, hs, rfl⟩
      simpa only [Real.norm_eq_abs] using h
    have h2 : n s ^ 2 ≤ M ^ 2 := by
      rw [← sq_abs]
      gcongr
    calc K * n s ^ 2 ≤ |K| * n s ^ 2 :=
          mul_le_mul_of_nonneg_right (le_abs_self K) (sq_nonneg _)
      _ ≤ |K| * M ^ 2 := mul_le_mul_of_nonneg_left h2 (abs_nonneg K)
  have hv : Measurable fun p => vnorm2 (b p) := by
    unfold vnorm2
    exact Real.continuous_sqrt.measurable.comp
      (Finset.measurable_sum _ fun i _ => (hb i).norm.pow_const 2)
  have ht : Measurable fun p => tnorm2 (G p) := by
    unfold tnorm2
    exact Real.continuous_sqrt.measurable.comp
      (Finset.measurable_sum _ fun i _ => Finset.measurable_sum _ fun j _ =>
        (hG i j).norm.pow_const 2)
  have hF : Measurable fun p =>
      ENNReal.ofReal (vnorm2 (b p) ^ 2 + tnorm2 (G p) ^ 2) :=
    ((hv.pow_const 2).add (ht.pow_const 2)).ennreal_ofReal
  have hprod : (volume : Measure (ℝ × (ℝ × ℝ))).restrict (Icc s₁ s₂ ×ˢ B0579.cell c) =
      (volume.restrict (Icc s₁ s₂)).prod (volume.restrict (B0579.cell c)) := by
    rw [Measure.volume_eq_prod, Measure.prod_restrict]
  rw [hprod, lintegral_prod _ hF.aemeasurable]
  calc _ ≤ ∫⁻ s in Icc s₁ s₂, ENNReal.ofReal (|K| * M ^ 2) :=
        setLIntegral_mono' measurableSet_Icc (fun s hs => key s hs)
    _ < ⊤ := by
        rw [setLIntegral_const]
        exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top
          (by rw [Real.volume_Icc]; exact ENNReal.ofReal_lt_top)

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
