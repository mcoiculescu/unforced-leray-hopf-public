import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.AdjTruncOrg.StreamPotOrg.Defs

/-!
# `BSHardyY2`: the weighted bound `ψ/|y| ∈ Y_2` for the Biot-Savart potential

Source `the November 2 reference manuscript` lines 1351-1362.
Integrates the slice Hardy inequality `HardyR3` over one phase period.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open UnforcedLeray.PhaseSpace UnforcedLeray.B0411
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- Pointwise weight bound: `‖‖y‖⁻¹ • v‖ₑ² ≤ ‖v‖ₑ² / ‖y‖ₑ²`. -/
theorem enorm_inv_smul_le_div (y : EuclideanSpace ℝ (Fin 3)) (v : CVec3) :
    ‖((‖y‖⁻¹ : ℝ)) • v‖ₑ ^ 2 ≤ ‖v‖ₑ ^ 2 / ‖y‖ₑ ^ 2 := by
  by_cases hy : y = 0
  · subst hy
    simp
  · have hn : 0 < ‖y‖ := norm_pos_iff.2 hy
    have hy' : ‖y‖ₑ = ENNReal.ofReal ‖y‖ := (ofReal_norm y).symm
    rw [enorm_smul, Real.enorm_eq_ofReal (inv_nonneg.2 (norm_nonneg y)),
      ENNReal.ofReal_inv_of_pos hn, hy', mul_pow, div_eq_mul_inv, ← ENNReal.inv_pow]
    exact le_of_eq (mul_comm _ _)

/-- **BSHardyY2** (source 1351-1362): from the slice Hardy inequality, `ψ/|y| ∈ Y_2` for
`ψ = bsPot Φ`. -/
theorem bsHardyY2 : BSHardyY2 := by
  intro hH P hP Φ _ _ hm hper Dψ hD hsl
  -- the slice Hardy bound, for a.e. phase
  have key : ∀ᵐ t ∂(volume : Measure ℝ),
      ∫⁻ y : EuclideanSpace ℝ (Fin 3), ‖((‖y‖⁻¹ : ℝ)) • bsPot Φ (t, y)‖ₑ ^ 2
        ≤ 4 * ∑ j : Fin 3, ∫⁻ y : EuclideanSpace ℝ (Fin 3), ‖Dψ j (t, y)‖ₑ ^ 2 := by
    filter_upwards [hsl] with τ hτ
    calc ∫⁻ y : EuclideanSpace ℝ (Fin 3), ‖((‖y‖⁻¹ : ℝ)) • bsPot Φ (τ, y)‖ₑ ^ 2
        ≤ ∫⁻ y : EuclideanSpace ℝ (Fin 3), ‖bsPot Φ (τ, y)‖ₑ ^ 2 / ‖y‖ₑ ^ 2 :=
          lintegral_mono fun y => enorm_inv_smul_le_div y _
      _ ≤ 4 * ∑ j : Fin 3, ∫⁻ y : EuclideanSpace ℝ (Fin 3), ‖Dψ j (τ, y)‖ₑ ^ 2 :=
          hH (fun y => bsPot Φ (τ, y)) (fun j y => Dψ j (τ, y)) hτ.1
            (fun j => (hτ.2 j).1) (fun j φ hφ hc => (hτ.2 j).2 φ hφ hc)
  -- measurability of the phase-slice energies of `Dψ j`
  have hGm : ∀ j : Fin 3, AEMeasurable
      (fun t : ℝ => ∫⁻ y : EuclideanSpace ℝ (Fin 3), ‖Dψ j (t, y)‖ₑ ^ 2) (volume : Measure ℝ) := by
    intro j
    have hf : AEMeasurable (fun x : ℝ × EuclideanSpace ℝ (Fin 3) => ‖Dψ j x‖ₑ ^ 2)
        (volume.prod volume) := by
      rw [← Measure.volume_eq_prod]
      have h1 : AEMeasurable (fun x : ℝ × EuclideanSpace ℝ (Fin 3) => ‖Dψ j x‖ₑ)
          (volume : Measure (ℝ × EuclideanSpace ℝ (Fin 3))) := (hD j).1.meas.enorm
      exact h1.pow_const 2
    exact hf.lintegral_prod_right'
  -- finiteness of each `Dψ j` phase norm, unpacked to the lintegral
  have hGfin : ∀ j : Fin 3,
      ∫⁻ t in Ioc (0 : ℝ) P, ∫⁻ y : EuclideanSpace ℝ (Fin 3), ‖Dψ j (t, y)‖ₑ ^ 2 < ⊤ := by
    intro j
    have h := (hD j).1.finite
    unfold UnforcedLeray.Short.IIb.phaseLpNorm at h
    simp only [ENNReal.rpow_two] at h
    have hb := (ENNReal.rpow_lt_top_iff_of_pos (by norm_num : (0 : ℝ) < 1 / 2)).1 h
    have hP' : ENNReal.ofReal P⁻¹ ≠ 0 := (ENNReal.ofReal_pos.2 (inv_pos.2 hP)).ne'
    exact ENNReal.lt_top_of_mul_ne_top_right (ne_top_of_lt hb) hP'
  refine ⟨?_, ?_, ?_⟩
  · filter_upwards [hper] with x hx
    simp only [hx]
  · exact ((measurable_snd.norm.inv).aestronglyMeasurable).smul hm
  · unfold UnforcedLeray.Short.IIb.phaseLpNorm
    simp only [ENNReal.rpow_two]
    have hJ : ∫⁻ t in Ioc (0 : ℝ) P, ∫⁻ y : EuclideanSpace ℝ (Fin 3),
        ‖((‖y‖⁻¹ : ℝ)) • bsPot Φ (t, y)‖ₑ ^ 2 < ⊤ := by
      calc ∫⁻ t in Ioc (0 : ℝ) P, ∫⁻ y : EuclideanSpace ℝ (Fin 3),
            ‖((‖y‖⁻¹ : ℝ)) • bsPot Φ (t, y)‖ₑ ^ 2
          ≤ ∫⁻ t in Ioc (0 : ℝ) P, 4 * ∑ j : Fin 3,
              ∫⁻ y : EuclideanSpace ℝ (Fin 3), ‖Dψ j (t, y)‖ₑ ^ 2 :=
            lintegral_mono_ae (ae_restrict_of_ae key)
        _ = 4 * ∑ j : Fin 3, ∫⁻ t in Ioc (0 : ℝ) P,
              ∫⁻ y : EuclideanSpace ℝ (Fin 3), ‖Dψ j (t, y)‖ₑ ^ 2 := by
            rw [lintegral_const_mul' _ _ (by simp),
              lintegral_finsetSum' _ (fun j _ => (hGm j).restrict)]
        _ < ⊤ := ENNReal.mul_lt_top (by simp) (ENNReal.sum_lt_top.2 fun j _ => hGfin j)
    exact ENNReal.rpow_lt_top_of_nonneg (by norm_num)
      (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hJ).ne

end UnforcedLeray.Short.PartIIIb.Concrete
