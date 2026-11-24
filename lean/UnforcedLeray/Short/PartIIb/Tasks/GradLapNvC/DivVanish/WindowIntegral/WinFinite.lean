import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T09_4_2
import UnforcedLeray.Short.PartIIb.Tasks.GradLapNvC.DivVanish.WindowIntegral.WinPerFacts

/-!
# Part II-b, task `PartII-b:T09/4/2/3` (`WinFinite`)

Source of record: `the November 2 reference manuscript`, lines 1639-1668, 1912-1916.

On the cell `winPer c χ = χ` (`WinPerFacts`), so the weighted integrand vanishes off the compact set
`tsupport χ ⊆ {s > 0}`, where the weight `c⁻¹ s^{-5/2}` is bounded and `χ` is bounded; integrability
of the locally integrable `g` on that compact set gives finiteness.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal

namespace UnforcedLeray.Short.IIb

theorem winFinite : UnforcedLeray.Short.IIb.WinFinite := by
  intro c χ g hc hχ hg
  have hKc : IsCompact (tsupport χ) := hχ.1.compact.isCompact
  have hKsub : tsupport χ ⊆ Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ)) := hχ.1.supp
  obtain ⟨B, hB⟩ := hχ.1.smooth.continuous.bounded_above_of_compact_support hχ.1.compact
  have hcont : ContinuousOn (fun p : Coord => c⁻¹ * p.1 ^ (-(5 / 2 : ℝ))) (tsupport χ) := by
    refine continuousOn_const.mul ?_
    refine ContinuousOn.rpow_const (continuous_fst.continuousOn) ?_
    intro p hp
    left
    exact (show (0 : ℝ) < p.1 from (hKsub hp).1).ne'
  obtain ⟨C, hC⟩ := hKc.exists_bound_of_continuousOn hcont
  have hgK : IntegrableOn g (tsupport χ) volume :=
    hg.integrableOn_compact_subset hKsub hKc
  have hS : MeasurableSet (Ioi (0 : ℝ) ×ˢ Axi.qCell c) :=
    measurableSet_Ioi.prod (measurableSet_Ico.prod MeasurableSet.univ)
  have hpt : ∀ p ∈ Ioi (0 : ℝ) ×ˢ Axi.qCell c,
      ENNReal.ofReal (c⁻¹ * p.1 ^ (-(5 / 2 : ℝ))) * ‖((winPer c χ p : ℝ) : ℂ) * g p‖ₑ ≤
        (tsupport χ).indicator (fun p => ENNReal.ofReal C * ENNReal.ofReal B * ‖g p‖ₑ) p := by
    intro p hp
    have hq : p.2.1 ∈ Ico (-c / 2) (c / 2) :=
      (Set.mem_prod.1 (show p.2 ∈ Ico (-c / 2) (c / 2) ×ˢ (univ : Set ℝ) from hp.2)).1
    have hcell : winPer c χ p = χ p := (winPerFacts c χ hc hχ).2.2 p hq
    rw [hcell]
    by_cases hK : p ∈ tsupport χ
    · rw [Set.indicator_of_mem hK]
      have h1 : ENNReal.ofReal (c⁻¹ * p.1 ^ (-(5 / 2 : ℝ))) ≤ ENNReal.ofReal C := by
        apply ENNReal.ofReal_le_ofReal
        have := hC p hK
        rw [Real.norm_eq_abs] at this
        exact (le_abs_self _).trans this
      have h2 : ‖((χ p : ℝ) : ℂ) * g p‖ₑ ≤ ENNReal.ofReal B * ‖g p‖ₑ := by
        rw [enorm_mul]
        gcongr
        rw [← ofReal_norm]
        exact ENNReal.ofReal_le_ofReal (by rw [Complex.norm_real]; exact hB p)
      calc ENNReal.ofReal (c⁻¹ * p.1 ^ (-(5 / 2 : ℝ))) * ‖((χ p : ℝ) : ℂ) * g p‖ₑ
          ≤ ENNReal.ofReal C * (ENNReal.ofReal B * ‖g p‖ₑ) := mul_le_mul' h1 h2
        _ = ENNReal.ofReal C * ENNReal.ofReal B * ‖g p‖ₑ := (mul_assoc _ _ _).symm
    · rw [Set.indicator_of_notMem hK, image_eq_zero_of_notMem_tsupport hK]
      simp
  have hfin : ∫⁻ p in Ioi (0 : ℝ) ×ˢ Axi.qCell c,
      ENNReal.ofReal (c⁻¹ * p.1 ^ (-(5 / 2 : ℝ))) * ‖((winPer c χ p : ℝ) : ℂ) * g p‖ₑ ≤
        ∫⁻ p in tsupport χ, ENNReal.ofReal C * ENNReal.ofReal B * ‖g p‖ₑ := by
    calc ∫⁻ p in Ioi (0 : ℝ) ×ˢ Axi.qCell c,
          ENNReal.ofReal (c⁻¹ * p.1 ^ (-(5 / 2 : ℝ))) * ‖((winPer c χ p : ℝ) : ℂ) * g p‖ₑ
        ≤ ∫⁻ p in Ioi (0 : ℝ) ×ˢ Axi.qCell c,
            (tsupport χ).indicator (fun p => ENNReal.ofReal C * ENNReal.ofReal B * ‖g p‖ₑ) p :=
          setLIntegral_mono' hS hpt
      _ ≤ ∫⁻ p, (tsupport χ).indicator (fun p => ENNReal.ofReal C * ENNReal.ofReal B * ‖g p‖ₑ) p :=
          setLIntegral_le_lintegral _ _
      _ = ∫⁻ p in tsupport χ, ENNReal.ofReal C * ENNReal.ofReal B * ‖g p‖ₑ :=
          lintegral_indicator hKc.isClosed.measurableSet _
  refine lt_of_le_of_lt hfin ?_
  rw [lintegral_const_mul' _ _ (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)]
  exact ENNReal.mul_lt_top (ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top)
    hgK.hasFiniteIntegral

end UnforcedLeray.Short.IIb
