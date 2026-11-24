import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D2_1_3_1_2_2

/-!
# Leaf 2 of `FWUAdjMoll`: `(μ + L₀ᵗ)Ψ ∈ Y_2` for a phase test `Ψ`

Source: `the November 2 reference manuscript` lines 1351-1362, 1556-1583
(the mollified field is a smooth, `P`-periodic, `y`-compactly supported field, hence a phase test;
`L₀ᵗ` preserves phase tests, and a phase test is in `Y_2`).
Proves `mollGraphInYr_of : MollIsSolTestL → MollGraphInYr`; the unconditional target needs leaf 1.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411
open UnforcedLeray.Cons.C03.Concrete (pairF phaseInt IsSolTest)

/-- A phase test lies in `Y_2`. -/
theorem isInYr_of_phaseTest {P : ℝ} (hP : 0 < P) {Ψ : ℝ × Space → CVec3}
    (hΨ : IsPhaseTest P Ψ) : UnforcedLeray.Short.IIb.IsInYr P 2 Ψ := by
  refine ⟨Filter.Eventually.of_forall fun x => hΨ.periodic x.1 x.2,
    hΨ.continuous.aestronglyMeasurable, ?_⟩
  obtain ⟨R, hR⟩ := hΨ.bounded_support
  have hK : IsCompact (Icc (0 : ℝ) P ×ˢ Metric.closedBall (0 : Space) R) :=
    isCompact_Icc.prod (isCompact_closedBall _ _)
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hΨ.continuous.continuousOn
  have hbd : ∀ t ∈ Ioc (0 : ℝ) P, ∀ y : Space,
      ‖Ψ (t, y)‖ₑ ^ (2 : ℝ) ≤
        (Metric.closedBall (0 : Space) R).indicator (fun _ => ENNReal.ofReal C ^ (2 : ℝ)) y := by
    intro t ht y
    by_cases hy : y ∈ Metric.closedBall (0 : Space) R
    · rw [Set.indicator_of_mem hy]
      gcongr
      have := hC (t, y) ⟨⟨ht.1.le, ht.2⟩, hy⟩
      rw [← ofReal_norm]
      exact ENNReal.ofReal_le_ofReal this
    · rw [Set.indicator_of_notMem hy]
      have : Ψ (t, y) = 0 := hR t y (by simpa [mem_closedBall_zero_iff] using hy)
      simp [this]
  have hfin : ∫⁻ t in Ioc (0 : ℝ) P, ∫⁻ y : Space, ‖Ψ (t, y)‖ₑ ^ (2 : ℝ) < ⊤ := by
    calc ∫⁻ t in Ioc (0 : ℝ) P, ∫⁻ y : Space, ‖Ψ (t, y)‖ₑ ^ (2 : ℝ)
        ≤ ∫⁻ t in Ioc (0 : ℝ) P, ∫⁻ y : Space,
            (Metric.closedBall (0 : Space) R).indicator
              (fun _ => ENNReal.ofReal C ^ (2 : ℝ)) y := by
          refine setLIntegral_mono' measurableSet_Ioc fun t ht => ?_
          exact lintegral_mono fun y => hbd t ht y
      _ < ⊤ := by
          simp only [lintegral_indicator_const measurableSet_closedBall, setLIntegral_const]
          refine ENNReal.mul_lt_top (ENNReal.mul_lt_top ?_ measure_closedBall_lt_top) ?_
          · exact ENNReal.rpow_lt_top_of_nonneg (by norm_num) ENNReal.ofReal_ne_top
          · simp
  show (ENNReal.ofReal P⁻¹ * _) ^ (1 / (2 : ℝ)) < ⊤
  exact ENNReal.rpow_lt_top_of_nonneg (by norm_num) (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hfin).ne

/-- `L₀ᵗ + μ` preserves phase tests. -/
theorem isPhaseTest_L0T_add {P ν μ : ℝ} {Ψ : ℝ × Space → CVec3} (hΨ : IsPhaseTest P Ψ) :
    IsPhaseTest P (fun x => L0T ν Ψ x + (μ : ℂ) • Ψ x) := by
  have h : (fun x => L0T ν Ψ x + (μ : ℂ) • Ψ x) =
      (PhaseSpace.driftT Ψ - ν • PhaseSpace.lapT Ψ - (1 / 2 : ℝ) • Ψ) + (μ : ℂ) • Ψ := by
    funext x
    simp [L0T, nuLapT]
  rw [h]
  exact (((hΨ.driftT).sub (hΨ.lapT.const_smul ν)).sub (hΨ.const_smul (1 / 2 : ℝ))).add
    (hΨ.const_smul (μ : ℂ))

theorem mollGraphInYr_of (h1 : MollIsSolTestL) : MollGraphInYr := by
  intro P ν μ hP hP1 hν hμ Φ g hΦ hsupp ρ
  exact isInYr_of_phaseTest hP (isPhaseTest_L0T_add (h1 P ν μ hP hP1 hν hμ Φ g hΦ hsupp ρ).1)

end UnforcedLeray.Short.PartIIIb.Concrete
