import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D2_1_3_1_2_2_3_2
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.AdjMollLocInt

/-!
# `PhaseLocalL2`: local `L²` of a `P`-periodic `Y_2` field on a time box

Source `the November 2 reference manuscript`
lines 1556-1583. The time box `[-R,R] × ℝ³` is unbounded in space, so it is covered by finitely
many phase cells `(kP,(k+1)P] × ℝ³` (time slabs), and each cell has the same `L²` integral as the
base cell (`setLIntegral_cellK`, `lint_cellBase_lt_top` from `AdjMollLocInt`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411

/-- Finitely many phase cells cover the time box `[-R,R] × ℝ³` (time-slab version of
`cover_closedBall`). -/
theorem cover_tBox (P : ℝ) (hP : 0 < P) (R : ℝ) :
    ∃ N : ℤ, tBox R ⊆ ⋃ k ∈ Finset.Icc (-N) N, (cellK P k : Set (ℝ × Space)) := by
  refine ⟨⌈R / P⌉ + 1, fun z hz => ?_⟩
  simp only [tBox, Set.mem_prod, Set.mem_Icc, Set.mem_univ, and_true] at hz
  obtain ⟨hlo, hhi⟩ := hz
  have hc1 : z.1 / P ≤ (⌈z.1 / P⌉ : ℝ) := Int.le_ceil _
  have hc2 : (⌈z.1 / P⌉ : ℝ) < z.1 / P + 1 := Int.ceil_lt_add_one _
  have hRP : R / P ≤ (⌈R / P⌉ : ℝ) := Int.le_ceil _
  have hlo' : -R / P ≤ z.1 / P := by
    apply div_le_div_of_nonneg_right _ hP.le
    linarith
  have hhi' : z.1 / P ≤ R / P := by
    apply div_le_div_of_nonneg_right _ hP.le
    linarith
  have hneg : -R / P = -(R / P) := by ring
  set k : ℤ := ⌈z.1 / P⌉ - 1 with hk
  have hkR : (k : ℝ) = (⌈z.1 / P⌉ : ℝ) - 1 := by rw [hk]; push_cast; ring
  have hk1 : (k : ℝ) * P < z.1 := by
    have : (k : ℝ) < z.1 / P := by rw [hkR]; linarith
    exact (lt_div_iff₀ hP).mp this
  have hk2 : z.1 ≤ ((k : ℝ) + 1) * P := by
    have : z.1 / P ≤ (k : ℝ) + 1 := by rw [hkR]; linarith
    exact (div_le_iff₀ hP).mp this
  have hN1 : -((⌈R / P⌉ + 1 : ℤ) : ℝ) ≤ (k : ℝ) := by
    push_cast
    linarith
  have hN2 : (k : ℝ) ≤ ((⌈R / P⌉ + 1 : ℤ) : ℝ) := by
    push_cast
    have : (k : ℝ) < z.1 / P := by rw [hkR]; linarith
    linarith
  have hN1' : -(⌈R / P⌉ + 1) ≤ k := by exact_mod_cast hN1
  have hN2' : k ≤ ⌈R / P⌉ + 1 := by exact_mod_cast hN2
  refine Set.mem_iUnion₂.mpr ⟨k, Finset.mem_Icc.mpr ⟨hN1', hN2'⟩, ?_⟩
  exact (mem_cellK_iff P k z).mpr ⟨hk1, hk2⟩

/-- The `L²` integral over the time box `[-R,R] × ℝ³` is finite for a `Y_2` field. -/
theorem lint_tBox_lt_top {P : ℝ} (hP : 0 < P) {g : ℝ × Space → CVec3}
    (hg : UnforcedLeray.Short.IIb.IsInYr P 2 g) (R : ℝ) :
    ∫⁻ x in tBox R, ‖g x‖ₑ ^ (2 : ℝ) < ⊤ := by
  obtain ⟨N, hN⟩ := cover_tBox P hP R
  have hmeas : AEMeasurable (fun z => ‖g z‖ₑ ^ (2 : ℝ)) volume :=
    (hg.meas.enorm).pow_const (2 : ℝ)
  have hT : MeasurableSet (tBox R) := measurableSet_Icc.prod MeasurableSet.univ
  calc ∫⁻ x in tBox R, ‖g x‖ₑ ^ (2 : ℝ)
      = ∫⁻ z, (tBox R).indicator (fun z => ‖g z‖ₑ ^ (2 : ℝ)) z :=
        (lintegral_indicator hT _).symm
    _ ≤ ∫⁻ z, ∑ k ∈ Finset.Icc (-N) N,
          (cellK P k).indicator (fun z => ‖g z‖ₑ ^ (2 : ℝ)) z := by
        apply lintegral_mono
        intro z
        by_cases hz : z ∈ tBox R
        · obtain ⟨k, hk, hzk⟩ := Set.mem_iUnion₂.mp (hN hz)
          calc (tBox R).indicator (fun z => ‖g z‖ₑ ^ (2 : ℝ)) z = ‖g z‖ₑ ^ (2 : ℝ) :=
                indicator_of_mem hz (fun z => ‖g z‖ₑ ^ (2 : ℝ))
            _ = (cellK P k).indicator (fun z => ‖g z‖ₑ ^ (2 : ℝ)) z :=
                (indicator_of_mem hzk (fun z => ‖g z‖ₑ ^ (2 : ℝ))).symm
            _ ≤ ∑ j ∈ Finset.Icc (-N) N,
                  (cellK P j).indicator (fun z => ‖g z‖ₑ ^ (2 : ℝ)) z :=
                Finset.single_le_sum (f := fun j =>
                  (cellK P j).indicator (fun z => ‖g z‖ₑ ^ (2 : ℝ)) z)
                  (fun j _ => zero_le) hk
        · rw [indicator_of_notMem hz]
          exact zero_le
    _ = ∑ k ∈ Finset.Icc (-N) N, ∫⁻ z in cellK P k, ‖g z‖ₑ ^ (2 : ℝ) := by
        rw [lintegral_finsetSum']
        · exact Finset.sum_congr rfl fun k _ =>
            lintegral_indicator (measurableSet_cellK P k) _
        · intro k _
          exact hmeas.indicator (measurableSet_cellK P k)
    _ < ⊤ := by
        refine ENNReal.sum_lt_top.mpr fun k _ => ?_
        rw [setLIntegral_cellK P k g hg.periodic]
        exact lint_cellBase_lt_top hP hg

theorem phaseLocalL2 : PhaseLocalL2 := by
  intro P hP g hg R
  exact lint_tBox_lt_top hP hg R

end UnforcedLeray.Short.PartIIIb.Concrete
