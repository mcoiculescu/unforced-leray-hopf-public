import UnforcedLeray.Cons.L2.BackgroundConcrete.SpatialProductCellApprox
import UnforcedLeray.Cons.L2.BackgroundConcrete.PeriodizedCellPair

set_option autoImplicit false
set_option maxHeartbeats 500000

noncomputable section

open MeasureTheory Set
open scoped ContDiff ENNReal Topology

namespace UnforcedLeray.Cons.C03.Concrete

open UnforcedLeray.Blueprint
open UnforcedLeray.PhaseSpace
open UnforcedLeray.PhaseTrace
open UnforcedLeray.B0411
open UnforcedLeray.B0412
open UnforcedLeray.Sob
open UnforcedLeray.B0005

/-- The actual scalar product with one phase cutoff. -/
def phaseCutoffScalarProduct (P : ℝ) (n : ℕ) (Φ : ℝ × Space → CVec3)
    (U : ℝ → SpatialField) : SpaceTime → ℂ := fun z =>
  phaseCutoffSpaceTime (phaseInteriorCutoff P n) z • scalarTestBackground Φ U z

/-- Its actual spacetime mollification, transferred back to the physical spacetime coordinates. -/
def mollifiedPhaseCutoffScalarProduct (P : ℝ) (n k : ℕ)
    (Φ : ℝ × Space → CVec3) (U : ℝ → SpatialField) : SpaceTime → ℂ :=
  (moll (spacetimeShrinkBump k) volume
    (phaseCutoffScalarProduct P n Φ U ∘ spacetimeHilbertEquiv.symm)) ∘
      spacetimeHilbertEquiv

/-- A second phase cutoff makes the mollified scalar product compactly supported away from the
phase seams. -/
def nestedCutoffMollification (P : ℝ) (n k : ℕ)
    (Φ : ℝ × Space → CVec3) (U : ℝ → SpatialField) : SpaceTime → ℂ := fun z =>
  phaseCutoffSpaceTime (phaseInteriorCutoff P n) z •
    mollifiedPhaseCutoffScalarProduct P n k Φ U z

/-- Smooth the phase-cutoff product and apply a second copy of the same phase cutoff. The
result is a genuine compactly supported pre-periodic scalar test, with support strictly inside
the phase interval. -/
theorem nestedCutoffMollification_isCompactInteriorTest {P : ℝ} [Fact (0 < P)]
    {Φ : ℝ × Space → CVec3} (hΦ : IsPhaseTest P Φ)
    {U : ℝ → SpatialField} (hU : IsBoundedBackground U)
    {n k : ℕ} (hn : 2 / ((n : ℝ) + 1) ≤ P) :
    ContDiff ℝ ∞ (nestedCutoffMollification P n k Φ U) ∧
      HasCompactSupport (nestedCutoffMollification P n k Φ U) ∧
      TimeSupp (1 / ((n : ℝ) + 1)) (P - 1 / ((n : ℝ) + 1))
        (nestedCutoffMollification P n k Φ U) ∧
      IsPhaseTest 0 (nestedCutoffMollification P n k Φ U) := by
  let χ : ℝ → ℝ := phaseInteriorCutoff P n
  have hχcd : ContDiff ℝ ∞ χ := contDiff_phaseInteriorCutoff P n
  have hχc : HasCompactSupport χ := hasCompactSupport_phaseInteriorCutoff_inner Fact.out hn
  letI : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨by norm_num⟩
  have hcell := scalarTestBackground_memLp_cell (p := 2) hΦ hU (by norm_num)
  have hFmem : MemLp (phaseCutoffScalarProduct P n Φ U) 2 volume := by
    change MemLp (fun z : SpaceTime => phaseCutoffSpaceTime
      (phaseInteriorCutoff P n) z • scalarTestBackground Φ U z) 2 volume
    exact memLp_phaseInteriorCutoff_of_cell_memLp (P := P) hcell n
  have hFmemST : MemLp
      (phaseCutoffScalarProduct P n Φ U ∘ spacetimeHilbertEquiv.symm) 2 volume :=
    memLp_spacetimeHilbertPullback hFmem
  have hMcd : ContDiff ℝ ∞ (mollifiedPhaseCutoffScalarProduct P n k Φ U) := by
    exact (contDiff_spacetimeMollification hFmemST k).comp spacetimeHilbertEquiv.contDiff
  have hMcompact : HasCompactSupport (mollifiedPhaseCutoffScalarProduct P n k Φ U) := by
    have hFcompact : HasCompactSupport
        (phaseCutoffScalarProduct P n Φ U ∘ spacetimeHilbertEquiv.symm) := by
      change HasCompactSupport ((fun z : SpaceTime => phaseCutoffSpaceTime
        (phaseInteriorCutoff P n) z • scalarTestBackground Φ U z) ∘
          spacetimeHilbertEquiv.symm)
      exact hasCompactSupport_hilbert_phaseCutoff_scalarTestBackground hΦ hχc
    exact (hasCompactSupport_spacetimeMollification hFcompact k).comp_homeomorph
      spacetimeHilbertEquiv.toHomeomorph
  have hGcd : ContDiff ℝ ∞ (nestedCutoffMollification P n k Φ U) := by
    exact (contDiff_phaseCutoffSpaceTime hχcd).smul hMcd
  have hGc : HasCompactSupport (nestedCutoffMollification P n k Φ U) := by
    change HasCompactSupport (fun z : SpaceTime =>
      Complex.ofReal (phaseInteriorCutoff P n z.1) *
        mollifiedPhaseCutoffScalarProduct P n k Φ U z)
    exact hMcompact.mul_left
  have htime : TimeSupp (1 / ((n : ℝ) + 1)) (P - 1 / ((n : ℝ) + 1))
      (nestedCutoffMollification P n k Φ U) := by
    intro τ y hτ
    simp only [mem_Icc, not_and_or, not_le] at hτ
    rcases hτ with hleft | hright
    · have hzero := phaseInteriorCutoff_eq_zero_left (P := P) n hleft.le
      simp [nestedCutoffMollification, phaseCutoffSpaceTime, hzero]
    · have hzero := phaseInteriorCutoff_eq_zero_right (P := P) n hright.le
      simp [nestedCutoffMollification, phaseCutoffSpaceTime, hzero]
  obtain ⟨R, _hR, _hT, hspace⟩ :=
    exists_window_of_hasCompactSupport hGc
  have hG0 : IsPhaseTest 0 (nestedCutoffMollification P n k Φ U) :=
    ⟨hGcd, (by intro τ y; simp), ⟨R, hspace⟩⟩
  exact ⟨hGcd, hGc, htime, hG0⟩

/-- Every nested-cutoff mollification is annihilated by actual phase solenoidality after
periodization. -/
theorem phaseSolenoidal_pairF_nestedCutoffMollification_zero {P : ℝ} [Fact (0 < P)]
    {w : Yq P q0E} (hw : IsPhaseSolenoidal w)
    {Φ : ℝ × Space → CVec3} (hΦ : IsPhaseTest P Φ)
    {U : ℝ → SpatialField} (hU : IsBoundedBackground U)
    {n k : ℕ} (hn : 2 / ((n : ℝ) + 1) ≤ P) :
    pairF P (PhaseSpace.gradT
      (perT P (nestedCutoffMollification P n k Φ U)))
      (fun x => rep w x.1 x.2) = 0 := by
  obtain ⟨_hcd, _hcompact, htime, hG0⟩ :=
    nestedCutoffMollification_isCompactInteriorTest hΦ hU hn
  exact phaseSolenoidal_pairF_grad_perT_zero hw htime hG0

#print axioms nestedCutoffMollification_isCompactInteriorTest
#print axioms phaseSolenoidal_pairF_nestedCutoffMollification_zero

end UnforcedLeray.Cons.C03.Concrete
