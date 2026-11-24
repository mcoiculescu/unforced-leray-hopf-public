import UnforcedLeray.Lib.TrainB.P0WeakGeneratorEta

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

open MeasureTheory Filter
open scoped ENNReal Topology
open UnforcedLeray.Cyl

namespace UnforcedLeray.TrainB

/-- The actual horizontal weak derivative of the cylinder Leray projection is the projection
of the horizontal weak derivative. The proof uses the compiled translation commutation and the
strong centered-cell quotient limit, then applies the distribution-pairing converse. -/
theorem hasWeakDeriv_P0_q_of_vecH1 {c : ℝ} (hc : 0 < c) (x : VecH1 c) :
    Sob.HasWeakDeriv (Sob.cylinder c) [((1 : ℝ), (0 : ℝ))]
      (Cyl.P0 c (vecH1ValueCellCLM_MP x) : Plane → Vec2)
      (Cyl.P0 c (vecH1DqCellCLM_MP x) : Plane → Vec2) := by
  let f : L2v c := vecH1ValueCellCLM_MP x
  let d : L2v c := vecH1DqCellCLM_MP x
  have hlim : Tendsto (fun h : ℝ => qDifferenceQuotientCLM hc h f)
      (nhdsWithin 0 {h : ℝ | h ≠ 0}) (𝓝 d) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    simpa [f, d] using tendsto_qDifferenceQuotientCLM_error_zero_of_vecH1 hc x
  have hcomm : ∀ h : ℝ,
      qDifferenceQuotientCLM hc h (Cyl.P0 c f) =
        Cyl.P0 c (qDifferenceQuotientCLM hc h f) := by
    intro h
    change h⁻¹ • (qShiftL2 hc h (Cyl.P0 c f) - Cyl.P0 c f) =
      Cyl.P0 c (h⁻¹ • (qShiftL2 hc h f - f))
    rw [qShiftL2_P0_comm hc]
    simp only [map_smul, map_sub]
  have hproj : Tendsto (fun h : ℝ => Cyl.P0 c (qDifferenceQuotientCLM hc h f))
      (nhdsWithin 0 {h : ℝ | h ≠ 0}) (𝓝 (Cyl.P0 c d)) :=
    ((Cyl.P0 c).continuous.tendsto d).comp hlim
  have hlimP0 : Tendsto (fun h : ℝ => qDifferenceQuotientCLM hc h (Cyl.P0 c f))
      (nhdsWithin 0 {h : ℝ | h ≠ 0}) (𝓝 (Cyl.P0 c d)) := by
    have heq : (fun h : ℝ => qDifferenceQuotientCLM hc h (Cyl.P0 c f)) =
        fun h => Cyl.P0 c (qDifferenceQuotientCLM hc h f) := funext hcomm
    rw [heq]
    exact hproj
  exact hasWeakDeriv_qDifferenceQuotientCLM hc (Cyl.P0 c f) (Cyl.P0 c d) hlimP0

/-- The actual axial weak derivative of the cylinder Leray projection is the projection
of the axial weak derivative. The proof uses the compiled translation commutation and the
strong centered-cell quotient limit, then applies the distribution-pairing converse. -/
theorem hasWeakDeriv_P0_eta_of_vecH1 {c : ℝ} (hc : 0 < c) (x : VecH1 c) :
    Sob.HasWeakDeriv (Sob.cylinder c) [((0 : ℝ), (1 : ℝ))]
      (Cyl.P0 c (vecH1ValueCellCLM_MP x) : Plane → Vec2)
      (Cyl.P0 c (vecH1DetaCellCLM_MP x) : Plane → Vec2) := by
  let f : L2v c := vecH1ValueCellCLM_MP x
  let d : L2v c := vecH1DetaCellCLM_MP x
  have hlim : Tendsto (fun h : ℝ => etaDifferenceQuotientCLM h f)
      (nhdsWithin 0 {h : ℝ | h ≠ 0}) (𝓝 d) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    simpa [f, d] using tendsto_etaDifferenceQuotientCLM_error_zero_of_vecH1 hc x
  have hcomm : ∀ h : ℝ,
      etaDifferenceQuotientCLM h (Cyl.P0 c f) =
        Cyl.P0 c (etaDifferenceQuotientCLM h f) := by
    intro h
    change h⁻¹ • (etaShiftL2 c h (Cyl.P0 c f) - Cyl.P0 c f) =
      Cyl.P0 c (h⁻¹ • (etaShiftL2 c h f - f))
    rw [etaShiftL2_P0_comm]
    simp only [map_smul, map_sub]
  have hproj : Tendsto (fun h : ℝ => Cyl.P0 c (etaDifferenceQuotientCLM h f))
      (nhdsWithin 0 {h : ℝ | h ≠ 0}) (𝓝 (Cyl.P0 c d)) :=
    ((Cyl.P0 c).continuous.tendsto d).comp hlim
  have hlimP0 : Tendsto (fun h : ℝ => etaDifferenceQuotientCLM h (Cyl.P0 c f))
      (nhdsWithin 0 {h : ℝ | h ≠ 0}) (𝓝 (Cyl.P0 c d)) := by
    have heq : (fun h : ℝ => etaDifferenceQuotientCLM h (Cyl.P0 c f)) =
        fun h => Cyl.P0 c (etaDifferenceQuotientCLM h f) := funext hcomm
    rw [heq]
    exact hproj
  exact hasWeakDeriv_etaDifferenceQuotientCLM hc (Cyl.P0 c f) (Cyl.P0 c d) hlimP0


#print axioms UnforcedLeray.TrainB.hasWeakDeriv_P0_q_of_vecH1
#print axioms UnforcedLeray.TrainB.hasWeakDeriv_P0_eta_of_vecH1

end UnforcedLeray.TrainB
