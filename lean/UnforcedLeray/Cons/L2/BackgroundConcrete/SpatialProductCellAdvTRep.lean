import UnforcedLeray.Cons.L2.BackgroundConcrete.SpatialProductCellAdvT
import UnforcedLeray.Cons.L2.BackgroundConcrete.RepresentativeLp

set_option autoImplicit false
set_option maxHeartbeats 3000000

noncomputable section

open MeasureTheory
open Set
open scoped ENNReal

namespace UnforcedLeray.Cons.C03.Concrete

open UnforcedLeray.Blueprint
open UnforcedLeray.PhaseSpace
open UnforcedLeray.B0412

private def advMapRep (Φ : ℝ × Space → CVec3) (z : SpaceTime) :
    CVec3 →L[ℂ] CVec3 :=
  ∑ j : Fin 3,
    (EuclideanSpace.proj j : CVec3 →L[ℂ] ℂ).smulRight (dy j Φ z)

/-- Advection of the actual joint representative of a graph-space field by a compact phase test
preserves its cell `L^q₀` integrability. The estimate is a bounded pointwise multiplier supported
on the compact spatial support of the test derivatives. -/
theorem memLp_advT_rep_cell {P : ℝ} [Fact (0 < P)]
    {w : Yq P q0E} {Φ : ℝ × Space → CVec3} (hΦ : IsPhaseTest P Φ) :
    MemLp (fun z : SpaceTime => advT (fun z => rep w z.1 z.2) Φ z) q0E
      (volume.restrict (phaseCell P)) := by
  let μ : Measure SpaceTime := volume.restrict (phaseCell P)
  let W : SpaceTime → CVec3 := fun z => rep w z.1 z.2
  let T : SpaceTime → CVec3 := fun z => advT W Φ z
  let A : SpaceTime → CVec3 →L[ℂ] CVec3 := advMapRep Φ
  have hW : MemLp W q0E μ := by
    simpa [W, μ, phaseCell] using memLp_rep_periodCell q0E_ne_top w
  have hAc : Continuous A := by
    apply continuous_finsetSum Finset.univ
    intro j hj
    exact (ContinuousLinearMap.smulRightL ℂ CVec3 CVec3
      (EuclideanSpace.proj j : CVec3 →L[ℂ] ℂ)).continuous.comp
      (hΦ.dy j).smooth.continuous
  have hWmeas : AEStronglyMeasurable W μ := hW.aestronglyMeasurable
  have htuple : AEStronglyMeasurable (fun z : SpaceTime => (A z, W z)) μ :=
    hAc.aestronglyMeasurable.prodMk hWmeas
  have heval : Continuous (fun a : (CVec3 →L[ℂ] CVec3) × CVec3 => a.1 a.2) :=
    isBoundedBilinearMap_apply.continuous.comp (continuous_fst.prodMk continuous_snd)
  have hTmeas : AEStronglyMeasurable T μ := by
    have hm := heval.comp_aestronglyMeasurable htuple
    have heq : (fun z : SpaceTime => A z (W z)) = T := by
      funext z
      simp [A, T, W, advMapRep, advT, ContinuousLinearMap.smulRight_apply,
        PiLp.proj_apply, Finset.sum_apply]
    exact hm.congr (ae_of_all _ fun z => congrFun heq z)
  obtain ⟨R0, hspace0⟩ := (hΦ.dy 0).bounded_support
  obtain ⟨R1, hspace1⟩ := (hΦ.dy 1).bounded_support
  obtain ⟨R2, hspace2⟩ := (hΦ.dy 2).bounded_support
  let R : ℝ := max R0 (max R1 R2)
  have hR0 : R0 ≤ R := le_max_left _ _
  have hR1 : R1 ≤ R := le_trans (le_max_left _ _) (le_max_right _ _)
  have hR2 : R2 ≤ R := le_trans (le_max_right _ _) (le_max_right _ _)
  let K : Set SpaceTime := Icc (0 : ℝ) P ×ˢ Metric.closedBall (0 : Space) R
  have hK : IsCompact K := isCompact_Icc.prod (isCompact_closedBall _ _)
  have hdy0c : Continuous (dy 0 Φ) := (hΦ.dy 0).smooth.continuous
  have hdy1c : Continuous (dy 1 Φ) := (hΦ.dy 1).smooth.continuous
  have hdy2c : Continuous (dy 2 Φ) := (hΦ.dy 2).smooth.continuous
  obtain ⟨MD0, hMD00, hMD0⟩ := exists_norm_bound_on_compact (dy 0 Φ) hdy0c
    (by simpa [K] using hK)
  obtain ⟨MD1, hMD10, hMD1⟩ := exists_norm_bound_on_compact (dy 1 Φ) hdy1c
    (by simpa [K] using hK)
  obtain ⟨MD2, hMD20, hMD2⟩ := exists_norm_bound_on_compact (dy 2 Φ) hdy2c
    (by simpa [K] using hK)
  let MD : ℝ := max MD0 (max MD1 MD2)
  have hdy0b : ∀ z ∈ phaseCell P, ‖dy 0 Φ z‖ ≤ MD0 := by
    intro z hz
    by_cases hy : ‖z.2‖ ≤ R
    · have hzK : z ∈ K := by
        change z.1 ∈ Icc (0 : ℝ) P ∧ z.2 ∈ Metric.closedBall (0 : Space) R
        exact ⟨⟨le_of_lt hz.1.1, hz.1.2⟩, by simpa [Metric.mem_closedBall] using hy⟩
      exact hMD0 z hzK
    · have h0 := hspace0 z.1 z.2 (lt_of_le_of_lt hR0 (lt_of_not_ge hy))
      rw [h0]
      simpa using hMD00
  have hdy1b : ∀ z ∈ phaseCell P, ‖dy 1 Φ z‖ ≤ MD1 := by
    intro z hz
    by_cases hy : ‖z.2‖ ≤ R
    · have hzK : z ∈ K := by
        change z.1 ∈ Icc (0 : ℝ) P ∧ z.2 ∈ Metric.closedBall (0 : Space) R
        exact ⟨⟨le_of_lt hz.1.1, hz.1.2⟩, by simpa [Metric.mem_closedBall] using hy⟩
      exact hMD1 z hzK
    · have h1 := hspace1 z.1 z.2 (lt_of_le_of_lt hR1 (lt_of_not_ge hy))
      rw [h1]
      simpa using hMD10
  have hdy2b : ∀ z ∈ phaseCell P, ‖dy 2 Φ z‖ ≤ MD2 := by
    intro z hz
    by_cases hy : ‖z.2‖ ≤ R
    · have hzK : z ∈ K := by
        change z.1 ∈ Icc (0 : ℝ) P ∧ z.2 ∈ Metric.closedBall (0 : Space) R
        exact ⟨⟨le_of_lt hz.1.1, hz.1.2⟩, by simpa [Metric.mem_closedBall] using hy⟩
      exact hMD2 z hzK
    · have h2 := hspace2 z.1 z.2 (lt_of_le_of_lt hR2 (lt_of_not_ge hy))
      rw [h2]
      simpa using hMD20
  have hMDnonneg : 0 ≤ MD := le_trans hMD00 (le_max_left _ _)
  have hdy : ∀ z ∈ phaseCell P, ∀ j : Fin 3, ‖dy j Φ z‖ ≤ MD := by
    intro z hz j
    fin_cases j
    · exact (hdy0b z hz).trans (le_max_left _ _)
    · exact (hdy1b z hz).trans (le_trans (le_max_left _ _) (le_max_right _ _))
    · exact (hdy2b z hz).trans (le_trans (le_max_right _ _) (le_max_right _ _))
  have hbound : ∀ᵐ z ∂μ, ‖T z‖ ≤ 3 * MD * ‖W z‖ := by
    filter_upwards [ae_restrict_mem (measurableSet_Ioc.prod MeasurableSet.univ)] with z hz
    change ‖advT W Φ z‖ ≤ 3 * MD * ‖W z‖
    rw [advT]
    calc
      ‖∑ j : Fin 3, W z j • dy j Φ z‖ ≤
          ∑ j : Fin 3, ‖W z j‖ * ‖dy j Φ z‖ := by
            calc
              ‖∑ j : Fin 3, W z j • dy j Φ z‖ ≤
                  ∑ j : Fin 3, ‖W z j • dy j Φ z‖ := norm_sum_le _ _
              _ = ∑ j : Fin 3, ‖W z j‖ * ‖dy j Φ z‖ := by
                    simp_rw [norm_smul]
      _ ≤ ∑ j : Fin 3, ‖W z‖ * MD := by
          apply Finset.sum_le_sum
          intro j hj
          exact mul_le_mul (PiLp.norm_apply_le _ j) (hdy z hz j)
            (norm_nonneg _) (norm_nonneg _)
      _ = 3 * MD * ‖W z‖ := by simp [Finset.sum_mul, Finset.mul_sum]; ring
  let C : ℝ := 3 * MD
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hCnorm : ‖C‖ = 3 * MD := by
    dsimp [C]
    exact abs_of_nonneg (mul_nonneg (by norm_num) hMDnonneg)
  have hmajor : MemLp (fun z : SpaceTime => C * ‖W z‖) q0E μ :=
    hW.norm.const_mul C
  have hTbound : ∀ᵐ z ∂μ, ‖T z‖ ≤ ‖C * ‖W z‖‖ := by
    filter_upwards [hbound] with z hz
    have hmajorNorm : ‖C * ‖W z‖‖ = C * ‖W z‖ := by
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hC (norm_nonneg _))]
    calc
      ‖T z‖ ≤ C * ‖W z‖ := by simpa [C, mul_assoc] using hz
      _ = ‖C * ‖W z‖‖ := hmajorNorm.symm
  have hTmem : MemLp T q0E μ := hmajor.of_le hTmeas hTbound
  simpa [T, W, μ] using hTmem

#print axioms memLp_advT_rep_cell

end UnforcedLeray.Cons.C03.Concrete
