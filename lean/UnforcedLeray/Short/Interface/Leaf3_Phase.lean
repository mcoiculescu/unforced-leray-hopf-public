import UnforcedLeray.Cons.C08PhysicalMode.BodyForce
import UnforcedLeray.Analysis.SobolevEmbedding.Density

/-!
# Interface leaf 3, one phase: the body force is in `L²`

Shorter proof, lines 6071-6075: `‖U‖_∞‖∇f‖₂ + ‖∇U‖₃‖f‖₆`.

This generalises the draft `lerayDivIntegral_eq_bodyForce` (`Cons/C08PhysicalMode/BodyForce.lean`,
lines 160-203). The derivative `dU j` of the background is an arbitrary weak derivative lying in
`L³`, not the classical `∂ⱼU` with bounded `DU`. The `L²` bound for the term `B_j(∂ⱼU, w)` is
Hölder `L³ × L⁶ → L²`, with `w ∈ L⁶` from `SobolevEmbedding.weak_memLp_six`. The identity is
the weak Leibniz rule followed by the compiled Leray commutation and self-adjointness, as in the
draft.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter
open scoped ENNReal ContDiff Topology

namespace UnforcedLeray.Short.Interface

open UnforcedLeray.Blueprint UnforcedLeray.SobolevGraph UnforcedLeray.Cons.C08

/-- Hölder exponents `1/3 + 1/6 = 1/2` for the product `∇U · w` with `∇U ∈ L³`, `w ∈ L⁶`. -/
instance holderTriple_three_six_two_leaf3 : ENNReal.HolderTriple 3 6 2 := by
  apply ENNReal.HolderTriple.of_toReal
  norm_num [Real.holderTriple_iff]

theorem lerayDivIntegral_eq_bodyForce_L3 {U w : SpatialField} {dU G : Fin 3 → SpatialField} (hU : Continuous U) {C : ℝ} (hUb : ∀ x, ‖U x‖ ≤ C) (hdU : ∀ j, HasWeakSpatialDerivative j U (dU j)) (hdU3 : ∀ j, MemLp (dU j) 3 volume) (hw : MemLp w 2 volume) (hG : ∀ i, MemLp (G i) 2 volume) (hwG : ∀ i, HasWeakSpatialDerivative i w (G i)) {φ : Space → Space} (hφ : IsVectorTest φ) : MemLp (bodyForce U dU G w) 2 volume ∧ lerayDivIntegral (symTensorColumns U w) φ = inner ℝ (Leray.projection (toL2 (bodyForce U dU G w))) (toL2 φ) := by
  have hUm : AEStronglyMeasurable U volume := hU.aestronglyMeasurable
  have hw6 : MemLp w 6 volume := SobolevEmbedding.weak_memLp_six hw hG hwG
  have hcol : ∀ j, MemLp (symTensorColumns U w j) 2 volume := fun j => by
    rw [symTensorColumns_eq]
    exact memLp_bilin_bdd (symCol j) hUm hUb hw
  set D : Fin 3 → SpatialField :=
    fun j x => symCol j (dU j x) (w x) + symCol j (U x) (G j x) with hDdef
  have hD : ∀ j, MemLp (D j) 2 volume := fun j =>
    ((symCol j).memLp_of_bilin 2 (hdU3 j) hw6).add
      (memLp_bilin_bdd (symCol j) hUm hUb (hG j))
  have hweak : ∀ j, HasWeakSpatialDerivative j (symTensorColumns U w j) (D j) := by
    intro j
    have hL := L01.leibniz (symCol j) j (hdU j)
      (locL2_of_bound hUm hUb)
      (fun _ hφ => L01.test_smul_memLp (s := 6) hφ (hdU3 j))
      (H1.ofFields w G hw hG hwG)
    simp only [H1.value_ofFields, H1.derivative_ofFields] at hL
    rw [symTensorColumns_eq]
    refine hL.congr ?_ ?_
    · filter_upwards [coeFn_toL2 hw] with x hx
      rw [hx]
    · filter_upwards [coeFn_toL2 hw, coeFn_toL2 (hG j)] with x hx hx'
      rw [hx, hx']
  have hP : ∀ j, HasWeakSpatialDerivative j
      (Leray.projection (toL2 (symTensorColumns U w j)) : SpatialField)
      (Leray.projection (toL2 (D j)) : SpatialField) := fun j =>
    Leray.weakDerivative_projection _ _ j
      ((hweak j).congr (coeFn_toL2 (hcol j)).symm (coeFn_toL2 (hD j)).symm)
  have hbf : bodyForce U dU G w = fun x => ∑ j, D j x := rfl
  have hmem : MemLp (bodyForce U dU G w) 2 volume := by
    rw [hbf]
    exact memLp_finsetSum Finset.univ (fun j _ => hD j)
  refine ⟨hmem, ?_⟩
  rw [lerayDivIntegral_eq_lerayDivPairing hcol, lerayDivPairing, hbf, toL2_finsetSum hD,
    map_sum, sum_inner, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← Leray.projection_selfadjoint, inner_testPartial_of_weak (hP j) hφ, neg_neg]

end UnforcedLeray.Short.Interface
