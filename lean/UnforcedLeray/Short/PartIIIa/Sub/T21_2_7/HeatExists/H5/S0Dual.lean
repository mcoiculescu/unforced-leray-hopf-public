import UnforcedLeray.Short.PartIIIa.Sub.T21_2_7.HeatExists.LeavesOf
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_7.HeatExists.H1
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_7.HeatExists.H5.KerUnfold
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_3_2_2_Smooth.Basic

/-!
# Part III-a, `PartIII-a:T21/2/7/1/8/5/1`: (H5.1) the dual identity of the heat flow

Source of record: `the November 2 reference manuscript` (SP), lines 2819-2836
and 3044-3050. Statement: `HeatExists/Leaves.lean` (`AdjHeatS0Dual`).
Proof: `adjKerUnfold` at the kernel `adjHeatKer ν θ` (Young bound from `adjHeatS0Young`), then the
pointwise identity `∫ G(z) ψ(x + z) dz = P_{νθ} ψ(x)` (substitution `z ↦ -z` and evenness of `G`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

theorem adjHeatS0Dual (m : ℝ) (hm : 8 < m) : AdjHeatS0Dual m := by
  intro ν c hν hc θ hθ w ψ hψ
  obtain ⟨M₀, _, hY⟩ := adjHeatS0Young m hm ν c hν hc
  have hθpos : 0 < θ := hθ.1
  have hνθ : 0 < ν * θ := mul_pos hν hθpos
  have key := adjKerUnfold m hm c hc (adjHeatKer ν θ) (continuous_adjHeatKer ν θ) M₀
    (hY θ hθ) w ψ hψ
  have hev : ∀ z : ℝ × ℝ, adjHeatKer ν θ (-z) = adjHeatKer ν θ z := by
    intro z
    simp only [adjHeatKer, UnforcedLeray.B0284.heatKernel2, Prod.fst_neg, Prod.snd_neg,
      UnforcedLeray.B0191.heatKernel, neg_sq]
  have hpt : ∀ x : ℝ × ℝ, (∫ z : ℝ × ℝ, adjHeatKer ν θ z * ψ (x + z)) =
      Exist.cylHeatSmooth c (ν * θ) ψ x := by
    intro x
    rw [Exist.cylHeatSmooth_apply_of_pos hνθ]
    have h : (∫ z : ℝ × ℝ, adjHeatKer ν θ (-z) * ψ (x + -z)) =
        ∫ z : ℝ × ℝ, adjHeatKer ν θ z * ψ (x + z) :=
      MeasureTheory.integral_neg_eq_self (fun z : ℝ × ℝ => adjHeatKer ν θ z * ψ (x + z)) _
    rw [← h]
    congr 1
    funext z
    rw [hev z, show x + -z = x - z by ring]
    rfl
  rw [adjS0Fun_eq_adjKerOp, key]
  simp_rw [hpt]

end UnforcedLeray.Short.IIIa
