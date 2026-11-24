import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_1_2_3_1
import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_1_2_3_1.L1

/-!
# Part III-b, task `IIIb-D2/3/1/2/3/1/2`: `HeatTailC2Pos`

Source of record: `the November 2 reference manuscript`, lines 3598-3610
(`K_t = δ G_t + ∂∂ ∫_t^∞ G_a da`).

Proof of `heatTailC2Pos : HeatTailC2Pos`. Let `t > 0`. We show:

1. (Induction on `m`, at every `y`.) `D^m (heatTail t) y = ∫_{(t,∞)} D^m G_a y da` for all `y`.
   This uses `heatTailStepPos`, which gives the derivative of `y ↦ ∫ D^m G_a y da` at every point.
2. Hence each `D^m (heatTail t)` equals a function that is differentiable everywhere, so
   `heatTail t` is `C²` (indeed `C^∞`) everywhere, by `contDiff_of_differentiable_iteratedFDeriv`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology

namespace UnforcedLeray.Short.PartIIIb.Concrete

set_option synthInstance.maxHeartbeats 400000 in
/-- A linear isometric equivalence commutes with Bochner integrals (no integrability needed). -/
theorem hti_integral_iso_comm {𝕜 X E F : Type*} [RCLike 𝕜] [MeasurableSpace X] {μ : Measure X}
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F] [NormedSpace ℝ F] [CompleteSpace F]
    (e : E ≃ₗᵢ[𝕜] F) (φ : X → E) :
    ∫ x, e (φ x) ∂μ = e (∫ x, φ x ∂μ) :=
  LinearIsometry.integral_comp_comm e.toLinearIsometry φ

set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in
/-- **`HeatTailC2Pos`** (`IIIb-D2/3/1/2/3/1/2`; SP 3598-3610): for `t > 0`, `heatTail t` is `C²`
at every point, including the origin. -/
theorem heatTailC2Pos : UnforcedLeray.Short.PartIIIb.Concrete.HeatTailC2Pos := by
  unfold HeatTailC2Pos
  intro t ht x
  -- the formula for all `m`, at every point of `Space` (no restriction to `y ≠ 0`)
  have hD : ∀ m : ℕ, ∀ y : Space,
      iteratedFDeriv ℝ m (IIIa.heatTail t) y =
        ∫ a in Ioi t, iteratedFDeriv ℝ m (IIIa.heatG a) y := by
    intro m
    induction m with
    | zero =>
      intro y
      have h0 : ∀ (f : Space → ℝ) (z : Space), iteratedFDeriv ℝ 0 f z =
          (continuousMultilinearCurryFin0 ℝ Space ℝ).symm (f z) := fun f z => rfl
      simp only [h0]
      show (continuousMultilinearCurryFin0 ℝ Space ℝ).symm (∫ a in Ioi t, IIIa.heatG a y) = _
      exact ((continuousMultilinearCurryFin0 ℝ Space ℝ).symm.toLinearIsometry.integral_comp_comm
        (fun a => IIIa.heatG a y)).symm
    | succ m ih =>
      intro y
      -- `D^{m+1} f = Φ⁻¹ (D (D^m f))` pointwise (`iteratedFDeriv_succ_eq_comp_left`)
      have hsymm : ∀ (f : Space → ℝ) (z : Space), iteratedFDeriv ℝ (m + 1) f z =
          (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (m + 1) => Space) ℝ).symm
            (fderiv ℝ (iteratedFDeriv ℝ m f) z) := by
        intro f z
        rw [iteratedFDeriv_succ_eq_comp_left, Function.comp_apply]
      -- the induction hypothesis holds as an equality of functions on all of `Space`
      have hfun : iteratedFDeriv ℝ m (IIIa.heatTail t) =
          fun z => ∫ a in Ioi t, iteratedFDeriv ℝ m (IIIa.heatG a) z := funext ih
      have hF : fderiv ℝ (iteratedFDeriv ℝ m (IIIa.heatTail t)) y =
          ∫ a in Ioi t, fderiv ℝ (iteratedFDeriv ℝ m (IIIa.heatG a)) y := by
        rw [hfun]
        exact (UnforcedLeray.Short.PartIIIb.heatTailStepPos t ht m y).fderiv
      have hcomm : ∫ a in Ioi t, (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (m + 1) => Space) ℝ).symm
          (fderiv ℝ (iteratedFDeriv ℝ m (IIIa.heatG a)) y) =
          (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (m + 1) => Space) ℝ).symm
            (∫ a in Ioi t, fderiv ℝ (iteratedFDeriv ℝ m (IIIa.heatG a)) y) := by
        exact hti_integral_iso_comm (𝕜 := ℝ) (μ := volume.restrict (Ioi t))
          (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (m + 1) => Space) ℝ).symm
          (fun a => fderiv ℝ (iteratedFDeriv ℝ m (IIIa.heatG a)) y)
      rw [hsymm (IIIa.heatTail t) y, hF, ← hcomm]
      exact integral_congr_ae (ae_of_all _ (fun a => (hsymm (IIIa.heatG a) y).symm))
  -- every `D^m (heatTail t)` is differentiable at every point of `Space`
  have hdiff : ∀ m : ℕ, Differentiable ℝ (iteratedFDeriv ℝ m (IIIa.heatTail t)) := by
    intro m
    have heq : iteratedFDeriv ℝ m (IIIa.heatTail t) =
        fun z => ∫ a in Ioi t, iteratedFDeriv ℝ m (IIIa.heatG a) z := funext (hD m)
    rw [heq]
    intro y
    exact (UnforcedLeray.Short.PartIIIb.heatTailStepPos t ht m y).differentiableAt
  -- smoothness, in particular `C²`, at `x`
  exact (contDiff_of_differentiable_iteratedFDeriv (n := 2) (fun m _ => hdiff m)).contDiffAt

end UnforcedLeray.Short.PartIIIb.Concrete
