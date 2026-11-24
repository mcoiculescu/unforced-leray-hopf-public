import UnforcedLeray.Short.PartIIIa.Sub.T15
import UnforcedLeray.Short.PartIIIa.T14_HeatGBound
import UnforcedLeray.Short.PartIIIa.T04_GaussInvIntegral
import UnforcedLeray.Short.PartIIIa.T15_SepKernelBounds.HeatTailStep

/-!
# Part III-a, task `PartIII-a:T15/4`: derivatives of the heat tail

Proves `heatTailIterated : HeatTailIterated` (`Sub/T15.lean`; SP 3604-3606). For `t ≥ 0` and
`x ≠ 0`, `heatTail t` is `C^∞` at `x` and `D^m(heatTail t)(x) = ∫_{(t,∞)} D^m G_a(x) da` for every
`m`.

Proof. Let `U = {y | y ≠ 0}` (open).

1. (Induction on `m`, at every `y ∈ U`.) The case `m = 0` is the isometry
   `continuousMultilinearCurryFin0` commuted with the Bochner integral. For the step, the
   identity `D^{m+1} f = curry⁻¹ (D(D^m f))` (`iteratedFDeriv_succ_eq_comp_left`) reduces the claim,
   after applying the isometry `continuousMultilinearCurryLeftEquiv`, to the equality
   `D(D^m heatTail t)(y) = ∫ D(D^m G_a)(y) da`. The left side is the derivative of a function
   that agrees with `y ↦ ∫ D^m G_a(y) da` on the neighbourhood `U` of `y` (induction hypothesis,
   `Filter.EventuallyEq.fderiv_eq`), and that derivative is `∫ D(D^m G_a)(y) da` by
   `heatTailStep`.
2. (Smoothness.) Each `D^m(heatTail t)` equals `y ↦ ∫ D^m G_a(y) da` on `U`, which is
   differentiable at every point of `U` by `heatTailStep`. Hence `heatTail t` is `C^∞` on the open
   set `U` (`contDiffOn_of_differentiableOn`), and therefore `C^∞` at `x`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

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
/-- **Derivatives of the heat tail** (`PartIII-a:T15/4`; SP 3604-3606). -/
theorem heatTailIterated : UnforcedLeray.Short.IIIa.HeatTailIterated := by
  unfold HeatTailIterated
  intro t ht x hx
  -- the formula for all `m`, at every point of the open set `{y ≠ 0}`
  have hD : ∀ m : ℕ, ∀ y : Space, y ≠ 0 →
      iteratedFDeriv ℝ m (heatTail t) y = ∫ a in Ioi t, iteratedFDeriv ℝ m (heatG a) y := by
    intro m
    induction m with
    | zero =>
      intro y _
      have h0 : ∀ (f : Space → ℝ) (z : Space), iteratedFDeriv ℝ 0 f z =
          (continuousMultilinearCurryFin0 ℝ Space ℝ).symm (f z) := fun f z => rfl
      simp only [h0]
      show (continuousMultilinearCurryFin0 ℝ Space ℝ).symm (∫ a in Ioi t, heatG a y) = _
      exact ((continuousMultilinearCurryFin0 ℝ Space ℝ).symm.toLinearIsometry.integral_comp_comm
        (fun a => heatG a y)).symm
    | succ m ih =>
      intro y hy
      -- `D^{m+1} f = Φ⁻¹ (D (D^m f))` pointwise (`iteratedFDeriv_succ_eq_comp_left`)
      have hsymm : ∀ (f : Space → ℝ) (z : Space), iteratedFDeriv ℝ (m + 1) f z =
          (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (m + 1) => Space) ℝ).symm
            (fderiv ℝ (iteratedFDeriv ℝ m f) z) := by
        intro f z
        rw [iteratedFDeriv_succ_eq_comp_left, Function.comp_apply]
      have hEv : iteratedFDeriv ℝ m (heatTail t) =ᶠ[𝓝 y]
          fun z => ∫ a in Ioi t, iteratedFDeriv ℝ m (heatG a) z :=
        eventually_of_mem (isOpen_ne.mem_nhds hy) (fun z hz => ih z hz)
      have hF : fderiv ℝ (iteratedFDeriv ℝ m (heatTail t)) y =
          ∫ a in Ioi t, fderiv ℝ (iteratedFDeriv ℝ m (heatG a)) y := by
        rw [hEv.fderiv_eq]
        exact (heatTailStep t ht m y hy).fderiv
      have hcomm : ∫ a in Ioi t, (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (m + 1) => Space) ℝ).symm
          (fderiv ℝ (iteratedFDeriv ℝ m (heatG a)) y) =
          (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (m + 1) => Space) ℝ).symm
            (∫ a in Ioi t, fderiv ℝ (iteratedFDeriv ℝ m (heatG a)) y) := by
        first
        | exact (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (m + 1) => Space) ℝ).symm.toLinearIsometry.integral_comp_comm (μ := volume.restrict (Ioi t)) (fun a => fderiv ℝ (iteratedFDeriv ℝ m (heatG a)) y)
        | exact (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (m + 1) => Space) ℝ).symm.toContinuousLinearEquiv.integral_comp_comm (μ := volume.restrict (Ioi t)) (fun a => fderiv ℝ (iteratedFDeriv ℝ m (heatG a)) y)
        | exact (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (m + 1) => Space) ℝ).symm.toLinearIsometry.toContinuousLinearMap.integral_comp_comm' (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (m + 1) => Space) ℝ).symm.antilipschitz (fun a => fderiv ℝ (iteratedFDeriv ℝ m (heatG a)) y)
        | exact hti_integral_iso_comm (𝕜 := ℝ) (μ := volume.restrict (Ioi t)) (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (m + 1) => Space) ℝ).symm (fun a => fderiv ℝ (iteratedFDeriv ℝ m (heatG a)) y)
      rw [hsymm (heatTail t) y, hF, ← hcomm]
      exact integral_congr_ae (ae_of_all _ (fun a => (hsymm (heatG a) y).symm))

  -- the open set `U = {y ≠ 0}`
  have hopen : IsOpen {z : Space | z ≠ 0} := isOpen_ne
  have hxU : {z : Space | z ≠ 0} ∈ 𝓝 x := hopen.mem_nhds hx
  -- `D^m(heatTail t)` agrees near each `y ≠ 0` with the integral of `D^m G_a`
  have hEqNhds : ∀ (m : ℕ) (y : Space), y ≠ 0 →
      iteratedFDeriv ℝ m (heatTail t) =ᶠ[𝓝 y]
        fun z => ∫ a in Ioi t, iteratedFDeriv ℝ m (heatG a) z :=
    fun m y hy => eventually_of_mem (hopen.mem_nhds hy) (fun z hz => hD m z hz)
  -- hence `D^m(heatTail t)` is differentiable at every `y ≠ 0`
  have hDiffAt : ∀ (m : ℕ) (y : Space), y ≠ 0 →
      DifferentiableAt ℝ (iteratedFDeriv ℝ m (heatTail t)) y := fun m y hy =>
    ((heatTailStep t ht m y hy).differentiableAt).congr_of_eventuallyEq (hEqNhds m y hy)
  have hdiffOn : ∀ m : ℕ, DifferentiableOn ℝ
      (iteratedFDerivWithin ℝ m (heatTail t) {z : Space | z ≠ 0}) {z : Space | z ≠ 0} := by
    intro m
    refine DifferentiableOn.congr (fun y hy => (hDiffAt m y hy).differentiableWithinAt) ?_
    intro y hy
    exact iteratedFDerivWithin_of_isOpen m hopen hy
  -- smoothness on the open set, hence at `x`
  have hCDon : ContDiffOn ℝ ∞ (heatTail t) {z : Space | z ≠ 0} :=
    contDiffOn_of_differentiableOn (fun m _ => hdiffOn m)
  exact ⟨hCDon.contDiffAt hxU, fun m => hD m x hx⟩

end UnforcedLeray.Short.IIIa
