import UnforcedLeray.Short.PartI.Sub.T02_1_4_6_4
import UnforcedLeray.Lib.HeatCylinder.CenteredHeatProjectionConditional
import UnforcedLeray.Lib.HeatCylinder.HeatVecGaussianAverageIdentification
import UnforcedLeray.Lib.HeatCylinder.CenteredGaussianShiftAveragePairing
import UnforcedLeray.Lib.HeatCylinder.HeatKernelAgeDerivative

/-!
# Part I, task `PartI:T02/1/4/6/4` (`CenteredHeatAgeDerivative`): reduction to three leaves

Target: `centeredHeatAgeDerivative : CenteredHeatAgeDerivative` (the Prop is defined in
`Short/PartI/Sub/T02_1_4_6_4.lean`; its docstring carries the proof idea, source lines 261-288).

This file proves, with no `sorry`:

* `centeredHeat_inner_eq_integral_CH`: the centered heat pairing is a Gaussian average of
  planar-shift pairings, with the smooth class in the second slot;
* `centeredHeatAgeDerivative_of_leaves`: `CenteredHeatAgeDerivative` follows from the three leaves
  `LeafAgeWeightedCH` (A), `LeafAgeIBPCH` (B) and `LeafShiftLapCH` (C).

The leaves are `Prop` definitions, not hypotheses of the target. The target theorem itself is not
stated here, because it cannot be closed without proving the three leaves.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff InnerProductSpace

namespace UnforcedLeray.Short.PartI

open UnforcedLeray
open UnforcedLeray.Train (Vec)
open UnforcedLeray.Cyl (Plane)
open UnforcedLeray.TrainB

/-! ### The shift pairing -/

/-- The planar-shift pairing `v ↦ ⟨τ_v ψL, G⟩` of a smooth test class `ψL` against an `L²` class
`G`, with `τ_v = planeShiftL2CLM hc v`. -/
def shiftPairCH {c : ℝ} (hc : 0 < c) (ψL G : Cyl.L2v c) : Plane → ℝ :=
  fun v => inner ℝ (HeatCylinder.planeShiftL2CLM hc v ψL) G

/-! ### The leaf statements -/

/-- **Leaf A** (age derivative against a bounded continuous planar weight).  The scalar version of
`hasDerivAt_heatVecConvolution_age` (`Lib/HeatCylinder/HeatVecAgeDerivative.lean:30`): for
`θ > 0` and a bounded continuous `G`, `s ↦ ∫ K_s(w) G(w) dw` has derivative
`∫ ∂_θ K_θ(w) G(w) dw` at `θ`. -/
def LeafAgeWeightedCH : Prop :=
  ∀ {θ : ℝ}, 0 < θ → ∀ G : Plane → ℝ, Continuous G → (∃ M : ℝ, ∀ w, ‖G w‖ ≤ M) →
    HasDerivAt (fun s : ℝ => ∫ w : Plane, UnforcedLeray.B0284.heatKernel2 s w * G w)
      (∫ w : Plane, UnforcedLeray.HeatCylinder.heatKernel2AgeDerivative θ w * G w) θ

/-- **Leaf B** (smooth Gaussian integration by parts in the age).  The smooth version of
`integral_heatKernel2AgeDerivative_mul_comp_sub` (`Lib/TrainB/P0GaussianSecondOrderIBP.lean:169`),
which assumes `ContDiff ℝ ⊤` (analytic) and is stated at the shifted point `z - w`.  Here `f` is
only `C^∞` with bounded derivatives up to order two, and the statement is at `w`.  The kernel
identity `∂_θ K_θ = ∂_q² K_θ + ∂_η² K_θ` (`heatKernel2AgeDerivative_eq_spatialLaplacian`,
`Lib/HeatCylinder/HeatKernelAgeLaplacian.lean:145`) turns the left side into a Gaussian
second-order integration by parts. -/
def LeafAgeIBPCH : Prop :=
  ∀ {θ : ℝ}, 0 < θ → ∀ {f : Plane → ℝ}, ContDiff ℝ ∞ f →
    (∃ M : ℝ, ∀ x, ‖f x‖ ≤ M) →
    (∃ M : ℝ, ∀ x, ‖fderiv ℝ f x‖ ≤ M) →
    (∃ M : ℝ, ∀ x, ‖fderiv ℝ (fun y => fderiv ℝ f y (1, 0)) x‖ ≤ M) →
    (∃ M : ℝ, ∀ x, ‖fderiv ℝ (fun y => fderiv ℝ f y (0, 1)) x‖ ≤ M) →
    ∫ w : Plane, UnforcedLeray.HeatCylinder.heatKernel2AgeDerivative θ w * f w =
      ∫ w : Plane, UnforcedLeray.B0284.heatKernel2 θ w * Train.lapS f w

/-- **Leaf C** (smoothness and Laplacian of the planar-shift pairing).  For a smooth
`c`-periodic test `ψ` with `η`-compact support (`IsCellTest c ψ`), with `L²(cell)` classes `ψL`
of `ψ` and `ψ'L` of `Δψ`, and any `L²(cell)` class `G`, the shift pairing
`v ↦ ⟨τ_v ψL, G⟩` is `C^∞` with bounded derivatives up to order two, and its Laplacian at `w`
is `⟨τ_w ψ'L, G⟩`.  Proof idea: differentiate `∫_cell ψ(z + v) G(z) dz` in `v` under the integral,
the derivatives falling on `ψ` (bounded, since `ψ` is periodic and vanishes for `|η|` large), and
`G ∈ L¹(cell)`. -/
def LeafShiftLapCH : Prop :=
  ∀ (c : ℝ) (hc : 0 < c) (ψ : Plane → Vec) (ψL ψ'L G : Cyl.L2v c),
    IsCellTest c ψ → ((ψL : Cyl.L2v c) : Plane → Vec) =ᵐ[Cyl.cellμ c] ψ →
    ((ψ'L : Cyl.L2v c) : Plane → Vec) =ᵐ[Cyl.cellμ c] Train.vecLaplacian ψ →
    ContDiff ℝ ∞ (shiftPairCH hc ψL G) ∧
    (∃ M : ℝ, ∀ x, ‖shiftPairCH hc ψL G x‖ ≤ M) ∧
    (∃ M : ℝ, ∀ x, ‖fderiv ℝ (shiftPairCH hc ψL G) x‖ ≤ M) ∧
    (∃ M : ℝ, ∀ x, ‖fderiv ℝ (fun y => fderiv ℝ (shiftPairCH hc ψL G) y (1, 0)) x‖ ≤ M) ∧
    (∃ M : ℝ, ∀ x, ‖fderiv ℝ (fun y => fderiv ℝ (shiftPairCH hc ψL G) y (0, 1)) x‖ ≤ M) ∧
    ∀ w : Plane, Train.lapS (shiftPairCH hc ψL G) w =
      inner ℝ (HeatCylinder.planeShiftL2CLM hc w ψ'L) G

/-! ### Bookkeeping -/

/-- The centered heat pairing is the Gaussian average of planar-shift pairings, with the smooth
class `x` in the heat slot (the same identity as `centeredHeat_inner_eq_integral` in
`SeedGenerator/Reduction.lean`, copied to keep this file independent of that draft). -/
theorem centeredHeat_inner_eq_integral_CH {c θ : ℝ} (hc : 0 < c) (hθ : 0 < θ)
    (x y : Cyl.L2v c) :
    inner ℝ (HeatCylinder.centeredHeatVecL2CLM hc θ x) y =
      ∫ w : Plane, UnforcedLeray.B0284.heatKernel2 θ w *
        inner ℝ (HeatCylinder.planeShiftL2CLM hc w x) y := by
  rw [HeatCylinder.centeredHeatVecL2CLM_eq_centeredGaussianShiftAverageCLM hc hθ x]
  exact HeatCylinder.inner_centeredGaussianShiftAverageCLM hc hθ x y

/-! ### Assembly -/

/-- `CenteredHeatAgeDerivative` from the three leaves.  For `θ > 0` the function
`s ↦ ⟨G, e^{sΔ} ψL⟩` equals `s ↦ ∫ K_s(w) ⟨τ_w ψL, G⟩ dw` near `θ`; leaf A differentiates the
right side, leaf B moves the age derivative onto the Laplacian of the shift pairing, and leaf C
identifies that Laplacian with `⟨τ_w ψ'L, G⟩`, which integrates back to `⟨G, e^{θΔ} ψ'L⟩`. -/
theorem centeredHeatAgeDerivative_of_leaves (hA : LeafAgeWeightedCH) (hB : LeafAgeIBPCH)
    (hC : LeafShiftLapCH) : CenteredHeatAgeDerivative := by
  intro c hc ψ ψL ψ'L hψ hψL hψ'L G θ hθ
  obtain ⟨hf, hfB, hdf, hq, he, hlap⟩ := hC c hc ψ ψL ψ'L G hψ hψL hψ'L
  have hAd := hA hθ (shiftPairCH hc ψL G) hf.continuous hfB
  have hEv : (fun s : ℝ => inner ℝ G (HeatCylinder.centeredHeatVecL2CLM hc s ψL)) =ᶠ[𝓝 θ]
      (fun s : ℝ => ∫ w : Plane, UnforcedLeray.B0284.heatKernel2 s w * shiftPairCH hc ψL G w) := by
    filter_upwards [Ioi_mem_nhds hθ] with s hs
    exact (real_inner_comm _ _).trans
      (centeredHeat_inner_eq_integral_CH hc (Set.mem_Ioi.mp hs) ψL G)
  have hIBP := hB hθ hf hfB hdf hq he
  have h2 : (∫ w : Plane, UnforcedLeray.B0284.heatKernel2 θ w *
        Train.lapS (shiftPairCH hc ψL G) w) =
      ∫ w : Plane, UnforcedLeray.B0284.heatKernel2 θ w *
        inner ℝ (HeatCylinder.planeShiftL2CLM hc w ψ'L) G := by
    refine integral_congr_ae (Eventually.of_forall fun w => ?_)
    dsimp only
    rw [hlap w]
  refine (hAd.congr_of_eventuallyEq hEv).congr_deriv ?_
  rw [hIBP, h2, ← centeredHeat_inner_eq_integral_CH hc hθ ψ'L G]
  exact real_inner_comm _ _

end UnforcedLeray.Short.PartI
