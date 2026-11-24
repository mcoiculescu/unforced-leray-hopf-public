import UnforcedLeray.Short.PartI.Sub.T02_1_4_6_4

/-!
# `stressOrbitIsHeat` from one abstract heat-divergence identity

Source: `the November 2 reference manuscript`, lines 261-288 (Duhamel term of the
mild solution is the heat flow of `div (u ⊗ u)`).

`stressOrbitIsHeat_of` reduces `StressOrbitIsHeat` to `HeatDivStressIdentity`, a statement about a
single `H³` element `x` with smooth solenoidal periodic representative `w`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff InnerProductSpace

namespace UnforcedLeray.Short.PartI

open UnforcedLeray
open UnforcedLeray.Train (Vec toVec)
open UnforcedLeray.Cyl (Plane)
open UnforcedLeray.TrainB
open UnforcedLeray.HeatCylinder

/-- **Abstract heat-divergence identity** (source lines 261-288).  If `x : VectorH3 c` has smooth
periodic solenoidal representative `w` with bounded derivatives (zero-order class of `x` equals
`w` a.e. on the cell) and `G` is the `L²` class of the advection `(w·∇)w`, then for `θ > 0` the
zero-order class of `actualHeatDivH3 θ (x ⊗ x)` is `e^{θΔ} G` (`centeredHeatVecL2CLM hc θ G`).

Proof sketch: tensor has row representative `planeRowTensorValue w w` a.e.
(`tensorH3Bilinear_planeValue_ae`, `Lib/TrainB/TensorBridge.lean:615`); the actual heat-divergence
is `heatDivVecL2CLM` of it (`vectorH3NormalizedValue_actualHeatDivH3`,
`Lib/HeatCylinder/H3Operator.lean:84`; `heatDivVecL2CLM_apply_to_periodic`,
`Lib/HeatCylinder/H3ActualLimit.lean:525`), pointwise `B0296.heatDiv θ T = heat θ (rowDivergence T)`
by Gaussian integration by parts (smooth bounded `T`), `rowDivergence (w ⊗ w) = advection w` for
`div w = 0`, and `heat θ (advection w)` is `centeredHeatVecL2CLM` of its class. -/
def HeatDivStressIdentity : Prop :=
  ∀ (c : ℝ) (hc : 0 < c) (hc1 : 1 ≤ c) (θ : ℝ) (hθ : 0 < θ) (x : VectorH3 c)
    (w : Plane → Vec), ContDiff ℝ ∞ w → Cyl.IsPeriodic c w →
    (∀ k : ℕ, ∃ M : ℝ, ∀ z, ‖iteratedFDeriv ℝ k w z‖ ≤ M) →
    (∀ z, Cyl.divergence w z = 0) →
    ((vecH3CellDerivCLM Sob.Idx.zero x : Cyl.L2v c) : Plane → Vec) =ᵐ[Cyl.cellμ c] w →
    ∀ G : Cyl.L2v c, ((G : Cyl.L2v c) : Plane → Vec) =ᵐ[Cyl.cellμ c] Train.advection w →
      vecH3CellDerivCLM Sob.Idx.zero (actualHeatDivH3 hc hθ (tensorH3Bilinear hc1 x x)) =
        centeredHeatVecL2CLM hc θ G

theorem stressOrbitIsHeat_of (h : HeatDivStressIdentity) : StressOrbitIsHeat := by
  intro ν c T hν hc hc1 hT u _hu w hw hdiv G hG t ht r hr
  have hrT : r ∈ Icc (0 : ℝ) T := ⟨hr.1.le, (hr.2.trans ht.2).le⟩
  have hpos : 0 < t - r := sub_pos.mpr hr.2
  have hθ : 0 < ν * (t - r) := mul_pos hν hpos
  have hs : compactMildStressPath hc1 hT.le u r =
      tensorH3Bilinear hc1 (u ⟨r, hrT⟩) (u ⟨r, hrT⟩) := by
    change tensorH3Bilinear hc1 (extendCompactPath hT.le u r) (extendCompactPath hT.le u r) = _
    rw [extendCompactPath_apply_of_mem hT.le u hrT]
  have hred : compactMildStressOrbit (ν := ν) hc hc1 hT.le u t r =
      vecH3CellDerivCLM Sob.Idx.zero
        (actualHeatDivH3 hc hθ (tensorH3Bilinear hc1 (u ⟨r, hrT⟩) (u ⟨r, hrT⟩))) := by
    unfold compactMildStressOrbit actualHeatDivH3Orbit
    rw [dif_pos hθ, hs]
    rfl
  rw [hred]
  refine h c hc hc1 _ hθ (u ⟨r, hrT⟩) (w r) (hw.smooth r hrT) (hw.periodic r hrT) ?_
    (hdiv r hrT) ?_ (G r) (hG r hrT)
  · intro k
    obtain ⟨M, hM⟩ := hw.bounded k
    exact ⟨M, hM r hrT⟩
  · simpa [Sob.iterD] using hw.represents ⟨r, hrT⟩ Sob.Idx.zero

end UnforcedLeray.Short.PartI
