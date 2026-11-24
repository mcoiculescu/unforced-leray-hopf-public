import UnforcedLeray.Short.PartI.Tasks.LocalClassicalBounded.HkPersistence.ProductRule.HeatDivDeriv.Defs
import UnforcedLeray.Lib.HeatCylinder.HeatVecL2NormalizedCenteredInverse

/-!
# Part I, task `PartI:T02/1/2/3/5`: leaves B and C (weak-derivative bridges)

Source of record: `the November 2 reference manuscript`, lines 261-288.

* `bdpHddTensorBridge_proof : BdpHddTensorBridge`: a weak `∂_j`-derivative pair of tensor `H³`
  elements has `W.deriv (∂_j) G = W.value G'` (uniqueness of weak derivatives, as in
  `weakDerivCell_proof`, `Short/PartI/Sub/T02_1_2_2/WeakDerivCell.lean`).
* `bdpHddVectorBridge_proof : BdpHddVectorBridge`: equal normalized components give a weak
  derivative pair (the centered-to-normalized transport has the left inverse
  `normalizedVecToCenteredLinear`).

No `sorry`, `admit`, `axiom` or `native_decide`.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff ENNReal

namespace UnforcedLeray.Short.PartI

open UnforcedLeray
open UnforcedLeray.Train (Vec toVec)
open UnforcedLeray.Cyl (Plane cellμ)
open UnforcedLeray.TrainB
open UnforcedLeray.HeatCylinder

theorem bdpHddTensorBridge_proof : BdpHddTensorBridge := by
  intro c _hc j G G' h
  have hw := Sob.W.hasWeakDeriv G (Sob.Idx.cons j (Sob.Idx.zero : Sob.Idx 2 2))
  rw [Sob.TestDomain.word_cons, Sob.TestDomain.word_zero] at hw
  have hxloc : LocallyIntegrable (Cyl.H.val G' : Plane → TensorVal) (Sob.cylinder c).μ :=
    Sob.locallyIntegrable_of_memLp (Lp.memLp _)
  have hdloc : LocallyIntegrable
      (Sob.W.deriv (Sob.cylinder c) (Cyl.ρwW c ^ (0 : ℝ)) ℝ TensorVal 3 2
        (Sob.Idx.cons j (Sob.Idx.zero : Sob.Idx 2 2)) G : Plane → TensorVal)
      (Sob.cylinder c).μ :=
    Sob.locallyIntegrable_of_memLp (Lp.memLp _)
  have hae := h.ae_unique hw hxloc hdloc
  apply Lp.ext
  exact ((Sob.ae_eq_wμ_iff _ _).mpr hae).symm

private theorem bdpHdd_centeredToNormalized_injective {c : ℝ} (hc : 0 < c) :
    Function.Injective (centeredVecToNormalizedCLM hc) := by
  intro x y hxy
  have hx := normalizedVecToCenteredLinear_centeredVecToNormalizedLinear hc x
  have hy := normalizedVecToCenteredLinear_centeredVecToNormalizedLinear hc y
  have hxy' : centeredVecToNormalizedLinear hc x = centeredVecToNormalizedLinear hc y := hxy
  rw [← hx, ← hy, hxy']

theorem bdpHddVectorBridge_proof : BdpHddVectorBridge := by
  intro c hc j Y Y' h
  have hcls : centeredVecH3DerivativeClass (Sob.Idx.cons j (Sob.Idx.zero : Sob.Idx 2 2)) Y =
      centeredVecH3DerivativeClass (Sob.Idx.zero : Sob.Idx 2 3) Y' :=
    bdpHdd_centeredToNormalized_injective hc h
  have haeCell : (Sob.W.deriv (Sob.cylinder c) (Cyl.ρwW c ^ (0 : ℝ)) ℝ Vec 3 2
        (Sob.Idx.cons j (Sob.Idx.zero : Sob.Idx 2 2)) Y : Plane → Vec) =ᵐ[cellμ c]
      (Sob.W.deriv (Sob.cylinder c) (Cyl.ρwW c ^ (0 : ℝ)) ℝ Vec 3 2
        (Sob.Idx.zero : Sob.Idx 2 3) Y' : Plane → Vec) := by
    filter_upwards [centeredVecH3DerivativeClass_coe_ae
        (Sob.Idx.cons j (Sob.Idx.zero : Sob.Idx 2 2)) Y,
      centeredVecH3DerivativeClass_coe_ae (Sob.Idx.zero : Sob.Idx 2 3) Y'] with z h1 h2
    rw [← h1, ← h2, hcls]
  have haeW : (Sob.W.deriv (Sob.cylinder c) (Cyl.ρwW c ^ (0 : ℝ)) ℝ Vec 3 2
        (Sob.Idx.cons j (Sob.Idx.zero : Sob.Idx 2 2)) Y : Plane → Vec) =ᵐ[
        Sob.wμ (Sob.cylinder c).μ (Cyl.ρwW c ^ (0 : ℝ))]
      (Sob.W.deriv (Sob.cylinder c) (Cyl.ρwW c ^ (0 : ℝ)) ℝ Vec 3 2
        (Sob.Idx.zero : Sob.Idx 2 3) Y' : Plane → Vec) := by
    exact (congrArg (fun μ : Measure Plane =>
      (Sob.W.deriv (Sob.cylinder c) (Cyl.ρwW c ^ (0 : ℝ)) ℝ Vec 3 2
        (Sob.Idx.cons j (Sob.Idx.zero : Sob.Idx 2 2)) Y : Plane → Vec) =ᵐ[μ]
      (Sob.W.deriv (Sob.cylinder c) (Cyl.ρwW c ^ (0 : ℝ)) ℝ Vec 3 2
        (Sob.Idx.zero : Sob.Idx 2 3) Y' : Plane → Vec))
      (heatVecH3_measure_eq_cell_deriv c)).mpr haeCell
  have hae : (Sob.W.deriv (Sob.cylinder c) (Cyl.ρwW c ^ (0 : ℝ)) ℝ Vec 3 2
        (Sob.Idx.cons j (Sob.Idx.zero : Sob.Idx 2 2)) Y : Plane → Vec) =ᵐ[(Sob.cylinder c).μ]
      (Cyl.H.val Y' : Plane → Vec) :=
    (Sob.ae_eq_wμ_iff _ _).mp haeW
  have hw := Sob.W.hasWeakDeriv Y (Sob.Idx.cons j (Sob.Idx.zero : Sob.Idx 2 2))
  rw [Sob.TestDomain.word_cons, Sob.TestDomain.word_zero] at hw
  exact hw.congr_ae (Filter.EventuallyEq.refl _ _) hae

end UnforcedLeray.Short.PartI

#print axioms UnforcedLeray.Short.PartI.bdpHddTensorBridge_proof
#print axioms UnforcedLeray.Short.PartI.bdpHddVectorBridge_proof
