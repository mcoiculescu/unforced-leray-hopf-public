import UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution.FluxBound

/-!
# Bounded linear map for the actual physical train flux

For fixed actual coefficients `v,E` satisfying their centered-cell bounds, this module turns the
physical flux decomposition into a continuous linear map on the real zero-circulation space. The
constant is explicit and is only intended for fixed-cylinder existence estimates.
-/

set_option autoImplicit false
set_option maxHeartbeats 500000

noncomputable section

namespace UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution

open MeasureTheory
open UnforcedLeray.B0579
open UnforcedLeray.B0581 (cellVol)
open UnforcedLeray.Train (Vec)

/-- One component of the actual physical flux as a bounded map on the circulation kernel. -/
def physicalFluxComponentCLM {c m : ℝ} [Fact (0 < c)] (hm : 1 ≤ m)
    (v : Plane → Vec) (E : Plane → ℝ) (hv : Continuous v) (hE : Continuous E)
    {Cv CE : ℝ} (hCv : 0 ≤ Cv) (hCE : 0 ≤ CE)
    (hvBound : ∀ x i, |v x i| ≤ Cv)
    (hEBound : ∀ x ∈ cell c, |bracket x ^ m * E x| ≤ CE) (i : Fin 2) :
    zeroCirculationSubmodule (c := c) (m := m) (by linarith : 1 / 2 < m) →L[ℝ] X c m := by
  let Z := zeroCirculationSubmodule (c := c) (m := m) (by linarith : 1 / 2 < m)
  exact
    (mulRCell c m (fun x => v x i) (by fun_prop) hCv (fun x hx => hvBound x i)).comp
        Z.subtypeL +
      (weightedCellMultiplier E hE hCE hEBound).comp
        (((trainVecComponentCLM i).compLpL 2 (cellVol c)).comp
          (realBiotSavartKernelCLM hm))

/-- Applying the component CLM gives the actual flux column from `Flux.lean`. -/
theorem physicalFluxComponentCLM_apply {c m : ℝ} [Fact (0 < c)] (hm : 1 ≤ m)
    (v : Plane → Vec) (E : Plane → ℝ) (hv : Continuous v) (hE : Continuous E)
    {Cv CE : ℝ} (hCv : 0 ≤ Cv) (hCE : 0 ≤ CE)
    (hvBound : ∀ x i, |v x i| ≤ Cv)
    (hEBound : ∀ x ∈ cell c, |bracket x ^ m * E x| ≤ CE)
    (w : zeroCirculationSubmodule (c := c) (m := m) (by linarith : 1 / 2 < m))
    (i : Fin 2) :
    physicalFluxComponentCLM hm v E hv hE hCv hCE hvBound hEBound i w =
      physicalFluxX hm v E w.1
        ((mem_zeroCirculationSubmodule_iff (by linarith : 1 / 2 < m) w.1).1 w.2)
        hCv hCE hv hE hvBound hEBound i := by
  rw [physicalFluxComponentCLM, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply]
  exact (physicalFluxX_component_decomp hm v E w.1
    ((mem_zeroCirculationSubmodule_iff (by linarith : 1 / 2 < m) w.1).1 w.2)
    hCv hCE hv hE hvBound hEBound i).symm

/-- The component map is bounded by the explicit velocity plus weighted-curl cost. -/
theorem norm_physicalFluxComponentCLM_le {c m : ℝ} [Fact (0 < c)] (hm : 1 ≤ m)
    (v : Plane → Vec) (E : Plane → ℝ) (hv : Continuous v) (hE : Continuous E)
    {Cv CE : ℝ} (hCv : 0 ≤ Cv) (hCE : 0 ≤ CE)
    (hvBound : ∀ x i, |v x i| ≤ Cv)
    (hEBound : ∀ x ∈ cell c, |bracket x ^ m * E x| ≤ CE) (i : Fin 2) :
    ‖physicalFluxComponentCLM hm v E hv hE hCv hCE hvBound hEBound i‖ ≤
      Cv + CE * (c / (2 * Real.pi) + 2) := by
  let M := Cv + CE * (c / (2 * Real.pi) + 2)
  have hc : 0 < c := Fact.out
  have hpi : 0 < Real.pi := Real.pi_pos
  have hM : 0 ≤ M := by dsimp [M]; positivity
  refine ContinuousLinearMap.opNorm_le_bound _ hM fun w => ?_
  have hcirc := (mem_zeroCirculationSubmodule_iff
    (by linarith : 1 / 2 < m) w.1).1 w.2
  have h := norm_physicalFluxX_component_le hm v E w.1 hcirc hCv hCE hv hE
    hvBound hEBound i
  rw [physicalFluxComponentCLM_apply hm v E hv hE hCv hCE hvBound hEBound w i]
  simpa [M] using h

/-- The two-component actual flux is a continuous linear map on the real circulation kernel. -/
def physicalFluxKernelCLM {c m : ℝ} [Fact (0 < c)] (hm : 1 ≤ m)
    (v : Plane → Vec) (E : Plane → ℝ) (hv : Continuous v) (hE : Continuous E)
    {Cv CE : ℝ} (hCv : 0 ≤ Cv) (hCE : 0 ≤ CE)
    (hvBound : ∀ x i, |v x i| ≤ Cv)
    (hEBound : ∀ x ∈ cell c, |bracket x ^ m * E x| ≤ CE) :
    zeroCirculationSubmodule (c := c) (m := m) (by linarith : 1 / 2 < m) →L[ℝ]
      (Fin 2 → X c m) :=
  ContinuousLinearMap.pi fun i =>
    physicalFluxComponentCLM hm v E hv hE hCv hCE hvBound hEBound i

/-- The physical two-component flux CLM has the same explicit fixed-cylinder bound. -/
theorem norm_physicalFluxKernelCLM_le {c m : ℝ} [Fact (0 < c)] (hm : 1 ≤ m)
    (v : Plane → Vec) (E : Plane → ℝ) (hv : Continuous v) (hE : Continuous E)
    {Cv CE : ℝ} (hCv : 0 ≤ Cv) (hCE : 0 ≤ CE)
    (hvBound : ∀ x i, |v x i| ≤ Cv)
    (hEBound : ∀ x ∈ cell c, |bracket x ^ m * E x| ≤ CE) :
    ‖physicalFluxKernelCLM hm v E hv hE hCv hCE hvBound hEBound‖ ≤
      Cv + CE * (c / (2 * Real.pi) + 2) := by
  apply ContinuousLinearMap.norm_pi_le_of_le
  · intro i
    exact norm_physicalFluxComponentCLM_le hm v E hv hE hCv hCE hvBound hEBound i
  · have hc : 0 < c := Fact.out
    have hpi : 0 < Real.pi := Real.pi_pos
    positivity

/-- On a zero-circulation input the bounded map is exactly the pre-existing physical flux linear
map, so this estimate concerns the same source used in B0610. -/
theorem physicalFluxKernelCLM_eq_linearMap_apply {c m : ℝ} [Fact (0 < c)] (hm : 1 ≤ m)
    (v : Plane → Vec) (E : Plane → ℝ) (hv : Continuous v) (hE : Continuous E)
    {Cv CE : ℝ} (hCv : 0 ≤ Cv) (hCE : 0 ≤ CE)
    (hvBound : ∀ x i, |v x i| ≤ Cv)
    (hEBound : ∀ x ∈ cell c, |bracket x ^ m * E x| ≤ CE)
    (w : zeroCirculationSubmodule (c := c) (m := m) (by linarith : 1 / 2 < m)) :
    physicalFluxKernelCLM hm v E hv hE hCv hCE hvBound hEBound w =
      physicalFluxKernelLinearMap hm v E hv hE hCv hCE hvBound hEBound w := by
  funext i
  change physicalFluxComponentCLM hm v E hv hE hCv hCE hvBound hEBound i w =
    (physicalFluxKernelLinearMap hm v E hv hE hCv hCE hvBound hEBound w) i
  rw [physicalFluxComponentCLM_apply hm v E hv hE hCv hCE hvBound hEBound w i]
  rfl

#print axioms physicalFluxComponentCLM_apply
#print axioms norm_physicalFluxComponentCLM_le
#print axioms norm_physicalFluxKernelCLM_le
#print axioms physicalFluxKernelCLM_eq_linearMap_apply

end UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution
