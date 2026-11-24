import UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution.FluxCLM

/-!
# Actual B0610 source map for the real train flux

This composes the concrete bounded flux map with the CCW flux rotation and B0610's actual curl
source. The rotation is explicit because `curlSource` has the opposite sign from the usual curl.
-/

set_option autoImplicit false
set_option maxHeartbeats 500000

noncomputable section

namespace UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution

open MeasureTheory
open UnforcedLeray.B0579
open UnforcedLeray.Train (Vec)

/-- The continuous linear realization of B0610's scalar curl source on vector `X_m` data. -/
def curlSourceCLM (c m : ℝ) : (Fin 2 → X c m) →L[ℝ] UnforcedLeray.B0579.Hneg c m :=
  (UnforcedLeray.B0579.derivSourceCLM c m 1).comp (ContinuousLinearMap.proj 0) -
    (UnforcedLeray.B0579.derivSourceCLM c m 0).comp (ContinuousLinearMap.proj 1)

/-- The flux rotation `J(Fq,Fη)=(-Fη,Fq)` used to turn B0610's `curlSource` into `-div F`. -/
def rotatePhysicalFluxCLM (c m : ℝ) : (Fin 2 → X c m) →L[ℝ] (Fin 2 → X c m) :=
  ContinuousLinearMap.pi fun i =>
    if i = 0 then -(ContinuousLinearMap.proj (1 : Fin 2))
    else ContinuousLinearMap.proj (0 : Fin 2)

/-- The actual B0610 source map built from the real Biot--Savart physical flux. -/
def physicalSourceKernelCLM {c m : ℝ} [Fact (0 < c)] (hm : 1 ≤ m)
    (v : Plane → Vec) (E : Plane → ℝ) (hv : Continuous v) (hE : Continuous E)
    {Cv CE : ℝ} (hCv : 0 ≤ Cv) (hCE : 0 ≤ CE)
    (hvBound : ∀ x i, |v x i| ≤ Cv)
    (hEBound : ∀ x ∈ cell c, |bracket x ^ m * E x| ≤ CE) :
    zeroCirculationSubmodule (c := c) (m := m) (by linarith : 1 / 2 < m) →L[ℝ]
      UnforcedLeray.B0579.Hneg c m :=
  (curlSourceCLM c m).comp ((rotatePhysicalFluxCLM c m).comp
    (physicalFluxKernelCLM hm v E hv hE hCv hCE hvBound hEBound))

/-- The CLM agrees exactly with the concrete B0610 definition on every zero-circulation input. -/
theorem physicalSourceKernelCLM_apply {c m : ℝ} [Fact (0 < c)] (hm : 1 ≤ m)
    (v : Plane → Vec) (E : Plane → ℝ) (hv : Continuous v) (hE : Continuous E)
    {Cv CE : ℝ} (hCv : 0 ≤ Cv) (hCE : 0 ≤ CE)
    (hvBound : ∀ x i, |v x i| ≤ Cv)
    (hEBound : ∀ x ∈ cell c, |bracket x ^ m * E x| ≤ CE)
    (w : zeroCirculationSubmodule (c := c) (m := m) (by linarith : 1 / 2 < m)) :
    physicalSourceKernelCLM hm v E hv hE hCv hCE hvBound hEBound w =
      UnforcedLeray.B0610.curlSource c m
        (rotatedPhysicalFluxX hm v E w.1
          ((mem_zeroCirculationSubmodule_iff (by linarith : 1 / 2 < m) w.1).1 w.2)
          hCv hCE hv hE hvBound hEBound) := by
  simp [physicalSourceKernelCLM, curlSourceCLM, rotatePhysicalFluxCLM,
    ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.proj_apply, UnforcedLeray.B0610.curlSource,
    physicalFluxKernelCLM,
    physicalFluxComponentCLM_apply, rotatedPhysicalFluxX]

/-- The actual train source is this bounded-source construction with B0238's `Vc` and `Ec`. -/
theorem trainPhysicalSource_eq_physicalSourceKernelCLM {ν c m : ℝ} [Fact (0 < c)]
    (tr : UnforcedLeray.B0140.TrainSol ν c) {s : ℝ} (hs : 0 ≤ s)
    (hm : 1 ≤ m) (w : zeroCirculationSubmodule (c := c) (m := m)
      (by linarith : 1 / 2 < m))
    {Cv CE : ℝ} (hCv : 0 ≤ Cv) (hCE : 0 ≤ CE)
    (hvBound : ∀ x i, |UnforcedLeray.B0238.Vc tr s x i| ≤ Cv)
    (hEBound : ∀ x ∈ cell c,
      |bracket x ^ m * UnforcedLeray.B0238.Ec tr s x| ≤ CE) :
    physicalSourceKernelCLM hm (UnforcedLeray.B0238.Vc tr s)
      (UnforcedLeray.B0238.Ec tr s)
      (UnforcedLeray.B0238.contDiff_Vc tr hs).continuous
      (by
        unfold UnforcedLeray.B0238.Ec
        exact UnforcedLeray.B0238.continuous_curl
          ((UnforcedLeray.B0238.contDiff_Vc tr hs).of_le (by norm_num)))
      hCv hCE hvBound hEBound w =
    trainPhysicalSource tr hs hm w.1
      ((mem_zeroCirculationSubmodule_iff (by linarith : 1 / 2 < m) w.1).1 w.2)
      hCv hCE hvBound hEBound := by
  rw [physicalSourceKernelCLM_apply]
  rfl

/-- B0610's source preserves zero circulation for the actual rotated flux. -/
theorem hasZeroCirculation_physicalSourceKernelCLM {c m : ℝ} [Fact (0 < c)] (hm : 1 ≤ m)
    (v : Plane → Vec) (E : Plane → ℝ) (hv : Continuous v) (hE : Continuous E)
    {Cv CE : ℝ} (hCv : 0 ≤ Cv) (hCE : 0 ≤ CE)
    (hvBound : ∀ x i, |v x i| ≤ Cv)
    (hEBound : ∀ x ∈ cell c, |bracket x ^ m * E x| ≤ CE)
    (w : zeroCirculationSubmodule (c := c) (m := m) (by linarith : 1 / 2 < m)) :
    UnforcedLeray.B0610.HasZeroCirculation c m (by linarith : 1 / 2 < m)
      (physicalSourceKernelCLM hm v E hv hE hCv hCE hvBound hEBound w) := by
  rw [physicalSourceKernelCLM_apply]
  exact UnforcedLeray.B0610.hasZeroCirculation_curlSource (by linarith : 1 / 2 < m) _

#print axioms physicalSourceKernelCLM_apply
#print axioms trainPhysicalSource_eq_physicalSourceKernelCLM
#print axioms hasZeroCirculation_physicalSourceKernelCLM

end UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution
