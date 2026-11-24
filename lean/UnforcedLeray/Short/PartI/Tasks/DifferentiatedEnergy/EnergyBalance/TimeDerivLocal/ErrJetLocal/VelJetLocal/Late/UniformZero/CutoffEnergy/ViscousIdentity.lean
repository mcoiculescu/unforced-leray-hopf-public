import UnforcedLeray.Short.PartI.Sub.PartI_T08_4_1_1_1_2_2_1_3_2

/-!
# Part I, task `PartI:T08/4/1/1/1/2/2/1/3/2/2`: leaf `VelViscousIdentity`

Source of record: `the November 2 reference manuscript`, lines 273-288.
Target: `velViscousIdentity_proof : VelViscousIdentity` (`Short/PartI/Sub/PartI_T08_4_1_1_1_2_2_1_3_2.lean`).

Single-train analogue (`v' = 0`) of `Tasks/TrainCutoffEnergyProof/ViscousIdentity.lean`.
For each component `f = v_i` the scalar cell integration by parts `vi_scalar` (imported from the
model module, with `CellIntegrableOfSupport` and `CellDerivZero` from `CellToolkit`) gives
`∫_cell φ f Δf = -∫_cell φ |∇f|² - ∫_cell φ' f ∂_η f`. Summing over the two components gives
`velCutoffViscous = velViscousRhs`. The cutoff facts come from `etaCutoffFacts`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.PartI

open UnforcedLeray.Cyl (Plane partialQ partialEta)
open UnforcedLeray.Train (Vec)

/-- **Leaf `VelViscousIdentity`** (`velCutoffViscous = velViscousRhs` for `s ≥ 0`). -/
theorem velViscousIdentity_proof : UnforcedLeray.Short.PartI.VelViscousIdentity := by
  intro ν c hν hc tr R hR s hs
  have hR0 : 0 < R := by linarith
  -- the cutoff facts at radius `R`
  have hcutF : EtaCutoffFacts := etaCutoffFacts
  unfold EtaCutoffFacts at hcutF
  obtain ⟨_C₀, -, hcut⟩ := hcutF
  obtain ⟨hsm, -, -, hzero, hder⟩ := hcut R hR
  have hdzero : ∀ η : ℝ, 2 * R ≤ |η| → deriv (etaCutoff R) η = 0 := by
    intro η hη'
    have h := hder η
    rw [hzero η hη', Real.sqrt_zero, mul_zero] at h
    exact abs_nonpos_iff.mp h
  -- smoothness and periodicity of `v = tr.v s` and of its components
  have hw : ContDiff ℝ ∞ (tr.v s) := (trainSliceSmooth ν c tr s hs).1
  have hwd : Differentiable ℝ (tr.v s) := hw.differentiable (by simp)
  have hwp : Cyl.IsPeriodic c (tr.v s) := tr.isTrain.periodic_v s hs
  have hcomp : ∀ i : Fin 2, ContDiff ℝ ∞ (fun z : Plane => tr.v s z i) := fun i =>
    (EuclideanSpace.proj i : Vec →L[ℝ] ℝ).contDiff.comp hw
  have hwpi : ∀ i : Fin 2, Cyl.IsPeriodic c (fun z : Plane => tr.v s z i) :=
    fun i z => by
      show tr.v s (z.1 + c, z.2) i = tr.v s z i
      rw [hwp z]
  -- the scalar identities for the two components
  obtain ⟨hA0, hB0, hC0, hE0⟩ := vi_scalar hc hR0 cellIntegrable_of_support
    cellDerivZero_of_periodic hsm hzero hdzero
    (fun z : Plane => tr.v s z 0) (hcomp 0) (hwpi 0)
  obtain ⟨hA1, hB1, hC1, hE1⟩ := vi_scalar hc hR0 cellIntegrable_of_support
    cellDerivZero_of_periodic hsm hzero hdzero
    (fun z : Plane => tr.v s z 1) (hcomp 1) (hwpi 1)
  -- pointwise expansions of the inner products
  have hinnerL : ∀ z : Plane,
      inner ℝ (tr.v s z) (Train.vecLaplacian (tr.v s) z) =
        tr.v s z 0 * (partialQ (partialQ (fun w : Plane => tr.v s w 0)) z +
            partialEta (partialEta (fun w : Plane => tr.v s w 0)) z) +
        tr.v s z 1 * (partialQ (partialQ (fun w : Plane => tr.v s w 1)) z +
            partialEta (partialEta (fun w : Plane => tr.v s w 1)) z) := by
    intro z
    simp only [PiLp.inner_apply, Fin.sum_univ_two, RCLike.inner_apply, conj_trivial,
      Train.vecLaplacian, Train.lapS, Train.toVec_zero, Train.toVec_one]
    ring
  have hinnerE : ∀ z : Plane,
      inner ℝ (tr.v s z) (Cyl.partialEta (tr.v s) z) =
        tr.v s z 0 * partialEta (fun w : Plane => tr.v s w 0) z +
        tr.v s z 1 * partialEta (fun w : Plane => tr.v s w 1) z := by
    intro z
    simp only [PiLp.inner_apply, Fin.sum_univ_two, RCLike.inner_apply, conj_trivial,
      vi_partialEta_comp hwd 0 z, vi_partialEta_comp hwd 1 z]
    ring
  have hgradP : ∀ z : Plane,
      etaCutoff R z.2 * gradNormSq (tr.v s) z =
        etaCutoff R z.2 * (partialQ (fun w : Plane => tr.v s w 0) z ^ 2 +
            partialEta (fun w : Plane => tr.v s w 0) z ^ 2) +
        etaCutoff R z.2 * (partialQ (fun w : Plane => tr.v s w 1) z ^ 2 +
            partialEta (fun w : Plane => tr.v s w 1) z ^ 2) := by
    intro z
    unfold gradNormSq
    ring
  have hV : ∀ z : Plane,
      etaCutoff R z.2 * inner ℝ (tr.v s z) (Train.vecLaplacian (tr.v s) z) =
        etaCutoff R z.2 * (tr.v s z 0 * (partialQ (partialQ
            (fun w : Plane => tr.v s w 0)) z + partialEta (partialEta
            (fun w : Plane => tr.v s w 0)) z)) +
        etaCutoff R z.2 * (tr.v s z 1 * (partialQ (partialQ
            (fun w : Plane => tr.v s w 1)) z + partialEta (partialEta
            (fun w : Plane => tr.v s w 1)) z)) := by
    intro z
    rw [hinnerL z]
    ring
  have hJ : ∀ z : Plane,
      deriv (etaCutoff R) z.2 * inner ℝ (tr.v s z) (Cyl.partialEta (tr.v s) z) =
        deriv (etaCutoff R) z.2 * (tr.v s z 0 *
            partialEta (fun w : Plane => tr.v s w 0) z) +
        deriv (etaCutoff R) z.2 * (tr.v s z 1 *
            partialEta (fun w : Plane => tr.v s w 1) z) := by
    intro z
    rw [hinnerE z]
    ring
  -- assemble the two components
  unfold velCutoffViscous velViscousRhs velCutoffDissipation
  simp only [hV, hgradP, hJ]
  rw [integral_add hA0 hA1, integral_add hB0 hB1, integral_add hC0 hC1]
  linear_combination (2 * ν) * hE0 + (2 * ν) * hE1

end UnforcedLeray.Short.PartI
