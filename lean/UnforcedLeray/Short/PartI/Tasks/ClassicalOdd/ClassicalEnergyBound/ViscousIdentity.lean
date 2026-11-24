import UnforcedLeray.Short.PartI.Sub.T02_3_10
import UnforcedLeray.Short.PartI.Tasks.TrainCutoffEnergyProof.ViscousIdentity

/-!
# Part I, task `PartI:T02/3/10`: `ebViscousIdentity` (leaf `EbViscousIdentity`)

Source of record: `the November 2 reference manuscript`, lines 276-282.
Target: `ebViscousIdentity : EtaCutoffFacts → CellIntegrableOfSupport → CellDerivZero →
EbSliceSmooth → EbViscousIdentity` (`Short/PartI/Sub/T02_3_10.lean`).

Route. This is the one-velocity analogue of `viscousIdentity`
(`Tasks/TrainCutoffEnergyProof/ViscousIdentity.lean`), with the difference `w = v - v'` replaced by
`v s`. For each component `f = v s · i` (`i = 0, 1`), the scalar identity `vi_scalar` gives
`∫ φ f Δf = -∫ φ |∇f|² - ∫ φ' f ∂_η f`. Smoothness comes from `EbSliceSmooth`, `q`-periodicity from
`IsClassicalOn`, and the cutoff facts from `EtaCutoffFacts`. Summing over `i` gives
`ebViscous = ebViscousRhs`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.PartI

open UnforcedLeray.Cyl (Plane partialQ partialEta)
open UnforcedLeray.Train (Vec)

/-- **Leaf `EbViscousIdentity`**: `T_visc = -2νD_R - 2ν ∫ φ' ⟨v, ∂_η v⟩`, from the cell integration
by parts of each component of `v s`. -/
theorem ebViscousIdentity : EtaCutoffFacts → CellIntegrableOfSupport → CellDerivZero →
    EbSliceSmooth → EbViscousIdentity := by
  intro hη hI hZ hS ν c T v p hc hcl R hR s hs
  obtain ⟨_C₀, -, hcut⟩ := hη
  obtain ⟨hsm, -, -, hzero, hder⟩ := hcut R hR
  have hR0 : 0 < R := by linarith
  have hdzero : ∀ η : ℝ, 2 * R ≤ |η| → deriv (etaCutoff R) η = 0 := by
    intro η hη'
    have h := hder η
    rw [hzero η hη', Real.sqrt_zero, mul_zero] at h
    exact abs_nonpos_iff.mp h
  -- smoothness and periodicity of `v s` and of its components
  have hsv : ContDiff ℝ ∞ (v s) := (hS ν c T v p hcl s hs).1
  have hvd : Differentiable ℝ (v s) := hsv.differentiable (by simp)
  have hp : Cyl.IsPeriodic c (v s) := hcl.periodic_v s hs
  have hcomp : ∀ i : Fin 2, ContDiff ℝ ∞ (fun z : Plane => v s z i) := fun i =>
    (EuclideanSpace.proj i : Vec →L[ℝ] ℝ).contDiff.comp hsv
  have hpi : ∀ i : Fin 2, Cyl.IsPeriodic c (fun z : Plane => v s z i) := fun i z => by
    show v s (z.1 + c, z.2) i = v s z i
    rw [hp z]
  -- the scalar identities for the two components
  obtain ⟨hA0, hB0, hC0, hE0⟩ := vi_scalar hc hR0 hI hZ hsm hzero hdzero
    (fun z : Plane => v s z 0) (hcomp 0) (hpi 0)
  obtain ⟨hA1, hB1, hC1, hE1⟩ := vi_scalar hc hR0 hI hZ hsm hzero hdzero
    (fun z : Plane => v s z 1) (hcomp 1) (hpi 1)
  -- pointwise expansions of the inner products
  have hinnerL : ∀ z : Plane,
      inner ℝ (v s z) (Train.vecLaplacian (v s) z) =
        v s z 0 * (partialQ (partialQ (fun w : Plane => v s w 0)) z +
            partialEta (partialEta (fun w : Plane => v s w 0)) z) +
        v s z 1 * (partialQ (partialQ (fun w : Plane => v s w 1)) z +
            partialEta (partialEta (fun w : Plane => v s w 1)) z) := by
    intro z
    simp only [PiLp.inner_apply, Fin.sum_univ_two, RCLike.inner_apply, conj_trivial,
      Train.vecLaplacian, Train.lapS, Train.toVec_zero, Train.toVec_one]
    ring
  have hinnerE : ∀ z : Plane,
      inner ℝ (v s z) (Cyl.partialEta (v s) z) =
        v s z 0 * partialEta (fun w : Plane => v s w 0) z +
        v s z 1 * partialEta (fun w : Plane => v s w 1) z := by
    intro z
    simp only [PiLp.inner_apply, Fin.sum_univ_two, RCLike.inner_apply, conj_trivial,
      vi_partialEta_comp hvd 0 z, vi_partialEta_comp hvd 1 z]
    ring
  have hgradP : ∀ z : Plane,
      etaCutoff R z.2 * gradNormSq (v s) z =
        etaCutoff R z.2 * (partialQ (fun w : Plane => v s w 0) z ^ 2 +
            partialEta (fun w : Plane => v s w 0) z ^ 2) +
        etaCutoff R z.2 * (partialQ (fun w : Plane => v s w 1) z ^ 2 +
            partialEta (fun w : Plane => v s w 1) z ^ 2) := by
    intro z
    unfold gradNormSq
    ring
  have hV : ∀ z : Plane,
      etaCutoff R z.2 * inner ℝ (v s z) (Train.vecLaplacian (v s) z) =
        etaCutoff R z.2 * (v s z 0 * (partialQ (partialQ
            (fun w : Plane => v s w 0)) z + partialEta (partialEta
            (fun w : Plane => v s w 0)) z)) +
        etaCutoff R z.2 * (v s z 1 * (partialQ (partialQ
            (fun w : Plane => v s w 1)) z + partialEta (partialEta
            (fun w : Plane => v s w 1)) z)) := by
    intro z
    rw [hinnerL z]
    ring
  have hJ : ∀ z : Plane,
      deriv (etaCutoff R) z.2 * inner ℝ (v s z) (Cyl.partialEta (v s) z) =
        deriv (etaCutoff R) z.2 * (v s z 0 *
            partialEta (fun w : Plane => v s w 0) z) +
        deriv (etaCutoff R) z.2 * (v s z 1 *
            partialEta (fun w : Plane => v s w 1) z) := by
    intro z
    rw [hinnerE z]
    ring
  -- assemble the two components
  unfold ebViscous ebViscousRhs ebDissipation
  simp only [hV, hgradP, hJ]
  rw [integral_add hA0 hA1, integral_add hB0 hB1, integral_add hC0 hC1]
  linear_combination (2 * ν) * hE0 + (2 * ν) * hE1

end UnforcedLeray.Short.PartI
