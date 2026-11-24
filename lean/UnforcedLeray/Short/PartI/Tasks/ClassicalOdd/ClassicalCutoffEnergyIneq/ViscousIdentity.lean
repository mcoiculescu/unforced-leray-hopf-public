import UnforcedLeray.Short.PartI.Sub.T02_3_11
import UnforcedLeray.Short.PartI.Tasks.TrainCutoffEnergyProof.ViscousIdentity

/-!
# Part I, task `PartI:T02/3/11`: `ccViscousIdentity` (leaf `CcViscousIdentity`)

Source of record: `the November 2 reference manuscript`, lines 276-288.
Target: `ccViscousIdentity : EtaCutoffFacts → CellIntegrableOfSupport → CellDerivZero →
CcSliceSmooth → CcViscousIdentity` (`Short/PartI/Sub/T02_3_11.lean`, the Prop `CcViscousIdentity`).

Route. This is the classical analogue of `viscousIdentity`
(`Tasks/TrainCutoffEnergyProof/ViscousIdentity.lean`), with the train difference `diffV tr tr' s`
replaced by `ccDiffV v v' s`. Fix `s ∈ [0, T]`, `R ≥ 1`, `φ = etaCutoff R`, and let
`w = v s - v' s`. For each component `f = w_i` the scalar cell identity `vi_scalar` (imported) gives
`∫_cell φ f Δf = -∫_cell φ |∇f|² - ∫_cell φ' f ∂_η f`. Summing over the two components, with the
common factor `2ν`, gives `ccViscous = ccViscousRhs`.

Hypotheses are used as follows. `EtaCutoffFacts` gives smoothness of `etaCutoff R`, its support
and the derivative vanishing for `|η| ≥ 2R`. `CellIntegrableOfSupport` and `CellDerivZero` are the
toolkit facts behind `vi_scalar`. `CcSliceSmooth` gives `C^∞` of `v s` and `v' s` on `[0, T]`, and
`IsClassicalOn.periodic_v` gives `c`-periodicity in `q`, so the difference is `C^∞` and periodic.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.PartI

open UnforcedLeray.Cyl (Plane partialQ partialEta)
open UnforcedLeray.Train (Vec)

/-- **Leaf `CcViscousIdentity`** (`T_visc = -2νD - 2ν ∫ φ' ⟨w, ∂_η w⟩` for the difference
`w = v s - v' s` of two classical solutions), from the cell integration by parts of each component
of `w`. -/
theorem ccViscousIdentity (hη : EtaCutoffFacts) (hI : CellIntegrableOfSupport) (hZ : CellDerivZero)
    (hS : CcSliceSmooth) : CcViscousIdentity := by
  intro ν c T M v v' p p' h R hR s hs
  obtain ⟨_C₀, -, hcut⟩ := hη
  obtain ⟨hsm, -, -, hzero, hder⟩ := hcut R hR
  have hc : 0 < c := by linarith [h.c_ge]
  have hR0 : 0 < R := by linarith
  have hdzero : ∀ η : ℝ, 2 * R ≤ |η| → deriv (etaCutoff R) η = 0 := by
    intro η hη'
    have h0 := hder η
    rw [hzero η hη', Real.sqrt_zero, mul_zero] at h0
    exact abs_nonpos_iff.mp h0
  -- smoothness and periodicity of `w = v s - v' s` and of its components
  have hsv : ContDiff ℝ ∞ (v s) := (hS ν c T v p h.cl s hs).1
  have hsv' : ContDiff ℝ ∞ (v' s) := (hS ν c T v' p' h.cl' s hs).1
  have hw : ContDiff ℝ ∞ (ccDiffV v v' s) := hsv.sub hsv'
  have hwd : Differentiable ℝ (ccDiffV v v' s) := hw.differentiable (by simp)
  have hp : Cyl.IsPeriodic c (v s) := h.cl.periodic_v s hs
  have hp' : Cyl.IsPeriodic c (v' s) := h.cl'.periodic_v s hs
  have hwp : Cyl.IsPeriodic c (ccDiffV v v' s) := fun z => by
    simp only [ccDiffV, hp z, hp' z]
  have hcomp : ∀ i : Fin 2, ContDiff ℝ ∞ (fun z : Plane => ccDiffV v v' s z i) := fun i =>
    (EuclideanSpace.proj i : Vec →L[ℝ] ℝ).contDiff.comp hw
  have hwpi : ∀ i : Fin 2, Cyl.IsPeriodic c (fun z : Plane => ccDiffV v v' s z i) :=
    fun i z => by
      show ccDiffV v v' s (z.1 + c, z.2) i = ccDiffV v v' s z i
      rw [hwp z]
  -- the scalar identities for the two components
  obtain ⟨hA0, hB0, hC0, hE0⟩ := vi_scalar hc hR0 hI hZ hsm hzero hdzero
    (fun z : Plane => ccDiffV v v' s z 0) (hcomp 0) (hwpi 0)
  obtain ⟨hA1, hB1, hC1, hE1⟩ := vi_scalar hc hR0 hI hZ hsm hzero hdzero
    (fun z : Plane => ccDiffV v v' s z 1) (hcomp 1) (hwpi 1)
  -- pointwise expansions of the inner products
  have hinnerL : ∀ z : Plane,
      inner ℝ (ccDiffV v v' s z) (Train.vecLaplacian (ccDiffV v v' s) z) =
        ccDiffV v v' s z 0 * (partialQ (partialQ (fun w : Plane => ccDiffV v v' s w 0)) z +
            partialEta (partialEta (fun w : Plane => ccDiffV v v' s w 0)) z) +
        ccDiffV v v' s z 1 * (partialQ (partialQ (fun w : Plane => ccDiffV v v' s w 1)) z +
            partialEta (partialEta (fun w : Plane => ccDiffV v v' s w 1)) z) := by
    intro z
    simp only [PiLp.inner_apply, Fin.sum_univ_two, RCLike.inner_apply, conj_trivial,
      Train.vecLaplacian, Train.lapS, Train.toVec_zero, Train.toVec_one]
    ring
  have hinnerE : ∀ z : Plane,
      inner ℝ (ccDiffV v v' s z) (Cyl.partialEta (ccDiffV v v' s) z) =
        ccDiffV v v' s z 0 * partialEta (fun w : Plane => ccDiffV v v' s w 0) z +
        ccDiffV v v' s z 1 * partialEta (fun w : Plane => ccDiffV v v' s w 1) z := by
    intro z
    simp only [PiLp.inner_apply, Fin.sum_univ_two, RCLike.inner_apply, conj_trivial,
      vi_partialEta_comp hwd 0 z, vi_partialEta_comp hwd 1 z]
    ring
  have hgradP : ∀ z : Plane,
      etaCutoff R z.2 * gradNormSq (ccDiffV v v' s) z =
        etaCutoff R z.2 * (partialQ (fun w : Plane => ccDiffV v v' s w 0) z ^ 2 +
            partialEta (fun w : Plane => ccDiffV v v' s w 0) z ^ 2) +
        etaCutoff R z.2 * (partialQ (fun w : Plane => ccDiffV v v' s w 1) z ^ 2 +
            partialEta (fun w : Plane => ccDiffV v v' s w 1) z ^ 2) := by
    intro z
    unfold gradNormSq
    ring
  have hV : ∀ z : Plane,
      etaCutoff R z.2 * inner ℝ (ccDiffV v v' s z) (Train.vecLaplacian (ccDiffV v v' s) z) =
        etaCutoff R z.2 * (ccDiffV v v' s z 0 * (partialQ (partialQ
            (fun w : Plane => ccDiffV v v' s w 0)) z + partialEta (partialEta
            (fun w : Plane => ccDiffV v v' s w 0)) z)) +
        etaCutoff R z.2 * (ccDiffV v v' s z 1 * (partialQ (partialQ
            (fun w : Plane => ccDiffV v v' s w 1)) z + partialEta (partialEta
            (fun w : Plane => ccDiffV v v' s w 1)) z)) := by
    intro z
    rw [hinnerL z]
    ring
  have hJ : ∀ z : Plane,
      deriv (etaCutoff R) z.2 * inner ℝ (ccDiffV v v' s z) (Cyl.partialEta (ccDiffV v v' s) z) =
        deriv (etaCutoff R) z.2 * (ccDiffV v v' s z 0 *
            partialEta (fun w : Plane => ccDiffV v v' s w 0) z) +
        deriv (etaCutoff R) z.2 * (ccDiffV v v' s z 1 *
            partialEta (fun w : Plane => ccDiffV v v' s w 1) z) := by
    intro z
    rw [hinnerE z]
    ring
  -- assemble the two components
  unfold ccViscous ccViscousRhs ccDissipation
  simp only [hV, hgradP, hJ]
  rw [integral_add hA0 hA1, integral_add hB0 hB1, integral_add hC0 hC1]
  linear_combination (2 * ν) * hE0 + (2 * ν) * hE1

end UnforcedLeray.Short.PartI
