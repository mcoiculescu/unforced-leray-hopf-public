import UnforcedLeray.Analysis.SobolevGraph.Pairing
import UnforcedLeray.TestFunctions
import Mathlib.Topology.Algebra.Module.ClosedSubmodule
import Mathlib.Tactic.Linarith

/-!
# Closed weak-derivative graphs in vector-valued L²(R³)

For each coordinate direction, the graph is the intersection of kernels of
continuous test functionals. Membership is proved equivalent to the concrete
`HasWeakSpatialDerivative` of the target statement, including integrability of
all vector-valued pairings. Thus closure is about actual distributional
spatial derivatives of L² fields, not an abstract operator assumption.

The kernel-intersection design is adapted from the Sobolev-space construction
in `NonUniqueEuler/Defs/Infra/SobolevSpace.lean` (Apache-2.0), public commit
d81c3f456505f8a3e8211f2a9f63313d0599ed5a. The present domain and values are
Euclidean R³, with the explicit derivative predicate of this project.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter
open scoped Topology

namespace UnforcedLeray.SobolevGraph

abbrev SpatialTest := {φ : Space → ℝ // IsSpatialTest φ}

/-- Testing `∂ᵢf=g` against a scalar test and a constant vector gives a
continuous scalar functional on the pair `(f,g)` of actual L² classes. -/
def derivativeFunctional (i : Fin 3) (φ : SpatialTest) (v : Space) :
    (L2Space × L2Space) →L[ℝ] ℝ :=
  (pairing (spatialTestDerivative i φ.1) (φ.2.derivative i) v).comp
      (ContinuousLinearMap.fst ℝ L2Space L2Space) +
    (pairing φ.1 φ.2 v).comp (ContinuousLinearMap.snd ℝ L2Space L2Space)

theorem derivativeFunctional_apply (i : Fin 3) (φ : SpatialTest) (v : Space)
    (F G : L2Space) :
    derivativeFunctional i φ v (F, G) =
      inner ℝ v (∫ x : Space, spatialTestDerivative i φ.1 x • F x) +
      inner ℝ v (∫ x : Space, φ.1 x • G x) := by
  change pairing (spatialTestDerivative i φ.1) (φ.2.derivative i) v F +
    pairing φ.1 φ.2 v G = _
  rw [pairing_apply, pairing_apply]

/-- The weak derivative graph, realized as a linear subspace of L²×L². -/
def derivativeGraph (i : Fin 3) : Submodule ℝ (L2Space × L2Space) :=
  ⨅ (φ : SpatialTest) (v : Space),
    LinearMap.ker (derivativeFunctional i φ v : (L2Space × L2Space) →ₗ[ℝ] ℝ)

/-- Kernel intersection membership is exactly the concrete weak derivative,
with all Bochner integrals justified by the L² test-pairing construction. -/
theorem mem_derivativeGraph_iff (i : Fin 3) (F G : L2Space) :
    (F, G) ∈ derivativeGraph i ↔
      HasWeakSpatialDerivative i (F : SpatialField) (G : SpatialField) := by
  simp only [derivativeGraph, Submodule.mem_iInf, LinearMap.mem_ker,
    ContinuousLinearMap.coe_coe, derivativeFunctional_apply]
  constructor
  · intro h
    refine ⟨?_, ?_, ?_⟩
    · intro φ hφ
      exact pairing_integrable (spatialTestDerivative i φ) (hφ.derivative i) F
    · intro φ hφ
      exact pairing_integrable φ hφ G
    · intro φ hφ
      apply ext_inner_left ℝ
      intro v
      have hv := h ⟨φ, hφ⟩ v
      rw [inner_neg_right]
      exact eq_neg_of_add_eq_zero_left hv
  · intro h φ v
    rw [h.identity φ.1 φ.2, inner_neg_right]
    exact neg_add_cancel _

/-- Weak spatial differentiation has a closed graph on L²(R³;R³). -/
theorem isClosed_derivativeGraph (i : Fin 3) :
    IsClosed (derivativeGraph i : Set (L2Space × L2Space)) := by
  rw [derivativeGraph, Submodule.coe_iInf]
  apply isClosed_iInter
  intro φ
  rw [Submodule.coe_iInf]
  exact isClosed_iInter fun v => (derivativeFunctional i φ v).isClosed_ker

/-- The subset written directly in the target's integral-based language is closed. -/
theorem isClosed_setOf_hasWeakSpatialDerivative (i : Fin 3) :
    IsClosed {p : L2Space × L2Space |
      HasWeakSpatialDerivative i (p.1 : SpatialField) (p.2 : SpatialField)} := by
  have he : {p : L2Space × L2Space |
      HasWeakSpatialDerivative i (p.1 : SpatialField) (p.2 : SpatialField)} =
      (derivativeGraph i : Set (L2Space × L2Space)) := by
    ext p
    exact (mem_derivativeGraph_iff i p.1 p.2).symm
  rw [he]
  exact isClosed_derivativeGraph i

/-- Closure under simultaneous strong L² limits of a field and its derivative. -/
theorem hasWeakSpatialDerivative_of_tendsto {ι : Type*} {l : Filter ι} [l.NeBot]
    (i : Fin 3) {F G : ι → L2Space} {F₀ G₀ : L2Space}
    (h : ∀ j, HasWeakSpatialDerivative i (F j : SpatialField) (G j : SpatialField))
    (hF : Tendsto F l (𝓝 F₀)) (hG : Tendsto G l (𝓝 G₀)) :
    HasWeakSpatialDerivative i (F₀ : SpatialField) (G₀ : SpatialField) := by
  exact (mem_derivativeGraph_iff i F₀ G₀).mp
    ((isClosed_derivativeGraph i).mem_of_tendsto (hF.prodMk_nhds hG)
      (Eventually.of_forall fun j => (mem_derivativeGraph_iff i (F j) (G j)).mpr (h j)))

/-- The closed graph itself is a complete normed real vector space. -/
instance derivativeGraph_completeSpace (i : Fin 3) : CompleteSpace (derivativeGraph i) :=
  (isClosed_derivativeGraph i).completeSpace_coe

end UnforcedLeray.SobolevGraph
