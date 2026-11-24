import UnforcedLeray.Analysis.SobolevGraph.Graph
import UnforcedLeray.Analysis.WeakDerivative
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.BigOperators.Fin

/-!
# The first-order weak Sobolev Hilbert graph on R³

The ambient Hilbert space contains an L² vector field and its three L²
coordinate derivatives, with the square-sum norm. The Sobolev graph is the
intersection of the three closed weak-derivative constraints. Its completeness
and Hilbert structure therefore concern genuine distributional derivatives
from the target statement, not assumed differential operators.

All four entries are vector-valued functions on Euclidean R³. The product
norm used temporarily in each derivative constraint is not used for the
Sobolev norm: the ambient space here is explicitly `PiLp 2`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory
open scoped Topology

namespace UnforcedLeray.SobolevGraph

/-- Slot zero stores the field and slots `i.succ` store its three derivatives. -/
abbrev H1Ambient := PiLp 2 (fun _ : Fin 4 => L2Space)

/-- The continuous projection to the field and one coordinate derivative. -/
def coordinatePair (i : Fin 3) : H1Ambient →L[ℝ] (L2Space × L2Space) :=
  (PiLp.proj 2 (fun _ : Fin 4 => L2Space) 0).prod
    (PiLp.proj 2 (fun _ : Fin 4 => L2Space) i.succ)

theorem coordinatePair_apply (i : Fin 3) (F : H1Ambient) :
    coordinatePair i F = (F.ofLp 0, F.ofLp i.succ) := rfl

/-- The actual first-order weak Sobolev graph as a linear subspace. -/
def H1Sub : Submodule ℝ H1Ambient :=
  ⨅ i : Fin 3, (derivativeGraph i).comap (coordinatePair i).toLinearMap

/-- Membership is precisely the three concrete distributional derivatives. -/
theorem mem_H1Sub_iff (F : H1Ambient) :
    F ∈ H1Sub ↔ ∀ i : Fin 3,
      HasWeakSpatialDerivative i (F.ofLp 0 : SpatialField) (F.ofLp i.succ : SpatialField) := by
  simp only [H1Sub, Submodule.mem_iInf, Submodule.mem_comap,
    ContinuousLinearMap.coe_coe, coordinatePair_apply, mem_derivativeGraph_iff]

/-- The first-order weak Sobolev graph is closed in its L² Hilbert product. -/
theorem isClosed_H1Sub : IsClosed (H1Sub : Set H1Ambient) := by
  rw [H1Sub, Submodule.coe_iInf]
  apply isClosed_iInter
  intro i
  change IsClosed ((coordinatePair i) ⁻¹' (derivativeGraph i : Set (L2Space × L2Space)))
  exact (isClosed_derivativeGraph i).preimage (coordinatePair i).continuous

/-- The Hilbert space of L² vector fields with three L² weak derivatives. -/
abbrev H1 := ↥H1Sub

instance H1_completeSpace : CompleteSpace H1 := isClosed_H1Sub.completeSpace_coe

/-- The real Hilbert structure is inherited from the square-sum L² product. -/
example : InnerProductSpace ℝ H1 := inferInstance

namespace H1

/-- The actual L² field component. -/
def value (F : H1) : L2Space := (F : H1Ambient).ofLp 0

/-- The actual L² derivative in coordinate direction i. -/
def derivative (F : H1) (i : Fin 3) : L2Space := (F : H1Ambient).ofLp i.succ

def valueCLM : H1 →L[ℝ] L2Space :=
  (PiLp.proj 2 (fun _ : Fin 4 => L2Space) 0).comp H1Sub.subtypeL

def derivativeCLM (i : Fin 3) : H1 →L[ℝ] L2Space :=
  (PiLp.proj 2 (fun _ : Fin 4 => L2Space) i.succ).comp H1Sub.subtypeL

@[simp] theorem valueCLM_apply (F : H1) : valueCLM F = F.value := rfl

@[simp] theorem derivativeCLM_apply (i : Fin 3) (F : H1) :
    derivativeCLM i F = F.derivative i := rfl

/-- These components satisfy the original integral-based weak derivative predicate. -/
theorem hasWeakDerivative (F : H1) (i : Fin 3) :
    HasWeakSpatialDerivative i (F.value : SpatialField) (F.derivative i : SpatialField) :=
  (mem_H1Sub_iff (F : H1Ambient)).mp F.property i

/-- The norm is exactly the standard first-order square-sum Sobolev graph norm. -/
theorem norm_sq (F : H1) :
    ‖F‖ ^ 2 = ‖F.value‖ ^ 2 + ∑ i : Fin 3, ‖F.derivative i‖ ^ 2 := by
  change ‖(F : H1Ambient)‖ ^ 2 = _
  rw [PiLp.norm_sq_eq_of_L2, Fin.sum_univ_succ]
  rfl

/-- The inner product sums the L² field and its three L² derivatives. -/
theorem inner_eq (F G : H1) :
    inner ℝ F G = inner ℝ F.value G.value +
      ∑ i : Fin 3, inner ℝ (F.derivative i) (G.derivative i) := by
  rw [Submodule.coe_inner, PiLp.inner_apply, Fin.sum_univ_succ]
  rfl

/-- The value determines the Sobolev element: weak derivative witnesses are
unique as L² equivalence classes. The graph adds no extra arbitrary data. -/
theorem value_injective : Function.Injective value := by
  intro F G hv
  have hd (i : Fin 3) : F.derivative i = G.derivative i := by
    have hG := G.hasWeakDerivative i
    rw [← hv] at hG
    apply Lp.ext
    exact (F.hasWeakDerivative i).ae_eq hG (Lp.memLp _) (Lp.memLp _)
  apply Subtype.ext
  apply (WithLp.ext_iff (p := 2)).mpr
  funext j
  refine Fin.cases ?_ (fun i => ?_) j
  · exact hv
  · exact hd i

@[ext] theorem ext {F G : H1} (h : F.value = G.value) : F = G :=
  value_injective h

theorem valueCLM_injective : Function.Injective valueCLM := value_injective

/-- Continuity in H¹ is exactly continuity of the field and its three L² derivatives. -/
theorem continuousOn_iff_components {α : Type*} [TopologicalSpace α]
    (f : α → H1) (s : Set α) :
    ContinuousOn f s ↔ ContinuousOn (fun x => (f x).value) s ∧
      ∀ i : Fin 3, ContinuousOn (fun x => (f x).derivative i) s := by
  constructor
  · intro hf
    exact ⟨valueCLM.continuous.comp_continuousOn hf,
      fun i => (derivativeCLM i).continuous.comp_continuousOn hf⟩
  · rintro ⟨hv, hd⟩
    apply (Topology.IsInducing.subtypeVal.continuousOn_iff).mpr
    apply ((PiLp.homeomorph 2 (fun _ : Fin 4 => L2Space)).isInducing.continuousOn_iff).mpr
    apply continuousOn_pi.mpr
    intro j
    refine Fin.cases ?_ (fun i => ?_) j
    · exact hv
    · exact hd i

end H1

/-- The canonical four-component Hilbert tuple built from L² classes. -/
def h1Tuple (F : L2Space) (G : Fin 3 → L2Space) : H1Ambient :=
  WithLp.toLp 2 (Fin.cons F G)

@[simp] theorem h1Tuple_zero (F : L2Space) (G : Fin 3 → L2Space) :
    (h1Tuple F G).ofLp 0 = F := rfl

@[simp] theorem h1Tuple_succ (F : L2Space) (G : Fin 3 → L2Space) (i : Fin 3) :
    (h1Tuple F G).ofLp i.succ = G i := rfl

/-- Genuine weak derivatives supply an element of the complete Hilbert graph. -/
def H1.ofWeakDerivatives (F : L2Space) (G : Fin 3 → L2Space)
    (h : ∀ i : Fin 3, HasWeakSpatialDerivative i (F : SpatialField) (G i : SpatialField)) : H1 :=
  ⟨h1Tuple F G, (mem_H1Sub_iff (h1Tuple F G)).mpr h⟩

@[simp] theorem H1.value_ofWeakDerivatives (F : L2Space) (G : Fin 3 → L2Space)
    (h : ∀ i : Fin 3, HasWeakSpatialDerivative i (F : SpatialField) (G i : SpatialField)) :
    (H1.ofWeakDerivatives F G h).value = F := rfl

@[simp] theorem H1.derivative_ofWeakDerivatives (F : L2Space) (G : Fin 3 → L2Space)
    (h : ∀ i : Fin 3, HasWeakSpatialDerivative i (F : SpatialField) (G i : SpatialField))
    (i : Fin 3) : (H1.ofWeakDerivatives F G h).derivative i = G i := rfl

end UnforcedLeray.SobolevGraph
