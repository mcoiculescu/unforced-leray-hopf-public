import UnforcedLeray.Analysis.SobolevGraph.H1

/-!
# The second-order weak Sobolev Hilbert graph on R³

The ambient square-sum Hilbert space stores one L² field, its three first
weak derivatives, and its nine ordered second weak derivatives. The convention
is exactly that of `Statement.lean`: the entry `(i,j)` is the j-th weak
derivative of the i-th first derivative. Every constraint is the preimage of
the actual closed derivative graph on vector-valued L²(R³).

This yields the complete H² graph and its componentwise continuity criterion.
The ordered mixed derivatives occur twice in the norm; no assertion of equality
with a norm counting each multi-index only once, or of a Fourier definition, is
made here.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory
open scoped Topology

namespace UnforcedLeray.SobolevGraph

abbrev H2Index := Unit ⊕ (Fin 3 ⊕ (Fin 3 × Fin 3))
abbrev H2Ambient := PiLp 2 (fun _ : H2Index => L2Space)

def h2ValueIndex : H2Index := Sum.inl ()
def h2FirstIndex (i : Fin 3) : H2Index := Sum.inr (Sum.inl i)
def h2SecondIndex (i j : Fin 3) : H2Index := Sum.inr (Sum.inr (i, j))

def firstPair (i : Fin 3) : H2Ambient →L[ℝ] (L2Space × L2Space) :=
  (PiLp.proj 2 (fun _ : H2Index => L2Space) h2ValueIndex).prod
    (PiLp.proj 2 (fun _ : H2Index => L2Space) (h2FirstIndex i))

def secondPair (i j : Fin 3) : H2Ambient →L[ℝ] (L2Space × L2Space) :=
  (PiLp.proj 2 (fun _ : H2Index => L2Space) (h2FirstIndex i)).prod
    (PiLp.proj 2 (fun _ : H2Index => L2Space) (h2SecondIndex i j))

theorem firstPair_apply (i : Fin 3) (F : H2Ambient) :
    firstPair i F = (F.ofLp h2ValueIndex, F.ofLp (h2FirstIndex i)) := rfl

theorem secondPair_apply (i j : Fin 3) (F : H2Ambient) :
    secondPair i j F = (F.ofLp (h2FirstIndex i), F.ofLp (h2SecondIndex i j)) := rfl

/-- All first and ordered-second distributional constraints, as a linear subspace. -/
def H2Sub : Submodule ℝ H2Ambient :=
  (⨅ i : Fin 3, (derivativeGraph i).comap (firstPair i).toLinearMap) ⊓
    (⨅ i : Fin 3, ⨅ j : Fin 3, (derivativeGraph j).comap (secondPair i j).toLinearMap)

theorem mem_H2Sub_iff (F : H2Ambient) :
    F ∈ H2Sub ↔
      (∀ i : Fin 3, HasWeakSpatialDerivative i
        (F.ofLp h2ValueIndex : SpatialField) (F.ofLp (h2FirstIndex i) : SpatialField)) ∧
      (∀ i j : Fin 3, HasWeakSpatialDerivative j
        (F.ofLp (h2FirstIndex i) : SpatialField)
        (F.ofLp (h2SecondIndex i j) : SpatialField)) := by
  simp only [H2Sub, Submodule.mem_inf, Submodule.mem_iInf, Submodule.mem_comap,
    ContinuousLinearMap.coe_coe, firstPair_apply, secondPair_apply, mem_derivativeGraph_iff]

/-- The second-order Sobolev graph is closed in its thirteen-component Hilbert product. -/
theorem isClosed_H2Sub : IsClosed (H2Sub : Set H2Ambient) := by
  rw [H2Sub, Submodule.coe_inf]
  apply IsClosed.inter
  · rw [Submodule.coe_iInf]
    apply isClosed_iInter
    intro i
    change IsClosed ((firstPair i) ⁻¹' (derivativeGraph i : Set (L2Space × L2Space)))
    exact (isClosed_derivativeGraph i).preimage (firstPair i).continuous
  · rw [Submodule.coe_iInf]
    apply isClosed_iInter
    intro i
    rw [Submodule.coe_iInf]
    apply isClosed_iInter
    intro j
    change IsClosed ((secondPair i j) ⁻¹' (derivativeGraph j : Set (L2Space × L2Space)))
    exact (isClosed_derivativeGraph j).preimage (secondPair i j).continuous

abbrev H2 := ↥H2Sub

instance H2_completeSpace : CompleteSpace H2 := isClosed_H2Sub.completeSpace_coe

example : InnerProductSpace ℝ H2 := inferInstance

namespace H2

def value (F : H2) : L2Space := (F : H2Ambient).ofLp h2ValueIndex
def first (F : H2) (i : Fin 3) : L2Space := (F : H2Ambient).ofLp (h2FirstIndex i)
def second (F : H2) (i j : Fin 3) : L2Space := (F : H2Ambient).ofLp (h2SecondIndex i j)

def valueCLM : H2 →L[ℝ] L2Space :=
  (PiLp.proj 2 (fun _ : H2Index => L2Space) h2ValueIndex).comp H2Sub.subtypeL

def firstCLM (i : Fin 3) : H2 →L[ℝ] L2Space :=
  (PiLp.proj 2 (fun _ : H2Index => L2Space) (h2FirstIndex i)).comp H2Sub.subtypeL

def secondCLM (i j : Fin 3) : H2 →L[ℝ] L2Space :=
  (PiLp.proj 2 (fun _ : H2Index => L2Space) (h2SecondIndex i j)).comp H2Sub.subtypeL

@[simp] theorem valueCLM_apply (F : H2) : valueCLM F = F.value := rfl
@[simp] theorem firstCLM_apply (i : Fin 3) (F : H2) : firstCLM i F = F.first i := rfl
@[simp] theorem secondCLM_apply (i j : Fin 3) (F : H2) :
    secondCLM i j F = F.second i j := rfl

theorem hasWeakFirst (F : H2) (i : Fin 3) :
    HasWeakSpatialDerivative i (F.value : SpatialField) (F.first i : SpatialField) :=
  ((mem_H2Sub_iff (F : H2Ambient)).mp F.property).1 i

theorem hasWeakSecond (F : H2) (i j : Fin 3) :
    HasWeakSpatialDerivative j (F.first i : SpatialField) (F.second i j : SpatialField) :=
  ((mem_H2Sub_iff (F : H2Ambient)).mp F.property).2 i j

/-- The exact ordered-derivative H² graph norm. -/
theorem norm_sq (F : H2) :
    ‖F‖ ^ 2 = ‖F.value‖ ^ 2 + (∑ i : Fin 3, ‖F.first i‖ ^ 2) +
      ∑ i : Fin 3, ∑ j : Fin 3, ‖F.second i j‖ ^ 2 := by
  change ‖(F : H2Ambient)‖ ^ 2 = _
  rw [PiLp.norm_sq_eq_of_L2]
  simp [Fintype.sum_sum_type, Fintype.sum_prod_type,
    value, first, second, h2ValueIndex, h2FirstIndex, h2SecondIndex, add_assoc]

theorem inner_eq (F G : H2) :
    inner ℝ F G = inner ℝ F.value G.value +
      (∑ i : Fin 3, inner ℝ (F.first i) (G.first i)) +
      ∑ i : Fin 3, ∑ j : Fin 3, inner ℝ (F.second i j) (G.second i j) := by
  rw [Submodule.coe_inner, PiLp.inner_apply]
  simp [Fintype.sum_sum_type, Fintype.sum_prod_type,
    value, first, second, h2ValueIndex, h2FirstIndex, h2SecondIndex, add_assoc]

/-- No arbitrary derivative data remain once the L² field is fixed. -/
theorem value_injective : Function.Injective value := by
  intro F G hv
  have hf (i : Fin 3) : F.first i = G.first i := by
    have hG := G.hasWeakFirst i
    rw [← hv] at hG
    apply Lp.ext
    exact (F.hasWeakFirst i).ae_eq hG (Lp.memLp _) (Lp.memLp _)
  have hs (i j : Fin 3) : F.second i j = G.second i j := by
    have hG := G.hasWeakSecond i j
    rw [← hf i] at hG
    apply Lp.ext
    exact (F.hasWeakSecond i j).ae_eq hG (Lp.memLp _) (Lp.memLp _)
  apply Subtype.ext
  apply (WithLp.ext_iff (p := 2)).mpr
  funext k
  rcases k with v | (i | ij)
  · cases v
    exact hv
  · exact hf i
  · exact hs ij.1 ij.2

@[ext] theorem ext {F G : H2} (h : F.value = G.value) : F = G := value_injective h

theorem valueCLM_injective : Function.Injective valueCLM := value_injective

/-- Continuity in H² is exactly continuity of its thirteen L² components. -/
theorem continuousOn_iff_components {α : Type*} [TopologicalSpace α]
    (f : α → H2) (s : Set α) :
    ContinuousOn f s ↔ ContinuousOn (fun x => (f x).value) s ∧
      (∀ i : Fin 3, ContinuousOn (fun x => (f x).first i) s) ∧
      (∀ i j : Fin 3, ContinuousOn (fun x => (f x).second i j) s) := by
  constructor
  · intro hf
    exact ⟨valueCLM.continuous.comp_continuousOn hf,
      (fun i => (firstCLM i).continuous.comp_continuousOn hf),
      fun i j => (secondCLM i j).continuous.comp_continuousOn hf⟩
  · rintro ⟨hv, hf, hs⟩
    apply (Topology.IsInducing.subtypeVal.continuousOn_iff).mpr
    apply ((PiLp.homeomorph 2 (fun _ : H2Index => L2Space)).isInducing.continuousOn_iff).mpr
    apply continuousOn_pi.mpr
    intro k
    rcases k with v | (i | ij)
    · cases v
      exact hv
    · exact hf i
    · exact hs ij.1 ij.2

end H2

/-- The canonical thirteen-component tuple of actual L² classes. -/
def h2Tuple (F : L2Space) (G : Fin 3 → L2Space) (H : Fin 3 → Fin 3 → L2Space) : H2Ambient :=
  WithLp.toLp 2 (Sum.elim (fun _ : Unit => F) (Sum.elim G (fun ij => H ij.1 ij.2)))

@[simp] theorem h2Tuple_value (F : L2Space) (G : Fin 3 → L2Space)
    (H : Fin 3 → Fin 3 → L2Space) : (h2Tuple F G H).ofLp h2ValueIndex = F := rfl

@[simp] theorem h2Tuple_first (F : L2Space) (G : Fin 3 → L2Space)
    (H : Fin 3 → Fin 3 → L2Space) (i : Fin 3) :
    (h2Tuple F G H).ofLp (h2FirstIndex i) = G i := rfl

@[simp] theorem h2Tuple_second (F : L2Space) (G : Fin 3 → L2Space)
    (H : Fin 3 → Fin 3 → L2Space) (i j : Fin 3) :
    (h2Tuple F G H).ofLp (h2SecondIndex i j) = H i j := rfl

/-- Actual first and ordered-second weak derivatives produce an H² element. -/
def H2.ofWeakDerivatives (F : L2Space) (G : Fin 3 → L2Space) (H : Fin 3 → Fin 3 → L2Space)
    (hfirst : ∀ i : Fin 3, HasWeakSpatialDerivative i (F : SpatialField) (G i : SpatialField))
    (hsecond : ∀ i j : Fin 3,
      HasWeakSpatialDerivative j (G i : SpatialField) (H i j : SpatialField)) : H2 :=
  ⟨h2Tuple F G H, (mem_H2Sub_iff (h2Tuple F G H)).mpr ⟨hfirst, hsecond⟩⟩

@[simp] theorem H2.value_ofWeakDerivatives (F : L2Space) (G : Fin 3 → L2Space)
    (H : Fin 3 → Fin 3 → L2Space)
    (hfirst : ∀ i : Fin 3, HasWeakSpatialDerivative i (F : SpatialField) (G i : SpatialField))
    (hsecond : ∀ i j : Fin 3,
      HasWeakSpatialDerivative j (G i : SpatialField) (H i j : SpatialField)) :
    (H2.ofWeakDerivatives F G H hfirst hsecond).value = F := rfl

@[simp] theorem H2.first_ofWeakDerivatives (F : L2Space) (G : Fin 3 → L2Space)
    (H : Fin 3 → Fin 3 → L2Space)
    (hfirst : ∀ i : Fin 3, HasWeakSpatialDerivative i (F : SpatialField) (G i : SpatialField))
    (hsecond : ∀ i j : Fin 3,
      HasWeakSpatialDerivative j (G i : SpatialField) (H i j : SpatialField)) (i : Fin 3) :
    (H2.ofWeakDerivatives F G H hfirst hsecond).first i = G i := rfl

@[simp] theorem H2.second_ofWeakDerivatives (F : L2Space) (G : Fin 3 → L2Space)
    (H : Fin 3 → Fin 3 → L2Space)
    (hfirst : ∀ i : Fin 3, HasWeakSpatialDerivative i (F : SpatialField) (G i : SpatialField))
    (hsecond : ∀ i j : Fin 3,
      HasWeakSpatialDerivative j (G i : SpatialField) (H i j : SpatialField)) (i j : Fin 3) :
    (H2.ofWeakDerivatives F G H hfirst hsecond).second i j = H i j := rfl

end UnforcedLeray.SobolevGraph
