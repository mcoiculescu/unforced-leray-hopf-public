import UnforcedLeray.Short.PartIIa.StatementsFree
import UnforcedLeray.Units.B0411.Separation
import UnforcedLeray.Lib.PhaseSpace.ExtendedTest

/-!
# Part II-a, task `PartII-a:F12`: density of smooth symmetric tensors (conditional)

Source of record: `the November 2 reference manuscript`, lines 1546-1586 ("the
completion from smooth tensors": smooth symmetric phase tensors are dense in `Y_2(Sym_3)`; the
spec cites 1533-1537 but the completion paragraph is at 1546-1586).

`SmoothTensorsDense` (`StatementsFree.lean`) says: the set of smooth symmetric phase tensors
`smoothTensor P G` (rows `G i` phase tests, `G i p j = G j p i`) is dense in the closed subspace
`symY2 P` of `Y2Sym P = PiLp 2 (Fin 3 → Yq P 2)`.

Proof (Hilbert-space orthogonality; no transposition operator is needed):

1. The smooth symmetric tensors form a subspace `M` of `symY2 P` (`SmoothSymSubmodule`).
2. If `Z ∈ symY2 P` is orthogonal to `M`, then `Z = 0` (`SmoothSymSeparation`): test with the
   symmetric rows `G_a = φ̄ e_b`, `G_b = φ̄ e_a` (`a ≠ b`) and `G_a = φ̄ e_a`; the symmetry of `Z`
   gives `⟨φ e_b, Z_a⟩ = 0` for all phase tests `φ`, hence `Z_a = 0` by separation
   (`B0411.eq_zero_of_forall_phasePair`). This needs the Hilbert inner product of `Y_2` against a
   phase test as the (conjugated) phase pairing (`PhaseInnerEqPairing`).
3. A closed subspace `S` of a Hilbert space with `M ≤ S` and `Mᗮ ∩ S = 0` satisfies
   `S ≤ closure M` (`dense_of_orthogonal`, proved here), whence density of `M` in `S`.

Proved here: closedness of `symY2 P` (`isClosed_symY2`), the Hilbert lemma, and the conditional
theorem `smoothTensorsDense_of`. Leaves: `SmoothSymSubmodule` (task `PartII-a:F12/1`),
`PhaseInnerEqPairing` (task `PartII-a:F12/2`), `SmoothSymSeparation` (task `PartII-a:F12/3`,
from `PhaseInnerEqPairing`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace UnforcedLeray.Short.PartIIa

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411 UnforcedLeray.RieszLp

/-- Pointwise complex conjugation of a `ℂ³`-valued function. -/
def conjF (Φ : ℝ × Space → CVec3) : ℝ × Space → CVec3 :=
  fun p => WithLp.toLp 2 fun k => star (Φ p k)

/-- **Leaf `PartII-a:F12/1`**: the smooth symmetric phase tensors form a linear subspace of
`Y2Sym P`, contained in the symmetric subspace `symY2 P`. (Closure under sums and complex
multiples: `G + G'`, `c • G` are again symmetric phase-test rows and `testElem_add`,
`testElem_const_smul` give additivity of `smoothTensor`. Containment: `symFun P i j φ` of a
smooth symmetric tensor is `∫∫ φ G_{ij} - ∫∫ φ G_{ji} = 0` by `phasePair_eq_periodIntegral`.) -/
def SmoothSymSubmodule : Prop :=
  ∀ (P : ℝ) [Fact (0 < P)], ∃ M : Submodule ℂ (Y2Sym P), M ≤ symY2 P ∧
    ∀ X : Y2Sym P, X ∈ M ↔ ∃ G : Fin 3 → ℝ × Space → CVec3,
      (∀ i, IsPhaseTest P (G i)) ∧ IsSymRows G ∧ smoothTensor P G = X

/-- **Leaf `PartII-a:F12/2`**: the conjugate of a phase test is a phase test, and the Hilbert inner
product of `Y_2` against `testElem Φ` is the phase pairing against the conjugate test:
`⟨Φ, g⟩_{Y_2} = ∫∫ conj(Φ) · g = phasePair P 2 (conj Φ) g`. -/
def PhaseInnerEqPairing : Prop :=
  ∀ (P : ℝ) [Fact (0 < P)] (Φ : ℝ × Space → CVec3), IsPhaseTest P Φ →
    IsPhaseTest P (conjF Φ) ∧ ∀ g : Yq P 2,
      inner ℂ (testElem P 2 Φ) g = phasePair P 2 (conjF Φ) g

/-- **Leaf `PartII-a:F12/3`** (from `PhaseInnerEqPairing`): a symmetric tensor `Z ∈ symY2 P` that is
orthogonal to all smooth symmetric phase tensors vanishes. -/
def SmoothSymSeparation : Prop :=
  ∀ (P : ℝ) [Fact (0 < P)] (Z : Y2Sym P), Z ∈ symY2 P →
    (∀ G : Fin 3 → ℝ × Space → CVec3, (∀ i, IsPhaseTest P (G i)) → IsSymRows G →
      inner ℂ (smoothTensor P G) Z = 0) → Z = 0

/-- The symmetric subspace is closed (an intersection of kernels of bounded functionals). -/
theorem isClosed_symY2 (P : ℝ) [Fact (0 < P)] : IsClosed (symY2 P : Set (Y2Sym P)) := by
  have : (symY2 P : Set (Y2Sym P)) =
      ⋂ (i : Fin 3) (j : Fin 3) (φ : {φ : ℝ × Space → ℂ // IsPhaseTest P φ}),
        (LinearMap.ker (symFun P i j φ.1).toLinearMap : Set (Y2Sym P)) := by
    simp [symY2, Submodule.coe_iInf]
  rw [this]
  exact isClosed_iInter fun i => isClosed_iInter fun j => isClosed_iInter fun φ =>
    (symFun P i j φ.1).isClosed_ker

/-- **Hilbert lemma**: a subspace `M` of a closed subspace `S` whose orthogonal complement meets
`S` trivially is dense in `S`. -/
theorem le_topologicalClosure_of_orthogonal {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E] (S M : Submodule ℂ E) (hS : IsClosed (S : Set E))
    (hMS : M ≤ S) (h : ∀ Z ∈ S, (∀ m ∈ M, inner ℂ m Z = 0) → Z = 0) :
    S ≤ M.topologicalClosure := by
  set K := M.topologicalClosure with hK
  have hKS : K ≤ S := M.topologicalClosure_minimal hMS hS
  have : CompleteSpace K := (Submodule.isClosed_topologicalClosure M).completeSpace_coe
  have hsup := Submodule.sup_orthogonal_inf_of_hasOrthogonalProjection hKS
  have hbot : Kᗮ ⊓ S = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro Z hZ
    refine h Z hZ.2 fun m hm => ?_
    exact (Submodule.mem_orthogonal K Z).1 hZ.1 m (M.le_topologicalClosure hm)
  rw [hbot, sup_bot_eq] at hsup
  exact hsup.ge

/-- **`PartII-a:F12`, conditional on the two leaves**: smooth symmetric phase tensors are dense in
`symY2 P` (source lines 1546-1586). -/
theorem smoothTensorsDense_of (h1 : SmoothSymSubmodule) (h2 : SmoothSymSeparation) :
    SmoothTensorsDense := by
  intro P _
  obtain ⟨M, hMS, hM⟩ := h1 P
  have hsub : symY2 P ≤ M.topologicalClosure :=
    le_topologicalClosure_of_orthogonal (symY2 P) M (isClosed_symY2 P) hMS fun Z hZ hZM =>
      h2 P Z hZ fun G hG hsym => hZM _ ((hM _).2 ⟨G, hG, hsym, rfl⟩)
  intro T
  set A : Set (symY2 P) := {T : symY2 P | ∃ G : Fin 3 → ℝ × Space → CVec3,
      (∀ i, IsPhaseTest P (G i)) ∧ IsSymRows G ∧ smoothTensor P G = (T : Y2Sym P)} with hAdef
  have hA : (Subtype.val '' A) = (M : Set (Y2Sym P)) := by
    ext X
    constructor
    · rintro ⟨T, ⟨G, hG, hs, he⟩, rfl⟩
      exact (hM _).2 ⟨G, hG, hs, he⟩
    · intro hX
      obtain ⟨G, hG, hs, he⟩ := (hM X).1 hX
      exact ⟨⟨X, hMS hX⟩, ⟨G, hG, hs, he⟩, rfl⟩
  show T ∈ closure A
  have hind : Topology.IsInducing (Subtype.val : symY2 P → Y2Sym P) :=
    Topology.IsInducing.subtypeVal
  rw [hind.closure_eq_preimage_closure_image A, hA]
  have := hsub T.2
  show (T : Y2Sym P) ∈ closure (M : Set (Y2Sym P))
  rw [← Submodule.topologicalClosure_coe]
  exact this

end UnforcedLeray.Short.PartIIa
