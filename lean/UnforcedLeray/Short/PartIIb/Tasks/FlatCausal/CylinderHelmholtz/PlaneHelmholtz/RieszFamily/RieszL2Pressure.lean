import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.CylinderHelmholtz.PlaneHelmholtz.RieszFamily.Defs
import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.CylinderHelmholtz.PlaneHelmholtz.RieszFamily.RieszTestMemLp
import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.CylinderHelmholtz.PlaneHelmholtz.RieszFamily.PressureIdentityTest
import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.CylinderHelmholtz.PlaneHelmholtz.RieszFamily.PlaneTestSub
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Topology.NhdsWithin

/-!
# Leaf `PartII-b:T12/1/1/2/44`: the pressure identity on `L²`

Source of record: `the November 2 reference manuscript`, line 1670 (`P_0`, the
ordinary planar cylinder projection) and lines 1923-1926 (`P_0` in the causal formula); classical
Calderón-Zygmund theory (Grafakos, *Classical Fourier Analysis*, Cor. 5.2.8).

For `L²` fields `F_0, F_1` and `L²` extensions `T_{ik}` of the test-level Riesz pairs,
`Σ_i ⟨F_i, Σ_k T_{ik} F_k⟩ = Σ_i ‖Σ_k T_{ik} F_k‖²`.  Both sides are continuous in `F`; they agree
on the dense set of tuples of test classes (`PlaneTestSub`), where the identity is the test-level
pressure identity `PressureIdentityTest`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set
open scoped ContDiff ENNReal NNReal Topology

namespace UnforcedLeray.Short.IIb.PlaneRiesz

/-- The inner product of two `L²` classes of (representatives) is the integral of the product. -/
theorem rieszL2_inner_toLp (a b : Pl → ℝ) (ha : MemLp a 2 volume) (hb : MemLp b 2 volume) :
    inner ℝ (ha.toLp a) (hb.toLp b) = ∫ x, a x * b x := by
  rw [L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [MemLp.coeFn_toLp ha, MemLp.coeFn_toLp hb] with x hx1 hx2
  rw [hx1, hx2]
  simp [RCLike.inner_apply, mul_comm]

/-- The pressure identity on `L²` for fields that are classes of planar tests. -/
theorem rieszL2_key (T : Fin 2 → Fin 2 → (PlaneL2 →L[ℝ] PlaneL2))
    (hT : ∀ i k, ExtendsRieszTest (T i k) i k)
    (f : Fin 2 → Pl → ℝ) (hf : ∀ k, IsTest (f k)) (hm : ∀ k, MemLp (f k) 2 volume) :
    ∑ i, inner ℝ ((hm i).toLp (f i)) (∑ k, T i k ((hm k).toLp (f k))) =
      ∑ i, ‖∑ k, T i k ((hm k).toLp (f k))‖ ^ 2 := by
  have hg : ∀ i k, MemLp (rieszTest i k (f k)) 2 volume :=
    fun i k => rieszTestMemLp i k (f k) (hf k)
  have hU : ∀ i k, T i k ((hm k).toLp (f k)) = (hg i k).toLp (rieszTest i k (f k)) :=
    fun i k => hT i k (f k) (hf k) (hm k) (hg i k)
  have hV : ∀ i, ∑ k, T i k ((hm k).toLp (f k)) =
      ((hg i 0).add (hg i 1)).toLp (rieszTest i 0 (f 0) + rieszTest i 1 (f 1)) := by
    intro i
    rw [Fin.sum_univ_two, hU i 0, hU i 1]
    exact (MemLp.toLp_add (hg i 0) (hg i 1)).symm
  have hLHS : ∀ i, inner ℝ ((hm i).toLp (f i)) (∑ k, T i k ((hm k).toLp (f k))) =
      ∫ x, f i x * (rieszTest i 0 (f 0) x + rieszTest i 1 (f 1) x) := by
    intro i
    rw [hV i, rieszL2_inner_toLp]
    simp only [Pi.add_apply]
  have hRHS : ∀ i, ‖∑ k, T i k ((hm k).toLp (f k))‖ ^ 2 =
      ∫ x, (rieszTest i 0 (f 0) x + rieszTest i 1 (f 1) x) ^ 2 := by
    intro i
    rw [hV i, ← real_inner_self_eq_norm_sq, rieszL2_inner_toLp]
    simp only [Pi.add_apply, sq]
  have hp := pressureIdentityTest f hf
  simp only [Fin.sum_univ_two] at hp
  simp only [hLHS, hRHS]
  simp only [Fin.sum_univ_two]
  exact hp

/-- **Leaf `PartII-b:T12/1/1/2/44`.**  The pressure identity on `L²`. -/
theorem rieszL2Pressure : RieszL2Pressure := by
  intro T hT F
  obtain ⟨M, hM1, _, hMd⟩ := planeTestSub
  let G : (Fin 2 → PlaneL2) → ℝ := fun F =>
    ∑ i, inner ℝ (F i) (∑ k, T i k (F k)) - ∑ i, ‖∑ k, T i k (F k)‖ ^ 2
  have hTc : ∀ i k, Continuous (fun F : Fin 2 → PlaneL2 => T i k (F k)) := fun i k =>
    (T i k).continuous.comp (continuous_apply k)
  have hS : ∀ i, Continuous (fun F : Fin 2 → PlaneL2 => ∑ k, T i k (F k)) := fun i =>
    continuous_finset_sum _ fun k _ => hTc i k
  have hGc : Continuous G := by
    have h1 : Continuous (fun F : Fin 2 → PlaneL2 => ∑ i, inner ℝ (F i) (∑ k, T i k (F k))) :=
      continuous_finset_sum _ fun i _ => (continuous_apply i).inner (hS i)
    have h2 : Continuous (fun F : Fin 2 → PlaneL2 => ∑ i, ‖∑ k, T i k (F k)‖ ^ 2) :=
      continuous_finset_sum _ fun i _ => ((hS i).norm).pow 2
    exact h1.sub h2
  have hzero : ∀ F : Fin 2 → PlaneL2, (∀ k, F k ∈ M) → G F = 0 := by
    intro F hFM
    choose f hf hm hFe using fun k => hM1 (F k) (hFM k)
    have key := rieszL2_key T hT f hf hm
    show (∑ i, inner ℝ (F i) (∑ k, T i k (F k))) - ∑ i, ‖∑ k, T i k (F k)‖ ^ 2 = 0
    rw [sub_eq_zero]
    simp only [hFe]
    exact key
  have hsub : Set.pi Set.univ (fun _ : Fin 2 => (M : Set PlaneL2)) ⊆ {F | G F = 0} := by
    intro F hF
    exact hzero F (fun k => hF k (Set.mem_univ k))
  have hdense : Dense (Set.pi Set.univ (fun _ : Fin 2 => (M : Set PlaneL2))) :=
    dense_pi Set.univ (fun _ _ => hMd)
  have hclosed : IsClosed {F : Fin 2 → PlaneL2 | G F = 0} := isClosed_eq hGc continuous_const
  have hall : G F = 0 := by
    have hF : F ∈ closure (Set.pi Set.univ (fun _ : Fin 2 => (M : Set PlaneL2))) := by
      rw [hdense.closure_eq]
      exact Set.mem_univ F
    exact closure_minimal hsub hclosed hF
  exact sub_eq_zero.mp hall

end UnforcedLeray.Short.IIb.PlaneRiesz
