import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.CylinderHelmholtz.PlaneHelmholtz.RieszFamily.Defs
import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.CylinderHelmholtz.PlaneHelmholtz.RieszFamily.PdTest
import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.CylinderHelmholtz.PlaneHelmholtz.RieszFamily.RieszTestMemLp
import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.CylinderHelmholtz.PlaneHelmholtz.RieszFamily.RieszTestGrad

/-!
# Leaf `PartII-b:T12/1/1/2/47`: the gradient test identity on `L²`

Source of record: `the November 2 reference manuscript`, line 1670 (`P_0`, the
ordinary planar cylinder projection) and lines 1923-1926 (`P_0` in the causal formula); classical
Calderón-Zygmund theory (Grafakos, *Classical Fourier Analysis*, Cor. 5.2.8).

For a test `φ`, each `∂_i φ` is a test (`PdTest`), so the extension property gives
`T_{ki} (∂_i φ) = S_{ki} (∂_i φ)` in `L²`.  Summing over `i` and using the pointwise identity
`Σ_i S_{ki} ∂_i φ = ∂_k φ` (`RieszTestGrad`) gives the claim.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set
open scoped ContDiff ENNReal NNReal Topology

namespace UnforcedLeray.Short.IIb.PlaneRiesz

/-- **Leaf `PartII-b:T12/1/1/2/47`.**  `Σ_i T_{ki} (∂_i φ) = ∂_k φ` in `L²`. -/
theorem rieszL2Grad : UnforcedLeray.Short.IIb.PlaneRiesz.RieszL2Grad := by
  intro T hT φ hC hS h k
  have hφ : IsTest φ := ⟨hC, hS⟩
  have hpdT : ∀ i, IsTest (pd i φ) := fun i => pdTest i φ hφ
  have e : ∀ i : Fin 2, T k i ((h i).toLp _) =
      (rieszTestMemLp k i (pd i φ) (hpdT i)).toLp (rieszTest k i (pd i φ)) :=
    fun i => hT k i (pd i φ) (hpdT i) (h i) (rieszTestMemLp k i (pd i φ) (hpdT i))
  simp only [e]
  rw [Fin.sum_univ_two]
  have m0 : MemLp (rieszTest k 0 (pd 0 φ)) 2 volume := rieszTestMemLp k 0 (pd 0 φ) (hpdT 0)
  have m1 : MemLp (rieszTest k 1 (pd 1 φ)) 2 volume := rieszTestMemLp k 1 (pd 1 φ) (hpdT 1)
  refine Lp.ext ?_
  filter_upwards [Lp.coeFn_add (m0.toLp (rieszTest k 0 (pd 0 φ)))
    (m1.toLp (rieszTest k 1 (pd 1 φ))),
    MemLp.coeFn_toLp m0, MemLp.coeFn_toLp m1, MemLp.coeFn_toLp (h k)] with x hA hB hC' hD
  have hG := rieszTestGrad φ hφ k x
  rw [Fin.sum_univ_two] at hG
  rw [hA, Pi.add_apply, hB, hC', hD]
  exact hG

end UnforcedLeray.Short.IIb.PlaneRiesz
