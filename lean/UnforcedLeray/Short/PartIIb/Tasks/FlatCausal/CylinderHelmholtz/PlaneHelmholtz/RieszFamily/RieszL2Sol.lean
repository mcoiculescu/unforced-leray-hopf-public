import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.CylinderHelmholtz.PlaneHelmholtz.RieszFamily.Defs
import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.CylinderHelmholtz.PlaneHelmholtz.RieszFamily.RieszTestMemLp
import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.CylinderHelmholtz.PlaneHelmholtz.RieszFamily.RieszTestSol

/-!
# Leaf `PartII-b:T12/1/1/2/48`: the `L²` Riesz pairs annihilate a solenoidal field

Source of record: `the November 2 reference manuscript`, line 1670 (`P_0`, the
ordinary planar cylinder projection) and lines 1923-1926 (`P_0` in the causal formula); classical
Calderón-Zygmund theory (Grafakos, *Classical Fourier Analysis*, Cor. 5.2.8).

For a solenoidal test field `Ψ` (`Σ_i ∂_i Ψ_i = 0`), the test-level identity
`Σ_i S_{ki} Ψ_i = 0` (`RieszTestSol`) transfers to `L²` through the extension property.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set
open scoped ContDiff ENNReal NNReal Topology

namespace UnforcedLeray.Short.IIb.PlaneRiesz

/-- **Leaf `PartII-b:T12/1/1/2/48`.**  `Σ_i T_{ki} Ψ_i = 0` in `L²` for a solenoidal test field. -/
theorem rieszL2Sol : UnforcedLeray.Short.IIb.PlaneRiesz.RieszL2Sol := by
  intro T hT Ψ hΨ hdiv h k
  have hΨt : ∀ i, IsTest (Ψ i) := fun i => hΨ i
  have e : ∀ i : Fin 2, T k i ((h i).toLp _) =
      (rieszTestMemLp k i (Ψ i) (hΨt i)).toLp (rieszTest k i (Ψ i)) :=
    fun i => hT k i (Ψ i) (hΨt i) (h i) (rieszTestMemLp k i (Ψ i) (hΨt i))
  simp only [e]
  rw [Fin.sum_univ_two]
  have m0 : MemLp (rieszTest k 0 (Ψ 0)) 2 volume := rieszTestMemLp k 0 (Ψ 0) (hΨt 0)
  have m1 : MemLp (rieszTest k 1 (Ψ 1)) 2 volume := rieszTestMemLp k 1 (Ψ 1) (hΨt 1)
  have hsol : ∀ x, rieszTest k 0 (Ψ 0) x + rieszTest k 1 (Ψ 1) x = 0 := by
    intro x
    have hd : ∀ y, divTest Ψ y = 0 := fun y => hdiv y
    have := rieszTestSol Ψ hΨt hd k x
    rw [Fin.sum_univ_two] at this
    exact this
  refine Lp.ext ?_
  filter_upwards [Lp.coeFn_add (m0.toLp (rieszTest k 0 (Ψ 0)))
    (m1.toLp (rieszTest k 1 (Ψ 1))),
    MemLp.coeFn_toLp m0, MemLp.coeFn_toLp m1,
    (Lp.coeFn_zero ℝ 2 volume : ⇑(0 : PlaneL2) =ᵐ[volume] 0)] with x hA hB hC hZ
  rw [hA, Pi.add_apply, hB, hC, hZ, Pi.zero_apply]
  exact hsol x

end UnforcedLeray.Short.IIb.PlaneRiesz
