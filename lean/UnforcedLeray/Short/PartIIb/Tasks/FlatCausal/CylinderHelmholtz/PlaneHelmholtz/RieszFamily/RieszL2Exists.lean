import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.CylinderHelmholtz.PlaneHelmholtz.RieszFamily.Defs
import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.CylinderHelmholtz.PlaneHelmholtz.RieszFamily.RieszL2Exists.Helpers
import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.CylinderHelmholtz.PlaneHelmholtz.RieszFamily.PlaneTestSub
import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.CylinderHelmholtz.PlaneHelmholtz.RieszFamily.ExtensionLemma
import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.CylinderHelmholtz.PlaneHelmholtz.RieszFamily.RieszTestL2Bound
import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.CylinderHelmholtz.PlaneHelmholtz.RieszFamily.RieszTestMemLp

/-!
# Leaf `PartII-b:T12/1/1/2/43`: existence of the `L²` operators `S_{ik}`

Source of record: `the November 2 reference manuscript`, line 1670 (`P_0`, the
ordinary planar cylinder projection) and lines 1923-1926 (`P_0` in the causal formula);
Grafakos, *Classical Fourier Analysis*, Cor. 5.2.8.

On the dense submodule of test classes (`planeTestSub`) the map `h.toLp f ↦ L²-class of S_{ik} f`
is well defined (`rl2_phi_eq`), linear (`rl2_phi_add`, `rl2_phi_smul`) and bounded by `1`
(`rieszTestL2Bound`); it extends to `PlaneL2` (`extensionLemma`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set
open scoped ContDiff ENNReal NNReal Topology

namespace UnforcedLeray.Short.IIb.PlaneRiesz

/-- A linear map on the test-class submodule `M` taking the class of a test `f` to the `L²`
class of `S_{ik} f`. -/
theorem rl2_linearOn (i k : Fin 2) (M : Submodule ℝ PlaneL2)
    (hrep : ∀ g ∈ M, ∃ f : Pl → ℝ, IsTest f ∧ ∃ h : MemLp f 2 volume, g = h.toLp f) :
    ∃ L : M →ₗ[ℝ] PlaneL2, ∀ (g : M) (f : Pl → ℝ) (hf : IsTest f) (h : MemLp f 2 volume),
      (g : PlaneL2) = h.toLp f → L g = rl2Phi i k f hf := by
  have hex : ∀ g : M, ∃ f : Pl → ℝ, IsTest f ∧ ∃ h : MemLp f 2 volume,
      (g : PlaneL2) = h.toLp f :=
    fun g => hrep (g : PlaneL2) g.2
  choose R hR hRg using hex
  have hQ : ∀ (g : M) (f : Pl → ℝ) (hf : IsTest f) (h : MemLp f 2 volume),
      (g : PlaneL2) = h.toLp f → rl2Phi i k (R g) (hR g) = rl2Phi i k f hf := by
    intro g f hf h e
    obtain ⟨h', e'⟩ := hRg g
    exact rl2_phi_eq i k (hR g) hf h' h (e'.symm.trans e)
  refine ⟨{ toFun := fun g => rl2Phi i k (R g) (hR g)
            map_add' := ?_
            map_smul' := ?_ }, fun g f hf h e => hQ g f hf h e⟩
  · intro x y
    show rl2Phi i k (R (x + y)) (hR (x + y)) = rl2Phi i k (R x) (hR x) + rl2Phi i k (R y) (hR y)
    obtain ⟨hx', ex⟩ := hRg x
    obtain ⟨hy', ey⟩ := hRg y
    have hs : IsTest (R x + R y) := rl2_isTest_add (hR x) (hR y)
    have e : ((x + y : M) : PlaneL2) = (rl2_memLp hs).toLp (R x + R y) := by
      rw [Submodule.coe_add, ex, ey]
      exact (MemLp.toLp_add hx' hy').symm
    exact (hQ (x + y) (R x + R y) hs (rl2_memLp hs) e).trans (rl2_phi_add i k (hR x) (hR y))
  · intro c x
    show rl2Phi i k (R (c • x)) (hR (c • x)) = (RingHom.id ℝ) c • rl2Phi i k (R x) (hR x)
    obtain ⟨hx', ex⟩ := hRg x
    have hs : IsTest (c • R x) := rl2_isTest_smul c (hR x)
    have e : ((c • x : M) : PlaneL2) = (rl2_memLp hs).toLp (c • R x) := by
      rw [Submodule.coe_smul, ex]
      exact (MemLp.toLp_const_smul c hx').symm
    exact (hQ (c • x) (c • R x) hs (rl2_memLp hs) e).trans (rl2_phi_smul i k c (hR x))

/-- **Leaf `PartII-b:T12/1/1/2/43`.** The `L²` operators `S_{ik}` exist with norm `≤ 1` and
extend the test-level Riesz pairs. -/
theorem rieszL2Exists : RieszL2Exists := by
  intro i k
  obtain ⟨M, hrep, hmem, hdense⟩ := planeTestSub
  obtain ⟨L, hL⟩ := rl2_linearOn i k M hrep
  have hbd : ∀ g : M, ‖L g‖ ≤ ‖(g : PlaneL2)‖ := by
    intro g
    obtain ⟨f, hf, h, e⟩ := hrep (g : PlaneL2) g.2
    rw [hL g f hf h e, e]
    exact rieszTestL2Bound i k f hf h (rieszTestMemLp i k f hf)
  obtain ⟨T, hT, hTL⟩ := extensionLemma M hdense L hbd
  refine ⟨T, hT, ?_⟩
  intro f hf h1 h2
  have hmemg : h1.toLp f ∈ M := hmem f hf h1
  exact (hTL ⟨h1.toLp f, hmemg⟩).trans (hL ⟨h1.toLp f, hmemg⟩ f hf h1 rfl)

end UnforcedLeray.Short.IIb.PlaneRiesz
