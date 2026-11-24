import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.CylinderHelmholtz.PlaneHelmholtz.RieszFamily.Defs
import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.CylinderHelmholtz.PlaneHelmholtz.RieszFamily.PdTest

/-!
# Leaf `PartII-b:T12/1/1/2/41`: the classes of planar tests form a dense subspace of `PlaneL2`

Source of record: `the November 2 reference manuscript`, line 1670 (`P_0`, the
ordinary planar cylinder projection) and lines 1923-1926 (`P_0` in the causal formula); classical
Calderón-Zygmund theory (Grafakos, *Classical Fourier Analysis*, Cor. 5.2.8).

The submodule `M` of `PlaneL2` consists of the classes `h.toLp f` of test functions `f`.  It is a
submodule because sums and scalar multiples of tests are tests and `toLp` is additive and
`ℝ`-homogeneous on `MemLp` functions.  It is dense because every class of a continuous compactly
supported `C^∞` function lies in it, and those classes are dense in `L²`
(`MeasureTheory.Lp.dense_hasCompactSupport_contDiff`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set
open scoped ContDiff ENNReal NNReal Topology

namespace UnforcedLeray.Short.IIb.PlaneRiesz

/-- **Leaf `PartII-b:T12/1/1/2/41`.** The test classes form a dense submodule of `PlaneL2`. -/
theorem planeTestSub : PlaneTestSub := by
  let M : Submodule ℝ PlaneL2 :=
    { carrier := {g | ∃ f : Pl → ℝ, IsTest f ∧ ∃ h : MemLp f 2 volume, g = h.toLp f}
      add_mem' := by
        rintro _ _ ⟨f, hf, hfm, rfl⟩ ⟨g, hg, hgm, rfl⟩
        exact ⟨f + g, ⟨hf.1.add hg.1, hf.2.add hg.2⟩, hfm.add hgm,
          (MemLp.toLp_add hfm hgm).symm⟩
      zero_mem' := ⟨0, ⟨contDiff_const, HasCompactSupport.zero⟩, MemLp.zero, rfl⟩
      smul_mem' := by
        rintro c _ ⟨f, hf, hfm, rfl⟩
        exact ⟨c • f, ⟨hf.1.const_smul c, hf.2.smul_left (f := fun _ : Pl => c)⟩,
          hfm.const_smul c, (MemLp.toLp_const_smul c hfm).symm⟩ }
  refine ⟨M, fun g hg => hg, fun f hf h => ⟨f, hf, h, rfl⟩, ?_⟩
  have hD : Dense {f : PlaneL2 | ∃ g : Pl → ℝ, f =ᵐ[volume] g ∧ HasCompactSupport g ∧
      ContDiff ℝ ∞ g} :=
    MeasureTheory.Lp.dense_hasCompactSupport_contDiff (by norm_num)
  refine Dense.mono ?_ hD
  rintro f ⟨g, hfg, hgc, hgs⟩
  have hgm : MemLp g 2 volume := hgs.continuous.memLp_of_hasCompactSupport hgc
  have hfeq : f = hgm.toLp g := Lp.ext (hfg.trans hgm.coeFn_toLp.symm)
  rw [hfeq]
  exact ⟨g, ⟨hgs, hgc⟩, hgm, rfl⟩

end UnforcedLeray.Short.IIb.PlaneRiesz
