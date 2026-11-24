import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T10_6_1

/-!
# Part II-b, task `PartII-b:T10/6/1/5` (`DriftNoSwirl/Leaf5`): `NvCInvariant`

Source of record: `the November 2 reference manuscript`, lines 1912-1915.

For `g` fixing `e₃`, the ring lift is equivariant: `g (Nv R F τ (g⁻¹ y)) = Nv R F τ y`. The ring
chart at `(τ, g⁻¹ y)` equals the chart at `(τ, y)` (the age, and the trans and phase coordinates,
depend only on `ϱ` and `y₃`, which `g` preserves), and the frame map satisfies
`g (frameL (g⁻¹ y) v) = frameL y v` by `eR`-equivariance (`Axi.map_eR_symm`). Then `gC g` and the
real/imaginary split `NvC` commute with this identity pointwise, so the a.e. statement holds
everywhere.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

open UnforcedLeray.Cons.C03.Concrete UnforcedLeray.PhaseSpace

namespace NvCInvariantHelp

/-- The ring lift of a real merid profile is equivariant under `g` fixing the axis. -/
lemma nv_equiv (R : ℝ) (F : ℝ × (ℝ × ℝ) → Axi.Merid) (g : Space ≃ₗᵢ[ℝ] Space)
    (hg : UnforcedLeray.FixesAxis g) (τ : ℝ) (y : Space) :
    g (Axi.Nv R F τ (g.symm y)) = Axi.Nv R F τ y := by
  have hage : Axi.age R (g.symm y) = Axi.age R y := by
    unfold Axi.age
    rw [Axi.ϱ_symm_apply g hg]
  have hchart : Axi.chart R τ (g.symm y) = Axi.chart R τ y := by
    unfold Axi.chart Axi.phase Axi.trans
    rw [hage, Axi.ϱ_symm_apply g hg, Axi.symm_apply_two g hg]
  have hfr : ∀ v : Axi.Merid, g (Axi.frameL (g.symm y) v) = Axi.frameL y v := by
    intro v
    rw [Axi.frameL_apply, Axi.frameL_apply, map_add, map_smul, map_smul,
      Axi.map_eR_symm g hg, show g Axi.e3 = Axi.e3 from hg]
  unfold Axi.Nv
  rw [hage, hchart, map_smul, hfr]

/-- Pointwise equivariance of the complex ring lift. -/
lemma nvC_equiv (R : ℝ) (b : CProf) (g : Space ≃ₗᵢ[ℝ] Space)
    (hg : UnforcedLeray.FixesAxis g) (x : ℝ × Space) :
    B0412.gC g (NvC R b (x.1, g.symm x.2)) = NvC R b x := by
  show B0412.gC g (B0412.realC (Axi.Nv R (fun z => reM (b z)) x.1 (g.symm x.2))
      + Complex.I • B0412.realC (Axi.Nv R (fun z => imM (b z)) x.1 (g.symm x.2)))
    = B0412.realC (Axi.Nv R (fun z => reM (b z)) x.1 x.2)
      + Complex.I • B0412.realC (Axi.Nv R (fun z => imM (b z)) x.1 x.2)
  rw [map_add, map_smul, B0412.gC_realC, B0412.gC_realC, nv_equiv R _ g hg,
    nv_equiv R _ g hg]

end NvCInvariantHelp

/-- **`NvCInvariant`**: `NvC R b` is `g`-invariant a.e. for `g` fixing `e₃`. -/
theorem nvCInvariant : UnforcedLeray.Short.IIb.NvCInvariant := by
  intro R b g hg
  have hfix : UnforcedLeray.FixesAxis g := hg
  refine Filter.Eventually.of_forall fun x => ?_
  show B0412.gC g (NvC R b (x.1, g.symm x.2)) = NvC R b x
  exact NvCInvariantHelp.nvC_equiv R b g hfix x

end UnforcedLeray.Short.IIb

#print axioms UnforcedLeray.Short.IIb.nvCInvariant
