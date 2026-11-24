import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_5_1_2_4_1.PointDom.FullKerReg.PrimInt2

/-!
# `primInt_main`: `C²` regularity and sharp bounds of the outward primitive
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray

/-- Continuity of the `u`-dependence of the first two `q`-derivatives of a jointly `C²` function. -/
theorem prim_partials_continuous {A : Space → ℝ} (hA : ContDiff ℝ 2 A) (w q : Space) :
    Continuous (fun u : ℝ => primF A w q u) ∧
    Continuous (fun u : ℝ => fderiv ℝ (fun q' => primF A w q' u) q) ∧
    Continuous (fun u : ℝ => fderiv ℝ (fun q' => fderiv ℝ (fun q'' => primF A w q'' u) q') q) := by
  have hJ : ContDiff ℝ 2 (fun p : ℝ × Space => primF A w p.2 p.1) :=
    (primF_contDiff hA w).comp (contDiff_snd.prodMk contDiff_fst)
  refine ⟨?_, ?_, ?_⟩
  · exact (hJ.continuous.comp (continuous_id.prodMk continuous_const))
  · have := ContDiff.fderiv (f := fun u : ℝ => fun q' : Space => primF A w q' u) (g := fun _ : ℝ => q)
      (m := 2) (n := 1) hJ contDiff_const (by norm_num)
    exact this.continuous
  · have h1 : ContDiff ℝ 1 (fun x : ℝ × Space =>
        fderiv ℝ (fun q' : Space => primF A w q' x.1) x.2) := by
      refine ContDiff.fderiv (f := fun (x : ℝ × Space) (q' : Space) => primF A w q' x.1)
        (g := fun x : ℝ × Space => x.2) (m := 2) (n := 1) ?_ contDiff_snd (by norm_num)
      exact (primF_contDiff hA w).comp (contDiff_snd.prodMk (contDiff_fst.comp contDiff_fst))
    have := ContDiff.fderiv (f := fun (u : ℝ) (q' : Space) =>
        fderiv ℝ (fun q'' : Space => primF A w q'' u) q') (g := fun _ : ℝ => q)
      (m := 1) (n := 0) h1 contDiff_const (by norm_num)
    exact this.continuous

end UnforcedLeray.Short.PartIIIb.Concrete

end
