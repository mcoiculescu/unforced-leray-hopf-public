import UnforcedLeray.Short.PartIIb.Sub.PartIIb_G4_3_6_2_1

/-!


Symmetry of the mixed second partials `∂_s∂_ηΨ = ∂_η∂_sΨ` at `s > 0` (SP 2419-2423).
The chart function is `C²` on the open set `{s > 0}`, so its second Fréchet derivative is
symmetric (`ContDiffAt.isSymmSndFDerivAt`); `∂_ηΨ` and `∂_sΨ` are its evaluations at fixed
directions, and the derivative of such an evaluation is the second derivative applied to the
same two vectors.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.IIb

private lemma psiChart_contDiffAt_symm {ψ : ℝ → UnforcedLeray.Cyl.Plane → ℝ}
    (hψ : ContDiffOn ℝ ∞ (psiChart ψ) (Ioi (0 : ℝ) ×ˢ (univ : Set UnforcedLeray.Cyl.Plane)))
    {y : Coord} (hy : 0 < y.1) : ContDiffAt ℝ 2 (psiChart ψ) y := by
  have hopen : IsOpen (Ioi (0 : ℝ) ×ˢ (univ : Set UnforcedLeray.Cyl.Plane)) :=
    isOpen_Ioi.prod isOpen_univ
  exact (hψ.contDiffAt (hopen.mem_nhds (Set.mk_mem_prod hy (mem_univ _)))).of_le (by simp)

private lemma fderiv_apply_const_symm {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : E → ℝ} {y : E} (hF : DifferentiableAt ℝ (fderiv ℝ F) y) (v e : E) :
    fderiv ℝ (fun z => fderiv ℝ F z v) y e = fderiv ℝ (fderiv ℝ F) y e v := by
  rw [fderiv_clm_apply hF (differentiableAt_const v)]
  simp

theorem raisedSymm_proof : UnforcedLeray.Short.IIb.RaisedSymm := by
  intro ψ hψ x hx
  have hcd : ContDiffAt ℝ 2 (psiChart ψ) x := psiChart_contDiffAt_symm hψ hx
  have hfd : DifferentiableAt ℝ (fderiv ℝ (psiChart ψ)) x :=
    (hcd.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hsym : IsSymmSndFDerivAt ℝ (psiChart ψ) x := hcd.isSymmSndFDerivAt (by simp)
  have e1 : Axi.dEta (psiChart ψ) = fun y : Coord => fderiv ℝ (psiChart ψ) y (0, (0, 1)) := rfl
  have e2 : Axi.dS (psiChart ψ) = fun y : Coord => fderiv ℝ (psiChart ψ) y (1, (0, 0)) := rfl
  rw [e1, e2, fderiv_apply_const_symm hfd (0, (0, 1)) (1, (0, 0)),
    fderiv_apply_const_symm hfd (1, (0, 0)) (0, (0, 1))]
  exact hsym _ _

end UnforcedLeray.Short.IIb
