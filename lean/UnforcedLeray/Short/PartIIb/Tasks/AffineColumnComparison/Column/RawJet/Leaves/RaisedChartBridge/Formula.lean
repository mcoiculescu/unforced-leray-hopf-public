import UnforcedLeray.Short.PartIIb.Sub.PartIIb_G4_3_6_2_1

/-!


Product rule for `raisedH ψ = Ψ - η ∂_ηΨ - 2s ∂_sΨ` at a point with `s > 0` (SP 2419, 2423).
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.IIb

private lemma psiChart_contDiffAt_formula {ψ : ℝ → UnforcedLeray.Cyl.Plane → ℝ}
    (hψ : ContDiffOn ℝ ∞ (psiChart ψ) (Ioi (0 : ℝ) ×ˢ (univ : Set UnforcedLeray.Cyl.Plane)))
    {y : Coord} (hy : 0 < y.1) : ContDiffAt ℝ ∞ (psiChart ψ) y := by
  have hopen : IsOpen (Ioi (0 : ℝ) ×ˢ (univ : Set UnforcedLeray.Cyl.Plane)) :=
    isOpen_Ioi.prod isOpen_univ
  exact hψ.contDiffAt (hopen.mem_nhds (Set.mk_mem_prod hy (mem_univ _)))

theorem raisedFormula_proof : UnforcedLeray.Short.IIb.RaisedFormula := by
  intro ψ hψ x hx e
  obtain ⟨s, ξ, η⟩ := x
  have hs : (0 : ℝ) < s := hx
  have hfc : ContDiffAt ℝ ∞ (psiChart ψ) ((s, (ξ, η)) : Coord) :=
    psiChart_contDiffAt_formula hψ hs
  have hfc2 : ContDiffAt ℝ 2 (psiChart ψ) ((s, (ξ, η)) : Coord) := hfc.of_le (by simp)
  have hD : ContDiffAt ℝ 1 (fderiv ℝ (psiChart ψ)) ((s, (ξ, η)) : Coord) :=
    hfc2.fderiv_right (m := 1) (by norm_num)
  have hdE : ContDiffAt ℝ 1 (fun y : Coord => fderiv ℝ (psiChart ψ) y (0, (0, 1))) ((s, (ξ, η)) : Coord) :=
    hD.clm_apply contDiffAt_const
  have hdS : ContDiffAt ℝ 1 (fun y : Coord => fderiv ℝ (psiChart ψ) y (1, (0, 0))) ((s, (ξ, η)) : Coord) :=
    hD.clm_apply contDiffAt_const
  have hf1 : DifferentiableAt ℝ (psiChart ψ) ((s, (ξ, η)) : Coord) :=
    hfc.differentiableAt (by simp)
  have hdE1 := hdE.differentiableAt (by norm_num)
  have hdS1 := hdS.differentiableAt (by norm_num)
  have hsnd2 : HasFDerivAt (fun y : Coord => y.2.2)
      ((ContinuousLinearMap.snd ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ)))
      ((s, (ξ, η)) : Coord) :=
    (hasFDerivAt_snd).comp ((s, (ξ, η)) : Coord) (hasFDerivAt_snd)
  have hfst2 : HasFDerivAt (fun y : Coord => 2 * y.1)
      ((2 : ℝ) • ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ)) ((s, (ξ, η)) : Coord) :=
    (hasFDerivAt_fst).const_mul (2 : ℝ)
  have key := ((hf1.hasFDerivAt.sub (hsnd2.mul hdE1.hasFDerivAt)).sub
    (hfst2.mul hdS1.hasFDerivAt))
  have hRH : HasFDerivAt (raisedH ψ) _ ((s, (ξ, η)) : Coord) := key
  have hfd := hRH.fderiv
  unfold Axi.dEta Axi.dS
  rw [hfd]
  dsimp only
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.sub_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.coe_snd', ContinuousLinearMap.coe_fst', smul_eq_mul, nsmul_eq_mul]
  ring

end UnforcedLeray.Short.IIb
