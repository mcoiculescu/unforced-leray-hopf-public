import UnforcedLeray.Short.PartIIb.Sub.PartIIb_G4_3_6_2_1

/-!


Mixed bounds `D_q ∂_sΨ` and `D_η ∂_sΨ` by `‖ageJet 1 1‖` (SP 2412-2423).
`∂_sΨ(s,z) = ∂_r ψ(r,z)|_{r=s}` on `s > 0`, so its chart derivative in the spatial
directions `(0,v)` is the plane derivative of the slice function `z ↦ ∂_sΨ(s,z)`, and
`ageJet 1 1 ψ s z` is the plane derivative of `z ↦ ∂_r ψ(r,z)|_{r=s}`.
Unit vectors have norm one in the sup norm on `ℝ × ℝ`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology
open scoped ContDiff

open UnforcedLeray.Short.PartI

namespace UnforcedLeray.Short.IIb

private lemma psiChart_contDiffAt_mixed {ψ : ℝ → UnforcedLeray.Cyl.Plane → ℝ}
    (hψ : ContDiffOn ℝ ∞ (psiChart ψ) (Ioi (0 : ℝ) ×ˢ (univ : Set UnforcedLeray.Cyl.Plane)))
    {y : Coord} (hy : 0 < y.1) : ContDiffAt ℝ ∞ (psiChart ψ) y := by
  have hopen : IsOpen (Ioi (0 : ℝ) ×ˢ (univ : Set UnforcedLeray.Cyl.Plane)) :=
    isOpen_Ioi.prod isOpen_univ
  exact hψ.contDiffAt (hopen.mem_nhds (Set.mk_mem_prod hy (mem_univ _)))

private lemma norm_ageJet_one_mixed {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (ℓ : ℕ) (F : ℝ → UnforcedLeray.Cyl.Plane → E) (s : ℝ) (z : UnforcedLeray.Cyl.Plane) :
    ‖ageJet ℓ 1 F s z‖ = ‖fderiv ℝ (fun z' => iteratedDeriv ℓ (fun r => F r z') s) z‖ := by
  simp [UnforcedLeray.Short.PartI.ageJet, UnforcedLeray.Train.jet, norm_iteratedFDeriv_one]

/-- `∂_s` of the chart function is the one-variable derivative of the slice. -/
private lemma dS_slice_mixed {ψ : ℝ → UnforcedLeray.Cyl.Plane → ℝ}
    (hψ : ContDiffOn ℝ ∞ (psiChart ψ) (Ioi (0 : ℝ) ×ˢ (univ : Set UnforcedLeray.Cyl.Plane)))
    {s : ℝ} (hs : 0 < s) (z : UnforcedLeray.Cyl.Plane) :
    Axi.dS (psiChart ψ) (s, z) = deriv (fun r => ψ r z) s := by
  have hd : DifferentiableAt ℝ (psiChart ψ) ((s, z) : Coord) :=
    (psiChart_contDiffAt_mixed hψ hs).differentiableAt (by simp)
  have hg : HasDerivAt (fun t : ℝ => ((t, z) : Coord)) ((1 : ℝ), ((0 : ℝ), (0 : ℝ))) s :=
    (hasDerivAt_id s).prodMk (hasDerivAt_const s z)
  have hc := hd.hasFDerivAt.comp_hasDerivAt s hg
  have hfun : (psiChart ψ ∘ fun t : ℝ => ((t, z) : Coord)) = fun t => ψ t z := rfl
  rw [hfun] at hc
  exact hc.deriv.symm

/-- The chart derivative `∂_s Ψ` in the spatial directions `(0,v)` is the plane derivative
of the slice `z' ↦ ∂_sΨ(s,z')`. -/
private lemma dS_fderiv_mixed {ψ : ℝ → UnforcedLeray.Cyl.Plane → ℝ}
    (hψ : ContDiffOn ℝ ∞ (psiChart ψ) (Ioi (0 : ℝ) ×ˢ (univ : Set UnforcedLeray.Cyl.Plane)))
    {s : ℝ} (hs : 0 < s) (z v : UnforcedLeray.Cyl.Plane) :
    fderiv ℝ (Axi.dS (psiChart ψ)) ((s, z) : Coord) (0, v) =
      fderiv ℝ (fun z' => Axi.dS (psiChart ψ) ((s, z') : Coord)) z v := by
  have hC : ContDiffAt ℝ ∞ (psiChart ψ) ((s, z) : Coord) :=
    psiChart_contDiffAt_mixed hψ hs
  have hC2 : ContDiffAt ℝ 2 (psiChart ψ) ((s, z) : Coord) := hC.of_le (by simp)
  have hD : ContDiffAt ℝ 1 (fderiv ℝ (psiChart ψ)) ((s, z) : Coord) :=
    hC2.fderiv_right (m := 1) (by norm_num)
  have e2 : Axi.dS (psiChart ψ) = fun y : Coord => fderiv ℝ (psiChart ψ) y (1, (0, 0)) := rfl
  have hdS : ContDiffAt ℝ 1 (fun y : Coord => fderiv ℝ (psiChart ψ) y (1, (0, 0)))
      ((s, z) : Coord) :=
    hD.clm_apply contDiffAt_const
  have hdSD : DifferentiableAt ℝ (Axi.dS (psiChart ψ)) ((s, z) : Coord) := by
    rw [e2]
    exact hdS.differentiableAt (by norm_num)
  have hι : HasFDerivAt (fun z' : UnforcedLeray.Cyl.Plane => ((s, z') : Coord))
      (ContinuousLinearMap.inr ℝ ℝ UnforcedLeray.Cyl.Plane) z := by
    have h := (hasFDerivAt_const (𝕜 := ℝ) s z).prodMk (hasFDerivAt_id (𝕜 := ℝ) z)
    refine h.congr_fderiv (ContinuousLinearMap.ext fun w => ?_)
    simp
  have hc := hdSD.hasFDerivAt.comp z hι
  have hfun : (Axi.dS (psiChart ψ) ∘ fun z' : UnforcedLeray.Cyl.Plane => ((s, z') : Coord)) =
      fun z' => Axi.dS (psiChart ψ) ((s, z') : Coord) := rfl
  rw [hfun] at hc
  rw [hc.fderiv]
  rfl

private lemma abs_apply_le_norm_mixed (L : UnforcedLeray.Cyl.Plane →L[ℝ] ℝ)
    (v : UnforcedLeray.Cyl.Plane) (hv : ‖v‖ ≤ 1) : |L v| ≤ ‖L‖ := by
  rw [← Real.norm_eq_abs]
  calc ‖L v‖ ≤ ‖L‖ * ‖v‖ := L.le_opNorm v
    _ ≤ ‖L‖ * 1 := mul_le_mul_of_nonneg_left hv (norm_nonneg _)
    _ = ‖L‖ := mul_one _

theorem raisedJetMixed_proof : UnforcedLeray.Short.IIb.RaisedJetMixed := by
  intro ψ hψ x hx
  obtain ⟨s, z⟩ := x
  have hs : (0 : ℝ) < s := hx
  -- the age jet `ageJet 1 1` is the plane derivative of the slice `z' ↦ ∂_r ψ(r,z')|_{r=s}`
  have hfun : (fun z' : UnforcedLeray.Cyl.Plane => iteratedDeriv 1 (fun r => ψ r z') s) =
      fun z' => Axi.dS (psiChart ψ) ((s, z') : Coord) := by
    funext z'
    rw [iteratedDeriv_one]
    exact (dS_slice_mixed hψ hs z').symm
  have hn : ‖ageJet 1 1 ψ s z‖ =
      ‖fderiv ℝ (fun z' => Axi.dS (psiChart ψ) ((s, z') : Coord)) z‖ := by
    rw [norm_ageJet_one_mixed, hfun]
  have hv1 : ‖((1 : ℝ), (0 : ℝ))‖ ≤ 1 := by
    rw [Prod.norm_def]; simp
  have hv2 : ‖((0 : ℝ), (1 : ℝ))‖ ≤ 1 := by
    rw [Prod.norm_def]; simp
  refine ⟨?_, ?_⟩
  · show |fderiv ℝ (Axi.dS (psiChart ψ)) ((s, z) : Coord) (0, ((1 : ℝ), (0 : ℝ)))| ≤
      ‖ageJet 1 1 ψ s z‖
    rw [hn, dS_fderiv_mixed hψ hs z ((1 : ℝ), (0 : ℝ))]
    exact abs_apply_le_norm_mixed _ _ hv1
  · show |fderiv ℝ (Axi.dS (psiChart ψ)) ((s, z) : Coord) (0, ((0 : ℝ), (1 : ℝ)))| ≤
      ‖ageJet 1 1 ψ s z‖
    rw [hn, dS_fderiv_mixed hψ hs z ((0 : ℝ), (1 : ℝ))]
    exact abs_apply_le_norm_mixed _ _ hv2

end UnforcedLeray.Short.IIb
