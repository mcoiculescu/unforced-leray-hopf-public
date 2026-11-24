import UnforcedLeray.Short.PartIIb.Sub.PartIIb_G4_3_6_2_1

/-!


Zeroth, first and `∂_s²` bounds of the chart partials by the age/space jets `ageJet ℓ j`
(SP 2412-2423). Unit vectors have norm one in the sup norm on `ℝ × ℝ`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology
open scoped ContDiff

open UnforcedLeray.Short.PartI

namespace UnforcedLeray.Short.IIb

private lemma psiChart_contDiffAt_first {ψ : ℝ → UnforcedLeray.Cyl.Plane → ℝ}
    (hψ : ContDiffOn ℝ ∞ (psiChart ψ) (Ioi (0 : ℝ) ×ˢ (univ : Set UnforcedLeray.Cyl.Plane)))
    {y : Coord} (hy : 0 < y.1) : ContDiffAt ℝ ∞ (psiChart ψ) y := by
  have hopen : IsOpen (Ioi (0 : ℝ) ×ˢ (univ : Set UnforcedLeray.Cyl.Plane)) :=
    isOpen_Ioi.prod isOpen_univ
  exact hψ.contDiffAt (hopen.mem_nhds (Set.mk_mem_prod hy (mem_univ _)))

private lemma norm_ageJet_zero_first {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (ℓ : ℕ) (F : ℝ → UnforcedLeray.Cyl.Plane → E) (s : ℝ) (z : UnforcedLeray.Cyl.Plane) :
    ‖ageJet ℓ 0 F s z‖ = ‖iteratedDeriv ℓ (fun r => F r z) s‖ := by
  simp [UnforcedLeray.Short.PartI.ageJet, UnforcedLeray.Train.jet, norm_iteratedFDeriv_zero]

private lemma norm_ageJet_one_first {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (ℓ : ℕ) (F : ℝ → UnforcedLeray.Cyl.Plane → E) (s : ℝ) (z : UnforcedLeray.Cyl.Plane) :
    ‖ageJet ℓ 1 F s z‖ = ‖fderiv ℝ (fun z' => iteratedDeriv ℓ (fun r => F r z') s) z‖ := by
  simp [UnforcedLeray.Short.PartI.ageJet, UnforcedLeray.Train.jet, norm_iteratedFDeriv_one]

/-- `∂_s` of the chart function is the one-variable derivative of the slice. -/
private lemma dS_slice_first {ψ : ℝ → UnforcedLeray.Cyl.Plane → ℝ}
    (hψ : ContDiffOn ℝ ∞ (psiChart ψ) (Ioi (0 : ℝ) ×ˢ (univ : Set UnforcedLeray.Cyl.Plane)))
    {s : ℝ} (hs : 0 < s) (z : UnforcedLeray.Cyl.Plane) :
    Axi.dS (psiChart ψ) (s, z) = deriv (fun r => ψ r z) s := by
  have hd : DifferentiableAt ℝ (psiChart ψ) ((s, z) : Coord) :=
    (psiChart_contDiffAt_first hψ hs).differentiableAt (by simp)
  have hg : HasDerivAt (fun t : ℝ => ((t, z) : Coord)) ((1 : ℝ), ((0 : ℝ), (0 : ℝ))) s :=
    (hasDerivAt_id s).prodMk (hasDerivAt_const s z)
  have hc := hd.hasFDerivAt.comp_hasDerivAt s hg
  have hfun : (psiChart ψ ∘ fun t : ℝ => ((t, z) : Coord)) = fun t => ψ t z := rfl
  rw [hfun] at hc
  exact hc.deriv.symm

/-- The `(0,v)` chart derivative is the derivative of the meridional slice. -/
private lemma fderiv_inr_first {ψ : ℝ → UnforcedLeray.Cyl.Plane → ℝ}
    (hψ : ContDiffOn ℝ ∞ (psiChart ψ) (Ioi (0 : ℝ) ×ˢ (univ : Set UnforcedLeray.Cyl.Plane)))
    {s : ℝ} (hs : 0 < s) (z v : UnforcedLeray.Cyl.Plane) :
    fderiv ℝ (psiChart ψ) ((s, z) : Coord) (0, v) = fderiv ℝ (fun z' => ψ s z') z v := by
  have hd : DifferentiableAt ℝ (psiChart ψ) ((s, z) : Coord) :=
    (psiChart_contDiffAt_first hψ hs).differentiableAt (by simp)
  have hι : HasFDerivAt (fun z' : UnforcedLeray.Cyl.Plane => ((s, z') : Coord))
      (ContinuousLinearMap.inr ℝ ℝ UnforcedLeray.Cyl.Plane) z := by
    have h := (hasFDerivAt_const (𝕜 := ℝ) s z).prodMk (hasFDerivAt_id (𝕜 := ℝ) z)
    refine h.congr_fderiv (ContinuousLinearMap.ext fun w => ?_)
    simp
  have hc := hd.hasFDerivAt.comp z hι
  have hfun : (psiChart ψ ∘ fun z' : UnforcedLeray.Cyl.Plane => ((s, z') : Coord)) =
      fun z' => ψ s z' := rfl
  rw [hfun] at hc
  rw [hc.fderiv]
  rfl

private lemma abs_apply_le_norm_first (L : UnforcedLeray.Cyl.Plane →L[ℝ] ℝ)
    (v : UnforcedLeray.Cyl.Plane) (hv : ‖v‖ ≤ 1) : |L v| ≤ ‖L‖ := by
  rw [← Real.norm_eq_abs]
  calc ‖L v‖ ≤ ‖L‖ * ‖v‖ := L.le_opNorm v
    _ ≤ ‖L‖ * 1 := mul_le_mul_of_nonneg_left hv (norm_nonneg _)
    _ = ‖L‖ := mul_one _

theorem raisedJetFirst_proof : UnforcedLeray.Short.IIb.RaisedJetFirst := by
  intro ψ hψ x hx
  obtain ⟨s, z⟩ := x
  have hs : (0 : ℝ) < s := hx
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- zeroth
    show |ψ s z| ≤ ‖ageJet 0 0 ψ s z‖
    rw [norm_ageJet_zero_first, iteratedDeriv_zero, Real.norm_eq_abs]
  · -- ∂_s
    show |Axi.dS (psiChart ψ) (s, z)| ≤ ‖ageJet 1 0 ψ s z‖
    rw [dS_slice_first hψ hs z, norm_ageJet_zero_first, iteratedDeriv_one, Real.norm_eq_abs]
  · -- ∂_q
    show |Axi.dQ (psiChart ψ) (s, z)| ≤ ‖ageJet 0 1 ψ s z‖
    rw [norm_ageJet_one_first]
    simp only [iteratedDeriv_zero]
    have hv : ‖((1 : ℝ), (0 : ℝ))‖ ≤ 1 := by
      rw [Prod.norm_def]; simp
    have h := fderiv_inr_first hψ hs z ((1 : ℝ), (0 : ℝ))
    unfold Axi.dQ
    rw [h]
    exact abs_apply_le_norm_first _ _ hv
  · -- ∂_η
    show |Axi.dEta (psiChart ψ) (s, z)| ≤ ‖ageJet 0 1 ψ s z‖
    rw [norm_ageJet_one_first]
    simp only [iteratedDeriv_zero]
    have hv : ‖((0 : ℝ), (1 : ℝ))‖ ≤ 1 := by
      rw [Prod.norm_def]; simp
    have h := fderiv_inr_first hψ hs z ((0 : ℝ), (1 : ℝ))
    unfold Axi.dEta
    rw [h]
    exact abs_apply_le_norm_first _ _ hv
  · -- ∂_s² via the chart derivative of `∂_sΨ`
    have hd : DifferentiableAt ℝ (psiChart ψ) ((s, z) : Coord) :=
      (psiChart_contDiffAt_first hψ hs).differentiableAt (by simp)
    -- the function `G y = ∂_r ψ(r, y.2)` at `y.1`
    set G : Coord → ℝ := fun y => deriv (fun r => ψ r y.2) y.1 with hGdef
    have hEq : Axi.dS (psiChart ψ) =ᶠ[𝓝 ((s, z) : Coord)] G := by
      have hopen : IsOpen {y : Coord | 0 < y.1} := isOpen_lt continuous_const continuous_fst
      filter_upwards [hopen.mem_nhds hs] with y hy
      exact dS_slice_first hψ hy y.2
    have hdS1 : DifferentiableAt ℝ (Axi.dS (psiChart ψ)) ((s, z) : Coord) := by
      have hC : ContDiffAt ℝ ∞ (psiChart ψ) ((s, z) : Coord) :=
        psiChart_contDiffAt_first hψ hs
      have hC2 : ContDiffAt ℝ 2 (psiChart ψ) ((s, z) : Coord) := hC.of_le (by simp)
      have hD : ContDiffAt ℝ 1 (fderiv ℝ (psiChart ψ)) ((s, z) : Coord) :=
        hC2.fderiv_right (m := 1) (by norm_num)
      have hdS : ContDiffAt ℝ 1 (fun y : Coord => fderiv ℝ (psiChart ψ) y (1, (0, 0)))
          ((s, z) : Coord) :=
        hD.clm_apply contDiffAt_const
      exact hdS.differentiableAt (by norm_num)
    have hGd : DifferentiableAt ℝ G ((s, z) : Coord) := hEq.differentiableAt_iff.mp hdS1
    have hfd : fderiv ℝ (Axi.dS (psiChart ψ)) ((s, z) : Coord) = fderiv ℝ G ((s, z) : Coord) :=
      hEq.fderiv_eq
    rw [hfd]
    set g : ℝ → ℝ := fun r => ψ r z with hgdef
    have hL : HasDerivAt (fun t : ℝ => ((t, z) : Coord)) ((1 : ℝ), ((0 : ℝ), (0 : ℝ))) s :=
      (hasDerivAt_id s).prodMk (hasDerivAt_const s z)
    have hc := hGd.hasFDerivAt.comp_hasDerivAt s hL
    have hfun : (G ∘ fun t : ℝ => ((t, z) : Coord)) = fun t => deriv g t := rfl
    rw [hfun] at hc
    -- smoothness of `g` and `deriv g` on `(0, ∞)`
    have hgOn : ContDiffOn ℝ ∞ g (Ioi (0 : ℝ)) := by
      intro r hr
      have hr' : (0 : ℝ) < r := hr
      have hcr : ContDiffAt ℝ ∞ (psiChart ψ ∘ fun t : ℝ => ((t, z) : Coord)) r :=
        ContDiffAt.comp r (psiChart_contDiffAt_first (y := ((r, z) : Coord)) hψ hr')
          (contDiffAt_id.prodMk contDiffAt_const)
      exact hcr.contDiffWithinAt
    have hdg : ContDiffOn ℝ 1 (deriv g) (Ioi (0 : ℝ)) :=
      hgOn.deriv_of_isOpen isOpen_Ioi (m := 1) (by norm_num)
    have hdgd : DifferentiableAt ℝ (deriv g) s :=
      (hdg.differentiableOn (by norm_num)).differentiableAt (isOpen_Ioi.mem_nhds hs)
    have hdd : HasDerivAt (deriv g) (deriv (deriv g) s) s := hdgd.hasDerivAt
    have hc' : HasDerivAt (deriv g) (fderiv ℝ G ((s, z) : Coord) ((1 : ℝ), ((0 : ℝ), (0 : ℝ)))) s :=
      hc
    have hval := hc'.unique hdd
    have hit : iteratedDeriv 2 g s = deriv (deriv g) s := by
      rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one]
    show |fderiv ℝ G ((s, z) : Coord) ((1 : ℝ), ((0 : ℝ), (0 : ℝ)))| ≤ ‖ageJet 2 0 ψ s z‖
    rw [hval, ← hit, ← Real.norm_eq_abs, norm_ageJet_zero_first]

end UnforcedLeray.Short.IIb
