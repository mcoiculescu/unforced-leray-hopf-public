import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_asrc_ra_5

/-!
# `PartIII-b:C/asrc/ra/5/7` : joint `C²` regularity of `h_A` coefficient from `h^p_A` and `ψ^p_A`

Source 4979-4980.  For `s > 0`, `ĥ_A = √s [(h^p_A)_r e_r + ((h^p_A)_z + ε(1 - 𝒦)ψ^p_A) e_z]`, so
`b = s^{-1/2} ĥ_A` is the meridional vector `(h^p_A)_1, (h^p_A)_2 + ε(ψ^p_A - 𝒦ψ^p_A)`.
The operator `𝒦ψ = η ∂_η ψ + 2 s ∂_s ψ` is `C²` because `ψ^p_A` is `C³` jointly on `s > 0`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- The `η`-slice derivative of a joint function, as a directional derivative. -/
theorem slice_eta_fderiv (g : ℝ × (ℝ × ℝ) → ℝ) (s : ℝ) (x : ℝ × ℝ)
    (hg : DifferentiableAt ℝ g (s, x)) (v : ℝ × ℝ) :
    fderiv ℝ (fun y : ℝ × ℝ => g (s, y)) x v = fderiv ℝ g (s, x) (0, v) := by
  have h1 : HasFDerivAt (fun y : ℝ × ℝ => ((s : ℝ), y))
      (ContinuousLinearMap.inr ℝ ℝ (ℝ × ℝ)) x :=
    hasFDerivAt_prodMk_right s x
  have h2 : HasFDerivAt (fun y : ℝ × ℝ => g (s, y))
      ((fderiv ℝ g (s, x)).comp (ContinuousLinearMap.inr ℝ ℝ (ℝ × ℝ))) x :=
    hg.hasFDerivAt.comp x h1
  rw [h2.fderiv]
  rfl

/-- The `s`-slice derivative of a joint function, as a directional derivative. -/
theorem slice_t_deriv (g : ℝ × (ℝ × ℝ) → ℝ) (s : ℝ) (x : ℝ × ℝ)
    (hg : DifferentiableAt ℝ g (s, x)) :
    deriv (fun t : ℝ => g (t, x)) s = fderiv ℝ g (s, x) (1, 0) := by
  have h1 : HasDerivAt (fun t : ℝ => (t, x)) ((1 : ℝ), ((0 : ℝ), (0 : ℝ))) s :=
    (hasDerivAt_id' s).prodMk (hasDerivAt_const s x)
  have h2 : HasDerivAt (fun t : ℝ => g (t, x)) (fderiv ℝ g (s, x) (1, 0)) s :=
    hg.hasFDerivAt.comp_hasDerivAt s h1
  exact h2.deriv

/-- The operator `p ↦ η ∂_η ψ + 2 s ∂_s ψ` of a joint `C³` function is `C²` on `s > 0`. -/
theorem kop_C2_of (g : ℝ × (ℝ × ℝ) → ℝ)
    (hg : ContDiffOn ℝ 3 g (Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ)))) :
    ContDiffOn ℝ 2
      (fun p : ℝ × (ℝ × ℝ) => p.2.2 * fderiv ℝ g p (0, ei 1) + 2 * p.1 * fderiv ℝ g p (1, 0))
      (Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))) := by
  have hUo : IsOpen (Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))) := isOpen_Ioi.prod isOpen_univ
  have hDg : ContDiffOn ℝ 2 (fun p : ℝ × (ℝ × ℝ) => fderiv ℝ g p)
      (Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))) :=
    hg.fderiv_of_isOpen hUo (by norm_num)
  have h1 : ContDiffOn ℝ 2 (fun p : ℝ × (ℝ × ℝ) => fderiv ℝ g p (0, ei 1))
      (Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))) :=
    hDg.clm_apply contDiffOn_const
  have h2 : ContDiffOn ℝ 2 (fun p : ℝ × (ℝ × ℝ) => fderiv ℝ g p (1, 0))
      (Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))) :=
    hDg.clm_apply contDiffOn_const
  have hc1 : ContDiffOn ℝ 2 (fun p : ℝ × (ℝ × ℝ) => p.2.2)
      (Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))) := by fun_prop
  have hc2 : ContDiffOn ℝ 2 (fun p : ℝ × (ℝ × ℝ) => p.1)
      (Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))) := by fun_prop
  exact (hc1.mul h1).add ((contDiffOn_const.mul hc2).mul h2)

theorem affHCoefC2_of_hp_psip (as : ℝ) (χf : ℝ → ℝ) (h1 : HpAC2 as χf) (h2 : PsipAC3 as χf) :
    AffHCoefC2 as χf := by
  unfold AffHCoefC2
  intro hχ ν ε hν A hA
  have hUo : IsOpen (Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))) := isOpen_Ioi.prod isOpen_univ
  have hHp : ContDiffOn ℝ 2 (fun p : ℝ × (ℝ × ℝ) => hpA ν χf A p.1 p.2)
      (Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))) :=
    h1 hχ ν hν A hA
  have hg : ContDiffOn ℝ 3 (fun p : ℝ × (ℝ × ℝ) => psipA ν χf A p.1 p.2)
      (Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))) :=
    h2 hχ ν hν A hA
  have hdiff : ∀ p ∈ (Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))),
      DifferentiableAt ℝ (fun p : ℝ × (ℝ × ℝ) => psipA ν χf A p.1 p.2) p :=
    fun p hp => (hg.differentiableOn (by norm_num)).differentiableAt (hUo.mem_nhds hp)
  have hKeq : ∀ p ∈ (Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))),
      Kop (fun s' y => psipA ν χf A s' y) p.1 p.2 =
        p.2.2 * fderiv ℝ (fun p : ℝ × (ℝ × ℝ) => psipA ν χf A p.1 p.2) p (0, ei 1)
          + 2 * p.1 * fderiv ℝ (fun p : ℝ × (ℝ × ℝ) => psipA ν χf A p.1 p.2) p (1, 0) := by
    intro p hp
    have hd := hdiff p hp
    have e1 : fderiv ℝ (fun y : ℝ × ℝ => psipA ν χf A p.1 y) p.2 (ei 1) =
        fderiv ℝ (fun p : ℝ × (ℝ × ℝ) => psipA ν χf A p.1 p.2) p (0, ei 1) :=
      slice_eta_fderiv (fun p : ℝ × (ℝ × ℝ) => psipA ν χf A p.1 p.2) p.1 p.2 hd (ei 1)
    have e2 : deriv (fun t : ℝ => psipA ν χf A t p.2) p.1 =
        fderiv ℝ (fun p : ℝ × (ℝ × ℝ) => psipA ν χf A p.1 p.2) p (1, 0) :=
      slice_t_deriv (fun p : ℝ × (ℝ × ℝ) => psipA ν χf A p.1 p.2) p.1 p.2 hd
    show p.2.2 * fderiv ℝ (fun y : ℝ × ℝ => psipA ν χf A p.1 y) p.2 (ei 1)
        + 2 * p.1 * deriv (fun t : ℝ => psipA ν χf A t p.2) p.1 = _
    rw [e1, e2]
  have hKC : ContDiffOn ℝ 2 (fun p : ℝ × (ℝ × ℝ) => Kop (fun s' y => psipA ν χf A s' y) p.1 p.2)
      (Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))) :=
    (kop_C2_of _ (hg.of_le (by norm_num))).congr (fun p hp => hKeq p hp)
  have ha : ContDiffOn ℝ 2 (fun p : ℝ × (ℝ × ℝ) => (hpA ν χf A p.1 p.2).1)
      (Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))) :=
    contDiff_fst.comp_contDiffOn hHp
  have hb : ContDiffOn ℝ 2 (fun p : ℝ × (ℝ × ℝ) =>
      (hpA ν χf A p.1 p.2).2 + ε * (psipA ν χf A p.1 p.2 -
        Kop (fun s' y => psipA ν χf A s' y) p.1 p.2))
      (Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))) :=
    (contDiff_snd.comp_contDiffOn hHp).add
      (contDiffOn_const.mul ((hg.of_le (by norm_num)).sub hKC))
  have hΦ : ContDiffOn ℝ 2 (fun p : ℝ × (ℝ × ℝ) =>
      (![(hpA ν χf A p.1 p.2).1, (hpA ν χf A p.1 p.2).2 + ε * (psipA ν χf A p.1 p.2 -
        Kop (fun s' y => psipA ν χf A s' y) p.1 p.2)] : Fin 2 → ℝ))
      (Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))) := by
    apply contDiffOn_pi.2
    intro i
    fin_cases i
    · exact ha
    · exact hb
  have hF := (EuclideanSpace.equiv (Fin 2) ℝ).symm.contDiff.comp_contDiffOn hΦ
  refine hF.congr ?_
  intro p hp
  have hs : 0 < p.1 := hp.1
  unfold hAcoef hhatA
  rw [smul_smul, inv_mul_cancel₀ (Real.sqrt_pos.2 hs).ne', one_smul]
  rfl

end UnforcedLeray.Short.PartIIIb.Concrete
