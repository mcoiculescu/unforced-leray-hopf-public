import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T18_2_4_1_3_1

/-!
# Part III-a, task `PartIII-a:T18/2/4/1/3/2` (leaf B): `Δw = ∫_{r>0} B(r) dr`

Target: `duhEqLap : DuhEqLap`. Source: `the November 2 reference manuscript`,
lines 3427-3440. Proof: `duhamelHeat ν h = duhFd ν h`; the spatial partial derivatives of
`duhFd ν g` are `duhFd ν (∂_{e_j} g)` (`Sub/PartIII-a_T18_2_4_1_3_1.lean`); so the Laplacian is
`duhFd ν T` with `T = ∂_{e_0}² h + ∂_{e_1}² h` a nice scalar, whose slice integrals are `duhLap`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology UnforcedLeray.Axi UnforcedLeray.Blueprint.Planar
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

/-- The spatial direction `e_j` in `ℝ × (ℝ × ℝ)`. -/
def duhEj (j : Fin 2) : ℝ × (ℝ × ℝ) := ((0 : ℝ), B0579.dir j)

theorem duhLap_add {c : ℝ} {f g : ℝ × (ℝ × ℝ) → ℂ} (hf : NiceScalar c f) (hg : NiceScalar c g) :
    NiceScalar c (fun q => f q + g q) := by
  obtain ⟨hsf, hpf, a, B, R, ha, hvf⟩ := hf
  obtain ⟨hsg, hpg, a', B', R', ha', hvg⟩ := hg
  refine ⟨hsf.add hsg, fun s x => by
    show f (s, (x.1 + c, x.2)) + g (s, (x.1 + c, x.2)) = f (s, x) + g (s, x)
    rw [hpf, hpg], min a a', max B B', max R R',
    lt_min ha ha', fun s x hx => ?_⟩
  have h1 : (s < a ∨ B < s ∨ R < |x.2|) := by
    rcases hx with h | h | h
    · exact Or.inl (lt_of_lt_of_le h (min_le_left _ _))
    · exact Or.inr (Or.inl (lt_of_le_of_lt (le_max_left _ _) h))
    · exact Or.inr (Or.inr (lt_of_le_of_lt (le_max_left _ _) h))
  have h2 : (s < a' ∨ B' < s ∨ R' < |x.2|) := by
    rcases hx with h | h | h
    · exact Or.inl (lt_of_lt_of_le h (min_le_right _ _))
    · exact Or.inr (Or.inl (lt_of_le_of_lt (le_max_right _ _) h))
    · exact Or.inr (Or.inr (lt_of_le_of_lt (le_max_right _ _) h))
  show f (s, x) + g (s, x) = 0
  rw [hvf s x h1, hvg s x h2, add_zero]

theorem duhLap_pd {g : ℝ × (ℝ × ℝ) → ℂ} (hg : ContDiff ℝ ∞ g) (j : Fin 2) (t : ℝ) :
    pdC j (fun y : ℝ × ℝ => g (t, y)) = fun y => duhDir (duhEj j) g (t, y) := by
  funext y
  unfold pdC duhDir duhEj
  have h1 : HasFDerivAt (fun y' : ℝ × ℝ => ((t, y') : ℝ × (ℝ × ℝ)))
      (ContinuousLinearMap.inr ℝ ℝ (ℝ × ℝ)) y := hasFDerivAt_prodMk_right t y
  have h2 := ((hg.differentiable (by simp)) (t, y)).hasFDerivAt.comp y h1
  rw [show fderiv ℝ (fun y' : ℝ × ℝ => g (t, y')) y = _ from h2.fderiv]
  simp

theorem duhLap_pdW {c ν : ℝ} {g : ℝ × (ℝ × ℝ) → ℂ} (hc : 0 < c) (hν : 0 < ν) (hg : NiceScalar c g)
    (j : Fin 2) (s : ℝ) :
    pdC j (fun y : ℝ × ℝ => duhFd ν g (s, y)) = fun y => duhFd ν (duhDir (duhEj j) g) (s, y) := by
  funext y
  unfold pdC
  have h1 : HasFDerivAt (fun y' : ℝ × ℝ => ((s, y') : ℝ × (ℝ × ℝ)))
      (ContinuousLinearMap.inr ℝ ℝ (ℝ × ℝ)) y := hasFDerivAt_prodMk_right s y
  have h2 := (duhFd_differentiable hc hν hg (s, y)).hasFDerivAt.comp y h1
  rw [show fderiv ℝ (fun y' : ℝ × ℝ => duhFd ν g (s, y')) y = _ from h2.fderiv]
  simp only [ContinuousLinearMap.coe_comp, Function.comp_apply, ContinuousLinearMap.inr_apply]
  have := duhFd_fderiv_apply hc hν hg (s, y) (duhEj j)
  unfold duhEj at this
  exact this

theorem duhEqLap : UnforcedLeray.Short.IIIa.DuhEqLap := by
  intro c ν h hc hν hn s x
  have hD0 := duhDir_nice hn (duhEj 0)
  have hD1 := duhDir_nice hn (duhEj 1)
  have hDD0 := duhDir_nice hD0 (duhEj 0)
  have hDD1 := duhDir_nice hD1 (duhEj 1)
  set T : ℝ × (ℝ × ℝ) → ℂ := fun q => duhDir (duhEj 0) (duhDir (duhEj 0) h) q
    + duhDir (duhEj 1) (duhDir (duhEj 1) h) q with hT
  have hTn : NiceScalar c T := duhLap_add hDD0 hDD1
  -- slices
  have hslice : ∀ r, duhLap ν h s x r = ∫ z : ℝ × ℝ,
      ((UnforcedLeray.B0284.heatKernel2 (ν * r) z : ℝ) : ℂ) *
        T (s - r, (x.1 - z.1, x.2 - z.2)) := by
    intro r
    unfold duhLap
    refine integral_congr_ae (Eventually.of_forall fun z => ?_)
    have e : lapC (fun y => h (s - r, y)) (x.1 - z.1, x.2 - z.2) =
        T (s - r, (x.1 - z.1, x.2 - z.2)) := by
      unfold lapC
      rw [duhLap_pd hn.1 0 (s - r), duhLap_pd hn.1 1 (s - r), duhLap_pd hD0.1 0 (s - r),
        duhLap_pd hD1.1 1 (s - r)]
    beta_reduce
    rw [e]
  have hfun : (fun r => duhLap ν h s x r) = fun r => ∫ z : ℝ × ℝ,
      ((UnforcedLeray.B0284.heatKernel2 (ν * r) z : ℝ) : ℂ) *
        T (s - r, (x.1 - z.1, x.2 - z.2)) := funext hslice
  rw [hfun]
  refine ⟨duhFd_slice_integrable hc hν hTn s x, ?_⟩
  have hint : ∫ r in Ioi (0 : ℝ), ∫ z : ℝ × ℝ,
      ((UnforcedLeray.B0284.heatKernel2 (ν * r) z : ℝ) : ℂ) *
        T (s - r, (x.1 - z.1, x.2 - z.2)) = duhamelHeat ν T s x := rfl
  rw [hint, duhFd_eq hc hν hTn (s, x)]
  -- the Laplacian of the Duhamel solution
  have hw : (fun y : ℝ × ℝ => duhamelHeat ν h s y) = fun y => duhFd ν h (s, y) :=
    funext fun y => duhFd_eq hc hν hn (s, y)
  rw [hw]
  unfold lapC
  rw [duhLap_pdW hc hν hn 0, duhLap_pdW hc hν hn 1]
  have hq0 : pdC 0 (fun y : ℝ × ℝ => duhFd ν (duhDir (duhEj 0) h) (s, y)) =
      fun y => duhFd ν (duhDir (duhEj 0) (duhDir (duhEj 0) h)) (s, y) :=
    duhLap_pdW hc hν hD0 0 s
  have hq1 : pdC 1 (fun y : ℝ × ℝ => duhFd ν (duhDir (duhEj 1) h) (s, y)) =
      fun y => duhFd ν (duhDir (duhEj 1) (duhDir (duhEj 1) h)) (s, y) :=
    duhLap_pdW hc hν hD1 1 s
  rw [hq0, hq1]
  -- additivity
  obtain ⟨M0, hM0⟩ := duhFd_bdd hc hDD0
  obtain ⟨M1, hM1⟩ := duhFd_bdd hc hDD1
  have i0 := duhSm_int_mul hν hDD0 M0 hM0 (s, x)
  have i1 := duhSm_int_mul hν hDD1 M1 hM1 (s, x)
  unfold duhFd
  rw [← integral_add i0 i1]
  refine integral_congr_ae (Eventually.of_forall fun α => ?_)
  simp only [hT]
  ring

end UnforcedLeray.Short.IIIa
