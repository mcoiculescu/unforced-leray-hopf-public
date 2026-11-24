import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c3_2_1_1_org3_b_L3.EigenLeaf.Core
import UnforcedLeray.Short.PartI.Tasks.EulerComplementJ0.XjM0Bridge

/-!
# Helpers for the planar relative bound (SP 2926-2935, 2976-2980)

Source: `the November 2 reference manuscript` (SP) 2926-2935 (the planar limit
`𝒬(𝓛-γ)𝒬 - 𝒫`, the horizontal mean and every angular sector), 2976-2980.

* `planarProj_ae_seedProjFun`: `𝒫 f = seedProjFun h f` a.e. for every seed profile `h` realizing
  `e₀, e₁` (the pairings read the sectors `±2`, `EigenLeafAux.planarEll_sector`).
* `planarProj_secEmb_eq_zero`, `secProf_zero_planarProj`: `𝒫` vanishes on the sectors `n ≠ ±2`
  and its range has no sector-`0` part.
* `one_le_of_seedCtx`: `C₀ ≥ 1`, from `SeedCtx` at `t = 0` on the sector-`1` vector `h(r)e^{iϑ}`.
* `inner_secEmb_zero_of`: the sector `0` is orthogonal to every field without sector-`0` part.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ContDiff ComplexConjugate InnerProductSpace

namespace UnforcedLeray.Short.IIIa.PlanarDysonL3.RelBoundAux

open UnforcedLeray.Short.IIIa.BlockPropagatorInteriorSub.OrgSplit
open UnforcedLeray.Short.IIIa.BlockPropagatorInteriorSub.OrgSplit3
open UnforcedLeray.Short.IIIa.BlockPropagatorInteriorSub.OrgSplit3.PlanarB
open EigenLeafAux

/-- `𝒫 f = ℓ(f₂) q + \overline{ℓ(\overline{f_{-2}})} q̄` a.e. (SP 601-604, 2926-2927). -/
theorem planarProj_ae_seedProjFun (κ : PlanarFrameKernels) (hκ : IsSeedKernels κ) {m : ℝ}
    (hm : 1 < m) {lam : ℂ} {h : ℝ → ℂ} {hh : MemLp h 2 B0010.xGMeasure}
    {ℓ : B0010.XG →L[ℂ] ℂ} (hs : PartI.IsSeedXG lam (hh.toLp h) ℓ)
    (he0 : ∀ y, κ.e 0 y = PartI.seedPlanar h (planeToC y))
    (he1 : ∀ y, κ.e 1 y = conj (PartI.seedPlanar h (planeToC y)))
    (f : Planar.L2w m) {F : ℂ → ℂ} (hF : ⇑f =ᵐ[volume] F) :
    ⇑(planarProj κ hm f) =ᵐ[volume] fun y => PartI.seedProjFun h F y := by
  obtain ⟨Λ, hΛ, hL0, hL1⟩ := planarEll_sector κ hκ hm hs he0
  have hsec := Planar.NUE.Ang.ParsevalH.ae_angularSector_eq hF
  have hv0 : planarEll κ hm 0 f = PartI.seedEll h (Planar.NUE.Polar.angularSector F 2) := by
    rw [hL0, hΛ]
    refine (PartI.seedEll_congr_prof m (PartI.coeFn_secProf m 2 f)).trans
      (PartI.seedEll_congr ?_)
    filter_upwards [hsec] with r hr
    exact hr 2
  have hv1 : planarEll κ hm 1 f =
      conj (PartI.seedEll h (fun r => conj (Planar.NUE.Polar.angularSector F (-2) r))) := by
    rw [hL1, PartI.starFunctional_apply, hΛ]
    congr 1
    refine (PartI.seedEll_congr_prof m (Planar.coeFn_star_prof _)).trans
      (PartI.seedEll_congr ?_)
    have h3 := (Planar.ac_profileMeasure m).ae_le (PartI.coeFn_secProf m (-2) f)
    filter_upwards [h3, hsec] with r a b
    rw [a, b (-2)]
  rw [planarProj_apply, Fin.sum_univ_two]
  filter_upwards [(Planar.volume_ac m).ae_le (Lp.coeFn_add (planarEll κ hm 0 f • planarE κ m 0)
      (planarEll κ hm 1 f • planarE κ m 1)),
    (Planar.volume_ac m).ae_le (Lp.coeFn_smul (planarEll κ hm 0 f) (planarE κ m 0)),
    (Planar.volume_ac m).ae_le (Lp.coeFn_smul (planarEll κ hm 1 f) (planarE κ m 1)),
    coeFn_planarE_vol κ m 0, coeFn_planarE_vol κ m 1] with y a b c d e
  rw [a, Pi.add_apply, b, c, Pi.smul_apply, Pi.smul_apply, d, e, smul_eq_mul, smul_eq_mul, hv0,
    hv1, he0, he1, planeToC_cToPlane]
  rfl

theorem planarProj_secEmb_eq_zero (κ : PlanarFrameKernels) (hκ : IsSeedKernels κ) {m : ℝ}
    (hm : 1 < m) {lam : ℂ} {h : ℝ → ℂ} {hh : MemLp h 2 B0010.xGMeasure}
    {ℓ : B0010.XG →L[ℂ] ℂ} (hs : PartI.IsSeedXG lam (hh.toLp h) ℓ)
    (he0 : ∀ y, κ.e 0 y = PartI.seedPlanar h (planeToC y))
    (v : Planar.ProfL2 m) {n : ℤ} (h2 : n ≠ 2) (hm2 : n ≠ -2) :
    planarProj κ hm (Planar.secEmb m n v) = 0 := by
  obtain ⟨Λ, -, hL0, hL1⟩ := planarEll_sector κ hκ hm hs he0
  rw [planarProj_apply, Fin.sum_univ_two, hL0, hL1, Planar.secProf_secEmb,
    Planar.secProf_secEmb, if_neg h2, if_neg hm2, map_zero, map_zero, zero_smul, zero_smul,
    add_zero]

theorem secProf_zero_planarProj (κ : PlanarFrameKernels) {m : ℝ} (hm : 1 < m) {h : ℝ → ℂ}
    {hh : MemLp h 2 B0010.xGMeasure}
    (he0 : ∀ y, κ.e 0 y = PartI.seedPlanar h (planeToC y))
    (he1 : ∀ y, κ.e 1 y = conj (PartI.seedPlanar h (planeToC y))) (f : Planar.L2w m) :
    Planar.secProf m 0 (planarProj κ hm f) = 0 := by
  have hwh := seedProfile_ae hm hh
  rw [planarProj_apply, Fin.sum_univ_two, map_add, map_smul, map_smul,
    planarE_zero_eq κ hwh he0, planarE_one_eq κ hwh he1, Planar.secProf_secEmb,
    Planar.secProf_secEmb, if_neg (by decide), if_neg (by decide), smul_zero, smul_zero,
    add_zero]

theorem norm_ofReal_exp_smul {m : ℝ} (r : ℝ) (v : Planar.L2w m) :
    ‖((Real.exp r : ℝ) : ℂ) • v‖ = Real.exp r * ‖v‖ := by
  rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]

/-- The sector `0` is orthogonal to every field without sector-`0` part. -/
theorem inner_secEmb_zero_of {m : ℝ} (v : Planar.ProfL2 m) {y : Planar.L2w m}
    (hy : Planar.secProf m 0 y = 0) : ⟪Planar.secEmb m 0 v, y⟫_ℂ = 0 := by
  have h1 : Planar.secEmb m 0 v = Planar.sectorProjW m 0 (Planar.secEmb m 0 v) := by
    rw [← Planar.secEmb_secProf, Planar.secProf_secEmb_self]
  rw [h1, Planar.inner_sectorProjW, ← Planar.secEmb_secProf m 0 y, hy, map_zero,
    inner_zero_right]

/-- **`C₀ ≥ 1`** from `SeedCtx` at `t = 0`, tested on the sector-`1` field `h(r)e^{iϑ}` (zero mass,
`𝒫 = 0`). -/
theorem one_le_of_seedCtx (κ : PlanarFrameKernels) (hκ : IsSeedKernels κ)
    (P : UnforcedLeray.Blueprint.Planar.PlanarData) {m : ℝ} (hm : 1 < m) {C₀ h : ℝ}
    (hctx : SeedCtx κ P m C₀ h) : 1 ≤ C₀ := by
  obtain ⟨lam₁, h₁, hh₁, ℓ₁, hs₁, he0₁, he1₁, -, hdec⟩ := hctx
  have hw0 : PartI.xgEmbM hm (hh₁.toLp h₁) ≠ 0 := fun h0 =>
    hs₁.ne_zero (PartI.xgEmbM_injective hm h0)
  set f' : Planar.L2w m := Planar.secEmb m 1 (PartI.xgEmbM hm (hh₁.toLp h₁)) with hf'
  have hf'X : f' ∈ Planar.X0 hm := Planar.massCLM_secEmb hm one_ne_zero _
  have hf'pos : 0 < ‖f'‖ := by
    rw [hf', LinearIsometry.norm_map]
    exact norm_pos_iff.2 hw0
  have hPf' : planarProj κ hm f' = 0 :=
    planarProj_secEmb_eq_zero κ hκ hm hs₁ he0₁ _ (by decide) (by decide)
  obtain ⟨g₀, hg₀v, hg₀n⟩ := (PartI.xjM0Bridge m hm).2 ⟨f', hf'X⟩
  obtain ⟨u, g, hu, hg, hb⟩ := hdec hm 0 le_rfl g₀
  have hsp := planarProj_ae_seedProjFun κ hκ hm hs₁ he0₁ he1₁ f' hg₀v.symm
  rw [hPf'] at hsp
  have hu' : u = f' := by
    apply Lp.ext
    refine (Planar.wMeasure_ac m).ae_le ?_
    filter_upwards [hu, hg₀v, hsp,
      (Planar.volume_ac m).ae_le (Lp.coeFn_zero ℂ 2 (Planar.wMeasure m))] with y a b c d
    rw [a, b, ← c, d, Pi.zero_apply, sub_zero]
  have hgv : ((g : B0008.HjM 0 m).value : Planar.L2w m) = f' := by
    have e : ((g : B0008.HjM 0 m).value : Planar.L2w m) = Planar.eulerGroupW hm 0 u :=
      Lp.ext ((B0008.wMeasure_ac m).ae_le hg)
    rw [e, Planar.eulerGroupW_zero, ContinuousLinearMap.one_apply, hu']
  have hgn : ‖g‖ = ‖f'‖ := by
    rw [← hgv]
    exact PartI.xjM0_norm_eq_value _
  have hg₀n' : ‖g₀‖ = ‖f'‖ := hg₀n
  simp only [mul_zero, Real.exp_zero, one_mul, mul_one] at hb
  rw [hgn, hg₀n'] at hb
  exact (le_mul_iff_one_le_left hf'pos).1 hb

end UnforcedLeray.Short.IIIa.PlanarDysonL3.RelBoundAux
