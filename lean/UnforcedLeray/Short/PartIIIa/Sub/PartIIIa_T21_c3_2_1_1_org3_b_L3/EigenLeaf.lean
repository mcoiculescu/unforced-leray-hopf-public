import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c3_2_1_1_org3_b_L3.EigenLeaf.Core

/-!
# Leaf D: the planar eigen relations in the Euler group (SP 593-610, 869-878, 2926-2927)

Source: `the November 2 reference manuscript` (SP) 593-610, 869-878, 2926-2927.

`PlanarEigenLeaf κ`: `e^{t𝓛}e_i = e^{λ_i t}e_i` and `ℓ_i(e^{t𝓛}f) = e^{λ_i t}ℓ_i(f)` on `L²_m`.

Proof. `e₀ = q = h(r)e^{2iϑ}` is the sector-`2` embedding of the profile `h`, and `L₀q = λq`
(`IsSeedXG.eigen`) transported by `PartI.xgEmbM_L0` is `𝓛₂ h = λ h`; `e₁ = q̄` is the sector `-2`
embedding of `h̄` with `𝓛₋₂ h̄ = λ̄ h̄` (`Planar.Lsec_star_eigen`). The Euler group acts on sector
`n` by `exp(t𝓛ₙ)`, which multiplies an eigenvector by `e^{zt}`. The pairings read only the sectors
`±2`: `ℓ₀ f = Λ(f₂)`, `ℓ₁ f = \overline{Λ(\overline{f_{-2}})}` (`EigenLeafAux.planarEll_sector`,
density of smooth compactly supported fields), where `Λ` is the bounded extension of the explicit
functional `seedEll h` of `eq:short-seed-functional` (`PartI.seedDualBounded`). `Λ` is a left
eigenfunctional, `Λ 𝓛₂ = λΛ` (on the dense range of `X_G` it is `ℓ`, and `ℓ L₀ = λℓ` because
`P = qℓ` is the Riesz projection, SP 869-878), hence `Λ exp(t𝓛₂) = e^{λt}Λ`; sector `-2` is the
conjugate.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ContDiff ComplexConjugate

namespace UnforcedLeray.Short.IIIa.PlanarDysonL3

open UnforcedLeray.Short.IIIa.BlockPropagatorInteriorSub.OrgSplit3.PlanarB
open EigenLeafAux

theorem seedEigen_zero (lam : ℂ) : seedEigen lam 0 = lam := if_pos rfl

theorem seedEigen_one (lam : ℂ) : seedEigen lam 1 = conj lam := if_neg (by decide)

/-- **Leaf D** (SP 593-610, 869-878, 2926-2927). -/
theorem planarEigenLeaf_proof (κ : UnforcedLeray.Short.IIIa.PlanarFrameKernels) :
    UnforcedLeray.Short.IIIa.PlanarDysonL3.PlanarEigenLeaf κ := by
  intro hκ m hm _hm8 lam h hh ℓ hs he0 i t _ht
  obtain ⟨lam', h', hh', ℓ', hs', he0', he1', hpair⟩ := hκ
  have he1 : ∀ y, κ.e 1 y = conj (PartI.seedPlanar h (planeToC y)) := by
    intro y
    rw [he1', ← he0', he0]
  obtain ⟨Λ, hΛ, hL0, hL1⟩ :=
    planarEll_sector κ ⟨lam', h', hh', ℓ', hs', he0', he1', hpair⟩ hm hs he0
  -- `Λ` is a left eigenfunctional of `𝓛₂`
  have hSF := PartI.seedFunctional_proof lam h hh ℓ hs
  have hΛe : ∀ f, Λ (PartI.xgEmbM hm f) = ℓ f := by
    intro f
    rw [hΛ, hSF.2.2.2.1 f]
    exact PartI.seedEll_congr_prof m (PartI.coeFn_xgEmbM hm f)
  have hℓL : ∀ f, ℓ (Planar.L0 f) = lam * ℓ f :=
    PartI.eigenfunctional_of_rankOne hs.ne_zero hs.proj.proj_mul
  have hΛL : ∀ v, Λ (Planar.Lsec hm 2 v) = lam * Λ v := by
    have hF1 : ⇑(Λ.comp (Planar.Lsec hm 2)) = ⇑(lam • Λ) := by
      refine DenseRange.equalizer (PartI.xgEmbDense m hm) (Λ.comp (Planar.Lsec hm 2)).continuous
        (lam • Λ).continuous ?_
      funext f
      simp only [Function.comp_apply, ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.smul_apply, smul_eq_mul]
      rw [← PartI.xgEmbM_L0, hΛe, hΛe, hℓL]
    intro v
    have := congrFun hF1 v
    simpa using this
  have hΛmL : ∀ v, PartI.starFunctional Λ (Planar.Lsec hm (-2) v) =
      conj lam * PartI.starFunctional Λ v := by
    intro v
    have h1 := Planar.Lsec_star hm 2 (star v)
    rw [star_star] at h1
    have h2' : star (Planar.Lsec hm (-2) v) = Planar.Lsec hm 2 (star v) := by
      rw [h1, star_star]
    rw [PartI.starFunctional_apply, PartI.starFunctional_apply, h2', hΛL, map_mul]
  -- the seed vectors
  have hwh := seedProfile_ae hm hh
  have hwL : Planar.Lsec hm 2 (PartI.xgEmbM hm (hh.toLp h)) =
      lam • PartI.xgEmbM hm (hh.toLp h) := seedProfile_eigen hm hs
  have hwmL := Planar.Lsec_star_eigen hm hwL
  have hE0 := planarE_zero_eq κ hwh he0
  have hE1 := planarE_one_eq κ hwh he1
  fin_cases i
  · refine ⟨?_, fun f => ?_⟩
    · show Planar.eulerGroupW hm t (planarE κ m 0) =
        Complex.exp (seedEigen lam 0 * t) • planarE κ m 0
      rw [hE0, seedEigen_zero]
      exact eulerGroupW_secEmb_eigen hm hwL t
    · show planarEll κ hm 0 (Planar.eulerGroupW hm t f) =
        Complex.exp (seedEigen lam 0 * t) * planarEll κ hm 0 f
      rw [seedEigen_zero]
      exact ell_eulerGroupW_of hm _ Λ hL0 hΛL t f
  · refine ⟨?_, fun f => ?_⟩
    · show Planar.eulerGroupW hm t (planarE κ m 1) =
        Complex.exp (seedEigen lam 1 * t) • planarE κ m 1
      rw [hE1, seedEigen_one]
      exact eulerGroupW_secEmb_eigen hm hwmL t
    · show planarEll κ hm 1 (Planar.eulerGroupW hm t f) =
        Complex.exp (seedEigen lam 1 * t) * planarEll κ hm 1 f
      rw [seedEigen_one]
      exact ell_eulerGroupW_of hm _ (PartI.starFunctional Λ) hL1 hΛmL t f

end UnforcedLeray.Short.IIIa.PlanarDysonL3
