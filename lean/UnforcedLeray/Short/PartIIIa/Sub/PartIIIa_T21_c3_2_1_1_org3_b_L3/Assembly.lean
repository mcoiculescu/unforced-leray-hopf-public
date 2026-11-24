import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c3_2_1_1_org3_b_L3.Dyson

/-!
# Leaf B3: the planar relative evolution (SP 2926-2935, 2976-2980), reduced to two Part I leaves

Source: `the November 2 reference manuscript` (SP) 2926-2935, 2976-2980.

Proved here and in `PartIII-a_T21_c3_2_1_1_org3_b_L3/` (complete proofs):
* `Objects`: `planarE κ m i ∈ L²_m` (the growing vectors `e_i`, Gaussian tails), the bounded planar
  pairings `planarEll κ hm i = ∫ λ_i ·`, `planarProj = Σ ℓ_i(·) e_i`, `ℓ_i(e_j) = δ_ij`, and
  `A0_eq_of`: every `A0` with `IsPlanarDampedInt` equals `𝒜 + Σ (γ - 1 - λ_i) ℓ_i(·) e_i` on all of
  `L²_m` (density of smooth compactly supported fields).
* `Dyson`: `relSol t = e^{-γt}e^{t𝓛}𝒬 + e^{-t}𝒫` solves the Duhamel equation of
  `(e^{-γ(t-s)}T(t-s), A0)` given the eigen relations (`relSol_duhamel`, via the shifted-exponent
  identity `c_identity`), and a Duhamel solution is the Dyson sum (`eq_of_isDysonSum`).
* `planarDampedDysonBound_of` (below): `PlanarDampedDysonBound κ` from the two leaves
  `PlanarEigenLeaf κ` (eigen and dual eigen relations of the seed pair in the Euler group on `L²_m`)
  and `PlanarRelBoundLeaf κ` (the norm bound `‖relSol B‖ ≤ C₀e^{-hB} + Cproj e^{-B}` from `SeedCtx`
  and `SeedProjBdd`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology

namespace UnforcedLeray.Short.IIIa.PlanarDysonL3

open UnforcedLeray.Short.IIIa.BlockPropagatorInteriorSub.OrgSplit
open UnforcedLeray.Short.IIIa.BlockPropagatorInteriorSub.OrgSplit3
open UnforcedLeray.Short.IIIa.BlockPropagatorInteriorSub.OrgSplit3.PlanarB

/-- **Leaf D (SP 593-610, 869-878, 2926-2927)**: the planar growing vectors are eigenvectors of the
Euler group on `L²_m`, `e^{t𝓛}e_i = e^{λ_i t}e_i`, and the planar pairings `ℓ_i = ∫ λ_i ·` are dual
eigenvectors, `ℓ_i(e^{t𝓛}f) = e^{λ_i t}ℓ_i(f)` (`t ≥ 0`), for the seed pair `λ₀ = λ`, `λ₁ = λ̄` of
seed data whose profile gives `κ.e 0` (`L₀q = λq`, `q̄` by conjugation; `𝒫` is the Riesz projection
and commutes with the group, `PartI.EulerSeedProjCommutes`, transferred to `L²_m`). -/
def PlanarEigenLeaf (κ : PlanarFrameKernels) : Prop :=
  IsSeedKernels κ →
  ∀ (m : ℝ) (hm : 1 < m), 8 < m →
  ∀ (lam : ℂ) (h_prof : ℝ → ℂ) (hh : MemLp h_prof 2 B0010.xGMeasure) (ℓ : B0010.XG →L[ℂ] ℂ),
    PartI.IsSeedXG lam (hh.toLp h_prof) ℓ →
    (∀ y, κ.e 0 y = PartI.seedPlanar h_prof (planeToC y)) →
    ∀ (i : Fin 2) (t : ℝ), 0 ≤ t →
      Planar.eulerGroupW hm t (planarE κ m i) = Complex.exp (seedEigen lam i * t) • planarE κ m i ∧
      ∀ f : Planar.L2w m, planarEll κ hm i (Planar.eulerGroupW hm t f) =
        Complex.exp (seedEigen lam i * t) * planarEll κ hm i f

/-- **Leaf F (SP 2926-2935)**: `‖e^{-γB}e^{B𝓛}𝒬 + e^{-B}𝒫‖ ≤ C₀e^{-hB} + Cproj e^{-B}`. Route: split
`f = f₀ + f_r` into the angular sector `0` and the rest (orthogonal, both invariant). On sector `0`,
`𝒫 = 0` (the pairings live on sectors `±2`) and `e^{t𝓛} = T(t)`, `‖T(t)‖ ≤ 1`, so the bound is
`e^{-γB} ≤ C₀e^{-hB}` (`γ ≥ h`, and `C₀ ≥ 1` from `SeedCtx` at `t = 0` on a nonzero zero-mass `f`
with `𝒫f = 0`). The rest has zero mass, so it lies in `𝒳_{0,m}`; there `𝒫f_r =ᵐ seedProjFun h (f_r)`
(the pairings agree with `seedEll` on smooth compactly supported fields, `IsSeedKernels`, and both
sides are bounded), and `SeedCtx` (`𝒬` part) and `SeedProjBdd` (`𝒫` part) give the bound. -/
def PlanarRelBoundLeaf (κ : PlanarFrameKernels) : Prop :=
  IsSeedKernels κ →
  ∀ (P : UnforcedLeray.Blueprint.Planar.PlanarData), UnforcedLeray.Blueprint.Planar.IsPlanarReference P →
  ∀ (m : ℝ) (hm : 1 < m), 8 < m →
  ∀ C₀ h Cproj B : ℝ,
    0 < C₀ → 0 < h → h ≤ P.eigenvalue.re → 0 ≤ Cproj → 0 < B →
    SeedCtx κ P m C₀ h → SeedProjBdd κ P m Cproj →
      ‖relSol κ P hm B‖ ≤ C₀ * Real.exp (-h * B) + Cproj * Real.exp (-B)

theorem clampB_of_mem {B t : ℝ} (h0 : 0 ≤ t) (hB : t ≤ B) : clampB B t = t := by
  unfold clampB
  rw [min_eq_left hB, max_eq_right h0]

theorem norm_planarRelTransportRe_le (P : UnforcedLeray.Blueprint.Planar.PlanarData) (m : ℝ)
    (hγ : 0 ≤ P.eigenvalue.re) {t r : ℝ} (hrt : r ≤ t) :
    ‖planarRelTransportRe P m t r‖ ≤ 1 := by
  unfold planarRelTransportRe
  have he : Real.exp (-P.eigenvalue.re * (t - r)) ≤ 1 :=
    Real.exp_le_one_iff.2 (by nlinarith [sub_nonneg.2 hrt])
  calc ‖((Real.exp (-P.eigenvalue.re * (t - r)) : ℝ) : ℂ) • Planar.transportGroupW m (t - r)‖
      ≤ ‖((Real.exp (-P.eigenvalue.re * (t - r)) : ℝ) : ℂ)‖ * ‖Planar.transportGroupW m (t - r)‖ :=
        ContinuousLinearMap.opNorm_smul_le _ _
    _ ≤ 1 * 1 := by
        gcongr
        · rw [Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
          exact he
        · exact Planar.norm_transportGroupW_le m _
    _ = 1 := one_mul 1

/-- **Assembly**: `PlanarDampedDysonBound κ` from the eigen leaf and the norm-bound leaf. -/
theorem planarDampedDysonBound_of (κ : PlanarFrameKernels) (hD : PlanarEigenLeaf κ)
    (hF : PlanarRelBoundLeaf κ) : PlanarDampedDysonBound κ := by
  intro hκ P hP m hm hm8 C₀ h Cproj B hC₀ hh hhγ hCp hB hctx hproj A0 hA0 U0 hU0
  obtain ⟨lam, hp, hhp, ℓ, hs, he0, hΦ⟩ := hA0
  have hA : A0 = dampOp κ P hm lam := A0_eq_of κ P hm A0 lam hΦ
  have hEig : ∀ (i : Fin 2) (t : ℝ), 0 ≤ t →
      Planar.eulerGroupW hm t (planarE κ m i) = Complex.exp (seedEigen lam i * t) • planarE κ m i :=
    fun i t ht => (hD hκ m hm hm8 lam hp hhp ℓ hs he0 i t ht).1
  have hDual : ∀ (i : Fin 2) (t : ℝ), 0 ≤ t → ∀ f : Planar.L2w m,
      planarEll κ hm i (Planar.eulerGroupW hm t f) =
        Complex.exp (seedEigen lam i * t) * planarEll κ hm i f :=
    fun i t ht => (hD hκ m hm hm8 lam hp hhp ℓ hs he0 i t ht).2
  have hγ0 : 0 ≤ P.eigenvalue.re := hh.le.trans hhγ
  subst hA
  have hUV : ∀ x, U0 () B 0 x = relSol κ P hm B x := by
    intro x
    refine eq_of_isDysonSum hU0 (dysonDefined_planarRelTransportRe P m B _)
      (K := ‖dampOp κ P hm lam‖) (fun _ => le_rfl) ?_ x (fun t => relSol κ P hm t x)
      (continuous_relSol_apply κ P hm x).continuousOn ?_ ?_ B ⟨hB.le, le_rfl⟩
    · intro t r hr hrt htB
      rw [clampB_of_mem (hr.trans hrt) htB, clampB_of_mem hr (hrt.trans htB)]
      exact norm_planarRelTransportRe_le P m hγ0 hrt
    · intro t _
      have hc : Continuous fun r => planarRelTransportRe P m (clampB B t) (clampB B r)
          (dampOp κ P hm lam (relSol κ P hm r x)) := by
        simp_rw [planarRelTransportRe_apply_eq]
        exact continuous_expSmulTransport m (-P.eigenvalue.re) 1 continuous_const
          (continuous_expSmulTransport m P.eigenvalue.re (-1) (continuous_clampB B)
            ((dampOp κ P hm lam).continuous.comp (continuous_relSol_apply κ P hm x)))
      exact hc.intervalIntegrable _ _
    · intro t ht
      have hd := relSol_duhamel κ P hm lam hEig hDual ht.1 x
      show relSol κ P hm t x = planarRelTransportRe P m (clampB B t) (clampB B 0) x +
        ∫ r in (0:ℝ)..t, planarRelTransportRe P m (clampB B t) (clampB B r)
          (dampOp κ P hm lam (relSol κ P hm r x))
      rw [clampB_of_mem ht.1 ht.2, clampB_of_mem le_rfl (hB.le), hd]
      congr 1
      apply intervalIntegral.integral_congr
      intro r hr
      rw [Set.uIcc_of_le ht.1] at hr
      simp only
      rw [clampB_of_mem hr.1 (hr.2.trans ht.2)]
  have hU : U0 () B 0 = relSol κ P hm B := ContinuousLinearMap.ext hUV
  rw [hU]
  exact hF hκ P hP m hm hm8 C₀ h Cproj B hC₀ hh hhγ hCp hB hctx hproj

end UnforcedLeray.Short.IIIa.PlanarDysonL3
