import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c3_2_1_1_org3_b_L3.Assembly
import UnforcedLeray.Short.PartI.Tasks.EulerComplementJ0.GrowProjAgree

/-!
# Helpers for the planar eigen leaf (SP 593-610, 869-878, 2926-2935)

Source: `the November 2 reference manuscript` (SP) 593-610 (the seed pair
`λ, λ̄`, eigenvectors `q = h(r)e^{2iϑ}`, `q̄`, and the functional `ℓ` of
`eq:short-seed-functional`), 869-878 (Riesz projections agree on the weighted spaces), 2926-2927
(`𝒫` removes both growing modes).

* `planarE_zero_eq`, `planarE_one_eq`: `e₀ = q` lies in sector `2` with profile `h`, `e₁ = q̄` in
  sector `-2` with profile `h̄` (`L₀ q = λ q` transported by `PartI.xgEmbM_L0`).
* `planarEll_sector`: the planar pairings read only the sectors `±2`,
  `ℓ₀ f = Λ(f₂)`, `ℓ₁ f = \overline{Λ(\overline{f_{-2}})}`, where `Λ` is the bounded extension of
  `seedEll h` (`PartI.seedDualBounded`); proof by density of smooth compactly supported fields and
  the pairing clause of `IsSeedKernels`.
* `exp_smul_apply_of_eigen`, `eigenfunctional_exp`: `e^{tA}v = e^{zt}v` for `Av = zv`, and
  `Λ e^{tA} = e^{zt}Λ` for `Λ A = zΛ` (exponential series).
* `eulerGroupW_secEmb_eigen`, `ell_eulerGroupW_of`: the same for the sector-sum Euler group.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ContDiff ComplexConjugate

namespace UnforcedLeray.Short.IIIa.PlanarDysonL3.EigenLeafAux

open UnforcedLeray.Short.IIIa.BlockPropagatorInteriorSub.OrgSplit3.PlanarB

/-! ### Profiles of the seed -/

theorem planeToC_cToPlane (z : ℂ) : planeToC (cToPlane z) = z := rfl

theorem seedPlanar_planeToC_real (h : ℝ → ℂ) {r : ℝ} (hr : 0 < r) :
    PartI.seedPlanar h (planeToC (r, 0)) = h r := by
  have hpc : planeToC (r, 0) = (r : ℂ) :=
    Complex.ext (by simp [planeToC]) (by simp [planeToC])
  rw [hpc]
  simp only [PartI.seedPlanar, Planar.NUE.Ang.ofProfile, Planar.NUE.Ang.angPhase]
  rw [Complex.norm_real, Real.norm_of_nonneg hr.le,
    div_self (Complex.ofReal_ne_zero.2 hr.ne'), one_zpow, mul_one]

/-- Two profiles giving the same `e₀` agree on `(0, ∞)`. -/
theorem profile_eq_of_e0 {κ : PlanarFrameKernels} {h₁ h₂ : ℝ → ℂ}
    (he₁ : ∀ y, κ.e 0 y = PartI.seedPlanar h₁ (planeToC y))
    (he₂ : ∀ y, κ.e 0 y = PartI.seedPlanar h₂ (planeToC y)) {r : ℝ} (hr : 0 < r) :
    h₁ r = h₂ r := by
  rw [← seedPlanar_planeToC_real h₁ hr, ← seedPlanar_planeToC_real h₂ hr, ← he₁, ← he₂]

theorem seedEll_eq_of_eqOn {h₁ h₂ : ℝ → ℂ} (heq : ∀ r, 0 < r → h₁ r = h₂ r) (g : ℝ → ℂ) :
    PartI.seedEll h₁ g = PartI.seedEll h₂ g := by
  unfold PartI.seedEll PartI.seedJ
  have e1 : ∫ r in Ioi (0:ℝ), h₁ r ^ 2 / (Blueprint.Planar.strainK r : ℂ) * (r : ℂ) =
      ∫ r in Ioi (0:ℝ), h₂ r ^ 2 / (Blueprint.Planar.strainK r : ℂ) * (r : ℂ) :=
    setIntegral_congr_fun measurableSet_Ioi (fun r hr => by simp only [heq r hr])
  have e2 : ∫ r in Ioi (0:ℝ), h₁ r * g r / (Blueprint.Planar.strainK r : ℂ) * (r : ℂ) =
      ∫ r in Ioi (0:ℝ), h₂ r * g r / (Blueprint.Planar.strainK r : ℂ) * (r : ℂ) :=
    setIntegral_congr_fun measurableSet_Ioi (fun r hr => by simp only [heq r hr])
  rw [e1, e2]

/-! ### The seed vectors in the sectors `±2` -/

theorem seedProfile_ae {m : ℝ} (hm : 1 < m) {h : ℝ → ℂ} (hh : MemLp h 2 B0010.xGMeasure) :
    ⇑(PartI.xgEmbM hm (hh.toLp h)) =ᵐ[Planar.profileMeasure m] h := by
  filter_upwards [PartI.coeFn_xgEmbM hm (hh.toLp h),
    (PartI.profileMeasure_ac_xGMeasure (PartI.xgEmbM_nonneg hm)).ae_le hh.coeFn_toLp]
    with r a b
  rw [a, b]

theorem seedProfile_eigen {m : ℝ} (hm : 1 < m) {lam : ℂ} {h : ℝ → ℂ}
    {hh : MemLp h 2 B0010.xGMeasure} {ℓ : B0010.XG →L[ℂ] ℂ}
    (hs : PartI.IsSeedXG lam (hh.toLp h) ℓ) :
    Planar.Lsec hm 2 (PartI.xgEmbM hm (hh.toLp h)) = lam • PartI.xgEmbM hm (hh.toLp h) := by
  rw [← PartI.xgEmbM_L0, hs.eigen, map_smul]

theorem planarE_zero_eq (κ : PlanarFrameKernels) {m : ℝ} {h : ℝ → ℂ} {w : Planar.ProfL2 m}
    (hw : ⇑w =ᵐ[Planar.profileMeasure m] h)
    (he0 : ∀ y, κ.e 0 y = PartI.seedPlanar h (planeToC y)) :
    planarE κ m 0 = Planar.secEmb m 2 w := by
  apply Lp.ext
  filter_upwards [coeFn_planarE κ m 0, Planar.coeFn_secEmb m 2 w,
    Planar.ofProfile_congr_ae' m 2 hw] with z a b c
  rw [a, b, c, he0, planeToC_cToPlane]

theorem planarE_one_eq (κ : PlanarFrameKernels) {m : ℝ} {h : ℝ → ℂ} {w : Planar.ProfL2 m}
    (hw : ⇑w =ᵐ[Planar.profileMeasure m] h)
    (he1 : ∀ y, κ.e 1 y = conj (PartI.seedPlanar h (planeToC y))) :
    planarE κ m 1 = Planar.secEmb m (-2) (star w) := by
  have hstar : ⇑(star w) =ᵐ[Planar.profileMeasure m] fun r => conj (h r) := by
    filter_upwards [Planar.coeFn_star_prof w, hw] with r a b
    rw [a, b]
  apply Lp.ext
  filter_upwards [coeFn_planarE κ m 1, Planar.coeFn_secEmb m (-2) (star w),
    Planar.ofProfile_congr_ae' m (-2) hstar,
    (Planar.wMeasure_ac m).ae_le (PartI.ofProfile_two_conj h)] with z a b c d
  rw [a, b, c, he1, planeToC_cToPlane]
  exact d.symm

/-! ### Exponentials on eigenvectors and eigenfunctionals -/

theorem exp_smul_apply_of_eigen {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [CompleteSpace E] (A : E →L[ℂ] E) {v : E} {z : ℂ} (hv : A v = z • v) (t : ℝ) :
    NormedSpace.exp ((t : ℂ) • A) v = Complex.exp (z * t) • v := by
  have hpow : ∀ n : ℕ, (((t : ℂ) • A) ^ n) v = ((t : ℂ) * z) ^ n • v := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ, ContinuousLinearMap.mul_apply, ContinuousLinearMap.smul_apply, hv, smul_smul,
        map_smul, ih, smul_smul, pow_succ]
      congr 1
      ring
  have h1 := (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) ((t : ℂ) • A)).mapL
    (ContinuousLinearMap.apply ℂ E v)
  have h2 := (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) ((t : ℂ) * z)).smul_const v
  simp only [ContinuousLinearMap.apply_apply, ContinuousLinearMap.smul_apply, hpow,
    smul_smul] at h1
  simp only [smul_eq_mul] at h2
  rw [Complex.exp_eq_exp_ℂ, mul_comm z]
  exact h1.unique h2

theorem eigenfunctional_exp {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [CompleteSpace E] (A : E →L[ℂ] E) (Λ : E →L[ℂ] ℂ) {z : ℂ} (hΛ : ∀ v, Λ (A v) = z * Λ v)
    (t : ℝ) (v : E) :
    Λ (NormedSpace.exp ((t : ℂ) • A) v) = Complex.exp (z * t) * Λ v := by
  have hpow : ∀ n : ℕ, Λ ((((t : ℂ) • A) ^ n) v) = ((t : ℂ) * z) ^ n * Λ v := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ', ContinuousLinearMap.mul_apply, ContinuousLinearMap.smul_apply, map_smul,
        hΛ, ih, smul_eq_mul, pow_succ']
      ring
  have h1 := (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) ((t : ℂ) • A)).mapL
    (Λ.comp (ContinuousLinearMap.apply ℂ E v))
  have h2 := (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) ((t : ℂ) * z)).mul_right (Λ v)
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.apply_apply,
    ContinuousLinearMap.smul_apply, map_smul, hpow, smul_eq_mul] at h1
  simp only [smul_eq_mul, mul_assoc] at h2
  rw [Complex.exp_eq_exp_ℂ, mul_comm z]
  exact h1.unique h2

/-! ### The Euler group on sector eigenvectors and sector eigenfunctionals -/

theorem eulerGroupW_secEmb_eigen {m : ℝ} (hm : 1 < m) {n : ℤ} {v : Planar.ProfL2 m} {z : ℂ}
    (hv : Planar.Lsec hm n v = z • v) (t : ℝ) :
    Planar.eulerGroupW hm t (Planar.secEmb m n v) =
      Complex.exp (z * t) • Planar.secEmb m n v := by
  apply Planar.eq_of_secProf
  intro k
  rw [Planar.secProf_eulerGroupW, map_smul, Planar.secProf_secEmb]
  split_ifs with hnk
  · subst hnk
    exact exp_smul_apply_of_eigen (Planar.Lsec hm n) hv t
  · rw [map_zero, smul_zero]

theorem ell_eulerGroupW_of {m : ℝ} (hm : 1 < m) (L : Planar.L2w m →L[ℂ] ℂ)
    (Λ : Planar.ProfL2 m →L[ℂ] ℂ) {n : ℤ} {z : ℂ}
    (hL : ∀ f, L f = Λ (Planar.secProf m n f)) (hΛ : ∀ v, Λ (Planar.Lsec hm n v) = z * Λ v)
    (t : ℝ) (f : Planar.L2w m) :
    L (Planar.eulerGroupW hm t f) = Complex.exp (z * t) * L f := by
  rw [hL, hL, Planar.secProf_eulerGroupW]
  exact eigenfunctional_exp (Planar.Lsec hm n) Λ hΛ t _

/-! ### The planar pairings read only the sectors `±2` -/

/-- `ℓ₀ f = Λ(f₂)` and `ℓ₁ f = \overline{Λ(\overline{f_{-2}})}` on all of `L²_m`, with `Λ` the
bounded extension of `seedEll h` to the profile space. -/
theorem planarEll_sector (κ : PlanarFrameKernels) (hκ : IsSeedKernels κ) {m : ℝ} (hm : 1 < m)
    {lam : ℂ} {h : ℝ → ℂ} {hh : MemLp h 2 B0010.xGMeasure} {ℓ : B0010.XG →L[ℂ] ℂ}
    (hs : PartI.IsSeedXG lam (hh.toLp h) ℓ)
    (he0 : ∀ y, κ.e 0 y = PartI.seedPlanar h (planeToC y)) :
    ∃ Λ : Planar.ProfL2 m →L[ℂ] ℂ, (∀ v, Λ v = PartI.seedEll h ⇑v) ∧
      (∀ f, planarEll κ hm 0 f = Λ (Planar.secProf m 2 f)) ∧
      (∀ f, planarEll κ hm 1 f = PartI.starFunctional Λ (Planar.secProf m (-2) f)) := by
  obtain ⟨Λ, hΛ⟩ := PartI.seedDualBounded lam h hh ℓ hs m hm
  obtain ⟨lam', h', hh', ℓ', hs', he0', he1', hpair⟩ := hκ
  have hhh : ∀ r, 0 < r → h' r = h r := fun r hr => profile_eq_of_e0 he0' he0 hr
  haveI : IsLocallyFiniteMeasure (Planar.wMeasure m) :=
    inferInstanceAs (IsLocallyFiniteMeasure (B0008.wMeasure m))
  have hD := Lp.dense_hasCompactSupport_contDiff (μ := Planar.wMeasure m) (F := ℂ) (p := 2)
    (by simp)
  refine ⟨Λ, hΛ, fun f => ?_, fun f => ?_⟩
  · have key : ⇑(planarEll κ hm 0) = ⇑(Λ.comp (Planar.secProf m 2)) := by
      refine Continuous.ext_on hD (planarEll κ hm 0).continuous
        (Λ.comp (Planar.secProf m 2)).continuous ?_
      rintro W ⟨Φ, hWΦ, hcs, hsm⟩
      have hWv : ⇑W =ᵐ[volume] Φ := (Planar.volume_ac m).ae_le hWΦ
      show planarEll κ hm 0 W = Λ (Planar.secProf m 2 W)
      rw [planarEll_eq_lamPair κ hm 0 hWv, planarLamPair, (hpair Φ hsm hcs).1, hΛ,
        seedEll_eq_of_eqOn hhh]
      refine ((PartI.seedEll_congr_prof m (PartI.coeFn_secProf m 2 W)).trans
        (PartI.seedEll_congr ?_)).symm
      filter_upwards [Planar.NUE.Ang.ParsevalH.ae_angularSector_eq hWv] with r hr
      exact hr 2
    exact congrFun key f
  · have key : ⇑(planarEll κ hm 1) =
        ⇑((PartI.starFunctional Λ).comp (Planar.secProf m (-2))) := by
      refine Continuous.ext_on hD (planarEll κ hm 1).continuous
        ((PartI.starFunctional Λ).comp (Planar.secProf m (-2))).continuous ?_
      rintro W ⟨Φ, hWΦ, hcs, hsm⟩
      have hWv : ⇑W =ᵐ[volume] Φ := (Planar.volume_ac m).ae_le hWΦ
      show planarEll κ hm 1 W = PartI.starFunctional Λ (Planar.secProf m (-2) W)
      rw [planarEll_eq_lamPair κ hm 1 hWv, planarLamPair, (hpair Φ hsm hcs).2,
        PartI.starFunctional_apply, hΛ, seedEll_eq_of_eqOn hhh]
      congr 1
      refine ((PartI.seedEll_congr_prof m (Planar.coeFn_star_prof _)).trans
        (PartI.seedEll_congr ?_)).symm
      have h3 := (Planar.ac_profileMeasure m).ae_le (PartI.coeFn_secProf m (-2) W)
      filter_upwards [h3, Planar.NUE.Ang.ParsevalH.ae_angularSector_eq hWv] with r a b
      rw [a, b (-2)]
    exact congrFun key f

end UnforcedLeray.Short.IIIa.PlanarDysonL3.EigenLeafAux
