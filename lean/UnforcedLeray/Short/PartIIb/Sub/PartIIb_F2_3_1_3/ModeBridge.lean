import UnforcedLeray.Short.PartIIb.Sub.PartIIb_F2_3_1_1.Bridge
import UnforcedLeray.Short.PartIIb.Sub.PartIIb_F2_3_1_4
import UnforcedLeray.Short.PartI.Sub.PartI_S15_2
import UnforcedLeray.Short.PartI.Tasks.DilationUniformComplement
import UnforcedLeray.Short.PartI.Tasks.DilationContinuity.DilX0StrongCont.CcDense
import UnforcedLeray.Short.PartI.Tasks.DilationContinuity.DilX0AdjStrongCont.AdjCcCont
import Mathlib.Analysis.InnerProductSpace.Dual

/-!
# `PartII-b:F2/3/1/3` (`ModeBridge.lean`): Mode identification and dual dilation continuity

Provides helper lemmas for `PlanarEulerSpectral`:
* `cToE2` / `e2ToC` bridging `ℂ` and `E2 = EuclideanSpace ℝ (Fin 2)` and intertwining
  multiplication by `e^{(τ / a²) λ}` with `rotScaleCLM`,
* `eulerGroupW_secEmb`, `expSec_eigen_of_proj`, and `eulerGroupW_comp_growingProjW`,
* `secProf_neg_two_toL2w`: conjugate sector symmetry `f₋₂ = star f₂` for real `f ∈ Xm m`,
* `toL2w_directMode_eq`: exact `L2w m` formula for `toL2w m (ι σ α)` in terms of
  `Planar.dilW hm ha (Planar.secEmb m 2 q')` and `Planar.dilW hm ha (Planar.secEmb m (-2) (star q'))`,
* `continuous_comp_dilW`: norm continuity of `a ↦ φ.comp (Planar.dilW hm a.2)` on `Ioi 0`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal InnerProductSpace ComplexConjugate

namespace UnforcedLeray.Short.IIb.PlanarSpectralBridge

open UnforcedLeray.Cons.C03.Concrete UnforcedLeray.PhaseSpace UnforcedLeray.B0411
open UnforcedLeray.Short.IIb.PartIIbF23Sub
open UnforcedLeray.Short.IIb.PlanarEulerBridge
open UnforcedLeray.Short.IIIa (cToPlane planeToC cToPlane_planeToC planeToC_cToPlane)
open UnforcedLeray.Infra.Dunford (IsSimpleSpectralProj rankOneProj)

/-! ## 1. Real/complex coordinate bridge `ℂ ↔ E2` and `rotScaleCLM` -/

/-- Real-linear equivalence map `ℂ →L[ℝ] E2`, `z ↦ (z.re, z.im)`. -/
def cToE2 : ℂ →L[ℝ] E2 :=
  Complex.reCLM.smulRight (WithLp.toLp 2 (![1, 0] : Fin 2 → ℝ)) +
    Complex.imCLM.smulRight (WithLp.toLp 2 (![0, 1] : Fin 2 → ℝ))

theorem cToE2_apply_zero (z : ℂ) : cToE2 z 0 = z.re := by
  simp [cToE2]

theorem cToE2_apply_one (z : ℂ) : cToE2 z 1 = z.im := by
  simp [cToE2]

/-- Complex coordinate `α 0 + α 1 * I` of `α : E2`. -/
def e2ToC (α : E2) : ℂ :=
  (α 0 : ℂ) + (α 1 : ℂ) * Complex.I

theorem cToE2_e2ToC (α : E2) : cToE2 (e2ToC α) = α := by
  ext i
  fin_cases i
  · simp [cToE2_apply_zero, e2ToC]
  · simp [cToE2_apply_one, e2ToC]

theorem e2ToC_cToE2 (z : ℂ) : e2ToC (cToE2 z) = z := by
  rw [e2ToC, cToE2_apply_zero, cToE2_apply_one, Complex.re_add_im]

theorem e2ToC_rotScaleCLM_exp (lam : ℂ) (τ a : ℝ) (α : E2) :
    let θ : ℝ := lam.im * τ / a ^ 2
    let r : ℝ := Real.exp (lam.re * τ / a ^ 2)
    e2ToC (rotScaleCLM r θ α) =
      Complex.exp (((τ / a ^ 2 : ℝ) : ℂ) * lam) * e2ToC α := by
  intro θ r
  have hexp_arg : (((τ / a ^ 2 : ℝ) : ℂ) * lam) =
      ((lam.re * τ / a ^ 2 : ℝ) : ℂ) + ((θ : ℝ) : ℂ) * Complex.I := by
    apply Complex.ext
    · simp only [Complex.mul_re, Complex.add_re, Complex.ofReal_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im, zero_mul, mul_zero, sub_zero, add_zero]
      ring
    · simp only [Complex.mul_im, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im, zero_mul, mul_zero, add_zero, mul_one, θ]
      ring
  rw [hexp_arg, Complex.exp_add, ← Complex.ofReal_exp, Complex.exp_mul_I,
    ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  apply Complex.ext
  · simp [e2ToC, rotScaleCLM_apply_zero, rotScaleCLM_apply_one, r]
    ring
  · simp [e2ToC, rotScaleCLM_apply_zero, rotScaleCLM_apply_one, r]
    ring

theorem conj_e2ToC_rotScaleCLM_exp (lam : ℂ) (τ a : ℝ) (α : E2) :
    let θ : ℝ := lam.im * τ / a ^ 2
    let r : ℝ := Real.exp (lam.re * τ / a ^ 2)
    conj (e2ToC (rotScaleCLM r θ α)) =
      Complex.exp (((τ / a ^ 2 : ℝ) : ℂ) * conj lam) * conj (e2ToC α) := by
  intro θ r
  have h := congrArg (starRingEnd ℂ) (e2ToC_rotScaleCLM_exp lam τ a α)
  rwa [map_mul, ← Complex.exp_conj, map_mul, Complex.conj_ofReal] at h

theorem mode_comb_eq_re_im (α : E2) (w : ℂ) :
    ((α 0 * (2 * w.re) + α 1 * (-2 * w.im) : ℝ) : ℂ) =
      e2ToC α * w + conj (e2ToC α) * conj w := by
  apply Complex.ext <;> simp [e2ToC] <;> ring

/-! ## 2. Sector exponential, commutation, and conjugate profile symmetry -/

theorem eulerGroupW_secEmb {m : ℝ} (hm : 1 < m) (t : ℝ) (n : ℤ) (h : Planar.ProfL2 m) :
    Planar.eulerGroupW hm t (Planar.secEmb m n h) =
      Planar.secEmb m n (Planar.expSec hm t n h) := by
  apply Planar.eq_of_secProf
  intro k
  rw [Planar.secProf_eulerGroupW, Planar.secProf_secEmb, Planar.secProf_secEmb]
  split_ifs with hnk
  · subst hnk; rfl
  · exact map_zero _

theorem expSec_eigen_of_proj {m : ℝ} (hm : 1 < m) {n : ℤ} {ℓ : Planar.ProfL2 m →L[ℂ] ℂ}
    {w : Planar.ProfL2 m} {z₀ : ℂ} (hℓw : ℓ w = 1)
    (hP : IsSimpleSpectralProj (Planar.Lsec hm n) (rankOneProj ℓ w) z₀) (t : ℝ) :
    Planar.expSec hm t n w = Complex.exp ((t : ℂ) * z₀) • w := by
  have hw : rankOneProj ℓ w w = w := by
    rw [Infra.Dunford.rankOneProj_apply, hℓw, one_smul]
  have hexp := congrArg (fun T : Planar.ProfL2 m →L[ℂ] Planar.ProfL2 m => T w)
    (Infra.Dunford.exp_mul_proj hP.mul_proj (t : ℂ))
  change Planar.expSec hm t n (rankOneProj ℓ w w) =
    Complex.exp ((t : ℂ) * z₀) • rankOneProj ℓ w w at hexp
  rwa [hw] at hexp

theorem eulerGroupW_comp_growingProjW {m : ℝ} (hm : 1 < m)
    {P₂ Pm : Planar.ProfL2 m →L[ℂ] Planar.ProfL2 m} {z₂ zm : ℂ}
    (hP₂ : IsSimpleSpectralProj (Planar.Lsec hm 2) P₂ z₂)
    (hPm : IsSimpleSpectralProj (Planar.Lsec hm (-2)) Pm zm) (t : ℝ) :
    Planar.eulerGroupW hm t ∘L Planar.growingProjW P₂ Pm =
      Planar.growingProjW P₂ Pm ∘L Planar.eulerGroupW hm t := by
  ext1 f
  apply Planar.eq_of_secProf
  intro n
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
    Planar.secProf_eulerGroupW, Planar.secProf_growingProjW,
    Planar.secProf_growingProjW, Planar.secProf_eulerGroupW]
  change (Planar.expSec hm t n * Planar.secProjFam P₂ Pm n) (Planar.secProf m n f) =
    (Planar.secProjFam P₂ Pm n * Planar.expSec hm t n) (Planar.secProf m n f)
  unfold Planar.secProjFam
  split_ifs with h2 hm2
  · subst h2
    have hc : Commute P₂ (Planar.Lsec hm 2) := hP₂.proj_mul.trans hP₂.mul_proj.symm
    exact congrArg (fun T : Planar.ProfL2 m →L[ℂ] Planar.ProfL2 m => T _)
      ((hc.smul_right (t : ℂ)).exp_right.eq.symm)
  · subst hm2
    have hc : Commute Pm (Planar.Lsec hm (-2)) := hPm.proj_mul.trans hPm.mul_proj.symm
    exact congrArg (fun T : Planar.ProfL2 m →L[ℂ] Planar.ProfL2 m => T _)
      ((hc.smul_right (t : ℂ)).exp_right.eq.symm)
  · simp only [mul_zero, zero_mul]

theorem secProf_neg_two_toL2w {m : ℝ} (g : Xm m) :
    Planar.secProf m (-2) (toL2w m g) = star (Planar.secProf m 2 (toL2w m g)) := by
  let F : ℂ → ℂ := fun z => ((g (cToPlane z) : ℝ) : ℂ)
  have hF_conj : (fun z => conj (F z)) = F := by
    funext z; exact Complex.conj_ofReal _
  have hW : (toL2w m g : ℂ → ℂ) =ᵐ[volume] F :=
    (Planar.volume_ac m).ae_le (coeFn_toL2w m g)
  have hsec := (Planar.profileMeasure_ac m).ae_le
    (Planar.NUE.Ang.ParsevalH.ae_angularSector_eq hW)
  apply Lp.ext
  filter_upwards [PartI.coeFn_secProf m (-2) (toL2w m g),
    Planar.coeFn_star_prof (Planar.secProf m 2 (toL2w m g)),
    PartI.coeFn_secProf m 2 (toL2w m g), hsec] with r hm2 hst h2 hr
  rw [hm2, hr (-2), hst, h2, hr 2]
  have hc := Planar.NUE.Ang.angularSector_conj F 2 r
  rwa [hF_conj] at hc

/-! ## 3. Growing eigenpair spectral data on `Planar.ProfL2 m` -/

theorem growing_spectral_data {m : ℝ} (hm : 1 < m) {lam : ℂ} {q : Blueprint.Planar.Profile}
    (hEig : Blueprint.Planar.IsGrowingEigenpair lam q) :
    ∃ (q' : Planar.ProfL2 m) (ℓ₂ ℓm : Planar.ProfL2 m →L[ℂ] ℂ),
      q' ≠ 0 ∧
      Planar.Lsec hm 2 q' = lam • q' ∧
      (⇑q' =ᵐ[Planar.profileMeasure m] q) ∧
      ℓ₂ q' = 1 ∧
      ℓm (star q') = 1 ∧
      IsSimpleSpectralProj (Planar.Lsec hm 2) (rankOneProj ℓ₂ q') lam ∧
      IsSimpleSpectralProj (Planar.Lsec hm (-2)) (rankOneProj ℓm (star q')) (conj lam) ∧
      (∀ x : Planar.ProfL2 m, ℓm x = conj (ℓ₂ (star x))) := by
  have hm_q : MemLp q 2 B0010.xGMeasure := Cons.G3b.memLp_of_memXG hEig.memXG
  have hL0 := PlanarSeedAux.growing_L0_eq lam q hEig hm_q
  have hne := PlanarSeedAux.growing_toLp_ne_zero q hEig.nonzero hm_q
  let q' : Planar.ProfL2 m := PartI.xgEmbM hm (hm_q.toLp q)
  have hq'0 : q' ≠ 0 := fun h0 => hne (PartI.xgEmbM_injective hm h0)
  have hq' : Planar.Lsec hm 2 q' = lam • q' := by
    show Planar.Lsec hm 2 (PartI.xgEmbM hm (hm_q.toLp q)) = _
    rw [← PartI.xgEmbM_L0 hm, hL0, map_smul]
  have hq'_ae : ⇑q' =ᵐ[Planar.profileMeasure m] q := by
    filter_upwards [PartI.coeFn_xgEmbM hm (hm_q.toLp q),
      (PartI.profileMeasure_ac_xGMeasure (PartI.xgEmbM_nonneg hm)).ae_le hm_q.coeFn_toLp]
      with r h1 h2
    exact h1.trans h2
  obtain ⟨ℓ₂, ℓm, h2q, hmq, hP₂, hPm, -⟩ :=
    Planar.eulerSemigroup_complement_bound hm (PartI.sectorOneStableAll m hm) hEig.re_pos hq'0 hq'
  have hℓ₂L : ∀ f, ℓ₂ (Planar.Lsec hm 2 f) = lam * ℓ₂ f :=
    PartI.eigenfunctional_of_rankOne hq'0 hP₂.proj_mul
  have hstarL : ∀ f, PartI.starFunctional ℓ₂ (Planar.Lsec hm (-2) f) =
      conj lam * PartI.starFunctional ℓ₂ f := by
    intro f
    have h1 := Planar.Lsec_star hm 2 (star f)
    rw [star_star] at h1
    have h2 : star (Planar.Lsec hm (-2) f) = Planar.Lsec hm 2 (star f) := by
      rw [h1, star_star]
    rw [PartI.starFunctional_apply, PartI.starFunctional_apply, h2, hℓ₂L, map_mul]
  have hstarq : PartI.starFunctional ℓ₂ (star q') = 1 := by
    rw [PartI.starFunctional_apply, star_star, h2q, map_one]
  have hℓm_eq : ∀ x : Planar.ProfL2 m, ℓm x = conj (ℓ₂ (star x)) := by
    intro x
    have h := ExternalInputs.apply_eq_apply_proj hPm hstarL x
    rw [Infra.Dunford.rankOneProj_apply, map_smul, hstarq, smul_eq_mul, mul_one,
      PartI.starFunctional_apply] at h
    exact h.symm
  exact ⟨q', ℓ₂, ℓm, hq'0, hq', hq'_ae, h2q, hmq, hP₂, hPm, hℓm_eq⟩

/-! ## 4. Pointwise and `L2w` direct-mode formulas -/

theorem angTwoPlanar_cToPlane (z : ℂ) :
    angTwoPlanar (cToPlane z) = Planar.NUE.Ang.angPhase 2 z := by
  unfold angTwoPlanar Planar.NUE.Ang.angPhase
  have hsq : z.re ^ 2 + z.im ^ 2 = ‖z‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    ring
  simp only [cToPlane, Complex.re_add_im, hsq, zpow_two, Complex.ofReal_pow]
  ring

theorem planarMode2D_cToPlane (q : Blueprint.Planar.Profile) (z : ℂ) :
    planarMode2D q (cToPlane z) = Planar.NUE.Ang.ofProfile 2 q z := by
  unfold planarMode2D Planar.NUE.Ang.ofProfile
  have hsq : z.re ^ 2 + z.im ^ 2 = ‖z‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    ring
  rw [angTwoPlanar_cToPlane]
  simp only [cToPlane, hsq, Real.sqrt_sq (norm_nonneg z)]

theorem dilPlanarMode_cToPlane {a : ℝ} (ha : 0 < a) (q : Blueprint.Planar.Profile) (z : ℂ) :
    dilPlanarMode q a (cToPlane z) = Planar.dilWFun a (Planar.NUE.Ang.ofProfile 2 q) z := by
  unfold dilPlanarMode Planar.dilWFun
  have hpt : ((cToPlane z).1 / Real.sqrt a, (cToPlane z).2 / Real.sqrt a) =
      cToPlane ((Real.sqrt a)⁻¹ • z) := by
    ext <;> simp only [cToPlane, Complex.smul_re, Complex.smul_im] <;> ring
  have hpow : a ^ (-2 : ℝ) = (a ^ 2)⁻¹ := by
    rw [Real.rpow_neg ha.le, Real.rpow_two]
  rw [hpt, planarMode2D_cToPlane, hpow]

theorem toL2w_directMode_eq {m : ℝ} (hm : 1 < m) {q : Blueprint.Planar.Profile}
    {q' : Planar.ProfL2 m} (hq'_ae : ⇑q' =ᵐ[Planar.profileMeasure m] q)
    {a : ℝ} (ha : 0 < a) {g : Xm m} {α : E2}
    (hg : (g : B0579.Plane → ℝ) =ᵐ[planeMeasure m]
      fun x => ∑ i : Fin 2, α i * planarFrozenDirectMode q a i x) :
    toL2w m g =
      e2ToC α • Planar.dilW hm ha (Planar.secEmb m 2 q') +
        conj (e2ToC α) • Planar.dilW hm ha (Planar.secEmb m (-2) (star q')) := by
  have hsec2 : ⇑(Planar.secEmb m 2 q') =ᵐ[Planar.wMeasure m] Planar.NUE.Ang.ofProfile 2 q := by
    have h1 := Planar.coeFn_secEmb m 2 q'
    have h2 := (Planar.wMeasure_ac m).ae_le
      (Planar.ofProfile_congr_ae 2 ((Planar.ac_profileMeasure m).ae_le hq'_ae))
    exact h1.trans h2
  have hdil2 : ⇑(Planar.dilW hm ha (Planar.secEmb m 2 q')) =ᵐ[Planar.wMeasure m]
      fun z => dilPlanarMode q a (cToPlane z) := by
    filter_upwards [Planar.coeFn_dilW hm ha (Planar.secEmb m 2 q'),
      Planar.dilWFun_congr ha hsec2] with z hz1 hz2
    have hzf : (((a ^ 2)⁻¹ : ℝ) : ℂ) * (Planar.secEmb m 2 q' : ℂ → ℂ) ((Real.sqrt a)⁻¹ • z) =
        Planar.dilWFun a (Planar.secEmb m 2 q') z := rfl
    rw [hz1, hzf, hz2, ← dilPlanarMode_cToPlane ha q z]
  have hstar_ae : ⇑(star q') =ᵐ[Planar.profileMeasure m] fun r => conj (q r) := by
    filter_upwards [Planar.coeFn_star_prof q', hq'_ae] with r hr1 hr2
    rw [hr1, hr2]
  have hsecm2 : ⇑(Planar.secEmb m (-2) (star q')) =ᵐ[Planar.wMeasure m]
      fun z => conj (Planar.NUE.Ang.ofProfile 2 q z) := by
    have h1 := Planar.coeFn_secEmb m (-2) (star q')
    have h2 := (Planar.wMeasure_ac m).ae_le
      (Planar.ofProfile_congr_ae (-2) ((Planar.ac_profileMeasure m).ae_le hstar_ae))
    have h3 := (Planar.wMeasure_ac m).ae_le (PartI.ofProfile_two_conj q)
    exact (h1.trans h2).trans h3
  have hdilm2 : ⇑(Planar.dilW hm ha (Planar.secEmb m (-2) (star q'))) =ᵐ[Planar.wMeasure m]
      fun z => conj (dilPlanarMode q a (cToPlane z)) := by
    filter_upwards [Planar.coeFn_dilW hm ha (Planar.secEmb m (-2) (star q')),
      Planar.dilWFun_congr ha hsecm2] with z hz1 hz2
    have hzf : (((a ^ 2)⁻¹ : ℝ) : ℂ) *
          (Planar.secEmb m (-2) (star q') : ℂ → ℂ) ((Real.sqrt a)⁻¹ • z) =
        Planar.dilWFun a (Planar.secEmb m (-2) (star q')) z := rfl
    rw [hz1, hzf, hz2, dilPlanarMode_cToPlane ha q z]
    unfold Planar.dilWFun
    rw [map_mul, Complex.conj_ofReal]
  set v₂ : Planar.L2w m := Planar.dilW hm ha (Planar.secEmb m 2 q')
  set vm : Planar.L2w m := Planar.dilW hm ha (Planar.secEmb m (-2) (star q'))
  apply Lp.ext
  filter_upwards [coeFn_toL2w m g,
    (measurePreserving_cToPlane m).quasiMeasurePreserving.ae_eq_comp hg,
    Lp.coeFn_add (e2ToC α • v₂) (conj (e2ToC α) • vm),
    Lp.coeFn_smul (e2ToC α) v₂, Lp.coeFn_smul (conj (e2ToC α)) vm,
    hdil2, hdilm2] with z hto hg_z hadd hsm2 hsmm hd2 hdm
  rw [hto, hadd, Pi.add_apply, hsm2, hsmm, Pi.smul_apply, Pi.smul_apply,
    smul_eq_mul, smul_eq_mul, hd2, hdm]
  have hg_z' : g (cToPlane z) =
      ∑ i : Fin 2, α i * planarFrozenDirectMode q a i (cToPlane z) := hg_z
  rw [hg_z', Fin.sum_univ_two]
  unfold planarFrozenDirectMode
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  exact mode_comb_eq_re_im α (dilPlanarMode q a (cToPlane z))

/-! ## 5. Coordinate functional `coordPi` and norm continuity via Hilbert adjoint -/

theorem dilW_congr_scale {m : ℝ} (hm : 1 < m) {a b : ℝ} (hab : a = b)
    (ha : 0 < a) (hb : 0 < b) :
    Planar.dilW hm ha = Planar.dilW hm hb := by
  subst hab
  rfl

/-- Clamped scale `max (1 + σ) (1 / 2) > 0`. -/
def clampScale (σ : ℝ) : ℝ :=
  max (1 + σ) (1 / 2)

theorem clampScale_pos (σ : ℝ) : 0 < clampScale σ :=
  lt_of_lt_of_le (by norm_num) (le_max_right _ _)

theorem continuous_clampScale : Continuous clampScale :=
  (continuous_const.add continuous_id).max continuous_const

theorem clampScale_eq_of_nonneg {σ : ℝ} (hσ : 0 ≤ σ) : clampScale σ = 1 + σ :=
  max_eq_left (by linarith)

/-- Complex sector-2 coordinate functional at clamped scale `clampScale σ`. -/
def coordLambda {m : ℝ} (hm : 1 < m) (ℓ₂ : Planar.ProfL2 m →L[ℂ] ℂ) (σ : ℝ) :
    Planar.L2w m →L[ℂ] ℂ :=
  (ℓ₂.comp (Planar.secProf m 2)).comp (Planar.dilW hm (inv_pos.2 (clampScale_pos σ)))

/-- Real coordinate functional `Xm m →L[ℝ] E2` at clamped scale `clampScale σ`. -/
def coordPi {m : ℝ} (hm : 1 < m) (ℓ₂ : Planar.ProfL2 m →L[ℂ] ℂ) (σ : ℝ) : Xm m →L[ℝ] E2 :=
  cToE2.comp (((coordLambda hm ℓ₂ σ).restrictScalars ℝ).comp (toL2w m).toContinuousLinearMap)

theorem coordPi_apply {m : ℝ} (hm : 1 < m) (ℓ₂ : Planar.ProfL2 m →L[ℂ] ℂ) (σ : ℝ) (f : Xm m) :
    coordPi hm ℓ₂ σ f = cToE2 (coordLambda hm ℓ₂ σ (toL2w m f)) := rfl

/-- Riesz representative in `Planar.L2w m` of `ℓ₂ ∘ secProf m 2`. -/
def rieszVec {m : ℝ} (ℓ₂ : Planar.ProfL2 m →L[ℂ] ℂ) : Planar.L2w m :=
  (InnerProductSpace.toDual ℂ (Planar.L2w m)).symm (ℓ₂.comp (Planar.secProf m 2))

/-- Inverse clamped scale curve in `Ioi 0`. -/
def scalePosCurve (σ : ℝ) : Set.Ioi (0 : ℝ) :=
  ⟨(clampScale σ)⁻¹, inv_pos.2 (clampScale_pos σ)⟩

/-- Adjoint dilation evaluation map on `Ioi 0`. -/
def adjMap {m : ℝ} (hm : 1 < m) (v : Planar.L2w m) (a : Set.Ioi (0 : ℝ)) : Planar.L2w m :=
  ContinuousLinearMap.adjoint (Planar.dilW hm a.2) v

/-- Hilbert-adjoint dilation curve `σ ↦ (J_{(clampScale σ)⁻¹})^* (rieszVec ℓ₂)` in `Planar.L2w m`. -/
def adjCurve {m : ℝ} (hm : 1 < m) (ℓ₂ : Planar.ProfL2 m →L[ℂ] ℂ) : ℝ → Planar.L2w m :=
  adjMap hm (rieszVec ℓ₂) ∘ scalePosCurve

theorem coordLambda_eq_inner {m : ℝ} (hm : 1 < m) (ℓ₂ : Planar.ProfL2 m →L[ℂ] ℂ)
    (σ : ℝ) (x : Planar.L2w m) :
    coordLambda hm ℓ₂ σ x = ⟪adjCurve hm ℓ₂ σ, x⟫_ℂ := by
  rw [adjCurve, Function.comp_apply, adjMap, scalePosCurve,
    ContinuousLinearMap.adjoint_inner_left, rieszVec, InnerProductSpace.toDual_symm_apply]
  rfl

theorem norm_coordPi_sub_le {m : ℝ} (hm : 1 < m) (ℓ₂ : Planar.ProfL2 m →L[ℂ] ℂ)
    (σ σ₀ : ℝ) :
    ‖coordPi hm ℓ₂ σ - coordPi hm ℓ₂ σ₀‖ ≤
      ‖cToE2‖ * ‖adjCurve hm ℓ₂ σ - adjCurve hm ℓ₂ σ₀‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _
    (mul_nonneg (norm_nonneg cToE2) (norm_nonneg _)) fun f => ?_
  have hsub : (coordPi hm ℓ₂ σ - coordPi hm ℓ₂ σ₀) f =
      cToE2 ⟪adjCurve hm ℓ₂ σ - adjCurve hm ℓ₂ σ₀, toL2w m f⟫_ℂ := by
    rw [sub_apply, coordPi_apply, coordPi_apply, ← map_sub,
      coordLambda_eq_inner, coordLambda_eq_inner, inner_sub_left]
  rw [hsub]
  calc ‖cToE2 ⟪adjCurve hm ℓ₂ σ - adjCurve hm ℓ₂ σ₀, toL2w m f⟫_ℂ‖
      ≤ ‖cToE2‖ * ‖⟪adjCurve hm ℓ₂ σ - adjCurve hm ℓ₂ σ₀, toL2w m f⟫_ℂ‖ := cToE2.le_opNorm _
    _ ≤ ‖cToE2‖ * (‖adjCurve hm ℓ₂ σ - adjCurve hm ℓ₂ σ₀‖ * ‖toL2w m f‖) :=
        mul_le_mul_of_nonneg_left (norm_inner_le_norm _ _) (norm_nonneg cToE2)
    _ = ‖cToE2‖ * ‖adjCurve hm ℓ₂ σ - adjCurve hm ℓ₂ σ₀‖ * ‖f‖ := by
        rw [(toL2w m).norm_map]
        ring

theorem continuous_coordPi {m : ℝ} (hm : 1 < m) (ℓ₂ : Planar.ProfL2 m →L[ℂ] ℂ) :
    Continuous (coordPi hm ℓ₂) := by
  have hb_cont : Continuous scalePosCurve :=
    Continuous.subtype_mk (continuous_clampScale.inv₀ fun σ => (clampScale_pos σ).ne') _
  have hadj : Continuous (adjMap hm (rieszVec ℓ₂)) :=
    PartI.dilWAdjStrongCont_of PartI.l2wCcDense PartI.dilWAdjCcCont m hm (rieszVec ℓ₂)
  rw [continuous_iff_continuousAt]
  intro σ₀
  rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
  have hadj_at : Tendsto (adjCurve hm ℓ₂) (𝓝 σ₀) (𝓝 (adjCurve hm ℓ₂ σ₀)) :=
    Filter.Tendsto.comp (hadj.continuousAt (x := scalePosCurve σ₀))
      (hb_cont.continuousAt (x := σ₀))
  have hlim : Tendsto (fun σ => ‖cToE2‖ * ‖adjCurve hm ℓ₂ σ - adjCurve hm ℓ₂ σ₀‖)
      (𝓝 σ₀) (𝓝 0) := by
    simpa only [mul_zero] using
      (tendsto_iff_norm_sub_tendsto_zero.1 hadj_at).const_mul ‖cToE2‖
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
    (fun _ => norm_nonneg _) (fun σ => norm_coordPi_sub_le hm ℓ₂ σ σ₀)

theorem coordLambda_apply_of_nonneg {m : ℝ} (hm : 1 < m) (ℓ₂ : Planar.ProfL2 m →L[ℂ] ℂ)
    {σ : ℝ} (hσ : 0 ≤ σ) (ha : 0 < 1 + σ) (W : Planar.L2w m) :
    coordLambda hm ℓ₂ σ W = ℓ₂ (Planar.secProf m 2 (Planar.dilW hm (inv_pos.2 ha) W)) := by
  have hd : Planar.dilW hm (inv_pos.2 (clampScale_pos σ)) = Planar.dilW hm (inv_pos.2 ha) :=
    dilW_congr_scale hm (congrArg Inv.inv (clampScale_eq_of_nonneg hσ)) _ _
  unfold coordLambda
  rw [hd]
  rfl

end UnforcedLeray.Short.IIb.PlanarSpectralBridge
