import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c5_3_1_1
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c5_1_1_1
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c5_3_1_1.SeedJetPlanar
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c5_3_1_1.SeedJetRadial
import UnforcedLeray.Lib.ComplexODEC

/-!
# `PartIII-a:T21/c5/3/1/1/1`: `C²` regularity and weighted jet decay of the seed dual kernels

Source `the November 2 reference manuscript`
lines 593-610 (`eq:short-seed-functional`: `ℓ(f) = J_q⁻¹ ∫ h f₂/k r dr`, the quotients at `k = 0`
removable) and 2891-2897 (the planar dual kernels and their fixed derivatives decay like
`|y|^{-2-j}`).

**Theorem** (`seedLamPJet2Decay_all`): for every `κ : PlanarFrameKernels` with
`IsSeedKernels κ`, the planar dual kernels `κ.lamP j` are `C²` and
`(1+‖z‖)‖Dλ_j(z)‖ ≤ C(1+|z₁|+|z₂|)^{-2}`, `‖D²λ_j(z)‖ ≤ C(1+|z₁|+|z₂|)^{-2}`.

**Proof.**
1. `CutFTCGradPerSum.lamP_eq_seedDualExplicit`: `λ₀ = c G(|y|) e^{-2iϑ}` with
   `G = R h/(e^{-r²/4} - iλ/2)` (`R = greenN 2`), and `λ₁ = \bar λ₀`.
2. `seed_greenN_eq_mode`: by uniqueness of the growing eigenvector (`Planar.L0_eigen_unique`) the
   seed profile is a multiple of the vorticity of the explicit Gaussian growing mode, so
   `R h(r) = μ β₀ r² b(r²)` with `b = regB c` the regular solution of `4(s b'' + 3 b') = κ_c b`.
3. Hence (`seedDualExplicit_zero_eq`) `λ₀(y) = F(\bar w)`, `w = y₁ + i y₂`, with the Cartesian
   angular-two function `F(u) = u² β(|u|²)` and the smooth profile `β(s) = K b(s)/(e^{-s/4} - iλ/2)`.
4. `betaFun_bounds` (`SeedJetRadial.lean`): `β, β', β''` decay like `(1+s)^{-2}, (1+s)^{-3},
   (1+s)^{-3}`; `angularTwo_jet2_decay` (`SeedJetPlanar.lean`): `‖DF‖ ≲ (1+|u|)^{-3}`,
   `‖D²F‖ ≲ (1+|u|)^{-2}`.
5. `kernel_jet2_transfer`: the bounds pass to `z ↦ F(conj(planeToC z))` (a linear map of norm
   `≤ 2`, with `1 + |z₁| + |z₂| ≤ 2(1 + |w|)`), and conjugation on the left preserves them.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ContDiff ComplexConjugate

namespace UnforcedLeray.Short.IIIa

namespace SeedJet2Aux

/-- **Step 2.** The seed profile's Green function is a multiple of the explicit mode profile:
`R h(r) = μ β₀ r² b(r²)` with `b = regB c`, for the Gaussian growing mode `(c, F)`. -/
theorem seed_greenN_eq_mode {lam : ℂ} {h : ℝ → ℂ} {hh : MemLp h 2 B0010.xGMeasure}
    {ℓ : B0010.XG →L[ℂ] ℂ} (hS : PartI.IsSeedXG lam (hh.toLp h) ℓ) :
    ∃ (c : ℂ) (F : ℝ → ℂ) (β₀ μ : ℂ), ComplexODEC.WholeLineData c F ∧
      ∀ r : ℝ, 0 < r → Planar.greenN 2 h r =
        μ * (β₀ * ((r ^ 2 : ℝ) : ℂ) * ComplexODEC.regB c (r ^ 2)) := by
  obtain ⟨c, him, hre0, hre1, -, F, hmode, -, hsmooth, h1, h2, h3, h4⟩ :=
    Rayleigh.Evans.exists_wholeLine_growing_mode
  have hF : ComplexODEC.WholeLineData c F := ⟨hmode, hsmooth, h1, h2, h3, h4⟩
  obtain ⟨g1, -, -⟩ := Rayleigh.Evans.growthRate_bounds him hre0 hre1
  have hw0 : (ComplexODEC.memLp_modeVort_XG hF).toLp (ComplexODEC.modeVort c F) ≠ 0 := by
    intro hw
    have hzeroX : ComplexODEC.modeVort c F =ᵐ[B0010.xGMeasure] (0 : ℝ → ℂ) := by
      filter_upwards [(ComplexODEC.memLp_modeVort_XG hF).coeFn_toLp,
        (show (⇑((ComplexODEC.memLp_modeVort_XG hF).toLp (ComplexODEC.modeVort c F)) :
            ℝ → ℂ) =ᵐ[B0010.xGMeasure] 0 from by
          rw [hw]
          exact Lp.coeFn_zero ℂ 2 B0010.xGMeasure)]
        with r e1 e2
      rw [← e1, e2]
    have hzeroR : ComplexODEC.modeVort c F =ᵐ[volume.restrict (Ioi (0 : ℝ))] (0 : ℝ → ℂ) :=
      B0012.restrict_ac.ae_le hzeroX
    obtain ⟨t, ht⟩ := hmode.nonzero
    apply ht
    have e := ComplexODEC.mode_eq_green hF (Real.exp t) (Real.exp_pos t)
    rw [ComplexODEC.greenN_congr_ae hzeroR (Real.exp t)] at e
    have e0 : Planar.greenN 2 (0 : ℝ → ℂ) (Real.exp t) = 0 := by simp [Planar.greenN]
    rw [e0, ComplexODEC.modeRadial, Real.log_exp] at e
    exact e
  obtain ⟨-, μ, hμ⟩ := Planar.L0_eigen_unique g1 hS.re_pos (ComplexODEC.L0_modeVort hF)
    hS.eigen hw0 hS.ne_zero
  have hae : h =ᵐ[volume.restrict (Ioi (0 : ℝ))] fun r => μ * ComplexODEC.modeVort c F r := by
    have hc := Lp.coeFn_smul μ
      ((ComplexODEC.memLp_modeVort_XG hF).toLp (ComplexODEC.modeVort c F))
    rw [← hμ] at hc
    have h1 : h =ᵐ[B0010.xGMeasure] fun r => μ * ComplexODEC.modeVort c F r := by
      filter_upwards [hh.coeFn_toLp, (ComplexODEC.memLp_modeVort_XG hF).coeFn_toLp, hc]
        with r a b c'
      rw [← a, c']
      simp [b]
    exact B0012.restrict_ac.ae_le h1
  obtain ⟨β₀, -, hβ⟩ := ComplexODEC.exists_mode_eq_regLog hF
  refine ⟨c, F, β₀, μ, hF, fun r hr => ?_⟩
  rw [ComplexODEC.greenN_congr_ae hae r, Planar.greenN_const_mul,
    ← ComplexODEC.mode_eq_green hF r hr, ComplexODEC.modeRadial_eq (fun t => (hβ t).1) hr]

/-- **Step 3.** The Cartesian form of the dual kernel `λ₀`. -/
theorem seedDualExplicit_zero_eq {lam : ℂ} (hre : 0 < lam.re) {h : ℝ → ℂ} {c β₀ μ : ℂ}
    (hG : ∀ r : ℝ, 0 < r → Planar.greenN 2 h r =
      μ * (β₀ * ((r ^ 2 : ℝ) : ℂ) * ComplexODEC.regB c (r ^ 2)))
    (z : ℝ × ℝ) :
    CutFTCGradPerSum.seedDualExplicit lam h 0 z =
      conj (planeToC z) ^ 2 * betaFun c (Complex.I * lam / 2)
        ((PartI.seedJ h)⁻¹ / (2 * Real.pi : ℂ) * μ * β₀) (‖conj (planeToC z)‖ ^ 2) := by
  simp only [CutFTCGradPerSum.seedDualExplicit, ↓reduceIte]
  rw [Complex.norm_conj]
  generalize planeToC z = W
  by_cases hw : W = 0
  · subst hw
    simp [CutFTCGradPerSum.seedDualRadialG]
  · have hr : 0 < ‖W‖ := norm_pos_iff.mpr hw
    rw [CutFTCGradPerSum.seedDualRadialG, if_pos hr, hG _ hr]
    unfold betaFun denM gaussE4 Planar.NUE.Ang.angPhase
    have hrad : GaussianVortex.radialOmega ‖W‖ = Real.exp (-(‖W‖ ^ 2 / 4)) := rfl
    rw [hrad]
    set D : ℂ := ((Real.exp (-(‖W‖ ^ 2 / 4)) : ℝ) : ℂ) - Complex.I * lam / 2 with hD
    have hD0 : D ≠ 0 := PartI.adjEig_den_ne hre _
    have hn : (‖W‖ : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
    have hk : (‖W‖ : ℂ) ^ 2 = W * conj W := by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
      push_cast
      ring
    have hphase : (W / (‖W‖ : ℂ)) ^ (-2 : ℤ) = (‖W‖ : ℂ) ^ 2 / W ^ 2 := by
      rw [zpow_neg, zpow_two, div_mul_div_comm, inv_div]
      ring
    have hsq : (‖W‖ : ℂ) ^ 2 * ((‖W‖ : ℂ) ^ 2 / W ^ 2) = conj W ^ 2 := by
      rw [hk]
      field_simp
    rw [hphase]
    push_cast
    calc (PartI.seedJ h)⁻¹ / (2 * (Real.pi : ℂ)) *
          (μ * (β₀ * (‖W‖ : ℂ) ^ 2 * ComplexODEC.regB c (‖W‖ ^ 2)) / D) *
          ((‖W‖ : ℂ) ^ 2 / W ^ 2)
        = (PartI.seedJ h)⁻¹ / (2 * (Real.pi : ℂ)) * μ * β₀ *
            (ComplexODEC.regB c (‖W‖ ^ 2) * D⁻¹) *
            ((‖W‖ : ℂ) ^ 2 * ((‖W‖ : ℂ) ^ 2 / W ^ 2)) := by
          rw [div_eq_mul_inv _ D]
          ring
      _ = _ := by
          rw [hsq, hD]
          ring

/-- `λ₁ = \bar λ₀` for the explicit dual kernel pair. -/
theorem seedDualExplicit_one_eq_conj (lam : ℂ) (h : ℝ → ℂ) :
    CutFTCGradPerSum.seedDualExplicit lam h 1 =
      fun y => conj (CutFTCGradPerSum.seedDualExplicit lam h 0 y) := by
  funext y
  simp only [CutFTCGradPerSum.seedDualExplicit, show (1 : Fin 2) ≠ 0 by decide, ↓reduceIte,
    map_mul]
  congr 1
  unfold Planar.NUE.Ang.angPhase
  by_cases hy : planeToC y = 0
  · simp [hy]
  · simp only [zpow_neg, zpow_two, map_inv₀, map_mul, map_div₀, Complex.conj_ofReal]
    have hsq : planeToC y * conj (planeToC y) = (‖planeToC y‖ : ℂ) ^ 2 := by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.ofReal_pow]
    have hn : (‖planeToC y‖ : ℂ) ≠ 0 := by exact_mod_cast (norm_pos_iff.mpr hy).ne'
    have hcy : conj (planeToC y) ≠ 0 := star_ne_zero.mpr hy
    have hdiv : (‖planeToC y‖ : ℂ) / conj (planeToC y) = planeToC y / (‖planeToC y‖ : ℂ) := by
      rw [div_eq_div_iff hcy hn]
      linear_combination -hsq
    rw [mul_inv, inv_div, hdiv]

/-- `z ↦ conj (planeToC z)` as a continuous linear map `ℝ × ℝ → ℂ`. -/
def conjPlaneCLM : ℝ × ℝ →L[ℝ] ℂ :=
  (Complex.conjCLE : ℂ →L[ℝ] ℂ).comp (Complex.equivRealProdCLM.symm : ℝ × ℝ →L[ℝ] ℂ)

theorem conjPlaneCLM_apply (z : ℝ × ℝ) : conjPlaneCLM z = conj (planeToC z) := by
  simp only [conjPlaneCLM, ContinuousLinearMap.coe_comp, Function.comp_apply,
    ContinuousLinearEquiv.coe_coe, Complex.equivRealProdCLM_symm_apply, Complex.conjCLE_apply]
  congr 1
  apply Complex.ext <;> simp [planeToC]

theorem abs_fst_le_norm_planeToC (z : ℝ × ℝ) : |z.1| ≤ ‖planeToC z‖ := by
  have h := Complex.abs_re_le_norm (planeToC z)
  simpa [planeToC] using h

theorem abs_snd_le_norm_planeToC (z : ℝ × ℝ) : |z.2| ≤ ‖planeToC z‖ := by
  have h := Complex.abs_im_le_norm (planeToC z)
  simpa [planeToC] using h

theorem norm_conjPlaneCLM_le : ‖conjPlaneCLM‖ ≤ 2 := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by norm_num) fun z => ?_
  rw [conjPlaneCLM_apply, Complex.norm_conj]
  refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
  have h1 : |(planeToC z).re| ≤ ‖z‖ := by
    have := norm_fst_le z
    simpa [planeToC, Real.norm_eq_abs] using this
  have h2 : |(planeToC z).im| ≤ ‖z‖ := by
    have := norm_snd_le z
    simpa [planeToC, Real.norm_eq_abs] using this
  linarith

theorem le_top_nat (n : ℕ) : ((n : ℕ) : ℕ∞ω) ≤ ∞ := by exact_mod_cast le_top

theorem le_top_two : (2 : ℕ∞ω) ≤ ∞ := le_top_nat 2

/-- **Step 5.** Transfer of the weighted jet bounds from `F` on `ℂ` to `z ↦ F(conj(planeToC z))`. -/
theorem kernel_jet2_transfer {F₀ : ℂ → ℂ} (hF : ContDiff ℝ ∞ F₀) {C : ℝ}
    (hb : ∀ w, ‖fderiv ℝ F₀ w‖ * (1 + ‖w‖) ^ 3 ≤ C ∧
      ‖iteratedFDeriv ℝ 2 F₀ w‖ * (1 + ‖w‖) ^ 2 ≤ C)
    {f : ℝ × ℝ → ℂ} (hf : ∀ z, f z = F₀ (conj (planeToC z))) :
    ContDiff ℝ ∞ f ∧ ∀ z : ℝ × ℝ,
      (1 + ‖z‖) * ‖fderiv ℝ f z‖ ≤ 8 * C * ((1 + |z.1| + |z.2|)⁻¹) ^ 2 ∧
      ‖iteratedFDeriv ℝ 2 f z‖ ≤ 16 * C * ((1 + |z.1| + |z.2|)⁻¹) ^ 2 := by
  have hfe : f = F₀ ∘ conjPlaneCLM :=
    funext fun z => by rw [hf z, Function.comp_apply, conjPlaneCLM_apply]
  have hcd : ContDiff ℝ ∞ f := by
    rw [hfe]
    exact hF.comp conjPlaneCLM.contDiff
  refine ⟨hcd, fun z => ?_⟩
  have hcomp : ∀ i : ℕ, i ≤ 2 →
      ‖iteratedFDeriv ℝ i f z‖ ≤ ‖iteratedFDeriv ℝ i F₀ (conjPlaneCLM z)‖ * 2 ^ i := by
    intro i hi
    have hi' : ((i : ℕ) : ℕ∞ω) ≤ ∞ := by exact_mod_cast le_top
    rw [hfe, ContinuousLinearMap.iteratedFDeriv_comp_right conjPlaneCLM hF z hi']
    refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    gcongr
    exact norm_conjPlaneCLM_le
  have hw : ‖conjPlaneCLM z‖ = ‖planeToC z‖ := by rw [conjPlaneCLM_apply, Complex.norm_conj]
  obtain ⟨hb1, hb2⟩ := hb (conjPlaneCLM z)
  rw [hw] at hb1 hb2
  set ρ : ℝ := ‖planeToC z‖ with hρ
  set A : ℝ := 1 + ρ with hA
  set Z : ℝ := 1 + |z.1| + |z.2| with hZ
  have hρ0 : 0 ≤ ρ := norm_nonneg _
  have hA1 : 1 ≤ A := by linarith
  have hZ1 : 1 ≤ Z := by
    have := abs_nonneg z.1
    have := abs_nonneg z.2
    linarith
  have hZA : Z ≤ 2 * A := by
    have := abs_fst_le_norm_planeToC z
    have := abs_snd_le_norm_planeToC z
    linarith
  have hzA : 1 + ‖z‖ ≤ A := by
    have : ‖z‖ ≤ ρ := by
      rw [Prod.norm_def]
      refine max_le ?_ ?_
      · rw [Real.norm_eq_abs]; exact abs_fst_le_norm_planeToC z
      · rw [Real.norm_eq_abs]; exact abs_snd_le_norm_planeToC z
    linarith
  have hZinv : 1 ≤ 4 * A ^ 2 * (Z⁻¹) ^ 2 := by
    have hZ0 : 0 < Z := by linarith
    rw [inv_pow, ← div_eq_mul_inv, le_div_iff₀ (by positivity), one_mul]
    nlinarith
  have hZi0 : 0 ≤ (Z⁻¹) ^ 2 := by positivity
  constructor
  · have h1 := hcomp 1 (by norm_num)
    rw [norm_iteratedFDeriv_one, norm_iteratedFDeriv_one, pow_one] at h1
    set d := ‖fderiv ℝ F₀ (conjPlaneCLM z)‖ with hd
    have hd0 : 0 ≤ d := norm_nonneg _
    calc (1 + ‖z‖) * ‖fderiv ℝ f z‖ ≤ A * (d * 2) := by
          gcongr
      _ ≤ A * (d * 2) * (4 * A ^ 2 * (Z⁻¹) ^ 2) :=
          le_mul_of_one_le_right (by positivity) hZinv
      _ = 8 * (d * A ^ 3) * (Z⁻¹) ^ 2 := by ring
      _ ≤ 8 * C * (Z⁻¹) ^ 2 := by gcongr
  · have h2 := hcomp 2 le_rfl
    set d := ‖iteratedFDeriv ℝ 2 F₀ (conjPlaneCLM z)‖ with hd
    have hd0 : 0 ≤ d := norm_nonneg _
    calc ‖iteratedFDeriv ℝ 2 f z‖ ≤ d * 2 ^ 2 := h2
      _ ≤ d * 2 ^ 2 * (4 * A ^ 2 * (Z⁻¹) ^ 2) :=
          le_mul_of_one_le_right (by positivity) hZinv
      _ = 16 * (d * A ^ 2) * (Z⁻¹) ^ 2 := by ring
      _ ≤ 16 * C * (Z⁻¹) ^ 2 := by gcongr

/-- Conjugation on the left does not increase iterated derivative norms. -/
theorem norm_iteratedFDeriv_conj_le {f : ℝ × ℝ → ℂ} (hf : ContDiff ℝ ∞ f) (z : ℝ × ℝ) (i : ℕ) :
    ‖iteratedFDeriv ℝ i (fun x => conj (f x)) z‖ ≤ ‖iteratedFDeriv ℝ i f z‖ := by
  have e : (fun x => conj (f x)) = (Complex.conjCLE : ℂ →L[ℝ] ℂ) ∘ f := by
    funext x
    simp
  rw [e]
  have hi : ((i : ℕ) : ℕ∞ω) ≤ ∞ := by exact_mod_cast le_top
  refine ((Complex.conjCLE : ℂ →L[ℝ] ℂ).norm_iteratedFDeriv_comp_left hf.contDiffAt hi).trans ?_
  rw [Complex.conjCLE_norm, one_mul]

end SeedJet2Aux

open SeedJet2Aux in
/-- **`PartIII-a:T21/c5/3/1/1/1`** (SP 593-610, 2891-2897): the Part I seed dual kernels are `C²`
with weighted first- and second-jet decay `O((1 + |z₁| + |z₂|)⁻²)`. -/
theorem seedLamPJet2Decay_all (kappa : UnforcedLeray.Short.IIIa.PlanarFrameKernels) :
    UnforcedLeray.Short.IIIa.SeedLamPJet2Decay kappa := by
  intro hκ
  obtain ⟨lam, h, hh, ℓ, hIS, -, -, -, hlamP⟩ := CutFTCGradPerSum.lamP_eq_seedDualExplicit hκ
  obtain ⟨c, F, β₀, μ, hF, hG⟩ := seed_greenN_eq_mode hIS
  have hre := hIS.re_pos
  have ha₀ : (Complex.I * lam / 2).im ≠ 0 := by
    have : (Complex.I * lam / 2).im = lam.re / 2 := by simp [Complex.div_ofNat_im]
    rw [this]
    positivity
  set K : ℂ := (PartI.seedJ h)⁻¹ / (2 * Real.pi : ℂ) * μ * β₀ with hK
  obtain ⟨hβc, B, hB0, hB1, hB2⟩ := betaFun_bounds hF ha₀ K
  set β : ℝ → ℂ := betaFun c (Complex.I * lam / 2) K with hβ
  have hBnn : 0 ≤ B := le_trans (by positivity) (hB0 0 le_rfl)
  have hF0c : ContDiff ℝ ∞ (fun w : ℂ => w ^ 2 * β (‖w‖ ^ 2)) := Planar.contDiff_angularTwo hβc
  have hjet : ∀ w : ℂ,
      ‖fderiv ℝ (fun w : ℂ => w ^ 2 * β (‖w‖ ^ 2)) w‖ * (1 + ‖w‖) ^ 3 ≤ 272 * B ∧
      ‖iteratedFDeriv ℝ 2 (fun w : ℂ => w ^ 2 * β (‖w‖ ^ 2)) w‖ * (1 + ‖w‖) ^ 2 ≤ 272 * B := by
    intro w
    obtain ⟨j1, j2⟩ := angularTwo_jet2_decay (hβc.of_le le_top_two) hB0 hB1 hB2 w
    exact ⟨j1.trans (by linarith), j2⟩
  have h0eq : ∀ z, kappa.lamP 0 z =
      (fun w : ℂ => w ^ 2 * β (‖w‖ ^ 2)) (conj (planeToC z)) := fun z => by
    rw [hlamP 0]
    exact seedDualExplicit_zero_eq hre hG z
  obtain ⟨hcd0, hbd0⟩ := kernel_jet2_transfer hF0c hjet h0eq
  have h1eq : kappa.lamP 1 = fun z => conj (kappa.lamP 0 z) := by
    rw [hlamP 1, hlamP 0, seedDualExplicit_one_eq_conj]
  have hcd1 : ContDiff ℝ ∞ (kappa.lamP 1) := by
    rw [h1eq]
    exact Complex.conjCLE.contDiff.comp hcd0
  refine ⟨fun j => ?_, 16 * (272 * B), by positivity, fun j z => ?_, fun j z => ?_⟩
  · fin_cases j
    · exact hcd0.of_le le_top_two
    · exact hcd1.of_le le_top_two
  · have hb := (hbd0 z).1
    have hZ : 0 ≤ ((1 + |z.1| + |z.2|)⁻¹) ^ 2 := by positivity
    have hle : 8 * (272 * B) * ((1 + |z.1| + |z.2|)⁻¹) ^ 2 ≤
        16 * (272 * B) * ((1 + |z.1| + |z.2|)⁻¹) ^ 2 := by
      gcongr
      norm_num
    fin_cases j
    · exact hb.trans hle
    · show (1 + ‖z‖) * ‖fderiv ℝ (kappa.lamP 1) z‖ ≤ _
      rw [h1eq]
      have hc := norm_iteratedFDeriv_conj_le hcd0 z 1
      rw [norm_iteratedFDeriv_one, norm_iteratedFDeriv_one] at hc
      refine le_trans ?_ (hb.trans hle)
      gcongr
  · have hb := (hbd0 z).2
    fin_cases j
    · exact hb
    · show ‖iteratedFDeriv ℝ 2 (kappa.lamP 1) z‖ ≤ _
      rw [h1eq]
      exact (norm_iteratedFDeriv_conj_le hcd0 z 2).trans hb

end UnforcedLeray.Short.IIIa
