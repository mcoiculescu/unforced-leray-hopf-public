import UnforcedLeray.Loc.Hyp.BackgroundStrongForm.ProductTest
import UnforcedLeray.Loc.Hyp.HeatProfileRegularity.Scaling

/-!
# H-BgStrong, helpers: heat smoothing of tests and its dilation commutator

Support for `Loc/Hyp/BackgroundStrongForm/HeatEquation.lean` (proof of
`HeatProfileEquation`, `paper/main.tex` lines 159–163, blueprint unit B0707).

For a vector test `χ` and `h > 0`, `Ψ_χ = e^{hΔ}χ = ∫ K_h(x) χ(· - x) dx` (`kconv`) is `C¹`
(`hasFDerivAt_kconv`, differentiation under the integral sign from `Units/B0306/Conv.lean`),
`Ψ_χ` and `DΨ_χ` decay like every power of `(1 + |v|)⁻¹` (`norm_kconv_le`, Peetre's inequality
and the Gaussian moments of `Loc/Hyp/HeatProfileRegularity/Smoothing.lean`), and the dilation
generator commutes with the heat flow up to a Laplacian:

  `DΨ_χ(v) v = Ψ_{(y·∇)χ}(v) - 2h Ψ_{Δχ}(v)`   (`fderiv_kconv_self`),

from `x K_h(x) = -2h ∇K_h(x)` and one integration by parts. This is the identity
`y·∇e^{hΔ} = e^{hΔ}(y·∇ - 2hΔ)` behind `∂_τH = hΔH + ½y·∇H + ½H`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Metric
open scoped ContDiff Topology ENNReal

namespace UnforcedLeray.Blueprint.HypBg

open UnforcedLeray.HeatProfileReg (integrable_kernel_mul_one_add_pow inv_one_add_pow_le)
open UnforcedLeray.Blueprint.L13 (radialDeriv isVectorTest_radialDeriv)

section KConv

variable {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- `e^{hΔ}g(v) = ∫ K_h(x) g(v - x) dx`. -/
def kconv (h : ℝ) (g : Space → F) (v : Space) : F := ∫ x, Heat.kernel h x • g (v - x)

/-- A continuous compactly supported function decays like every power. -/
theorem decay_of_compact {g : Space → F} (hc : Continuous g) (hs : HasCompactSupport g)
    (m : ℕ) : ∃ M : ℝ, 0 ≤ M ∧ ∀ x, ‖g x‖ ≤ M / (1 + ‖x‖) ^ m := by
  have hcont : Continuous fun x => ‖g x‖ * (1 + ‖x‖) ^ m := hc.norm.mul (by fun_prop)
  have hsupp : HasCompactSupport fun x => ‖g x‖ * (1 + ‖x‖) ^ m := hs.norm.mul_right
  obtain ⟨M, hM⟩ := hcont.bounded_above_of_compact_support hsupp
  refine ⟨max M 0, le_max_right _ _, fun x => ?_⟩
  have hpos : 0 < (1 + ‖x‖) ^ m := by positivity
  rw [le_div_iff₀ hpos]
  have h1 := hM x
  rw [Real.norm_of_nonneg (by positivity)] at h1
  exact h1.trans (le_max_left _ _)

theorem integrable_kconv_integrand {h : ℝ} (hh : 0 < h) {g : Space → F} (hg : Continuous g)
    {B : ℝ} (hB : ∀ x, ‖g x‖ ≤ B) (v : Space) :
    Integrable (fun x => Heat.kernel h x • g (v - x)) :=
  (Heat.kernel_integrable hh).smul_of_top_left
    (memLp_top_of_bound (hg.comp (continuous_const.sub continuous_id)).aestronglyMeasurable B
      (Eventually.of_forall fun x => hB (v - x)))

/-- **Decay of the heat smoothing.** -/
theorem norm_kconv_le {h : ℝ} (hh : 0 < h) {g : Space → F} {M : ℝ} {m : ℕ} (hM0 : 0 ≤ M)
    (hM : ∀ x, ‖g x‖ ≤ M / (1 + ‖x‖) ^ m) (v : Space) :
    ‖kconv h g v‖ ≤ (M * ∫ x, Heat.kernel h x * (1 + ‖x‖) ^ m) / (1 + ‖v‖) ^ m := by
  have hI := integrable_kernel_mul_one_add_pow hh m
  have hb : ∀ x, ‖Heat.kernel h x • g (v - x)‖ ≤
      (M / (1 + ‖v‖) ^ m) * (Heat.kernel h x * (1 + ‖x‖) ^ m) := by
    intro x
    have hK := Heat.kernel_nonneg hh x
    rw [norm_smul, Real.norm_of_nonneg hK]
    have h1 := hM (v - x)
    have h2 := inv_one_add_pow_le v x m
    have hpv : 0 < (1 + ‖v‖) ^ m := by positivity
    have hpvx : 0 < (1 + ‖v - x‖) ^ m := by positivity
    calc Heat.kernel h x * ‖g (v - x)‖ ≤ Heat.kernel h x * (M / (1 + ‖v - x‖) ^ m) :=
          mul_le_mul_of_nonneg_left h1 hK
      _ = Heat.kernel h x * M * (1 / (1 + ‖v - x‖) ^ m) := by ring
      _ ≤ Heat.kernel h x * M * ((1 + ‖x‖) ^ m / (1 + ‖v‖) ^ m) :=
          mul_le_mul_of_nonneg_left h2 (mul_nonneg hK hM0)
      _ = (M / (1 + ‖v‖) ^ m) * (Heat.kernel h x * (1 + ‖x‖) ^ m) := by ring
  calc ‖kconv h g v‖ ≤ ∫ x, (M / (1 + ‖v‖) ^ m) * (Heat.kernel h x * (1 + ‖x‖) ^ m) :=
        norm_integral_le_of_norm_le (hI.const_mul _) (Eventually.of_forall hb)
    _ = (M * ∫ x, Heat.kernel h x * (1 + ‖x‖) ^ m) / (1 + ‖v‖) ^ m := by
        rw [integral_const_mul]
        ring

theorem kconv_add {h : ℝ} (hh : 0 < h) {g₁ g₂ : Space → F} (hg₁ : Continuous g₁)
    (hg₂ : Continuous g₂) {B₁ B₂ : ℝ} (hB₁ : ∀ x, ‖g₁ x‖ ≤ B₁) (hB₂ : ∀ x, ‖g₂ x‖ ≤ B₂)
    (v : Space) : kconv h (fun x => g₁ x + g₂ x) v = kconv h g₁ v + kconv h g₂ v := by
  unfold kconv
  simp only [smul_add]
  exact integral_add (integrable_kconv_integrand hh hg₁ hB₁ v)
    (integrable_kconv_integrand hh hg₂ hB₂ v)

theorem kconv_smul (h c : ℝ) (g : Space → F) (v : Space) :
    kconv h (fun x => c • g x) v = c • kconv h g v := by
  unfold kconv
  rw [← integral_smul]
  congr 1
  funext x
  exact smul_comm _ _ _

end KConv

/-! ## Vector tests -/

variable {h : ℝ} {χ : Space → Space}

theorem vtest_bound (hχ : IsVectorTest χ) : ∃ B, ∀ x, ‖χ x‖ ≤ B :=
  hχ.smooth.continuous.bounded_above_of_compact_support hχ.compact

theorem vtest_fderiv_bound (hχ : IsVectorTest χ) :
    ∃ B, ∀ x, ‖fderiv ℝ χ x‖ ≤ B :=
  (hχ.smooth.continuous_fderiv (by simp)).bounded_above_of_compact_support
    (hχ.compact.fderiv (𝕜 := ℝ))

theorem continuous_kconv (hh : 0 < h) (hχ : IsVectorTest χ) : Continuous (kconv h χ) := by
  obtain ⟨M0, hM0⟩ := vtest_bound hχ
  obtain ⟨M1, hM1⟩ := vtest_fderiv_bound hχ
  refine continuous_iff_continuousAt.mpr fun v => ?_
  exact (B0306.hasFDerivAt_bconv (ContinuousLinearMap.lsmul ℝ ℝ) (Heat.kernel_integrable hh)
    (hχ.smooth.of_le (by simp)) hM0 hM1 v).continuousAt

theorem hasFDerivAt_kconv (hh : 0 < h) (hχ : IsVectorTest χ) (v : Space) :
    HasFDerivAt (kconv h χ) (kconv h (fderiv ℝ χ) v) v := by
  obtain ⟨M0, hM0⟩ := vtest_bound hχ
  obtain ⟨M1, hM1⟩ := vtest_fderiv_bound hχ
  have hd := B0306.hasFDerivAt_bconv (ContinuousLinearMap.lsmul ℝ ℝ) (Heat.kernel_integrable hh)
    (hχ.smooth.of_le (by simp)) hM0 hM1 v
  have e1 : B0306.bconv (ContinuousLinearMap.lsmul ℝ ℝ) (Heat.kernel h) χ = kconv h χ := rfl
  have e2 : B0306.bconv ((ContinuousLinearMap.lsmul ℝ ℝ).precompR Space) (Heat.kernel h)
      (fderiv ℝ χ) v = kconv h (fderiv ℝ χ) v := by
    unfold B0306.bconv kconv
    congr 1
  rw [e1, e2] at hd
  exact hd

theorem fderiv_kconv_apply (hh : 0 < h) (hχ : IsVectorTest χ) (v a : Space) :
    fderiv ℝ (kconv h χ) v a = ∫ x, Heat.kernel h x • fderiv ℝ χ (v - x) a := by
  obtain ⟨M1, hM1⟩ := vtest_fderiv_bound hχ
  rw [(hasFDerivAt_kconv hh hχ v).fderiv, kconv, ContinuousLinearMap.integral_apply
    (integrable_kconv_integrand hh (hχ.smooth.continuous_fderiv (by simp)) hM1 v)]
  rfl

/-- **Decay of `Ψ_χ` and `DΨ_χ`.** -/
theorem kconv_decay (hh : 0 < h) (hχ : IsVectorTest χ) (m : ℕ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ v, ‖kconv h χ v‖ ≤ M / (1 + ‖v‖) ^ m ∧
      ‖fderiv ℝ (kconv h χ) v‖ ≤ M / (1 + ‖v‖) ^ m := by
  obtain ⟨M0, hM00, hM0⟩ := decay_of_compact hχ.smooth.continuous hχ.compact m
  obtain ⟨M1, hM10, hM1⟩ := decay_of_compact (hχ.smooth.continuous_fderiv (by simp))
    (hχ.compact.fderiv (𝕜 := ℝ)) m
  set I := ∫ x, Heat.kernel h x * (1 + ‖x‖) ^ m
  have hI : 0 ≤ I := integral_nonneg fun x =>
    mul_nonneg (Heat.kernel_nonneg hh x) (by positivity)
  refine ⟨max (M0 * I) (M1 * I), (mul_nonneg hM00 hI).trans (le_max_left _ _), fun v => ?_⟩
  have hpos : 0 < (1 + ‖v‖) ^ m := by positivity
  refine ⟨(norm_kconv_le hh hM00 hM0 v).trans ?_, ?_⟩
  · exact div_le_div_of_nonneg_right (le_max_left _ _) hpos.le
  · rw [(hasFDerivAt_kconv hh hχ v).fderiv]
    exact (norm_kconv_le hh hM10 hM1 v).trans
      (div_le_div_of_nonneg_right (le_max_right _ _) hpos.le)

/-! ## The dilation commutator -/

theorem kernel_fderiv_coord (hh : 0 < h) (x : Space) (j : Fin 3) :
    x j * Heat.kernel h x = -(2 * h) * fderiv ℝ (Heat.kernel h) x (coordinateVector j) := by
  have e := Heat.Gaussian.kernel_fderiv (4 * h) (coordinateVector j) x
  change fderiv ℝ (Heat.Gaussian.kernel (4 * h)) x (coordinateVector j) = _ at e
  change _ = -(2 * h) * fderiv ℝ (Heat.Gaussian.kernel (4 * h)) x (coordinateVector j)
  rw [e, Heat.Gaussian.firstKernel]
  have hi : inner ℝ x (coordinateVector j) = x j := by
    simp [coordinateVector, EuclideanSpace.inner_single_right]
  rw [hi]
  change x j * Heat.Gaussian.kernel (4 * h) x = _
  field_simp
  ring

theorem coord_expand (L : Space →L[ℝ] Space) (x : Space) :
    L x = ∑ j : Fin 3, x j • L (coordinateVector j) := by
  conv_lhs => rw [← L01.space_sum_single x]
  simp [map_sum, map_smul, coordinateVector]

theorem hasCompactSupport_comp_sub {g : Space → Space} (hg : HasCompactSupport g) (v : Space) :
    HasCompactSupport fun x => g (v - x) :=
  hg.comp_homeomorph (Homeomorph.subLeft v)

/-- One integration by parts against the Gaussian: `∫ ∂ⱼK(x) ∂ⱼχ(v - x) dx = Ψ_{∂ⱼ∂ⱼχ}(v)`. -/
theorem integral_kernel_partial (hh : 0 < h) (hχ : IsVectorTest χ) (v : Space) (j : Fin 3) :
    ∫ x, fderiv ℝ (Heat.kernel h) x (coordinateVector j) • testPartial χ j (v - x) =
      kconv h (testPartial (testPartial χ j) j) v := by
  have hχj := L14.isVectorTest_testPartial hχ j
  have hχjj := L14.isVectorTest_testPartial hχj j
  set g : Space → Space := fun x => testPartial χ j (v - x) with hg
  have hKs : ContDiff ℝ ∞ (Heat.kernel h) := Heat.Gaussian.kernel_smooth (4 * h)
  have hgd : ∀ x, HasFDerivAt g (-(fderiv ℝ (testPartial χ j) (v - x))) x := by
    intro x
    have h1 : HasFDerivAt (testPartial χ j) (fderiv ℝ (testPartial χ j) (v - x)) (v - x) :=
      (hχj.smooth.differentiable (by simp) _).hasFDerivAt
    have h2 : HasFDerivAt (fun x : Space => v - x) (-ContinuousLinearMap.id ℝ Space) x :=
      (hasFDerivAt_id x).const_sub v
    have h3 := h1.comp x h2
    have h4 : (fderiv ℝ (testPartial χ j) (v - x)).comp (-ContinuousLinearMap.id ℝ Space) =
        -(fderiv ℝ (testPartial χ j) (v - x)) := by
      ext a
      simp
    rw [h4] at h3
    exact h3
  have hgfd : ∀ x, fderiv ℝ g x (coordinateVector j) =
      -testPartial (testPartial χ j) j (v - x) := by
    intro x
    rw [(hgd x).fderiv]
    rfl
  have hgc : HasCompactSupport g := hasCompactSupport_comp_sub hχj.compact v
  have hgcont : Continuous g := hχj.smooth.continuous.comp (continuous_const.sub continuous_id)
  have hKd : Continuous fun x => fderiv ℝ (Heat.kernel h) x (coordinateVector j) :=
    (hKs.continuous_fderiv (by simp)).clm_apply continuous_const
  have hi2 : Integrable (fun x => Heat.kernel h x • fderiv ℝ g x (coordinateVector j)) := by
    simp only [hgfd]
    have hc2 : Continuous fun x => -testPartial (testPartial χ j) j (v - x) :=
      (hχjj.smooth.continuous.comp (continuous_const.sub continuous_id)).neg
    exact (hKs.continuous.smul hc2).integrable_of_hasCompactSupport
      (hasCompactSupport_comp_sub hχjj.compact v).neg.smul_left
  have hibp := integral_smul_fderiv_eq_neg_fderiv_smul_of_integrable (μ := volume)
    (f := Heat.kernel h) (g := g) (v := coordinateVector j)
    ((hKd.smul hgcont).integrable_of_hasCompactSupport hgc.smul_left) hi2
    ((hKs.continuous.smul hgcont).integrable_of_hasCompactSupport hgc.smul_left)
    (fun x _ => (hKs.differentiable (by simp) x))
    (fun x _ => (hgd x).differentiableAt)
  simp only [hgfd, smul_neg, integral_neg, neg_inj] at hibp
  rw [← hibp]
  rfl

theorem kconv_testLaplacian (hh : 0 < h) (hχ : IsVectorTest χ) (v : Space) :
    kconv h (testLaplacian χ) v = ∑ j : Fin 3, kconv h (testPartial (testPartial χ j) j) v := by
  have hint : ∀ j ∈ (Finset.univ : Finset (Fin 3)),
      Integrable (fun x => Heat.kernel h x • testPartial (testPartial χ j) j (v - x)) := by
    intro j _
    have hjj := L14.isVectorTest_testPartial (L14.isVectorTest_testPartial hχ j) j
    obtain ⟨B, hB⟩ := vtest_bound hjj
    exact integrable_kconv_integrand hh hjj.smooth.continuous hB v
  unfold kconv testLaplacian
  simp only [Finset.smul_sum]
  exact integral_finset_sum _ hint

/-- **The dilation commutator** `DΨ_χ(v)v = Ψ_{(y·∇)χ}(v) - 2hΨ_{Δχ}(v)`. -/
theorem fderiv_kconv_self (hh : 0 < h) (hχ : IsVectorTest χ) (v : Space) :
    fderiv ℝ (kconv h χ) v v =
      kconv h (radialDeriv χ) v - (2 * h) • kconv h (testLaplacian χ) v := by
  rw [fderiv_kconv_apply hh hχ v v]
  have hpt : ∀ x, Heat.kernel h x • fderiv ℝ χ (v - x) v =
      Heat.kernel h x • radialDeriv χ (v - x) +
        ∑ j : Fin 3, (-(2 * h)) • (fderiv ℝ (Heat.kernel h) x (coordinateVector j) •
          testPartial χ j (v - x)) := by
    intro x
    have e1 : fderiv ℝ χ (v - x) v = fderiv ℝ χ (v - x) (v - x) + fderiv ℝ χ (v - x) x := by
      rw [← map_add, sub_add_cancel]
    rw [e1, smul_add, coord_expand (fderiv ℝ χ (v - x)) x, Finset.smul_sum]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [smul_smul, smul_smul, ← kernel_fderiv_coord hh x j, mul_comm (Heat.kernel h x)]
    rfl
  have hR := isVectorTest_radialDeriv hχ
  obtain ⟨BR, hBR⟩ := vtest_bound hR
  have hKs : ContDiff ℝ ∞ (Heat.kernel h) := Heat.Gaussian.kernel_smooth (4 * h)
  have hKd : ∀ j : Fin 3, Continuous fun x => fderiv ℝ (Heat.kernel h) x (coordinateVector j) :=
    fun j => (hKs.continuous_fderiv (by simp)).clm_apply continuous_const
  have hBj : ∀ j ∈ (Finset.univ : Finset (Fin 3)), Integrable (fun x => (-(2 * h)) •
      (fderiv ℝ (Heat.kernel h) x (coordinateVector j) • testPartial χ j (v - x))) := by
    intro j _
    have hj := L14.isVectorTest_testPartial hχ j
    have hc : Continuous fun x => testPartial χ j (v - x) :=
      hj.smooth.continuous.comp (continuous_const.sub continuous_id)
    have h3 : Integrable (fun x => fderiv ℝ (Heat.kernel h) x (coordinateVector j) •
        testPartial χ j (v - x)) :=
      ((hKd j).smul hc).integrable_of_hasCompactSupport
        (hasCompactSupport_comp_sub hj.compact v).smul_left
    exact h3.smul (-(2 * h))
  rw [integral_congr_ae (Eventually.of_forall hpt),
    integral_add (integrable_kconv_integrand hh hR.smooth.continuous hBR v)
      (integrable_finset_sum _ hBj), integral_finset_sum _ hBj]
  simp only [integral_smul, integral_kernel_partial hh hχ v]
  rw [← Finset.smul_sum, ← kconv_testLaplacian hh hχ v, neg_smul, ← sub_eq_add_neg]
  rfl

end UnforcedLeray.Blueprint.HypBg
