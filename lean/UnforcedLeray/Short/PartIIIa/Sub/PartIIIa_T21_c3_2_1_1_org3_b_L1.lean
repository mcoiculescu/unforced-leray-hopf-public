import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c3_2_1_1_org3_b0
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex

/-!
# Leaf B1: existence of the bounded planar damped interaction (SP 2920-2925)

`A0 W = couplingW W + Σ_i c_i ℓ_i(W) e_i` with `c_i = (Re γ - 1) - seedEigen lam i`,
`ℓ_i(W) = ∫ W ψ_i`, `ψ_i z = κ.lamP i (z.re, z.im)`, `e_i z = κ.e i (z.re, z.im)`.
The pairing `ℓ_i` is `inner` with `B0008.dualVec`, and `e_i ∈ L²_m` by the Gaussian decay,
`ψ_i ∈` the dual weight class by the `O(|y|^{-2})` decay.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ComplexConjugate ContDiff InnerProductSpace InnerProduct ENNReal

namespace UnforcedLeray.Short.IIIa

namespace BlockPropagatorInteriorSub

namespace OrgSplit3

namespace PlanarB

namespace PlanarDampedProof

/-- Gaussian integrability on `ℂ`. -/
theorem gauss_integrable (b : ℝ) (hb : 0 < b) :
    Integrable (fun z : ℂ => Real.exp (-b * ‖z‖ ^ 2)) := by
  have h := GaussianFourier.integrable_cexp_neg_mul_sq_norm_add (V := ℂ) (b := (b : ℂ))
    (by simpa using hb) (0 : ℂ) (0 : ℂ)
  refine h.norm.congr (Filter.Eventually.of_forall fun z => ?_)
  dsimp only
  rw [Complex.norm_exp]
  simp [pow_two]

/-- Gaussian `L²` bound on `ℂ`. -/
theorem memLp_gauss (K b : ℝ) (hb : 0 < b) :
    MemLp (fun z : ℂ => K * Real.exp (-b * ‖z‖ ^ 2)) 2 volume := by
  have hc : Continuous fun z : ℂ => K * Real.exp (-b * ‖z‖ ^ 2) := by fun_prop
  rw [memLp_two_iff_integrable_sq_norm hc.aestronglyMeasurable]
  refine ((gauss_integrable (2 * b) (by linarith)).const_mul (K ^ 2)).congr
    (Filter.Eventually.of_forall fun z => ?_)
  dsimp only
  have e2 : Real.exp (-b * ‖z‖ ^ 2) ^ 2 = Real.exp (-(2 * b) * ‖z‖ ^ 2) := by
    rw [← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  rw [Real.norm_eq_abs, sq_abs, mul_pow, e2]

/-- `(1+s)^k ≤ (16k)^k e^{s/16}` for `s ≥ 0`, `k > 0`, `16k ≥ 1`. -/
theorem rpow_le_exp (k : ℝ) (hk : 0 < k) (hk16 : 1 ≤ 16 * k) (s : ℝ) (hs : 0 ≤ s) :
    (1 + s) ^ k ≤ (16 * k) ^ k * Real.exp (s / 16) := by
  have hk' : k ≠ 0 := hk.ne'
  set t := s / (16 * k) with ht
  have ht0 : 0 ≤ t := by positivity
  have hst : 16 * k * t = s := by
    rw [ht]
    field_simp
  have h1 : 1 + s ≤ 16 * k * (1 + t) := by nlinarith
  have h2 : (1 + s) ^ k ≤ (16 * k * (1 + t)) ^ k :=
    Real.rpow_le_rpow (by positivity) h1 hk.le
  have h3 : (16 * k * (1 + t)) ^ k = (16 * k) ^ k * (1 + t) ^ k :=
    Real.mul_rpow (by positivity) (by positivity)
  have h4 : (1 + t) ^ k ≤ (Real.exp t) ^ k :=
    Real.rpow_le_rpow (by positivity) (by linarith [Real.add_one_le_exp t]) hk.le
  have h5 : (Real.exp t) ^ k = Real.exp (s / 16) := by
    rw [← Real.exp_mul]
    congr 1
    rw [ht]
    field_simp
  calc (1 + s) ^ k ≤ (16 * k * (1 + t)) ^ k := h2
    _ = (16 * k) ^ k * (1 + t) ^ k := h3
    _ ≤ (16 * k) ^ k * (Real.exp t) ^ k := by gcongr
    _ = (16 * k) ^ k * Real.exp (s / 16) := by rw [h5]

/-- The bracket power in closed form. -/
theorem bracket_pow_eq (M : ℝ) (y : ℂ) :
    UnforcedLeray.B0008.bracket y ^ M = (1 + ‖y‖ ^ 2) ^ (M / 2) := by
  unfold UnforcedLeray.B0008.bracket
  rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (by positivity)]
  congr 1
  ring

/-- Planar kernels cut to `ℂ`. -/
theorem cToPlane_continuous : Continuous cToPlane :=
  Complex.continuous_re.prodMk Complex.continuous_im

/-- `e_i ∈ L²(⟨y⟩^{2m} dy)` for `m > 1`, by the Gaussian tail of `κ.e_decay`. -/
theorem memLp_e (κ : PlanarFrameKernels) (i : Fin 2) {m : ℝ} (hm : 1 < m) :
    MemLp (fun z : ℂ => κ.e i (cToPlane z)) 2 (UnforcedLeray.B0008.wMeasure m) := by
  obtain ⟨C, hC⟩ := κ.e_decay
  refine (UnforcedLeray.B0008.memLp_wMeasure_iff m).2 ?_
  have hk : 0 < m / 2 := by linarith
  have hk16 : 1 ≤ 16 * (m / 2) := by linarith
  refine MemLp.of_le (memLp_gauss (|C| * (16 * (m / 2)) ^ (m / 2)) (1 / 16) (by norm_num))
    ?_ (Filter.Eventually.of_forall fun z => ?_)
  · exact ((UnforcedLeray.B0008.continuous_bracket_rpow m).smul
      ((κ.e_cont i).comp cToPlane_continuous)).aestronglyMeasurable
  · have hs : 0 ≤ ‖z‖ ^ 2 := by positivity
    have hs2 : (cToPlane z).1 ^ 2 + (cToPlane z).2 ^ 2 = ‖z‖ ^ 2 := by
      unfold cToPlane
      rw [Complex.sq_norm, Complex.normSq_apply]
      ring
    have hdec := hC i (cToPlane z)
    rw [hs2] at hdec
    have hE : ‖κ.e i (cToPlane z)‖ ≤ |C| * Real.exp (-(‖z‖ ^ 2) / 8) :=
      hdec.trans (mul_le_mul_of_nonneg_right (le_abs_self C) (Real.exp_pos _).le)
    have hR := rpow_le_exp (m / 2) hk hk16 (‖z‖ ^ 2) hs
    have hb := UnforcedLeray.B0008.bracket_pos z
    have hexp : Real.exp (‖z‖ ^ 2 / 16) * Real.exp (-(‖z‖ ^ 2) / 8)
        = Real.exp (-(1 / 16) * ‖z‖ ^ 2) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [norm_smul, Real.norm_of_nonneg (Real.rpow_nonneg hb.le _), bracket_pow_eq,
      Real.norm_of_nonneg (show 0 ≤ |C| * (16 * (m / 2)) ^ (m / 2) *
        Real.exp (-(1 / 16) * ‖z‖ ^ 2) by positivity)]
    calc (1 + ‖z‖ ^ 2) ^ (m / 2) * ‖κ.e i (cToPlane z)‖
        ≤ ((16 * (m / 2)) ^ (m / 2) * Real.exp (‖z‖ ^ 2 / 16)) *
            (|C| * Real.exp (-(‖z‖ ^ 2) / 8)) :=
          mul_le_mul hR hE (norm_nonneg _) (by positivity)
      _ = |C| * (16 * (m / 2)) ^ (m / 2) * Real.exp (-(1 / 16) * ‖z‖ ^ 2) := by
          linear_combination (|C| * (16 * (m / 2)) ^ (m / 2)) * hexp

/-- The dual-weight bound `|C| (1+‖z‖)^{-2}` is square integrable on `ℂ`. -/
theorem memLp_dual_bound (C : ℝ) :
    MemLp (fun z : ℂ => |C| * (1 + ‖z‖) ^ (-2 : ℝ)) 2 volume := by
  have hc : Continuous fun z : ℂ => |C| * (1 + ‖z‖) ^ (-2 : ℝ) :=
    continuous_const.mul (Continuous.rpow_const (by fun_prop) fun z => Or.inl (by positivity))
  rw [memLp_two_iff_integrable_sq_norm hc.aestronglyMeasurable]
  have hI : Integrable (fun z : ℂ => (1 + ‖z‖) ^ (-4 : ℝ)) volume :=
    integrable_one_add_norm (by rw [Complex.finrank_real_complex]; norm_num)
  refine (hI.const_mul (|C| ^ 2)).congr (Filter.Eventually.of_forall fun z => ?_)
  dsimp only
  have h4 : ((1 + ‖z‖) ^ (-2 : ℝ)) ^ 2 = (1 + ‖z‖) ^ (-4 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
    norm_num
  simp only [Real.norm_eq_abs, mul_pow, sq_abs, h4]

/-- A continuous `ψ` with `‖ψ z‖ ≤ C (1+‖z‖)^{-2}` has `dualFun m ψ ∈ L²(⟨y⟩^{2m} dy)`. -/
theorem memLp_dualFun_of_bound (ψ : ℂ → ℂ) (hψc : Continuous ψ) (C : ℝ)
    (hψ : ∀ z, ‖ψ z‖ ≤ C * (1 + ‖z‖) ^ (-2 : ℝ)) {m : ℝ} (hm : 1 < m) :
    MemLp (UnforcedLeray.B0008.dualFun m ψ) 2 (UnforcedLeray.B0008.wMeasure m) := by
  refine (UnforcedLeray.B0008.memLp_wMeasure_iff m).2 ?_
  have hinv : Continuous (UnforcedLeray.B0008.invWeight m) := by
    unfold UnforcedLeray.B0008.invWeight
    exact Complex.continuous_ofReal.comp ((UnforcedLeray.B0008.continuous_coe_density m).inv₀
      fun y => (UnforcedLeray.B0008.density_pos m y).ne')
  have hd : Continuous (UnforcedLeray.B0008.dualFun m ψ) := by
    have : UnforcedLeray.B0008.dualFun m ψ =
        fun y => star (ψ y) * UnforcedLeray.B0008.invWeight m y := rfl
    rw [this]
    exact hψc.star.mul hinv
  have hc : Continuous fun y => UnforcedLeray.B0008.bracket y ^ m •
      UnforcedLeray.B0008.dualFun m ψ y :=
    (UnforcedLeray.B0008.continuous_bracket_rpow m).smul hd
  refine MemLp.of_le (memLp_dual_bound C) hc.aestronglyMeasurable
    (Filter.Eventually.of_forall fun y => ?_)
  have hw : ‖UnforcedLeray.B0008.bracket y ^ m • UnforcedLeray.B0008.invWeight m y‖ ≤ 1 := by
    have h2 := UnforcedLeray.B0008.norm_sq_bracket_smul_invWeight m y
    have hle : (1 + ‖y‖ ^ 2) ^ (-m) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by nlinarith [sq_nonneg ‖y‖]) (by linarith)
    nlinarith [norm_nonneg (UnforcedLeray.B0008.bracket y ^ m • UnforcedLeray.B0008.invWeight m y)]
  have hdual : UnforcedLeray.B0008.bracket y ^ m • UnforcedLeray.B0008.dualFun m ψ y =
      star (ψ y) * (UnforcedLeray.B0008.bracket y ^ m • UnforcedLeray.B0008.invWeight m y) := by
    show UnforcedLeray.B0008.bracket y ^ m • (star (ψ y) * UnforcedLeray.B0008.invWeight m y) = _
    rw [mul_smul_comm]
  rw [hdual, norm_mul, norm_star, Real.norm_of_nonneg (by positivity)]
  calc ‖ψ y‖ * ‖UnforcedLeray.B0008.bracket y ^ m • UnforcedLeray.B0008.invWeight m y‖
      ≤ ‖ψ y‖ * 1 := mul_le_mul_of_nonneg_left hw (norm_nonneg _)
    _ = ‖ψ y‖ := mul_one _
    _ ≤ C * (1 + ‖y‖) ^ (-2 : ℝ) := hψ y
    _ ≤ |C| * (1 + ‖y‖) ^ (-2 : ℝ) :=
        mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity)

/-- The planar pairing `∫ Φ ψ` on `ℂ` equals the planar pairing `planarLamPair`. -/
theorem pair_eq (κ : PlanarFrameKernels) (i : Fin 2) (Φ : ℂ → ℂ) :
    ∫ z : ℂ, Φ z * κ.lamP i (cToPlane z) = planarLamPair κ i Φ := by
  unfold planarLamPair
  refine Eq.trans ?_
    (Complex.volume_preserving_equiv_real_prod.integral_comp'
      (fun y : ℝ × ℝ => κ.lamP i y * Φ (planeToC y)))
  refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
  have hp : planeToC (z.re, z.im) = z := Complex.eta z
  show Φ z * κ.lamP i (cToPlane z) = κ.lamP i (z.re, z.im) * Φ (planeToC (z.re, z.im))
  rw [hp, mul_comm]
  rfl

end PlanarDampedProof

open PlanarDampedProof in
/-- **Leaf B1 (bounded extension, SP 2920-2925)**: `PlanarDampedIntExists` holds. -/
theorem planarDampedIntExists_proof (κ : PlanarFrameKernels) : PlanarDampedIntExists κ := by
  unfold PlanarDampedIntExists
  intro hκ P _hP m hm _hm8
  obtain ⟨lam, h, hh, ℓ0, hX, he0, he1, hlam⟩ := hκ
  have hψb : ∀ i : Fin 2, ∃ C : ℝ, ∀ z : ℂ,
      ‖κ.lamP i (cToPlane z)‖ ≤ C * (1 + ‖z‖) ^ (-2 : ℝ) := by
    intro i
    obtain ⟨C, hC⟩ := κ.lamP_decay
    refine ⟨|C|, fun z => ?_⟩
    have h1 : 1 + ‖z‖ ≤ 1 + |(cToPlane z).1| + |(cToPlane z).2| := by
      have := Complex.norm_le_abs_re_add_abs_im z
      unfold cToPlane
      simp only
      linarith
    have h2 : (1 + |(cToPlane z).1| + |(cToPlane z).2|)⁻¹ ≤ (1 + ‖z‖)⁻¹ :=
      inv_anti₀ (by positivity) h1
    have h3 : ((1 + |(cToPlane z).1| + |(cToPlane z).2|)⁻¹) ^ 2 ≤ ((1 + ‖z‖)⁻¹) ^ 2 :=
      pow_le_pow_left₀ (by positivity) h2 2
    have h4 : ((1 + ‖z‖)⁻¹) ^ 2 = (1 + ‖z‖) ^ (-2 : ℝ) := by
      rw [show (-2 : ℝ) = -(2 : ℕ) by norm_num, Real.rpow_neg (by positivity),
        Real.rpow_natCast, inv_pow]
    have hX2 : 0 ≤ ((1 + |(cToPlane z).1| + |(cToPlane z).2|)⁻¹) ^ 2 := by positivity
    calc ‖κ.lamP i (cToPlane z)‖
        ≤ C * ((1 + |(cToPlane z).1| + |(cToPlane z).2|)⁻¹) ^ 2 := hC i (cToPlane z)
      _ ≤ |C| * ((1 + |(cToPlane z).1| + |(cToPlane z).2|)⁻¹) ^ 2 :=
          mul_le_mul_of_nonneg_right (le_abs_self C) hX2
      _ ≤ |C| * ((1 + ‖z‖)⁻¹) ^ 2 := mul_le_mul_of_nonneg_left h3 (abs_nonneg C)
      _ = |C| * (1 + ‖z‖) ^ (-2 : ℝ) := by rw [h4]
  have hL : ∀ i : Fin 2, ∃ L : UnforcedLeray.Planar.L2w m →L[ℂ] ℂ,
      ∀ F : UnforcedLeray.Planar.L2w m, L F = ∫ y, F y * κ.lamP i (cToPlane y) := by
    intro i
    obtain ⟨C, hC⟩ := hψb i
    have hd := memLp_dualFun_of_bound (fun z => κ.lamP i (cToPlane z))
      ((κ.lamP_cont i).comp cToPlane_continuous) C hC hm
    refine ⟨innerSL ℂ (UnforcedLeray.B0008.dualVec m _ hd), fun F => ?_⟩
    exact (innerSL_apply_apply ℂ (UnforcedLeray.B0008.dualVec m _ hd) F).trans
      (UnforcedLeray.B0008.inner_dualVec m hd F)
  choose ℓ hℓ using hL
  have hE : ∀ i : Fin 2, ∃ f : UnforcedLeray.Planar.L2w m,
      ⇑f =ᵐ[UnforcedLeray.Planar.wMeasure m] fun z => κ.e i (cToPlane z) :=
    fun i => ⟨(memLp_e κ i hm).toLp _, MemLp.coeFn_toLp _⟩
  choose e he using hE
  refine ⟨UnforcedLeray.Planar.couplingW hm +
      ((((P.eigenvalue.re - 1 : ℝ) : ℂ) - seedEigen lam 0) • (ℓ 0).smulRight (e 0)) +
      ((((P.eigenvalue.re - 1 : ℝ) : ℂ) - seedEigen lam 1) • (ℓ 1).smulRight (e 1)), ?_⟩
  unfold IsPlanarDampedInt
  refine ⟨lam, h, hh, ℓ0, hX, he0, ?_⟩
  intro Φ _hΦc _hΦs W hW
  have hℓW : ∀ i : Fin 2, ℓ i W = planarLamPair κ i Φ := fun i => by
    rw [hℓ i W]
    exact (integral_congr_ae (hW.mono fun z hz => by simp only [hz])).trans (pair_eq κ i Φ)
  refine (UnforcedLeray.Planar.volume_ac m).ae_le ?_
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.smulRight_apply, smul_smul]
  filter_upwards [Lp.coeFn_add (UnforcedLeray.Planar.couplingW hm W +
      (((((P.eigenvalue.re - 1 : ℝ) : ℂ) - seedEigen lam 0) * ℓ 0 W) • e 0))
      (((((P.eigenvalue.re - 1 : ℝ) : ℂ) - seedEigen lam 1) * ℓ 1 W) • e 1),
    Lp.coeFn_add (UnforcedLeray.Planar.couplingW hm W)
      (((((P.eigenvalue.re - 1 : ℝ) : ℂ) - seedEigen lam 0) * ℓ 0 W) • e 0),
    Lp.coeFn_smul ((((P.eigenvalue.re - 1 : ℝ) : ℂ) - seedEigen lam 0) * ℓ 0 W) (e 0),
    Lp.coeFn_smul ((((P.eigenvalue.re - 1 : ℝ) : ℂ) - seedEigen lam 1) * ℓ 1 W) (e 1),
    he 0, he 1] with z h1 h2 h3 h4 h5 h6
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at h1 h2 h3 h4 h5 h6
  rw [h1, h2, h3, h4, h5, h6, hℓW 0, hℓW 1, Fin.sum_univ_two]
  ring

end PlanarB

end OrgSplit3

end BlockPropagatorInteriorSub

end UnforcedLeray.Short.IIIa

end
