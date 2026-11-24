import UnforcedLeray.Lib.CZL2.HessianKernel
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# Hörmander condition for the Newton Hessian kernel (INF01 level L0, target T1)

Blueprint: INF01 target T1 (scoping note `INF01-CZ.md` §4.2, §5,
`hormander_newtonHessianKernel`). Manuscript: the Calderón–Zygmund input for
`R_iR_k = ∂_i∂_k(-Δ)^{-1}` (`paper/main.tex` lines 107–111, Grafakos Cor. 5.2.8 at
line 290), whose kernel `K_ik = (3xᵢxₖ - δᵢₖ|x|²)/(4π|x|⁵)` is homogeneous of degree
`-3` with `|∇K_ik(x)| ≲ |x|⁻⁴`.

* `exists_hasFDerivAt_newtonHessianKernel`: away from the origin `K_ik` is differentiable
  and its derivative satisfies `|DK_ik(x) v| ≤ 7π⁻¹ |v| |x|⁻⁴`.
* `abs_newtonHessianKernel_sub_le`: if `2|y| < |x|`, then
  `|K_ik(x - y) - K_ik(x)| ≤ 112π⁻¹ |y| |x|⁻⁴` (mean value theorem on the segment).
* `lintegral_norm_inv_pow_four`: `∫_{|x|>r} |x|⁻⁴ dx = 3|B₁| r⁻¹` (polar coordinates,
  Mathlib `integral_fun_norm_addHaar`).
* `hormander_newtonHessianKernel`: `∫_{|x|>2|y|} |K_ik(x - y) - K_ik(x)| dx ≤ B` with
  `B = 168π⁻¹|B₁|` independent of `y`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set Metric
open scoped ContDiff ENNReal NNReal Topology

namespace UnforcedLeray.RieszLp

open PressureAnalysis

/-- `δᵢₖ` as a real number. -/
def hessKron (i k : Fin 3) : ℝ := if i = k then 1 else 0

theorem hessKron_nonneg (i k : Fin 3) : 0 ≤ hessKron i k := by
  unfold hessKron; split_ifs <;> norm_num

theorem hessKron_le_one (i k : Fin 3) : hessKron i k ≤ 1 := by
  unfold hessKron; split_ifs <;> norm_num

private lemma norm_sq_rpow_neg_five_halves' (x : Space) :
    (‖x‖ ^ 2) ^ (-(5 : ℝ) / 2) = (‖x‖ ^ 5)⁻¹ := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg x)]
  norm_num

private lemma norm_sq_rpow_neg_seven_halves (x : Space) :
    (‖x‖ ^ 2) ^ (-(5 : ℝ) / 2 - 1) = (‖x‖ ^ 7)⁻¹ := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg x)]
  norm_num

/-- Product form of the kernel with a real power, valid at every point (at `0` both
sides are `0`). -/
theorem newtonHessianKernel_eq_mul (i k : Fin 3) (x : Space) :
    newtonHessianKernel i k x =
      (3 * x i * x k - hessKron i k * ‖x‖ ^ 2) *
        ((4 * Real.pi)⁻¹ * (‖x‖ ^ 2) ^ (-(5 : ℝ) / 2)) := by
  rw [norm_sq_rpow_neg_five_halves', newtonHessianKernel, div_eq_mul_inv, mul_inv, hessKron]
  split_ifs <;> ring

/-- The scalar inequality behind the derivative bound. -/
private lemma hessian_deriv_bound {a w p q s t I d : ℝ} (ha : 0 < a) (hp : |p| ≤ a)
    (hq : |q| ≤ a) (hs : |s| ≤ w) (ht : |t| ≤ w) (hI : |I| ≤ a * w) (hd0 : 0 ≤ d)
    (hd1 : d ≤ 1) :
    |(3 * p * q - d * a ^ 2) * ((4 * Real.pi)⁻¹ * ((-(5 : ℝ) / 2) * (a ^ 7)⁻¹ * (2 * I))) +
        ((4 * Real.pi)⁻¹ * (a ^ 5)⁻¹) * (3 * (p * t + s * q) - d * (2 * I))| ≤
      7 * Real.pi⁻¹ * w * (a ^ 4)⁻¹ := by
  have hw : 0 ≤ w := (abs_nonneg s).trans hs
  have hN : |3 * p * q - d * a ^ 2| ≤ 4 * a ^ 2 := by
    have h1 : |3 * p * q| ≤ 3 * a ^ 2 := by
      rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 3)]
      nlinarith [abs_nonneg p, abs_nonneg q]
    have h2 : |d * a ^ 2| ≤ a ^ 2 := by
      rw [abs_mul, abs_of_nonneg hd0, abs_of_nonneg (by positivity)]
      nlinarith [sq_nonneg a]
    calc _ ≤ |3 * p * q| + |d * a ^ 2| := abs_sub _ _
      _ ≤ 4 * a ^ 2 := by linarith
  have hN' : |3 * (p * t + s * q) - d * (2 * I)| ≤ 8 * a * w := by
    have h1 : |3 * (p * t + s * q)| ≤ 6 * a * w := by
      rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 3)]
      have : |p * t + s * q| ≤ 2 * a * w := by
        calc _ ≤ |p * t| + |s * q| := abs_add_le _ _
          _ = |p| * |t| + |s| * |q| := by rw [abs_mul, abs_mul]
          _ ≤ a * w + w * a := by gcongr
          _ = 2 * a * w := by ring
      linarith
    have h2 : |d * (2 * I)| ≤ 2 * a * w := by
      rw [abs_mul, abs_of_nonneg hd0, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      nlinarith [abs_nonneg I]
    calc _ ≤ |3 * (p * t + s * q)| + |d * (2 * I)| := abs_sub _ _
      _ ≤ 8 * a * w := by linarith
  have hc : 0 < (4 * Real.pi)⁻¹ := by positivity
  have e1 : (3 * p * q - d * a ^ 2) *
      ((4 * Real.pi)⁻¹ * ((-(5 : ℝ) / 2) * (a ^ 7)⁻¹ * (2 * I))) =
      -(5 * (4 * Real.pi)⁻¹ * (a ^ 7)⁻¹) * ((3 * p * q - d * a ^ 2) * I) := by ring
  have b1 : |-(5 * (4 * Real.pi)⁻¹ * (a ^ 7)⁻¹) * ((3 * p * q - d * a ^ 2) * I)| ≤
      5 * (4 * Real.pi)⁻¹ * (a ^ 7)⁻¹ * (4 * a ^ 2 * (a * w)) := by
    rw [abs_mul, abs_neg, abs_of_pos (by positivity), abs_mul]
    exact mul_le_mul_of_nonneg_left
      (mul_le_mul hN hI (abs_nonneg _) (by positivity)) (by positivity)
  have b2 : |(4 * Real.pi)⁻¹ * (a ^ 5)⁻¹ * (3 * (p * t + s * q) - d * (2 * I))| ≤
      (4 * Real.pi)⁻¹ * (a ^ 5)⁻¹ * (8 * a * w) := by
    rw [abs_mul, abs_of_pos (by positivity)]
    exact mul_le_mul_of_nonneg_left hN' (by positivity)
  rw [e1]
  calc _ ≤ _ := abs_add_le _ _
    _ ≤ _ := add_le_add b1 b2
    _ = 7 * Real.pi⁻¹ * w * (a ^ 4)⁻¹ := by
      field_simp
      ring

/-- **INF01 T1 (gradient bound).** Away from the origin `K_ik` is differentiable, with
`|DK_ik(x) v| ≤ 7π⁻¹ |v| |x|⁻⁴`. -/
theorem exists_hasFDerivAt_newtonHessianKernel (i k : Fin 3) {x : Space} (hx : x ≠ 0) :
    ∃ L : Space →L[ℝ] ℝ, HasFDerivAt (newtonHessianKernel i k) L x ∧
      ∀ v : Space, |L v| ≤ 7 * Real.pi⁻¹ * ‖v‖ * (‖x‖ ^ 4)⁻¹ := by
  have hn : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  have ha : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hpi : HasFDerivAt (fun y : Space => y i) (EuclideanSpace.proj i : Space →L[ℝ] ℝ) x :=
    (EuclideanSpace.proj i : Space →L[ℝ] ℝ).hasFDerivAt
  have hpk : HasFDerivAt (fun y : Space => y k) (EuclideanSpace.proj k : Space →L[ℝ] ℝ) x :=
    (EuclideanSpace.proj k : Space →L[ℝ] ℝ).hasFDerivAt
  have hsq : HasFDerivAt (fun y : Space => ‖y‖ ^ 2) (2 • innerSL ℝ x) x :=
    (hasStrictFDerivAt_norm_sq x).hasFDerivAt
  have hN := ((hpi.const_mul 3).mul hpk).sub (hsq.const_mul (hessKron i k))
  have hr := (hsq.rpow_const (p := -(5 : ℝ) / 2) (Or.inl (pow_ne_zero 2 hn))).const_mul
    ((4 * Real.pi)⁻¹)
  have h := (hN.mul hr).congr_of_eventuallyEq (f₁ := newtonHessianKernel i k)
    (Eventually.of_forall fun y => by
      simp only [Pi.mul_apply, Pi.sub_apply]
      exact newtonHessianKernel_eq_mul i k y)
  refine ⟨_, h, fun v => ?_⟩
  refine le_trans (le_of_eq (congrArg abs ?_)) (hessian_deriv_bound (p := x i) (q := x k)
    (s := v i) (t := v k) (I := inner ℝ x v) (d := hessKron i k) ha (PiLp.norm_apply_le x i)
    (PiLp.norm_apply_le x k) (PiLp.norm_apply_le v i) (PiLp.norm_apply_le v k)
    (abs_real_inner_le_norm x v) (hessKron_nonneg i k) (hessKron_le_one i k))
  simp only [Pi.mul_apply, Pi.sub_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply, smul_eq_mul,
    innerSL_apply_apply, nsmul_eq_mul, Nat.cast_ofNat, PiLp.proj_apply,
    norm_sq_rpow_neg_five_halves', norm_sq_rpow_neg_seven_halves]
  ring

/-- **INF01 T1 (smoothness estimate).** If `2|y| < |x|`, then
`|K_ik(x - y) - K_ik(x)| ≤ 112π⁻¹ |y| |x|⁻⁴`. -/
theorem abs_newtonHessianKernel_sub_le (i k : Fin 3) {x y : Space} (h : 2 * ‖y‖ < ‖x‖) :
    |newtonHessianKernel i k (x - y) - newtonHessianKernel i k x| ≤
      112 * Real.pi⁻¹ * ‖y‖ * (‖x‖ ^ 4)⁻¹ := by
  have hx : 0 < ‖x‖ := lt_of_le_of_lt (by positivity) h
  have hseg : ∀ z ∈ segment ℝ x (x - y), ‖x‖ / 2 ≤ ‖z‖ := by
    intro z hz
    obtain ⟨a, b, ha, hb, hab, rfl⟩ := hz
    have he : a • x + b • (x - y) = x - b • y := by
      rw [smul_sub, ← add_sub_assoc, ← add_smul, hab, one_smul]
    have hb1 : b ≤ 1 := by linarith
    have hby : ‖b • y‖ ≤ ‖y‖ := by
      rw [norm_smul, Real.norm_of_nonneg hb]
      exact mul_le_of_le_one_left (norm_nonneg y) hb1
    rw [he]
    have := norm_sub_norm_le x (b • y)
    linarith
  have hz0 : ∀ z ∈ segment ℝ x (x - y), z ≠ 0 := fun z hz =>
    norm_pos_iff.mp (lt_of_lt_of_le (by positivity) (hseg z hz))
  have hdiff : ∀ z ∈ segment ℝ x (x - y), DifferentiableAt ℝ (newtonHessianKernel i k) z := by
    intro z hz
    obtain ⟨L, hL, -⟩ := exists_hasFDerivAt_newtonHessianKernel i k (hz0 z hz)
    exact hL.differentiableAt
  have hbound : ∀ z ∈ segment ℝ x (x - y),
      ‖fderiv ℝ (newtonHessianKernel i k) z‖ ≤ 112 * Real.pi⁻¹ * (‖x‖ ^ 4)⁻¹ := by
    intro z hz
    obtain ⟨L, hL, hLb⟩ := exists_hasFDerivAt_newtonHessianKernel i k (hz0 z hz)
    rw [hL.fderiv]
    refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun v => ?_
    rw [Real.norm_eq_abs]
    refine (hLb v).trans ?_
    have hzx := hseg z hz
    have h4 : (‖z‖ ^ 4)⁻¹ ≤ 16 * (‖x‖ ^ 4)⁻¹ := by
      have e : (16 : ℝ) * (‖x‖ ^ 4)⁻¹ = ((‖x‖ / 2) ^ 4)⁻¹ := by
        field_simp
        norm_num
      rw [e]
      exact inv_anti₀ (by positivity) (pow_le_pow_left₀ (by positivity) hzx 4)
    calc 7 * Real.pi⁻¹ * ‖v‖ * (‖z‖ ^ 4)⁻¹
        ≤ 7 * Real.pi⁻¹ * ‖v‖ * (16 * (‖x‖ ^ 4)⁻¹) := by gcongr
      _ = 112 * Real.pi⁻¹ * (‖x‖ ^ 4)⁻¹ * ‖v‖ := by ring
  have hmv := (convex_segment x (x - y)).norm_image_sub_le_of_norm_fderiv_le hdiff hbound
    (left_mem_segment ℝ x (x - y)) (right_mem_segment ℝ x (x - y))
  rw [Real.norm_eq_abs, sub_sub_cancel_left, norm_neg] at hmv
  exact hmv.trans (le_of_eq (by ring))

/-- Radial integral: `∫_{|x|>r} |x|⁻⁴ dx = 3|B₁| r⁻¹` for `r > 0`. -/
theorem lintegral_norm_inv_pow_four {r : ℝ} (hr : 0 < r) :
    ∫⁻ x in {x : Space | r < ‖x‖}, ENNReal.ofReal ((‖x‖ ^ 4)⁻¹) =
      ENNReal.ofReal (3 * volume.real (ball (0 : Space) 1) * r⁻¹) := by
  set g : ℝ → ℝ := fun s => if r < s then (s ^ 4)⁻¹ else 0 with hg
  have hS : MeasurableSet {x : Space | r < ‖x‖} :=
    measurableSet_lt measurable_const measurable_norm
  have hind : ∀ x : Space, {x : Space | r < ‖x‖}.indicator
      (fun x => ENNReal.ofReal ((‖x‖ ^ 4)⁻¹)) x = ENNReal.ofReal (g ‖x‖) := by
    intro x
    by_cases h : r < ‖x‖
    · rw [indicator_of_mem (by exact h)]
      simp [hg, h]
    · rw [indicator_of_notMem (by exact h)]
      simp [hg, h]
  rw [← lintegral_indicator hS]
  simp_rw [hind]
  have hdim : Module.finrank ℝ Space = 3 := finrank_euclideanSpace_fin
  have hrad : ∀ y ∈ Ioi (0 : ℝ), y ^ (Module.finrank ℝ Space - 1) • g y =
      (Ioi r).indicator (fun t => t ^ (-2 : ℝ)) y := by
    intro y hy
    have hy0 : 0 < y := hy
    rw [hdim, smul_eq_mul]
    by_cases h : r < y
    · rw [indicator_of_mem (by exact h)]
      simp only [hg, h, ite_true]
      rw [Real.rpow_neg hy0.le, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      field_simp
    · rw [indicator_of_notMem (by exact h)]
      simp [hg, h]
  have hint1 : IntegrableOn (fun y : ℝ => y ^ (Module.finrank ℝ Space - 1) • g y) (Ioi 0) := by
    refine IntegrableOn.congr_fun ?_ (fun y hy => (hrad y hy).symm) measurableSet_Ioi
    exact ((integrableOn_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) hr).integrable_indicator
      measurableSet_Ioi).integrableOn
  have hint : Integrable (fun x : Space => g ‖x‖) volume :=
    (integrable_fun_norm_addHaar volume).2 hint1
  have hnn : 0 ≤ᵐ[volume] fun x : Space => g ‖x‖ := Eventually.of_forall fun x => by
    simp only [hg, Pi.zero_apply]
    split_ifs
    · positivity
    · exact le_rfl
  rw [← ofReal_integral_eq_lintegral_ofReal hint hnn, integral_fun_norm_addHaar volume g]
  congr 1
  rw [setIntegral_congr_fun measurableSet_Ioi hrad, integral_indicator measurableSet_Ioi,
    Measure.restrict_restrict measurableSet_Ioi, Ioi_inter_Ioi, sup_of_le_left hr.le,
    integral_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) hr, hdim]
  rw [show (-2 : ℝ) + 1 = -1 by norm_num, Real.rpow_neg_one, nsmul_eq_mul, smul_eq_mul]
  push_cast
  ring

/-- **INF01 T1 (Hörmander condition).** There is `B` such that for every `y`,
`∫_{|x|>2|y|} |K_ik(x - y) - K_ik(x)| dx ≤ B` (here `B = 168π⁻¹|B₁|`). -/
theorem hormander_newtonHessianKernel (i k : Fin 3) : ∃ B : ℝ≥0, ∀ y : Space,
    ∫⁻ x in {x : Space | 2 * ‖y‖ < ‖x‖},
      ‖newtonHessianKernel i k (x - y) - newtonHessianKernel i k x‖ₑ ≤ B := by
  set V := volume.real (ball (0 : Space) 1)
  refine ⟨Real.toNNReal (168 * Real.pi⁻¹ * V), fun y => ?_⟩
  by_cases hy : y = 0
  · subst hy
    simp
  have hy0 : 0 < ‖y‖ := norm_pos_iff.mpr hy
  have hV : 0 ≤ V := measureReal_nonneg
  have hmeas : Measurable fun x : Space =>
      ENNReal.ofReal ((‖x‖ ^ 4)⁻¹) := ((measurable_norm.pow_const 4).inv).ennreal_ofReal
  calc ∫⁻ x in {x : Space | 2 * ‖y‖ < ‖x‖},
        ‖newtonHessianKernel i k (x - y) - newtonHessianKernel i k x‖ₑ
      ≤ ∫⁻ x in {x : Space | 2 * ‖y‖ < ‖x‖},
          ENNReal.ofReal (112 * Real.pi⁻¹ * ‖y‖) * ENNReal.ofReal ((‖x‖ ^ 4)⁻¹) := by
        refine setLIntegral_mono (measurable_const.mul hmeas) fun x hx => ?_
        rw [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_mul (by positivity)]
        exact ENNReal.ofReal_le_ofReal (abs_newtonHessianKernel_sub_le i k hx)
    _ = ENNReal.ofReal (112 * Real.pi⁻¹ * ‖y‖) * ENNReal.ofReal (3 * V * (2 * ‖y‖)⁻¹) := by
        rw [lintegral_const_mul _ hmeas, lintegral_norm_inv_pow_four (by positivity)]
    _ = ENNReal.ofReal (168 * Real.pi⁻¹ * V) := by
        rw [← ENNReal.ofReal_mul (by positivity)]
        congr 1
        field_simp
        ring
    _ ≤ _ := le_rfl

end UnforcedLeray.RieszLp
