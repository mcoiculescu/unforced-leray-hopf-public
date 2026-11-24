import UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst.Pair.Defs
import UnforcedLeray.Lib.CylinderB.Periodize
import UnforcedLeray.Lib.Gaussian.PeriodizationCell

/-!
# Zero circulation of `q_{k,s}` (source 4349-4350, 597)

`qFun κ ν c k s = J_a P_d e_k` is the periodization `Cyl.periodize c (J_a e_k)` of the Jscale
of the planar growing vector, so `∫_cell q = ∫_{ℝ²} J_a e_k = a^{-2} ∫ e_k(√a⁻¹ • y) dy = 0`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal ComplexConjugate

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst.Pair

/-- The age band `a = bandA ν s` lies in `[1, 3]` for `ν > 0`. -/
theorem bandA_bounds {ν s : ℝ} (hν : 0 < ν) : 1 ≤ bandA ν s ∧ bandA ν s ≤ 3 := by
  have hν' : ν ≠ 0 := hν.ne'
  have ht0 : 0 ≤ bandAge ν s := le_max_left _ _
  have hfs : (0 : ℝ) ≤ flatSigma / ν := div_nonneg (by norm_num [flatSigma]) hν.le
  have ht1 : bandAge ν s ≤ flatSigma / ν := max_le hfs (min_le_right _ _)
  have hmul : ν * (flatSigma / ν) = 2 := by
    unfold flatSigma
    field_simp
  have hle : ν * bandAge ν s ≤ 2 := by
    rw [← hmul]
    exact mul_le_mul_of_nonneg_left ht1 hν.le
  have hnn : 0 ≤ ν * bandAge ν s := mul_nonneg hν.le ht0
  unfold bandA IIIa.clockA
  constructor <;> linarith

/-- The periodized Jscale is the periodization of the Jscale (source 2894-2896). -/
theorem jscale_perE_eq_periodize (κ : IIIa.PlanarFrameKernels) (a c : ℝ) (k : Fin 2)
    (ha : 0 < a) (x : ℝ × ℝ) :
    IIIa.Jscale a (IIIa.perE κ (c / Real.sqrt a) k) x =
      UnforcedLeray.Cyl.periodize c (IIIa.Jscale a (κ.e k)) x := by
  simp only [IIIa.Jscale, IIIa.perE, IIIa.perSum, UnforcedLeray.Cyl.periodize]
  rw [← tsum_mul_left]
  refine (tsum_congr fun n => ?_).trans ((Equiv.neg ℤ).tsum_eq _)
  try dsimp only [Equiv.neg_apply]
  have harg : ((x.1 / Real.sqrt a + (n : ℝ) * (c / Real.sqrt a), x.2 / Real.sqrt a) : ℝ × ℝ) =
      (((x.1 - ((-n : ℤ) : ℝ) * c) / Real.sqrt a), x.2 / Real.sqrt a) := by
    apply Prod.ext
    · show x.1 / Real.sqrt a + (n : ℝ) * (c / Real.sqrt a) =
        (x.1 - ((-n : ℤ) : ℝ) * c) / Real.sqrt a
      push_cast
      ring
    · rfl
  rw [harg]
  rfl

/-- The Jscale of a planar growing vector is continuous. -/
theorem jscale_e_continuous (κ : IIIa.PlanarFrameKernels) (a : ℝ) (k : Fin 2) :
    Continuous (IIIa.Jscale a (κ.e k)) := by
  unfold IIIa.Jscale
  exact continuous_const.mul ((κ.e_cont k).comp (by fun_prop))

/-- The Jscale of a planar growing vector is integrable (Gaussian tails, `a ∈ [1,3]`). -/
theorem jscale_e_integrable (κ : IIIa.PlanarFrameKernels) (a : ℝ) (ha1 : 1 ≤ a) (ha3 : a ≤ 3)
    (k : Fin 2) :
    Integrable (IIIa.Jscale a (κ.e k)) := by
  obtain ⟨C, hC⟩ := κ.e_decay
  have ha0 : 0 < a := by linarith
  have hsq : Real.sqrt a ^ 2 = a := Real.sq_sqrt ha0.le
  have hpow : (0 : ℝ) ≤ a ^ (-2 : ℝ) := Real.rpow_nonneg ha0.le _
  have hpow1 : a ^ (-2 : ℝ) ≤ 1 := by
    rw [Real.rpow_neg ha0.le, Real.rpow_two]
    apply inv_le_one_of_one_le₀
    nlinarith
  have hint := (UnforcedLeray.Gaussian.integrable_gauss_plane (a := 6) (by norm_num)).const_mul
    (max C 0)
  refine Integrable.mono' hint (jscale_e_continuous κ a k).aestronglyMeasurable ?_
  refine Filter.Eventually.of_forall fun z => ?_
  show ‖IIIa.Jscale a (κ.e k) z‖ ≤ max C 0 * Real.exp (-(z.1 ^ 2 + z.2 ^ 2) / (4 * 6))
  have hnorm : ‖IIIa.Jscale a (κ.e k) z‖ =
      a ^ (-2 : ℝ) * ‖κ.e k (z.1 / Real.sqrt a, z.2 / Real.sqrt a)‖ := by
    unfold IIIa.Jscale
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hpow]
  have hQ : (z.1 / Real.sqrt a) ^ 2 + (z.2 / Real.sqrt a) ^ 2 = (z.1 ^ 2 + z.2 ^ 2) / a := by
    rw [div_pow, div_pow, hsq]
    ring
  have hQnn : 0 ≤ z.1 ^ 2 + z.2 ^ 2 := by positivity
  have hdiv : (z.1 ^ 2 + z.2 ^ 2) / 3 ≤ (z.1 ^ 2 + z.2 ^ 2) / a :=
    div_le_div_of_nonneg_left hQnn ha0 ha3
  have hexp : Real.exp (-((z.1 ^ 2 + z.2 ^ 2) / a) / 8) ≤
      Real.exp (-(z.1 ^ 2 + z.2 ^ 2) / (4 * 6)) := by
    apply Real.exp_le_exp.2
    linarith
  have h0 : ‖κ.e k (z.1 / Real.sqrt a, z.2 / Real.sqrt a)‖ ≤
      C * Real.exp (-((z.1 / Real.sqrt a) ^ 2 + (z.2 / Real.sqrt a) ^ 2) / 8) :=
    hC k _
  rw [hQ] at h0
  have he : ‖κ.e k (z.1 / Real.sqrt a, z.2 / Real.sqrt a)‖ ≤
      max C 0 * Real.exp (-(z.1 ^ 2 + z.2 ^ 2) / (4 * 6)) :=
    h0.trans (mul_le_mul (le_max_left _ _) hexp (Real.exp_nonneg _) (le_max_right _ _))
  rw [hnorm]
  calc a ^ (-2 : ℝ) * ‖κ.e k (z.1 / Real.sqrt a, z.2 / Real.sqrt a)‖
      ≤ 1 * ‖κ.e k (z.1 / Real.sqrt a, z.2 / Real.sqrt a)‖ :=
        mul_le_mul_of_nonneg_right hpow1 (norm_nonneg _)
    _ ≤ 1 * (max C 0 * Real.exp (-(z.1 ^ 2 + z.2 ^ 2) / (4 * 6))) :=
        mul_le_mul_of_nonneg_left he zero_le_one
    _ = max C 0 * Real.exp (-(z.1 ^ 2 + z.2 ^ 2) / (4 * 6)) := one_mul _

/-- **Zero circulation of `q_{k,s}`** (source 4349-4350, 597: `∫ q = 0`), in the form `QFunCirc`. -/
theorem qFunCirc : QFunCirc := by
  intro κ ν c k s hν hc hint
  have hb := bandA_bounds (ν := ν) (s := s) hν
  have ha0 : 0 < bandA ν s := by linarith [hb.1]
  have hcpos : 0 < c := by linarith
  have hcell : B0579.cell c = UnforcedLeray.Cyl.cell c := by
    simp only [B0579.cell, UnforcedLeray.Cyl.cell, neg_div]
  have hqfun : qFun κ ν c k s =
      UnforcedLeray.Cyl.periodize c (IIIa.Jscale (bandA ν s) (κ.e k)) := by
    funext x
    exact jscale_perE_eq_periodize κ (bandA ν s) c k ha0 x
  have hF := jscale_e_integrable κ (bandA ν s) hb.1 hb.2 k
  have hfg : Integrable (fun z => IIIa.Jscale (bandA ν s) (κ.e k) z *
      (fun _ : ℝ × ℝ => (1 : ℂ)) z) := by
    simpa using hF
  have hper := UnforcedLeray.Cyl.integral_cell_periodize_mul (𝕜 := ℂ) hcpos
    (jscale_e_continuous κ (bandA ν s) k).stronglyMeasurable
    (stronglyMeasurable_const : StronglyMeasurable fun _ : ℝ × ℝ => (1 : ℂ))
    (fun _ => rfl) hfg
  simp only [mul_one] at hper
  have hJ : ∫ z, IIIa.Jscale (bandA ν s) (κ.e k) z = 0 := by
    have hsmul : ∀ z : ℝ × ℝ, κ.e k (z.1 / Real.sqrt (bandA ν s), z.2 / Real.sqrt (bandA ν s)) =
        κ.e k ((Real.sqrt (bandA ν s))⁻¹ • z) := by
      intro z
      congr 1
      ext
      · simp [div_eq_inv_mul]
      · simp [div_eq_inv_mul]
    simp only [IIIa.Jscale]
    rw [integral_const_mul]
    simp only [hsmul]
    rw [Measure.integral_comp_smul (volume : Measure (ℝ × ℝ)) (κ.e k) (Real.sqrt (bandA ν s))⁻¹,
      hint, smul_zero, mul_zero]
  rw [hqfun, hcell, hper, hJ]

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst.Pair
