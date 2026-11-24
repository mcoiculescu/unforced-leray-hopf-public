import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_3_2_1_2_3
import UnforcedLeray.Units.B0224.PlaneHeat
import UnforcedLeray.Lib.Gaussian.Kernel
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Planar heat moment bound (task `PartIII-b:C/flatset/col/7/3/2/1/2/3/1`)

Source `the November 2 reference manuscript` 1650-1656.  The planar heat kernel
`G_θ(y) = (4πθ)^{-1} e^{-|y|²/(4θ)}` on `ℝ²` has `∫G_θ = 1` and `∫G_θ‖y‖² = 4θ`.  The second
moment is computed in polar coordinates (`integral_fun_norm_addHaar`), and the two radial
integrals are related by the substitution `u = y²` (`integral_comp_rpow_Ioi`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

open UnforcedLeray.B0220 (HSpace measureH Profile)
open UnforcedLeray.B0223 (MeridC)
open UnforcedLeray.Short.PartIIa (IsMeridTest pdS pdQ pdEta)

/-- Substitution `u = y²` in a radial integral: `∫_{(0,∞)} y g(y²) dy = (1/2) ∫_{(0,∞)} g`. -/
theorem moment_radial_half (g : ℝ → ℝ) :
    ∫ y in Ioi (0 : ℝ), y * g (y ^ 2) = (1 / 2) * ∫ u in Ioi (0 : ℝ), g u := by
  have h := integral_comp_rpow_Ioi g (p := (2 : ℝ)) two_ne_zero
  have e : ∀ x : ℝ, (|(2 : ℝ)| * x ^ ((2 : ℝ) - 1)) • g (x ^ (2 : ℝ)) = 2 * (x * g (x ^ 2)) := by
    intro x
    rw [abs_two, show (2 : ℝ) - 1 = 1 by norm_num, Real.rpow_one, Real.rpow_two, smul_eq_mul]
    ring
  simp only [e] at h
  rw [integral_const_mul] at h
  linarith

/-- `∫_{(0,∞)} K e^{-bu} du = K b⁻¹` for `b > 0`. -/
theorem moment_int_exp_one (K b : ℝ) (hb : 0 < b) :
    ∫ u in Ioi (0 : ℝ), K * Real.exp (-b * u) = K * b⁻¹ := by
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := 1) (r := b) one_pos hb
  have hc : ∫ u in Ioi (0 : ℝ), K * Real.exp (-b * u) =
      K * ∫ u in Ioi (0 : ℝ), u ^ ((1 : ℝ) - 1) * Real.exp (-(b * u)) := by
    rw [← integral_const_mul]
    congr 1
    funext u
    rw [sub_self, Real.rpow_zero, one_mul, neg_mul]
  rw [hc, h, Real.rpow_one, Real.Gamma_one]
  ring

/-- `∫_{(0,∞)} K e^{-bu} u du = K (b⁻¹)²` for `b > 0`. -/
theorem moment_int_exp_mul (K b : ℝ) (hb : 0 < b) :
    ∫ u in Ioi (0 : ℝ), K * Real.exp (-b * u) * u = K * (b⁻¹) ^ 2 := by
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := 2) (r := b) two_pos hb
  have hc : ∫ u in Ioi (0 : ℝ), K * Real.exp (-b * u) * u =
      K * ∫ u in Ioi (0 : ℝ), u ^ ((2 : ℝ) - 1) * Real.exp (-(b * u)) := by
    rw [← integral_const_mul]
    congr 1
    funext u
    rw [show (2 : ℝ) - 1 = 1 by norm_num, Real.rpow_one, neg_mul]
    ring
  rw [hc, h, Real.Gamma_two, Real.rpow_two]
  ring

/-- Polar coordinates on `ℝ²`: `∫_{ℝ²} F(‖y‖) dy = 2·|B₁| ∫_{(0,∞)} y F(y) dy`. -/
theorem moment_polar (F : ℝ → ℝ) :
    ∫ x : UnforcedLeray.Gaussian.Euc 2, F ‖x‖ =
      2 * (volume : Measure (UnforcedLeray.Gaussian.Euc 2)).real (Metric.ball 0 1) *
        ∫ y in Ioi (0 : ℝ), y * F y := by
  have h := integral_fun_norm_addHaar (volume : Measure (UnforcedLeray.Gaussian.Euc 2)) F
  rw [finrank_euclideanSpace_fin] at h
  rw [h]
  simp only [smul_eq_mul, nsmul_eq_mul, Nat.cast_ofNat, show (2 : ℕ) - 1 = 1 from rfl, pow_one]
  ring

/-- Integrability in polar coordinates on `ℝ²`. -/
theorem moment_polar_integrable (F : ℝ → ℝ)
    (h : IntegrableOn (fun y : ℝ => y * F y) (Ioi (0 : ℝ))) :
    Integrable (fun x : UnforcedLeray.Gaussian.Euc 2 => F ‖x‖) := by
  refine (integrable_fun_norm_addHaar (volume : Measure (UnforcedLeray.Gaussian.Euc 2))).2 ?_
  rw [finrank_euclideanSpace_fin]
  simpa using h

/-- The planar Gaussian second moment: `∫_{ℝ²} G_θ(y)‖y‖² dy = 4θ`, with `G_θ` integrable against
`‖y‖²` (`θ > 0`). -/
theorem gauss_second_moment {θ : ℝ} (hθ : 0 < θ) :
    Integrable (fun y : UnforcedLeray.Gaussian.Euc 2 =>
        UnforcedLeray.Gaussian.gaussKernel 2 θ y * ‖y‖ ^ 2) ∧
      ∫ y : UnforcedLeray.Gaussian.Euc 2,
        UnforcedLeray.Gaussian.gaussKernel 2 θ y * ‖y‖ ^ 2 = 4 * θ := by
  obtain ⟨K, hK⟩ : ∃ K : ℝ, K = (4 * Real.pi * θ) ^ (-((2 : ℕ) : ℝ) / 2) := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b : ℝ, b = (4 * θ)⁻¹ := ⟨_, rfl⟩
  have hb0 : 0 < b := by rw [hb]; positivity
  have hbinv : b⁻¹ = 4 * θ := by rw [hb, inv_inv]
  have hG : ∀ y : UnforcedLeray.Gaussian.Euc 2,
      UnforcedLeray.Gaussian.gaussKernel 2 θ y = K * Real.exp (-b * ‖y‖ ^ 2) := by
    intro y
    rw [UnforcedLeray.Gaussian.gaussKernel, hK, hb]
    congr 2
    ring
  -- integrability of the second moment
  have hI3 : IntegrableOn (fun y : ℝ => y * (K * Real.exp (-b * y ^ 2) * y ^ 2)) (Ioi (0 : ℝ)) := by
    have h := (integrableOn_rpow_mul_exp_neg_mul_sq (s := 3) hb0 (by norm_num)).const_mul K
    refine IntegrableOn.congr_fun h (fun y hy => ?_) measurableSet_Ioi
    have hy0 : 0 < y := hy
    rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    ring
  have hGsq_int : Integrable (fun y : UnforcedLeray.Gaussian.Euc 2 =>
      UnforcedLeray.Gaussian.gaussKernel 2 θ y * ‖y‖ ^ 2) := by
    have h := moment_polar_integrable (fun r => K * Real.exp (-b * r ^ 2) * r ^ 2) hI3
    refine h.congr (ae_of_all _ fun y => ?_)
    simp only [hG]
  refine ⟨hGsq_int, ?_⟩
  -- the two radial integrals
  have hG1 : ∫ y : UnforcedLeray.Gaussian.Euc 2, UnforcedLeray.Gaussian.gaussKernel 2 θ y = 1 :=
    UnforcedLeray.Gaussian.integral_gaussKernel (d := 2) hθ
  have hI1 : IntegrableOn (fun y : ℝ => y * (K * Real.exp (-b * y ^ 2))) (Ioi (0 : ℝ)) := by
    have h := (integrableOn_rpow_mul_exp_neg_mul_sq (s := 1) hb0 (by norm_num)).const_mul K
    refine IntegrableOn.congr_fun h (fun y hy => ?_) measurableSet_Ioi
    have hy0 : 0 < y := hy
    rw [show (1 : ℝ) = ((1 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    ring
  have hG1' : ∫ y : UnforcedLeray.Gaussian.Euc 2, UnforcedLeray.Gaussian.gaussKernel 2 θ y =
      2 * (volume : Measure (UnforcedLeray.Gaussian.Euc 2)).real (Metric.ball 0 1) *
        ∫ y in Ioi (0 : ℝ), y * (K * Real.exp (-b * y ^ 2)) := by
    rw [← moment_polar (fun r => K * Real.exp (-b * r ^ 2))]
    exact integral_congr_ae (ae_of_all _ fun y => hG y)
  have hG3 : ∫ y : UnforcedLeray.Gaussian.Euc 2,
      UnforcedLeray.Gaussian.gaussKernel 2 θ y * ‖y‖ ^ 2 =
      2 * (volume : Measure (UnforcedLeray.Gaussian.Euc 2)).real (Metric.ball 0 1) *
        ∫ y in Ioi (0 : ℝ), y * (K * Real.exp (-b * y ^ 2) * y ^ 2) := by
    rw [← moment_polar (fun r => K * Real.exp (-b * r ^ 2) * r ^ 2)]
    exact integral_congr_ae (ae_of_all _ fun y => by simp only [hG])
  have hR1 : ∫ y in Ioi (0 : ℝ), y * (K * Real.exp (-b * y ^ 2)) = (1 / 2) * (K * b⁻¹) := by
    have h := moment_radial_half (fun u => K * Real.exp (-b * u))
    rw [h, moment_int_exp_one K b hb0]
  have hR3 : ∫ y in Ioi (0 : ℝ), y * (K * Real.exp (-b * y ^ 2) * y ^ 2) =
      (1 / 2) * (K * (b⁻¹) ^ 2) := by
    have h := moment_radial_half (fun u => K * Real.exp (-b * u) * u)
    rw [h, moment_int_exp_mul K b hb0]
  rw [hG3, hR3]
  rw [hG1', hR1] at hG1
  rw [hbinv] at hG1 ⊢
  linear_combination (4 * θ) * hG1

/-- **Planar heat moment bound** (source 1650-1656; second Gaussian moment
`∫ G_θ‖y‖² = 4θ` on `ℝ²`): a function `v` of `(q,η)` bounded by `M` and vanishing for
`|η| > L` satisfies `(1+η²)‖e^{θΔ}v(q,η)‖ ≤ M(1+2L²+8θ)`, because where `v(x-ιy) ≠ 0` one has
`|x₁ - y₁| ≤ L`, so `1 + x₁² ≤ 1 + 2L² + 2‖y‖²`. -/
theorem plane_heat_moment : UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst.PlaneHeatMoment := by
  intro θ L M hθ v hv hvL x
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hv 0)
  have hGi : Integrable (fun y : UnforcedLeray.Gaussian.Euc 2 =>
      UnforcedLeray.Gaussian.gaussKernel 2 θ y) :=
    UnforcedLeray.Gaussian.integrable_gaussKernel (d := 2) hθ
  obtain ⟨hGsq, hGsq_val⟩ := gauss_second_moment hθ
  have hG1 : ∫ y : UnforcedLeray.Gaussian.Euc 2, UnforcedLeray.Gaussian.gaussKernel 2 θ y = 1 :=
    UnforcedLeray.Gaussian.integral_gaussKernel (d := 2) hθ
  have hGnn : ∀ y : UnforcedLeray.Gaussian.Euc 2, 0 ≤ UnforcedLeray.Gaussian.gaussKernel 2 θ y :=
    fun y => UnforcedLeray.Gaussian.gaussKernel_nonneg hθ y
  rw [UnforcedLeray.B0224.planeHeat_of_pos hθ v x]
  have hstep1 : (1 + x.2 ^ 2) * ‖∫ y : UnforcedLeray.Gaussian.Euc 2,
      UnforcedLeray.Gaussian.gaussKernel 2 θ y • v (x - UnforcedLeray.B0224.planeι y)‖ ≤
      ∫ y : UnforcedLeray.Gaussian.Euc 2,
        (1 + x.2 ^ 2) * ‖UnforcedLeray.Gaussian.gaussKernel 2 θ y •
          v (x - UnforcedLeray.B0224.planeι y)‖ := by
    rw [integral_const_mul]
    exact mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm _) (by positivity)
  have hbig_int : Integrable (fun y : UnforcedLeray.Gaussian.Euc 2 =>
      M * (UnforcedLeray.Gaussian.gaussKernel 2 θ y * (1 + 2 * L ^ 2 + 2 * ‖y‖ ^ 2))) := by
    have h := (hGi.const_mul (M * (1 + 2 * L ^ 2))).add (hGsq.const_mul (2 * M))
    refine h.congr (ae_of_all _ fun y => ?_)
    simp only [Pi.add_apply]
    ring
  have hpoint : ∀ y : UnforcedLeray.Gaussian.Euc 2,
      (1 + x.2 ^ 2) * ‖UnforcedLeray.Gaussian.gaussKernel 2 θ y •
        v (x - UnforcedLeray.B0224.planeι y)‖ ≤
      M * (UnforcedLeray.Gaussian.gaussKernel 2 θ y * (1 + 2 * L ^ 2 + 2 * ‖y‖ ^ 2)) := by
    intro y
    rw [norm_smul, Real.norm_of_nonneg (hGnn y)]
    have hfst : (x - UnforcedLeray.B0224.planeι y).2 = x.2 - y 1 := by
      rw [Prod.snd_sub, UnforcedLeray.B0224.planeι_apply]
    by_cases hy : |x.2 - y 1| ≤ L
    · have hvM : ‖v (x - UnforcedLeray.B0224.planeι y)‖ ≤ M := hv _
      have hsq1 : (y 1) ^ 2 ≤ ‖y‖ ^ 2 := by
        rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two]
        nlinarith [sq_nonneg (y 0)]
      have hsqL : (x.2 - y 1) ^ 2 ≤ L ^ 2 := by
        rw [← sq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) hy 2
      have hA : x.2 ^ 2 ≤ 2 * L ^ 2 + 2 * (y 1) ^ 2 := by
        nlinarith [sq_nonneg (x.2 - 2 * y 1)]
      have hB : (1 + x.2 ^ 2) ≤ 1 + 2 * L ^ 2 + 2 * ‖y‖ ^ 2 := by
        nlinarith
      calc (1 + x.2 ^ 2) * (UnforcedLeray.Gaussian.gaussKernel 2 θ y * ‖v (x - UnforcedLeray.B0224.planeι y)‖)
          ≤ (1 + 2 * L ^ 2 + 2 * ‖y‖ ^ 2) * (UnforcedLeray.Gaussian.gaussKernel 2 θ y * M) :=
            mul_le_mul hB (mul_le_mul_of_nonneg_left hvM (hGnn y))
              (mul_nonneg (hGnn y) (norm_nonneg _)) (by positivity)
        _ = M * (UnforcedLeray.Gaussian.gaussKernel 2 θ y * (1 + 2 * L ^ 2 + 2 * ‖y‖ ^ 2)) := by ring
    · have hv0 : v (x - UnforcedLeray.B0224.planeι y) = 0 :=
        hvL _ (by rw [hfst]; exact not_le.mp hy)
      rw [hv0, norm_zero, mul_zero, mul_zero]
      exact mul_nonneg hM0 (mul_nonneg (hGnn y) (by positivity))
  have hstep2 : ∫ y : UnforcedLeray.Gaussian.Euc 2,
      (1 + x.2 ^ 2) * ‖UnforcedLeray.Gaussian.gaussKernel 2 θ y •
        v (x - UnforcedLeray.B0224.planeι y)‖ ≤
      ∫ y : UnforcedLeray.Gaussian.Euc 2,
        M * (UnforcedLeray.Gaussian.gaussKernel 2 θ y * (1 + 2 * L ^ 2 + 2 * ‖y‖ ^ 2)) :=
    integral_mono_of_nonneg (ae_of_all _ fun y => mul_nonneg (by positivity) (norm_nonneg _))
      hbig_int (ae_of_all _ hpoint)
  have hval : ∫ y : UnforcedLeray.Gaussian.Euc 2,
      M * (UnforcedLeray.Gaussian.gaussKernel 2 θ y * (1 + 2 * L ^ 2 + 2 * ‖y‖ ^ 2)) =
      M * (1 + 2 * L ^ 2 + 8 * θ) := by
    have e : (fun y : UnforcedLeray.Gaussian.Euc 2 =>
        M * (UnforcedLeray.Gaussian.gaussKernel 2 θ y * (1 + 2 * L ^ 2 + 2 * ‖y‖ ^ 2))) =
        fun y => (M * (1 + 2 * L ^ 2)) * UnforcedLeray.Gaussian.gaussKernel 2 θ y +
          (2 * M) * (UnforcedLeray.Gaussian.gaussKernel 2 θ y * ‖y‖ ^ 2) := by
      funext y
      ring
    rw [e, integral_add (hGi.const_mul _) (hGsq.const_mul _), integral_const_mul,
      integral_const_mul, hG1, hGsq_val]
    ring
  exact hstep1.trans (hstep2.trans hval.le)

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
