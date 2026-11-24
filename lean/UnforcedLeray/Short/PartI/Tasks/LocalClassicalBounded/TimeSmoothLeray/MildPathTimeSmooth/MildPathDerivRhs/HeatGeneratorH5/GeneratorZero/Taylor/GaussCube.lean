import UnforcedLeray.Short.PartI.Sub.PartI_T02_1_4_4_1_7_1_1_1_1_1
import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup
import Mathlib.MeasureTheory.Integral.Gamma

/-!
# Part I, `PartI:T02/1/4/4/1/7/1/1/1/1/1/3`: the third Gaussian moment

Proves `HeatGaussCube` (see `Sub/PartI_T02_1_4_4_1_7_1_1_1_1_1.lean`): `∫ K_h |w|^3 = O(h^{3/2})`.
The planar kernel is a product of one-dimensional kernels, `‖w‖^3 ≤ |w₁|^3 + |w₂|^3` for the max
norm, and the one-dimensional moment is computed from the Gamma integral:
`∫ G_h |x|^3 = (√(4πh))⁻¹ · 16 h²`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace UnforcedLeray.Short.PartI

open UnforcedLeray
open UnforcedLeray.Cyl (Plane)

namespace HeatGaussCubeAux

theorem heatKernel1_eq {h : ℝ} (hh : 0 < h) (x : ℝ) :
    B0191.heatKernel 1 h x
      = (Real.sqrt (4 * Real.pi * 1 * h))⁻¹ * Real.exp (-(1 / (4 * h)) * x ^ 2) := by
  unfold B0191.heatKernel
  congr 2
  ring

theorem heatKernel1_nonneg {h : ℝ} (x : ℝ) : 0 ≤ B0191.heatKernel 1 h x := by
  unfold B0191.heatKernel
  positivity

theorem integrable_heatKernel1 {h : ℝ} (hh : 0 < h) :
    Integrable fun x : ℝ => B0191.heatKernel 1 h x := by
  have hb : (0:ℝ) < 1 / (4 * h) := by positivity
  have hG : Integrable fun x : ℝ => Real.exp (-(1 / (4 * h)) * x ^ 2) := by
    have := integrable_rpow_mul_exp_neg_mul_sq hb (s := 0) (by norm_num)
    simpa only [Real.rpow_zero, one_mul] using this
  exact (hG.const_mul (Real.sqrt (4 * Real.pi * 1 * h))⁻¹).congr
    (ae_of_all _ fun x => (heatKernel1_eq hh x).symm)

theorem integrable_heatKernel1_abs_cube {h : ℝ} (hh : 0 < h) :
    Integrable fun x : ℝ => B0191.heatKernel 1 h x * |x| ^ 3 := by
  have hb : (0:ℝ) < 1 / (4 * h) := by positivity
  have e3 : ∀ x : ℝ, x ^ (3:ℝ) = x ^ 3 := fun x => by
    rw [show (3:ℝ) = ((3:ℕ):ℝ) by norm_num, Real.rpow_natCast]
  have h3 : Integrable fun x : ℝ => x ^ (3:ℝ) * Real.exp (-(1 / (4 * h)) * x ^ 2) :=
    integrable_rpow_mul_exp_neg_mul_sq hb (by norm_num)
  have h3' : Integrable fun x : ℝ => x ^ 3 * Real.exp (-(1 / (4 * h)) * x ^ 2) := by
    simpa only [e3] using h3
  refine (h3'.abs.const_mul (Real.sqrt (4 * Real.pi * 1 * h))⁻¹).congr (ae_of_all _ fun x => ?_)
  show (Real.sqrt (4 * Real.pi * 1 * h))⁻¹ * |x ^ 3 * Real.exp (-(1 / (4 * h)) * x ^ 2)|
    = B0191.heatKernel 1 h x * |x| ^ 3
  rw [heatKernel1_eq hh x, abs_mul, abs_pow, abs_of_pos (Real.exp_pos _)]
  ring

theorem integral_heatKernel1_abs_cube {h : ℝ} (hh : 0 < h) :
    ∫ x : ℝ, B0191.heatKernel 1 h x * |x| ^ 3
      = (Real.sqrt (4 * Real.pi * 1 * h))⁻¹ * (16 * h ^ 2) := by
  have hb : (0:ℝ) < 1 / (4 * h) := by positivity
  have hI : ∫ y in Ioi (0:ℝ), y ^ 3 * Real.exp (-(1 / (4 * h)) * y ^ 2) = 8 * h ^ 2 := by
    have e : ∀ y ∈ Ioi (0:ℝ), y ^ 3 * Real.exp (-(1 / (4 * h)) * y ^ 2)
        = y ^ (3:ℝ) * Real.exp (-(1 / (4 * h)) * y ^ (2:ℝ)) := by
      intro y _
      rw [show (3:ℝ) = ((3:ℕ):ℝ) by norm_num, show (2:ℝ) = ((2:ℕ):ℝ) by norm_num,
        Real.rpow_natCast, Real.rpow_natCast]
    rw [setIntegral_congr_fun measurableSet_Ioi e,
      integral_rpow_mul_exp_neg_mul_rpow (p := 2) (q := 3) (b := 1 / (4 * h))
        (by norm_num) (by norm_num) hb]
    rw [show (-((3:ℝ) + 1) / 2) = -2 by norm_num, show ((3:ℝ) + 1) / 2 = 2 by norm_num,
      Real.Gamma_two, Real.rpow_neg hb.le, Real.rpow_two]
    field_simp
    ring
  have hIC := integral_comp_abs (f := fun y : ℝ => y ^ 3 * Real.exp (-(1 / (4 * h)) * y ^ 2))
  simp only [sq_abs] at hIC
  calc ∫ x : ℝ, B0191.heatKernel 1 h x * |x| ^ 3
      = ∫ x : ℝ, (Real.sqrt (4 * Real.pi * 1 * h))⁻¹
          * (|x| ^ 3 * Real.exp (-(1 / (4 * h)) * x ^ 2)) :=
        integral_congr_ae (ae_of_all _ fun x => by
          dsimp only
          rw [heatKernel1_eq hh x]
          ring)
    _ = (Real.sqrt (4 * Real.pi * 1 * h))⁻¹
          * ∫ x : ℝ, |x| ^ 3 * Real.exp (-(1 / (4 * h)) * x ^ 2) :=
        integral_const_mul _ _
    _ = (Real.sqrt (4 * Real.pi * 1 * h))⁻¹ * (2 * ∫ y in Ioi (0:ℝ),
          y ^ 3 * Real.exp (-(1 / (4 * h)) * y ^ 2)) := by rw [hIC]
    _ = (Real.sqrt (4 * Real.pi * 1 * h))⁻¹ * (16 * h ^ 2) := by rw [hI]; ring

/-- The product bound: `K_h(w) ‖w‖^3 ≤ K(w₁)|w₁|^3 K(w₂) + K(w₁) K(w₂)|w₂|^3`. -/
theorem heatGaussCube_pointwise {h : ℝ} (hh : 0 < h) (w : Plane) :
    B0284.heatKernel2 h w * ‖w‖ ^ 3 ≤
      (B0191.heatKernel 1 h w.1 * |w.1| ^ 3) * B0191.heatKernel 1 h w.2
        + B0191.heatKernel 1 h w.1 * (B0191.heatKernel 1 h w.2 * |w.2| ^ 3) := by
  have hn : ‖w‖ ^ 3 ≤ |w.1| ^ 3 + |w.2| ^ 3 := by
    have hn' : ‖w‖ = max |w.1| |w.2| := by
      rw [Prod.norm_def, Real.norm_eq_abs, Real.norm_eq_abs]
    rw [hn']
    rcases le_total |w.1| |w.2| with hle | hle
    · rw [max_eq_right hle]
      have := pow_nonneg (abs_nonneg w.1) 3
      linarith
    · rw [max_eq_left hle]
      have := pow_nonneg (abs_nonneg w.2) 3
      linarith
  have hK2 : B0284.heatKernel2 h w
      = B0191.heatKernel 1 h w.1 * B0191.heatKernel 1 h w.2 := rfl
  rw [hK2]
  have hp : 0 ≤ B0191.heatKernel 1 h w.1 * B0191.heatKernel 1 h w.2 :=
    mul_nonneg (heatKernel1_nonneg _) (heatKernel1_nonneg _)
  calc _ ≤ (B0191.heatKernel 1 h w.1 * B0191.heatKernel 1 h w.2) * (|w.1| ^ 3 + |w.2| ^ 3) :=
        mul_le_mul_of_nonneg_left hn hp
    _ = _ := by ring

theorem heatGaussCube_bound {h : ℝ} (hh : 0 < h) :
    Integrable (fun w : Plane => B0284.heatKernel2 h w * ‖w‖ ^ 3) ∧
      ∫ w : Plane, B0284.heatKernel2 h w * ‖w‖ ^ 3
        ≤ (32 / Real.sqrt (4 * Real.pi * 1)) * h ^ (3 / 2 : ℝ) := by
  have hKi := integrable_heatKernel1 hh
  have hMi := integrable_heatKernel1_abs_cube hh
  have hA : Integrable (fun w : Plane =>
      (B0191.heatKernel 1 h w.1 * |w.1| ^ 3) * B0191.heatKernel 1 h w.2) :=
    hMi.mul_prod hKi
  have hB : Integrable (fun w : Plane =>
      B0191.heatKernel 1 h w.1 * (B0191.heatKernel 1 h w.2 * |w.2| ^ 3)) :=
    hKi.mul_prod hMi
  have hAint : ∫ w : Plane, (B0191.heatKernel 1 h w.1 * |w.1| ^ 3) * B0191.heatKernel 1 h w.2
      = (∫ x : ℝ, B0191.heatKernel 1 h x * |x| ^ 3) * ∫ y : ℝ, B0191.heatKernel 1 h y :=
    integral_prod_mul (μ := volume) (ν := volume)
      (fun x : ℝ => B0191.heatKernel 1 h x * |x| ^ 3) (fun x : ℝ => B0191.heatKernel 1 h x)
  have hBint : ∫ w : Plane, B0191.heatKernel 1 h w.1 * (B0191.heatKernel 1 h w.2 * |w.2| ^ 3)
      = (∫ x : ℝ, B0191.heatKernel 1 h x) * ∫ y : ℝ, B0191.heatKernel 1 h y * |y| ^ 3 :=
    integral_prod_mul (μ := volume) (ν := volume)
      (fun x : ℝ => B0191.heatKernel 1 h x) (fun x : ℝ => B0191.heatKernel 1 h x * |x| ^ 3)
  have hnn : ∀ w : Plane, 0 ≤ B0284.heatKernel2 h w * ‖w‖ ^ 3 := fun w =>
    mul_nonneg (mul_nonneg (heatKernel1_nonneg _) (heatKernel1_nonneg _)) (pow_nonneg (norm_nonneg _) 3)
  have hint : Integrable (fun w : Plane => B0284.heatKernel2 h w * ‖w‖ ^ 3) := by
    refine Integrable.mono' (hA.add hB) ?_ (ae_of_all _ fun w => ?_)
    · apply Continuous.aestronglyMeasurable
      unfold B0284.heatKernel2 B0191.heatKernel
      fun_prop
    · rw [Real.norm_of_nonneg (hnn w)]
      exact heatGaussCube_pointwise hh w
  refine ⟨hint, ?_⟩
  have hsum : ∫ w : Plane, B0284.heatKernel2 h w * ‖w‖ ^ 3
      ≤ ∫ w : Plane, ((B0191.heatKernel 1 h w.1 * |w.1| ^ 3) * B0191.heatKernel 1 h w.2
          + B0191.heatKernel 1 h w.1 * (B0191.heatKernel 1 h w.2 * |w.2| ^ 3)) :=
    integral_mono hint (hA.add hB) (fun w => heatGaussCube_pointwise hh w)
  rw [integral_add hA hB, hAint, hBint, integral_heatKernel1_abs_cube hh,
    B0284.integral_heatKernel_one hh] at hsum
  refine hsum.trans (le_of_eq ?_)
  have h32 : h ^ (3 / 2 : ℝ) = h * Real.sqrt h := by
    rw [Real.sqrt_eq_rpow, show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num,
      Real.rpow_add hh, Real.rpow_one]
  have hs : Real.sqrt h ^ 2 = h := Real.sq_sqrt hh.le
  have hs0 : 0 < Real.sqrt h := Real.sqrt_pos.mpr hh
  have ht : 0 < Real.sqrt (4 * Real.pi * 1) := Real.sqrt_pos.mpr (by positivity)
  rw [h32, Real.sqrt_mul (by positivity : (0:ℝ) ≤ 4 * Real.pi * 1) h]
  have e1 : (Real.sqrt (4 * Real.pi * 1) * Real.sqrt h)⁻¹ * (16 * h ^ 2) * 1
      + 1 * ((Real.sqrt (4 * Real.pi * 1) * Real.sqrt h)⁻¹ * (16 * h ^ 2))
      = 32 * h ^ 2 / (Real.sqrt (4 * Real.pi * 1) * Real.sqrt h) := by
    ring
  rw [e1, div_mul_eq_mul_div, div_eq_div_iff (by positivity) (by positivity)]
  linear_combination (-32 * h * Real.sqrt (4 * Real.pi * 1)) * hs

end HeatGaussCubeAux

/-- **Leaf C (third Gaussian moment).** -/
theorem heatGaussCube : HeatGaussCube := by
  unfold HeatGaussCube
  exact ⟨32 / Real.sqrt (4 * Real.pi * 1), fun h hh _ => HeatGaussCubeAux.heatGaussCube_bound hh⟩

end UnforcedLeray.Short.PartI
