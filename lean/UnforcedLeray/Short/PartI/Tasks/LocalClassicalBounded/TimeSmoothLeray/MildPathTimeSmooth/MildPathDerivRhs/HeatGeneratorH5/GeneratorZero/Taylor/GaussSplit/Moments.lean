import UnforcedLeray.Short.PartI.Sub.PartI_T02_1_4_4_1_7_1_1_1_1_1_2
import Mathlib.MeasureTheory.Integral.Gamma

/-!
# Part I, `PartI:T02/1/4/4/1/7/1/1/1/1/1/2/1`: Gaussian moments `HGMoments`

Source `the November 2 reference manuscript`, lines 261-288. The planar kernel
`K_h(w) = G_h(w₁) G_h(w₂)` with `G_h(x) = (4πh)^{-1/2} e^{-x²/(4h)}` has unit mass, odd
moments zero and second moments `2h` in each coordinate.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace UnforcedLeray.Short.PartI

open UnforcedLeray
open UnforcedLeray.Cyl (Plane)

namespace HGMomentsAux

theorem heatKernel1_eq {h : ℝ} (hh : 0 < h) (x : ℝ) :
    B0191.heatKernel 1 h x
      = (Real.sqrt (4 * Real.pi * 1 * h))⁻¹ * Real.exp (-(1 / (4 * h)) * x ^ 2) := by
  unfold B0191.heatKernel
  congr 2
  ring

theorem heatKernel1_neg (h : ℝ) (x : ℝ) :
    B0191.heatKernel 1 h (-x) = B0191.heatKernel 1 h x := by
  simp only [B0191.heatKernel, neg_sq]

theorem integrable_G {h : ℝ} (hh : 0 < h) :
    Integrable (fun x : ℝ => B0191.heatKernel 1 h x) := by
  have hb : (0:ℝ) < 1 / (4 * h) := by positivity
  exact ((integrable_exp_neg_mul_sq hb).const_mul (Real.sqrt (4 * Real.pi * 1 * h))⁻¹).congr
    (ae_of_all _ fun x => (heatKernel1_eq hh x).symm)

theorem integrable_G_mul_x {h : ℝ} (hh : 0 < h) :
    Integrable (fun x : ℝ => B0191.heatKernel 1 h x * x) := by
  have hb : (0:ℝ) < 1 / (4 * h) := by positivity
  refine ((integrable_mul_exp_neg_mul_sq hb).const_mul (Real.sqrt (4 * Real.pi * 1 * h))⁻¹).congr
    (ae_of_all _ fun x => ?_)
  dsimp only
  rw [heatKernel1_eq hh x]
  ring

theorem integrable_G_mul_xx {h : ℝ} (hh : 0 < h) :
    Integrable (fun x : ℝ => B0191.heatKernel 1 h x * (x * x)) := by
  have hb : (0:ℝ) < 1 / (4 * h) := by positivity
  have h2 := integrable_rpow_mul_exp_neg_mul_sq hb (s := 2) (by norm_num)
  simp only [Real.rpow_two] at h2
  refine (h2.const_mul (Real.sqrt (4 * Real.pi * 1 * h))⁻¹).congr (ae_of_all _ fun x => ?_)
  dsimp only
  rw [heatKernel1_eq hh x]
  ring

theorem integral_G_mul_x {h : ℝ} (hh : 0 < h) :
    ∫ x : ℝ, B0191.heatKernel 1 h x * x = 0 := by
  have hodd := integral_neg_eq_self (fun x : ℝ => B0191.heatKernel 1 h x * x) volume
  have e : ∀ x : ℝ, B0191.heatKernel 1 h (-x) * (-x) = -(B0191.heatKernel 1 h x * x) :=
    fun x => by rw [heatKernel1_neg]; ring
  simp only [e, integral_neg] at hodd
  linarith

theorem sqrt_four_pi_h {h : ℝ} (hh : 0 < h) :
    Real.sqrt (4 * Real.pi * 1 * h) = 2 * Real.sqrt Real.pi * Real.sqrt h := by
  have h4 : Real.sqrt (4:ℝ) = 2 := by
    rw [show (4:ℝ) = 2 ^ 2 by norm_num]
    exact Real.sqrt_sq (by norm_num)
  rw [Real.sqrt_mul (x := 4 * Real.pi * 1) (by positivity) h,
    Real.sqrt_mul (x := 4 * Real.pi) (by positivity) 1,
    Real.sqrt_mul (x := 4) (by positivity) Real.pi, Real.sqrt_one, h4]
  ring

theorem pow_three_half {h : ℝ} (hh : 0 < h) :
    (1 / (4 * h)) ^ (-((2:ℝ) + 1) / 2) = 8 * h * Real.sqrt h := by
  have hpos : (0:ℝ) ≤ 4 * h := by positivity
  have key : (1 / (4 * h)) ^ (-((2:ℝ) + 1) / 2) = (4 * h) ^ ((3:ℝ) / 2) := by
    rw [show -((2:ℝ) + 1) / 2 = -((3:ℝ) / 2) by norm_num, Real.rpow_neg (by positivity),
      one_div, Real.inv_rpow hpos, inv_inv]
  rw [key, show (3:ℝ) / 2 = 1 + 1 / 2 by norm_num, Real.rpow_add (by positivity), Real.rpow_one,
    ← Real.sqrt_eq_rpow]
  have h4 : Real.sqrt (4 * h) = 2 * Real.sqrt h := by
    rw [Real.sqrt_mul (x := 4) (by positivity) h]
    congr 1
    rw [show (4:ℝ) = 2 ^ 2 by norm_num]
    exact Real.sqrt_sq (by norm_num)
  rw [h4]
  have hs : Real.sqrt h ^ 2 = h := Real.sq_sqrt hh.le
  nlinarith [hs]

theorem integral_G_mul_xx {h : ℝ} (hh : 0 < h) :
    ∫ x : ℝ, B0191.heatKernel 1 h x * (x * x) = 2 * h := by
  have hb : (0:ℝ) < 1 / (4 * h) := by positivity
  have hI : ∫ x : ℝ, B0191.heatKernel 1 h x * (x * x)
      = (Real.sqrt (4 * Real.pi * 1 * h))⁻¹
        * ∫ x : ℝ, x ^ 2 * Real.exp (-(1 / (4 * h)) * x ^ 2) := by
    rw [← integral_const_mul]
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    dsimp only
    rw [heatKernel1_eq hh x]
    ring
  have hE : ∫ x : ℝ, x ^ 2 * Real.exp (-(1 / (4 * h)) * x ^ 2)
      = 2 * ∫ x in Ioi (0:ℝ), x ^ 2 * Real.exp (-(1 / (4 * h)) * x ^ 2) := by
    have := integral_comp_abs (f := fun y : ℝ => y ^ 2 * Real.exp (-(1 / (4 * h)) * y ^ 2))
    simp only [sq_abs] at this
    exact this
  have e2 : ∫ x in Ioi (0:ℝ), x ^ 2 * Real.exp (-(1 / (4 * h)) * x ^ 2)
      = ∫ x in Ioi (0:ℝ), x ^ (2:ℝ) * Real.exp (-(1 / (4 * h)) * x ^ (2:ℝ)) := by
    refine setIntegral_congr_fun measurableSet_Ioi (fun x _ => ?_)
    simp only [Real.rpow_two]
  have hIoi : ∫ x in Ioi (0:ℝ), x ^ 2 * Real.exp (-(1 / (4 * h)) * x ^ 2)
      = (1 / (4 * h)) ^ (-((2:ℝ) + 1) / 2) * (1 / 2) * ((1 / 2) * Real.sqrt Real.pi) := by
    rw [e2, integral_rpow_mul_exp_neg_mul_rpow (p := 2) (q := 2) (by norm_num) (by norm_num) hb,
      show ((2:ℝ) + 1) / 2 = 1 / 2 + 1 by norm_num,
      Real.Gamma_add_one (s := 1 / 2) (by norm_num), Real.Gamma_one_half_eq]
  rw [hI, hE, hIoi, pow_three_half hh, sqrt_four_pi_h hh]
  have hpi : 0 < Real.sqrt Real.pi := Real.sqrt_pos.mpr Real.pi_pos
  have hs0 : 0 < Real.sqrt h := Real.sqrt_pos.mpr hh
  field_simp
  ring

theorem integrable_of_pointwise {F : Plane → ℝ} {f g : ℝ → ℝ}
    (hfg : ∀ w : Plane, F w = f w.1 * g w.2) (hf : Integrable f) (hg : Integrable g) :
    Integrable F :=
  (hf.mul_prod hg).congr (ae_of_all _ fun w => (hfg w).symm)

theorem integral_of_pointwise {F : Plane → ℝ} {f g : ℝ → ℝ}
    (hfg : ∀ w : Plane, F w = f w.1 * g w.2) :
    ∫ w : Plane, F w = (∫ x, f x) * ∫ y, g y :=
  (integral_congr_ae (ae_of_all _ hfg)).trans
    (integral_prod_mul (μ := volume) (ν := volume) f g)

end HGMomentsAux

open HGMomentsAux in
theorem heatGaussSplit_moments : UnforcedLeray.Short.PartI.HGMoments := by
  intro h hh
  have G0 := integrable_G hh
  have G1 := integrable_G_mul_x hh
  have G2 := integrable_G_mul_xx hh
  have m0 : ∫ x : ℝ, B0191.heatKernel 1 h x = 1 := B0284.integral_heatKernel_one hh
  have m1 := integral_G_mul_x hh
  have m2 := integral_G_mul_xx hh
  have iK : Integrable (fun w : Plane => B0284.heatKernel2 h w) :=
    integrable_of_pointwise (F := fun w : Plane => B0284.heatKernel2 h w)
      (f := fun x => B0191.heatKernel 1 h x) (g := fun x => B0191.heatKernel 1 h x)
      (fun w => rfl) G0 G0
  have iw1 : Integrable (fun w : Plane => B0284.heatKernel2 h w * w.1) :=
    integrable_of_pointwise (F := fun w : Plane => B0284.heatKernel2 h w * w.1)
      (f := fun x => B0191.heatKernel 1 h x * x) (g := fun x => B0191.heatKernel 1 h x)
      (fun w => by simp only [B0284.heatKernel2]; ring) G1 G0
  have iw2 : Integrable (fun w : Plane => B0284.heatKernel2 h w * w.2) :=
    integrable_of_pointwise (F := fun w : Plane => B0284.heatKernel2 h w * w.2)
      (f := fun x => B0191.heatKernel 1 h x) (g := fun x => B0191.heatKernel 1 h x * x)
      (fun w => by simp only [B0284.heatKernel2]; ring) G0 G1
  have iw11 : Integrable (fun w : Plane => B0284.heatKernel2 h w * (w.1 * w.1)) :=
    integrable_of_pointwise (F := fun w : Plane => B0284.heatKernel2 h w * (w.1 * w.1))
      (f := fun x => B0191.heatKernel 1 h x * (x * x)) (g := fun x => B0191.heatKernel 1 h x)
      (fun w => by simp only [B0284.heatKernel2]; ring) G2 G0
  have iw22 : Integrable (fun w : Plane => B0284.heatKernel2 h w * (w.2 * w.2)) :=
    integrable_of_pointwise (F := fun w : Plane => B0284.heatKernel2 h w * (w.2 * w.2))
      (f := fun x => B0191.heatKernel 1 h x) (g := fun x => B0191.heatKernel 1 h x * (x * x))
      (fun w => by simp only [B0284.heatKernel2]; ring) G0 G2
  have iw12 : Integrable (fun w : Plane => B0284.heatKernel2 h w * (w.1 * w.2)) :=
    integrable_of_pointwise (F := fun w : Plane => B0284.heatKernel2 h w * (w.1 * w.2))
      (f := fun x => B0191.heatKernel 1 h x * x) (g := fun x => B0191.heatKernel 1 h x * x)
      (fun w => by simp only [B0284.heatKernel2]; ring) G1 G1
  have j0 : ∫ w : Plane, B0284.heatKernel2 h w = 1 := by
    rw [integral_of_pointwise (F := fun w : Plane => B0284.heatKernel2 h w)
      (f := fun x => B0191.heatKernel 1 h x) (g := fun x => B0191.heatKernel 1 h x)
      (fun w => rfl), m0, one_mul]
  have j1 : ∫ w : Plane, B0284.heatKernel2 h w * w.1 = 0 := by
    rw [integral_of_pointwise (F := fun w : Plane => B0284.heatKernel2 h w * w.1)
      (f := fun x => B0191.heatKernel 1 h x * x) (g := fun x => B0191.heatKernel 1 h x)
      (fun w => by simp only [B0284.heatKernel2]; ring), m1, zero_mul]
  have j2 : ∫ w : Plane, B0284.heatKernel2 h w * w.2 = 0 := by
    rw [integral_of_pointwise (F := fun w : Plane => B0284.heatKernel2 h w * w.2)
      (f := fun x => B0191.heatKernel 1 h x) (g := fun x => B0191.heatKernel 1 h x * x)
      (fun w => by simp only [B0284.heatKernel2]; ring), m1, mul_zero]
  have j11 : ∫ w : Plane, B0284.heatKernel2 h w * (w.1 * w.1) = 2 * h := by
    rw [integral_of_pointwise (F := fun w : Plane => B0284.heatKernel2 h w * (w.1 * w.1))
      (f := fun x => B0191.heatKernel 1 h x * (x * x)) (g := fun x => B0191.heatKernel 1 h x)
      (fun w => by simp only [B0284.heatKernel2]; ring), m2, m0, mul_one]
  have j22 : ∫ w : Plane, B0284.heatKernel2 h w * (w.2 * w.2) = 2 * h := by
    rw [integral_of_pointwise (F := fun w : Plane => B0284.heatKernel2 h w * (w.2 * w.2))
      (f := fun x => B0191.heatKernel 1 h x) (g := fun x => B0191.heatKernel 1 h x * (x * x))
      (fun w => by simp only [B0284.heatKernel2]; ring), m2, m0, one_mul]
  have j12 : ∫ w : Plane, B0284.heatKernel2 h w * (w.1 * w.2) = 0 := by
    rw [integral_of_pointwise (F := fun w : Plane => B0284.heatKernel2 h w * (w.1 * w.2))
      (f := fun x => B0191.heatKernel 1 h x * x) (g := fun x => B0191.heatKernel 1 h x * x)
      (fun w => by simp only [B0284.heatKernel2]; ring), m1, zero_mul]
  exact ⟨iK, iw1, iw2, iw11, iw22, iw12, j0, j1, j2, j11, j22, j12⟩

end UnforcedLeray.Short.PartI
