import UnforcedLeray.Short.PartI.Sub.PartI_T02_1_4_4_1_7_1_1_1_1_2_1

/-!
# Part I, `PartI:T02/1/4/4/1/7/1/1/1/1/2/1/1`: the Gaussian tail of the heat convolution

Source `the November 2 reference manuscript`, lines 261-288.

For `f` bounded by `M` and vanishing at `z - w` whenever `|w₂| < s`, the planar heat kernel
`K_h(w) = G_h(w₁) G_h(w₂)` (with `G_h = B0191.heatKernel 1 h`, unit mass) gives
`‖∫ K_h(w) f(z - w) dw‖ ≤ M ∫ K_h(w) 1_{|w₂| ≥ s} dw`.  Completing the square,
`G_h(x) 1_{|x| ≥ s} ≤ e^{-s²/(4h)} (G_h(x - s) + G_h(x + s))`, and `∫ G_h = 1` yields the bound
`2 M e^{-s²/(4h)}`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter
open scoped Topology ENNReal

namespace HeatTailConvAux

open UnforcedLeray

theorem heatKernel1_eq {h : ℝ} (hh : 0 < h) (x : ℝ) :
    B0191.heatKernel 1 h x
      = (Real.sqrt (4 * Real.pi * 1 * h))⁻¹ * Real.exp (-(1 / (4 * h)) * x ^ 2) := by
  unfold B0191.heatKernel
  congr 2
  ring

theorem heatKernel1_nonneg {h : ℝ} (hh : 0 < h) (x : ℝ) : 0 ≤ B0191.heatKernel 1 h x := by
  rw [heatKernel1_eq hh x]
  positivity

theorem integrable_heatKernel1 {h : ℝ} (hh : 0 < h) :
    Integrable fun x : ℝ => B0191.heatKernel 1 h x := by
  have hb : (0:ℝ) < 1 / (4 * h) := by positivity
  have hG : Integrable fun x : ℝ => Real.exp (-(1 / (4 * h)) * x ^ 2) := by
    have := integrable_rpow_mul_exp_neg_mul_sq hb (s := 0) (by norm_num)
    simpa only [Real.rpow_zero, one_mul] using this
  exact (hG.const_mul (Real.sqrt (4 * Real.pi * 1 * h))⁻¹).congr
    (ae_of_all _ fun x => (heatKernel1_eq hh x).symm)

theorem integral_heatKernel1 {h : ℝ} (hh : 0 < h) :
    ∫ x : ℝ, B0191.heatKernel 1 h x = 1 :=
  B0284.integral_heatKernel_one hh

/-- Completing the square: for `|x| ≥ s`, the kernel is dominated by the two shifted kernels. -/
theorem tail_pointwise {s h : ℝ} (hs : 0 ≤ s) (hh : 0 < h) (x : ℝ) (hx : s ≤ |x|) :
    B0191.heatKernel 1 h x ≤ Real.exp (-(s ^ 2) / (4 * h)) *
      (B0191.heatKernel 1 h (x - s) + B0191.heatKernel 1 h (x + s)) := by
  have hk : 0 < 1 / (4 * h) := by positivity
  have hE : 0 ≤ Real.exp (-(s ^ 2) / (4 * h)) := (Real.exp_pos _).le
  have hP : 0 ≤ (Real.sqrt (4 * Real.pi * 1 * h))⁻¹ := by positivity
  have ee : -(s ^ 2) / (4 * h) = -((1 / (4 * h)) * s ^ 2) := by ring
  rcases le_total 0 x with hx0 | hx0
  · have hsx : s ≤ x := by
      rw [abs_of_nonneg hx0] at hx
      exact hx
    have key : Real.exp (-(1 / (4 * h)) * x ^ 2)
        ≤ Real.exp (-(s ^ 2) / (4 * h)) * Real.exp (-(1 / (4 * h)) * (x - s) ^ 2) := by
      rw [← Real.exp_add, ee]
      apply Real.exp_le_exp.2
      nlinarith [mul_nonneg hk.le (mul_nonneg hs (sub_nonneg.2 hsx))]
    have h1 : B0191.heatKernel 1 h x
        ≤ Real.exp (-(s ^ 2) / (4 * h)) * B0191.heatKernel 1 h (x - s) := by
      rw [heatKernel1_eq hh x, heatKernel1_eq hh (x - s)]
      calc (Real.sqrt (4 * Real.pi * 1 * h))⁻¹ * Real.exp (-(1 / (4 * h)) * x ^ 2)
          ≤ (Real.sqrt (4 * Real.pi * 1 * h))⁻¹ * (Real.exp (-(s ^ 2) / (4 * h))
              * Real.exp (-(1 / (4 * h)) * (x - s) ^ 2)) :=
            mul_le_mul_of_nonneg_left key hP
        _ = Real.exp (-(s ^ 2) / (4 * h)) * ((Real.sqrt (4 * Real.pi * 1 * h))⁻¹
              * Real.exp (-(1 / (4 * h)) * (x - s) ^ 2)) := by ring
    have h2 : 0 ≤ Real.exp (-(s ^ 2) / (4 * h)) * B0191.heatKernel 1 h (x + s) :=
      mul_nonneg hE (heatKernel1_nonneg hh _)
    nlinarith [h1, h2]
  · have hsx : x ≤ -s := by
      rw [abs_of_nonpos hx0] at hx
      linarith
    have key : Real.exp (-(1 / (4 * h)) * x ^ 2)
        ≤ Real.exp (-(s ^ 2) / (4 * h)) * Real.exp (-(1 / (4 * h)) * (x + s) ^ 2) := by
      rw [← Real.exp_add, ee]
      apply Real.exp_le_exp.2
      nlinarith [mul_nonneg hk.le (mul_nonneg hs (by linarith : (0:ℝ) ≤ -(x + s)))]
    have h1 : B0191.heatKernel 1 h x
        ≤ Real.exp (-(s ^ 2) / (4 * h)) * B0191.heatKernel 1 h (x + s) := by
      rw [heatKernel1_eq hh x, heatKernel1_eq hh (x + s)]
      calc (Real.sqrt (4 * Real.pi * 1 * h))⁻¹ * Real.exp (-(1 / (4 * h)) * x ^ 2)
          ≤ (Real.sqrt (4 * Real.pi * 1 * h))⁻¹ * (Real.exp (-(s ^ 2) / (4 * h))
              * Real.exp (-(1 / (4 * h)) * (x + s) ^ 2)) :=
            mul_le_mul_of_nonneg_left key hP
        _ = Real.exp (-(s ^ 2) / (4 * h)) * ((Real.sqrt (4 * Real.pi * 1 * h))⁻¹
              * Real.exp (-(1 / (4 * h)) * (x + s) ^ 2)) := by ring
    have h2 : 0 ≤ Real.exp (-(s ^ 2) / (4 * h)) * B0191.heatKernel 1 h (x - s) :=
      mul_nonneg hE (heatKernel1_nonneg hh _)
    nlinarith [h1, h2]

/-- The planar dominating function `F_{M,s}(w) = M e^{-s²/(4h)} G_h(w₁)(G_h(w₂-s) + G_h(w₂+s))`. -/
theorem integral_dominant {s h : ℝ} (hh : 0 < h) (M E : ℝ) :
    ∫ w : Cyl.Plane, M * E * (B0191.heatKernel 1 h w.1
        * (B0191.heatKernel 1 h (w.2 - s) + B0191.heatKernel 1 h (w.2 + s)))
      = 2 * M * E := by
  have hG := integrable_heatKernel1 hh
  have hsub : ∫ y : ℝ, B0191.heatKernel 1 h (y - s) = 1 :=
    (integral_sub_right_eq_self (fun x => B0191.heatKernel 1 h x) s).trans
      (integral_heatKernel1 hh)
  have hadd : ∫ y : ℝ, B0191.heatKernel 1 h (y + s) = 1 :=
    (integral_add_right_eq_self (fun x => B0191.heatKernel 1 h x) s).trans
      (integral_heatKernel1 hh)
  have hT_int : ∫ y : ℝ, (B0191.heatKernel 1 h (y - s) + B0191.heatKernel 1 h (y + s)) = 2 := by
    rw [integral_add (hG.comp_sub_right s) (hG.comp_add_right s), hsub, hadd]
    norm_num
  have hprod : ∫ w : Cyl.Plane, B0191.heatKernel 1 h w.1
        * (B0191.heatKernel 1 h (w.2 - s) + B0191.heatKernel 1 h (w.2 + s)) = 2 := by
    have e : ∫ w : Cyl.Plane, B0191.heatKernel 1 h w.1
          * (B0191.heatKernel 1 h (w.2 - s) + B0191.heatKernel 1 h (w.2 + s))
        = (∫ x : ℝ, B0191.heatKernel 1 h x)
          * ∫ y : ℝ, (B0191.heatKernel 1 h (y - s) + B0191.heatKernel 1 h (y + s)) :=
      integral_prod_mul (fun x => B0191.heatKernel 1 h x)
        (fun y => B0191.heatKernel 1 h (y - s) + B0191.heatKernel 1 h (y + s))
    rw [e, integral_heatKernel1 hh, hT_int, one_mul]
  rw [integral_const_mul, hprod]
  ring

theorem integrable_dominant {s h : ℝ} (hh : 0 < h) (M E : ℝ) :
    Integrable (fun w : Cyl.Plane => M * E * (B0191.heatKernel 1 h w.1
        * (B0191.heatKernel 1 h (w.2 - s) + B0191.heatKernel 1 h (w.2 + s)))) := by
  have hG := integrable_heatKernel1 hh
  have hT : Integrable (fun y : ℝ => B0191.heatKernel 1 h (y - s)
      + B0191.heatKernel 1 h (y + s)) :=
    (hG.comp_sub_right s).add (hG.comp_add_right s)
  have hP : Integrable (fun w : Cyl.Plane => B0191.heatKernel 1 h w.1
      * (B0191.heatKernel 1 h (w.2 - s) + B0191.heatKernel 1 h (w.2 + s))) :=
    Integrable.mul_prod hG hT
  exact hP.const_mul (M * E)

/-- The pointwise domination of the integrand. -/
theorem pointwise_bound {s h M : ℝ} (hs : 0 ≤ s) (hh : 0 < h) (hM : 0 ≤ M)
    (f : Cyl.Plane → Cyl.Vec2) (hbd : ∀ y, ‖f y‖ ≤ M) (z w : Cyl.Plane)
    (hsupp : ∀ w : Cyl.Plane, |w.2| < s → f (z - w) = 0) :
    B0284.heatKernel2 h w * ‖f (z - w)‖ ≤
      M * Real.exp (-(s ^ 2) / (4 * h)) * (B0191.heatKernel 1 h w.1
        * (B0191.heatKernel 1 h (w.2 - s) + B0191.heatKernel 1 h (w.2 + s))) := by
  have hK0 : 0 ≤ B0284.heatKernel2 h w := B0284.heatKernel2_nonneg hh w
  have hK : B0284.heatKernel2 h w = B0191.heatKernel 1 h w.1 * B0191.heatKernel 1 h w.2 := rfl
  have hE : 0 ≤ Real.exp (-(s ^ 2) / (4 * h)) := (Real.exp_pos _).le
  have hRHS : 0 ≤ M * Real.exp (-(s ^ 2) / (4 * h)) * (B0191.heatKernel 1 h w.1
      * (B0191.heatKernel 1 h (w.2 - s) + B0191.heatKernel 1 h (w.2 + s))) :=
    mul_nonneg (mul_nonneg hM hE)
      (mul_nonneg (heatKernel1_nonneg hh _)
        (add_nonneg (heatKernel1_nonneg hh _) (heatKernel1_nonneg hh _)))
  by_cases hw : |w.2| < s
  · rw [hsupp w hw, norm_zero, mul_zero]
    exact hRHS
  · push Not at hw
    have h2 := tail_pointwise hs hh w.2 hw
    rw [hK]
    calc B0191.heatKernel 1 h w.1 * B0191.heatKernel 1 h w.2 * ‖f (z - w)‖
        ≤ B0191.heatKernel 1 h w.1 * B0191.heatKernel 1 h w.2 * M :=
          mul_le_mul_of_nonneg_left (hbd _) (by rw [← hK]; exact hK0)
      _ ≤ B0191.heatKernel 1 h w.1 * (Real.exp (-(s ^ 2) / (4 * h))
            * (B0191.heatKernel 1 h (w.2 - s) + B0191.heatKernel 1 h (w.2 + s))) * M := by
          apply mul_le_mul_of_nonneg_right _ hM
          exact mul_le_mul_of_nonneg_left h2 (heatKernel1_nonneg hh _)
      _ = M * Real.exp (-(s ^ 2) / (4 * h)) * (B0191.heatKernel 1 h w.1
            * (B0191.heatKernel 1 h (w.2 - s) + B0191.heatKernel 1 h (w.2 + s))) := by ring

theorem heatTailConv_aux (f : Cyl.Plane → Cyl.Vec2) (M s h : ℝ) (z : Cyl.Plane)
    (hh : 0 < h) (hs : 0 ≤ s) (hM : 0 ≤ M) (hbd : ∀ y, ‖f y‖ ≤ M)
    (hsupp : ∀ w : Cyl.Plane, |w.2| < s → f (z - w) = 0) :
    ‖HeatCylinder.heatVecConvolution h f z‖ ≤ 2 * M * Real.exp (-(s ^ 2) / (4 * h)) := by
  unfold HeatCylinder.heatVecConvolution
  calc ‖∫ w : Cyl.Plane, B0284.heatKernel2 h w • f (z - w)‖
      ≤ ∫ w : Cyl.Plane, ‖B0284.heatKernel2 h w • f (z - w)‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ w : Cyl.Plane, M * Real.exp (-(s ^ 2) / (4 * h)) * (B0191.heatKernel 1 h w.1
          * (B0191.heatKernel 1 h (w.2 - s) + B0191.heatKernel 1 h (w.2 + s))) := by
          apply integral_mono_of_nonneg (Eventually.of_forall fun w => norm_nonneg _)
            (integrable_dominant hh _ _)
          refine Eventually.of_forall fun w => ?_
          dsimp only
          rw [norm_smul, Real.norm_of_nonneg (B0284.heatKernel2_nonneg hh w)]
          exact pointwise_bound hs hh hM f hbd z w hsupp
    _ = 2 * M * Real.exp (-(s ^ 2) / (4 * h)) := integral_dominant hh _ _

end HeatTailConvAux

/-- **Leaf T (Gaussian tail of the heat convolution; source lines 261-288).** -/
theorem heatTailConv : UnforcedLeray.Short.PartI.HeatTailConv := by
  unfold UnforcedLeray.Short.PartI.HeatTailConv
  intro f M s h z hh hs hM hbd hsupp
  exact HeatTailConvAux.heatTailConv_aux f M s h z hh hs hM hbd hsupp
