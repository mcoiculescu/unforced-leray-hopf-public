import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D3_2.G2Org
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_data_1.GaussPointBound

/-!
# `PartIII-b:IIIb-D3/2/G2/2`: continuity and Gaussian decay of the unit modes (source 4565-4570)
-/

set_option autoImplicit false

noncomputable section

open Filter Topology Set MeasureTheory
open scoped ComplexConjugate

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatUnif.G2

open FlatSettingInst

theorem g2mb_gaussRdE_one (r : ℝ) :
    gaussRdE 1 r = -((r ^ 2 / 2) * (4 - r ^ 2 / 2) * Real.exp (-(r ^ 2) / 4)) := by
  have := gaussRdE_eq 1 r one_ne_zero
  simpa using this

theorem g2mb_cont_rd : Continuous (gaussRdE 1) := by
  have : gaussRdE 1 = fun r => -((r ^ 2 / 2) * (4 - r ^ 2 / 2) * Real.exp (-(r ^ 2) / 4)) :=
    funext g2mb_gaussRdE_one
  rw [this]
  fun_prop

theorem g2mb_cont_E : Continuous (gaussE 1) := by
  unfold gaussE
  fun_prop

theorem g2mb_planeR_cont : Continuous planeR := by
  unfold planeR
  fun_prop

theorem g2mb_planeR_zero {x : ℝ × ℝ} (h : planeR x = 0) : x = 0 := by
  unfold planeR at h
  rw [Real.sqrt_eq_zero (by positivity)] at h
  have h1 : x.1 = 0 := by nlinarith [sq_nonneg x.1, sq_nonneg x.2]
  have h2 : x.2 = 0 := by nlinarith [sq_nonneg x.1, sq_nonneg x.2]
  exact Prod.ext h1 h2

theorem g2mb_planeR_sq (y : ℝ × ℝ) : planeR y ^ 2 = y.1 ^ 2 + y.2 ^ 2 := by
  unfold planeR
  exact Real.sq_sqrt (by positivity)

theorem g2mb_hMode_norm (y : ℝ × ℝ) : ‖hMode 1 y‖ ≤ |gaussRdE 1 (planeR y)| := by
  unfold hMode
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  exact mul_le_of_le_one_right (abs_nonneg _) (angTwo_norm_le y)

theorem g2mb_rMode_norm (y : ℝ × ℝ) :
    ‖rMode 1 y‖ ≤ |gaussRdE 1 (planeR y)| + 2 * |gaussE 1 (planeR y)| := by
  unfold rMode
  rw [Complex.norm_real, Real.norm_eq_abs]
  have h := abs_add_le (gaussRdE 1 (planeR y)) (2 * gaussE 1 (planeR y))
  rw [abs_mul, abs_two] at h
  exact h

theorem g2mb_hMode_cont : Continuous (hMode 1) := by
  rw [continuous_iff_continuousAt]
  intro x
  by_cases hx : x = 0
  · subst hx
    have h0 : hMode 1 0 = 0 := by
      unfold hMode
      have : planeR (0 : ℝ × ℝ) = 0 := by simp [planeR]
      rw [this, g2mb_gaussRdE_one]; simp
    rw [ContinuousAt, h0]
    have hz : Tendsto (fun y : ℝ × ℝ => |gaussRdE 1 (planeR y)|) (𝓝 0) (𝓝 0) := by
      have hc : Continuous fun y : ℝ × ℝ => |gaussRdE 1 (planeR y)| :=
        (g2mb_cont_rd.comp g2mb_planeR_cont).abs
      have := hc.tendsto 0
      have h00 : |gaussRdE 1 (planeR (0 : ℝ × ℝ))| = 0 := by
        have : planeR (0 : ℝ × ℝ) = 0 := by simp [planeR]
        rw [this, g2mb_gaussRdE_one]; simp
      rwa [h00] at this
    rw [tendsto_zero_iff_norm_tendsto_zero]
    exact squeeze_zero (fun _ => norm_nonneg _) (fun y => g2mb_hMode_norm y) hz
  · have hne : x.1 ^ 2 + x.2 ^ 2 ≠ 0 := by
      intro h
      apply hx
      have h1 : x.1 = 0 := by nlinarith [sq_nonneg x.1, sq_nonneg x.2]
      have h2 : x.2 = 0 := by nlinarith [sq_nonneg x.1, sq_nonneg x.2]
      exact Prod.ext h1 h2
    have hne' : ((x.1 ^ 2 + x.2 ^ 2 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hne
    unfold hMode IIIa.angTwo
    have : ContinuousAt (fun y : ℝ × ℝ => ((gaussRdE 1 (planeR y) : ℝ) : ℂ)) x :=
      (Complex.continuous_ofReal.comp (g2mb_cont_rd.comp g2mb_planeR_cont)).continuousAt
    refine this.mul (ContinuousAt.div ?_ ?_ hne')
    · fun_prop
    · fun_prop

theorem g2mb_rMode_cont : Continuous (rMode 1) := by
  unfold rMode
  exact Complex.continuous_ofReal.comp
    ((g2mb_cont_rd.comp g2mb_planeR_cont).add (continuous_const.mul (g2mb_cont_E.comp g2mb_planeR_cont)))

theorem g2mb_poly (u : ℝ) (hu : 0 ≤ u) : 16 * u + 16 * u ^ 2 ≤ 32 * Real.exp u := by
  nlinarith [Real.quadratic_le_exp_of_nonneg hu]

theorem g2mb_decay (r : ℝ) :
    |gaussRdE 1 r| + 2 * |gaussE 1 r| ≤ 32 * Real.exp (-(r ^ 2) / 8) := by
  have h1 := gaussRdE_abs_le 1 r le_rfl
  have h2 := gaussE_abs_le 1 r le_rfl
  have hu : 0 ≤ r ^ 2 / 8 := by positivity
  have hp := Real.quadratic_le_exp_of_nonneg hu
  have hE : 0 < Real.exp (-(r ^ 2) / (4 * 1)) := Real.exp_pos _
  have hsplit : Real.exp (-(r ^ 2) / (4 * 1)) = Real.exp (-(r ^ 2) / 8) * Real.exp (-(r ^ 2) / 8) := by
    rw [← Real.exp_add]; congr 1; ring
  have hE8 : 0 < Real.exp (-(r ^ 2) / 8) := Real.exp_pos _
  have hprod : Real.exp (r ^ 2 / 8) * Real.exp (-(r ^ 2) / 8) = 1 := by
    rw [← Real.exp_add, show r ^ 2 / 8 + -(r ^ 2) / 8 = 0 by ring, Real.exp_zero]
  have hbound : (r ^ 2 / 2) * (4 + r ^ 2 / 2) + 2 * (2 + r ^ 2 / 2) ≤ 32 * Real.exp (r ^ 2 / 8) := by
    nlinarith [hp]
  calc |gaussRdE 1 r| + 2 * |gaussE 1 r|
      ≤ ((r ^ 2 / 2) * (4 + r ^ 2 / 2) + 2 * (2 + r ^ 2 / 2)) * Real.exp (-(r ^ 2) / (4 * 1)) := by
        nlinarith
    _ ≤ (32 * Real.exp (r ^ 2 / 8)) * Real.exp (-(r ^ 2) / (4 * 1)) :=
        mul_le_mul_of_nonneg_right hbound hE.le
    _ = 32 * Real.exp (-(r ^ 2) / 8) := by
        rw [hsplit]
        calc 32 * Real.exp (r ^ 2 / 8) * (Real.exp (-(r ^ 2) / 8) * Real.exp (-(r ^ 2) / 8))
            = 32 * (Real.exp (r ^ 2 / 8) * Real.exp (-(r ^ 2) / 8)) * Real.exp (-(r ^ 2) / 8) := by ring
          _ = _ := by rw [hprod]; ring

theorem g2ModeBounds : UnforcedLeray.Short.PartIIIb.Concrete.FlatUnif.G2.ModeBounds := by
  refine ⟨g2mb_hMode_cont, g2mb_rMode_cont, 32, fun y => ?_⟩
  have hsq : planeR y ^ 2 = y.1 ^ 2 + y.2 ^ 2 := g2mb_planeR_sq y
  have hd := g2mb_decay (planeR y)
  rw [hsq] at hd
  have a1 := g2mb_hMode_norm y
  have a2 := g2mb_rMode_norm y
  have hb : 0 ≤ |gaussE 1 (planeR y)| := abs_nonneg _
  constructor <;> linarith
