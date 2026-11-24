import UnforcedLeray.Short.PartIIIa.Clock.WeakSmoothing
import UnforcedLeray.Units.B0579

/-!
# Periodic weight: calculus helpers (SP 3044-3050)

Helpers for `PeriodicWeightLogBounds` (file `WeakSmoothing/WeightLogBounds.lean`).
With `Q_d(y) = 1 + y₂² + (d/π)² sin²(π y₁/d)` one has `p_d = Q_d^m`, hence
`log p_d = m log Q_d` (`logW`). Partial derivatives are computed on the coordinate line
through the point (`pd0_eq`, `pd1_eq`); the bounds are elementary inequalities.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology

namespace UnforcedLeray.Short.IIIa

namespace WLB

/-- `Q_d(y) = 1 + y₂² + (d/π)² sin²(π y₁/d)`; `periodicWeight m d = Q_d^m`. -/
def Qf (d : ℝ) (y : ℝ × ℝ) : ℝ :=
  1 + y.2 ^ 2 + (d / Real.pi) ^ 2 * Real.sin (Real.pi * y.1 / d) ^ 2

/-- `∂₁ Q_d(y) = (d/π) · 2 sin(π y₁/d) cos(π y₁/d)`. -/
def Pf (d : ℝ) (y : ℝ × ℝ) : ℝ :=
  d / Real.pi * 2 * Real.sin (Real.pi * y.1 / d) * Real.cos (Real.pi * y.1 / d)

/-- `∂_d Q_d(y)` at fixed `y`. -/
def DQ (d : ℝ) (y : ℝ × ℝ) : ℝ :=
  2 * (d / Real.pi) * (1 / Real.pi) * Real.sin (Real.pi * y.1 / d) ^ 2 +
    (d / Real.pi) ^ 2 * (2 * Real.sin (Real.pi * y.1 / d) * Real.cos (Real.pi * y.1 / d) *
      (-(Real.pi * y.1) / d ^ 2))

theorem Qf_pos (d : ℝ) (y : ℝ × ℝ) : 0 < Qf d y := by
  unfold Qf; positivity

theorem one_le_Qf (d : ℝ) (y : ℝ × ℝ) : 1 ≤ Qf d y := by
  unfold Qf
  have h2 : 0 ≤ (d / Real.pi) ^ 2 * Real.sin (Real.pi * y.1 / d) ^ 2 := by positivity
  have h1 : 0 ≤ y.2 ^ 2 := sq_nonneg _
  linarith

theorem one_add_sq_le_Qf (d : ℝ) (y : ℝ × ℝ) : 1 + y.2 ^ 2 ≤ Qf d y := by
  unfold Qf
  have h2 : 0 ≤ (d / Real.pi) ^ 2 * Real.sin (Real.pi * y.1 / d) ^ 2 := by positivity
  linarith

theorem tsq_le_Qf (d : ℝ) (y : ℝ × ℝ) :
    (d / Real.pi) ^ 2 * Real.sin (Real.pi * y.1 / d) ^ 2 ≤ Qf d y := by
  unfold Qf
  have h1 : 0 ≤ y.2 ^ 2 := sq_nonneg _
  linarith

theorem logW (m d : ℝ) (y : ℝ × ℝ) :
    Real.log (periodicWeight m d y) = m * Real.log (Qf d y) := by
  unfold periodicWeight Qf
  exact Real.log_rpow (by positivity) m

theorem cs_eq (d : ℝ) (y : ℝ × ℝ) :
    Real.cos (Real.pi * y.1 / d) ^ 2 + Real.sin (Real.pi * y.1 / d) ^ 2 = 1 := by
  linarith [Real.sin_sq_add_cos_sq (Real.pi * y.1 / d)]

/-- Jordan's inequality in the form `|u| ≤ (π/2) |sin u|` for `|u| ≤ π/2`. -/
theorem jordan (u : ℝ) (hu : |u| ≤ Real.pi / 2) :
    |u| ≤ Real.pi / 2 * |Real.sin u| := by
  have hp2 : (0:ℝ) ≤ Real.pi / 2 := by positivity
  rcases le_total 0 u with h | h
  · rw [abs_of_nonneg h] at hu ⊢
    have hs : 0 ≤ Real.sin u :=
      Real.sin_nonneg_of_nonneg_of_le_pi h (by linarith [Real.pi_pos])
    rw [abs_of_nonneg hs]
    have h4 := Real.mul_le_sin h hu
    have h2 : Real.pi / 2 * (2 / Real.pi * u) = u := by
      field_simp <;> ring
    nlinarith [mul_le_mul_of_nonneg_left h4 hp2]
  · rw [abs_of_nonpos h] at hu ⊢
    have h3 : 0 ≤ Real.sin (-u) :=
      Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith [Real.pi_pos])
    have h4 := Real.mul_le_sin (by linarith : (0:ℝ) ≤ -u) hu
    rw [Real.sin_neg] at h3 h4
    have hs : Real.sin u ≤ 0 := by linarith
    rw [abs_of_nonpos hs]
    have h2 : Real.pi / 2 * (2 / Real.pi * -u) = -u := by
      field_simp <;> ring
    nlinarith [mul_le_mul_of_nonneg_left h4 hp2]

theorem abs_div_le_of {A Q K : ℝ} (hQ : 0 < Q) (h : |A| ≤ K * Q) : |A / Q| ≤ K := by
  rw [abs_div, abs_of_pos hQ, div_le_iff₀ hQ]
  linarith

theorem abs_mul_le_of {m X K : ℝ} (hX : |X| ≤ K) (hK : K ≤ 5 + Real.pi) :
    |m * X| ≤ (5 + Real.pi) * |m| := by
  rw [abs_mul]
  have h0 := abs_nonneg m
  nlinarith [mul_le_mul_of_nonneg_left hX h0, mul_le_mul_of_nonneg_left hK h0]

theorem abs_Pf_le (d : ℝ) (y : ℝ × ℝ) : |Pf d y| ≤ Qf d y := by
  have hs := Real.sin_sq_add_cos_sq (Real.pi * y.1 / d)
  have h1 := sq_nonneg (d / Real.pi * Real.sin (Real.pi * y.1 / d) - Real.cos (Real.pi * y.1 / d))
  have h2 := sq_nonneg (d / Real.pi * Real.sin (Real.pi * y.1 / d) + Real.cos (Real.pi * y.1 / d))
  have h3 := sq_nonneg y.2
  have h4 := sq_nonneg (Real.sin (Real.pi * y.1 / d))
  unfold Pf Qf
  rw [abs_le]
  constructor <;> nlinarith

theorem sq_Pf_le (d : ℝ) (y : ℝ × ℝ) : Pf d y ^ 2 ≤ Qf d y ^ 2 := by
  have h := abs_Pf_le d y
  nlinarith [mul_le_mul h h (abs_nonneg _) (Qf_pos d y).le, sq_abs (Pf d y)]

theorem abs_two_mul_le (y Q : ℝ) (h : 1 + y ^ 2 ≤ Q) : |2 * y| ≤ Q := by
  rw [abs_le]
  constructor <;> nlinarith [sq_nonneg (y - 1), sq_nonneg (y + 1)]

theorem bound_S00 {c s P Q : ℝ} (hQ : 1 ≤ Q) (hcs : c ^ 2 + s ^ 2 = 1) (hP : P ^ 2 ≤ Q ^ 2) :
    |2 * (c ^ 2 - s ^ 2) * Q - P * P| ≤ 3 * Q ^ 2 := by
  have hQ0 : 0 ≤ Q := by linarith
  have hc2 := sq_nonneg c
  have hs2 := sq_nonneg s
  have hPP := mul_self_nonneg P
  have hQQ : 0 ≤ Q * (Q - 1) := mul_nonneg hQ0 (by linarith)
  have hcsQ : (c ^ 2 + s ^ 2) * Q = Q := by rw [hcs, one_mul]
  rw [abs_le]
  constructor
  · nlinarith [mul_nonneg hc2 hQ0, mul_nonneg hs2 hQ0]
  · nlinarith [mul_nonneg hc2 hQ0, mul_nonneg hs2 hQ0]

theorem bound_mixed {P y Q : ℝ} (hP : |P| ≤ Q) (hy : |2 * y| ≤ Q) :
    |-(P * (2 * y))| ≤ 1 * Q ^ 2 := by
  rw [abs_neg, abs_mul, one_mul, sq]
  exact mul_le_mul hP hy (abs_nonneg _) (le_trans (abs_nonneg P) hP)

theorem bound_S11 {y Q : ℝ} (hy : |2 * y| ≤ Q) (hQ : 1 ≤ Q) :
    |2 * Q - 2 * y * (2 * y)| ≤ 3 * Q ^ 2 := by
  have hsq : 2 * y * (2 * y) = |2 * y| ^ 2 := by
    rw [sq_abs]; ring
  have h2 : |2 * y| ^ 2 ≤ Q ^ 2 := by nlinarith [abs_nonneg (2 * y)]
  rw [hsq, abs_le]
  have hQ0 : 0 ≤ Q := by linarith
  have hQQ : 0 ≤ Q * (Q - 1) := mul_nonneg hQ0 (by linarith)
  have hA : 0 ≤ |2 * y| ^ 2 := sq_nonneg _
  constructor <;> nlinarith

/-! ## Coordinate derivatives on lines -/

theorem lin_t (d a : ℝ) : HasDerivAt (fun t : ℝ => Real.pi * t / d) (Real.pi / d) a := by
  have h := ((hasDerivAt_id a).const_mul Real.pi).div_const d
  exact h.congr_deriv (by simp)

theorem sin_t (d a : ℝ) :
    HasDerivAt (fun t : ℝ => Real.sin (Real.pi * t / d))
      (Real.cos (Real.pi * a / d) * (Real.pi / d)) a :=
  (lin_t d a).sin

theorem cos_t (d a : ℝ) :
    HasDerivAt (fun t : ℝ => Real.cos (Real.pi * t / d))
      (-Real.sin (Real.pi * a / d) * (Real.pi / d)) a :=
  (lin_t d a).cos

theorem Qf_t1 (d : ℝ) (hd : d ≠ 0) (y : ℝ × ℝ) :
    HasDerivAt (fun t : ℝ => Qf d (t, y.2)) (Pf d y) y.1 := by
  have hpi0 : Real.pi ≠ 0 := Real.pi_ne_zero
  have hsq := (sin_t d y.1).fun_pow 2
  have hfull := (hsq.const_mul ((d / Real.pi) ^ 2)).const_add (1 + y.2 ^ 2)
  refine hfull.congr_deriv ?_
  unfold Pf
  (try norm_num) <;> field_simp <;> ring

theorem Qf_t2 (d : ℝ) (y : ℝ × ℝ) :
    HasDerivAt (fun t : ℝ => Qf d (y.1, t)) (2 * y.2) y.2 := by
  have hid := (hasDerivAt_id y.2).fun_pow 2
  have hfull := (hid.const_add 1).add_const
    ((d / Real.pi) ^ 2 * Real.sin (Real.pi * y.1 / d) ^ 2)
  refine hfull.congr_deriv ?_
  norm_num

theorem Pf_t1 (d : ℝ) (hd : d ≠ 0) (y : ℝ × ℝ) :
    HasDerivAt (fun t : ℝ => Pf d (t, y.2))
      (2 * (Real.cos (Real.pi * y.1 / d) ^ 2 - Real.sin (Real.pi * y.1 / d) ^ 2)) y.1 := by
  have hpi0 : Real.pi ≠ 0 := Real.pi_ne_zero
  have hf := ((sin_t d y.1).const_mul (d / Real.pi * 2)).mul (cos_t d y.1)
  refine hf.congr_deriv ?_
  field_simp
  ring

theorem Qf_d (d : ℝ) (hd : d ≠ 0) (y : ℝ × ℝ) :
    HasDerivAt (fun e : ℝ => Qf e y) (DQ d y) d := by
  have hl : HasDerivAt (fun e : ℝ => Real.pi * y.1 / e) ((0 * d - Real.pi * y.1 * 1) / d ^ 2) d :=
    (hasDerivAt_const d (Real.pi * y.1)).div (hasDerivAt_id d) hd
  have hsq := (hl.sin).fun_pow 2
  have hdp := ((hasDerivAt_id d).div_const Real.pi).fun_pow 2
  have hfull := (hdp.mul hsq).const_add (1 + y.2 ^ 2)
  refine hfull.congr_deriv ?_
  unfold DQ
  (try norm_num) <;> field_simp <;> (try simp) <;> ring

theorem d_DQ (d : ℝ) (hd : 0 < d) (y : ℝ × ℝ) :
    d * DQ d y = 2 * (d / Real.pi) ^ 2 * Real.sin (Real.pi * y.1 / d) ^ 2 - y.1 * Pf d y := by
  have hd0 : d ≠ 0 := hd.ne'
  have hpi0 : Real.pi ≠ 0 := Real.pi_ne_zero
  unfold DQ Pf
  field_simp
  ring

/-! ## Partial derivatives through a point -/

theorem pd0_eq (f : ℝ × ℝ → ℝ) (y : ℝ × ℝ) (D : ℝ) (hf : DifferentiableAt ℝ f y)
    (hD : HasDerivAt (fun t : ℝ => f (t, y.2)) D y.1) : B0579.pd 0 f y = D := by
  have hg : HasDerivAt (fun t : ℝ => ((t, y.2) : ℝ × ℝ)) ((1 : ℝ), (0 : ℝ)) y.1 :=
    (hasDerivAt_id y.1).prodMk (hasDerivAt_const y.1 y.2)
  have hc := hf.hasFDerivAt.comp_hasDerivAt y.1 hg
  have hdir : B0579.dir 0 = ((1 : ℝ), (0 : ℝ)) := by simp [B0579.dir]
  unfold B0579.pd
  rw [hdir]
  exact hc.unique hD

theorem pd1_eq (f : ℝ × ℝ → ℝ) (y : ℝ × ℝ) (D : ℝ) (hf : DifferentiableAt ℝ f y)
    (hD : HasDerivAt (fun t : ℝ => f (y.1, t)) D y.2) : B0579.pd 1 f y = D := by
  have hg : HasDerivAt (fun t : ℝ => ((y.1, t) : ℝ × ℝ)) ((0 : ℝ), (1 : ℝ)) y.2 :=
    (hasDerivAt_const y.2 y.1).prodMk (hasDerivAt_id y.2)
  have hc := hf.hasFDerivAt.comp_hasDerivAt y.2 hg
  have hdir : B0579.dir 1 = ((0 : ℝ), (1 : ℝ)) := by simp [B0579.dir]
  unfold B0579.pd
  rw [hdir]
  exact hc.unique hD

theorem diff_Qf (d : ℝ) (x : ℝ × ℝ) : DifferentiableAt ℝ (fun z : ℝ × ℝ => Qf d z) x := by
  unfold Qf
  fun_prop

theorem diff_Pf (d : ℝ) (x : ℝ × ℝ) : DifferentiableAt ℝ (fun z : ℝ × ℝ => Pf d z) x := by
  unfold Pf
  fun_prop

theorem diff_lin2 (x : ℝ × ℝ) : DifferentiableAt ℝ (fun z : ℝ × ℝ => 2 * z.2) x := by
  fun_prop

/-- Differentiability of a quotient of two multivariable differentiable functions. -/
theorem diff_quot (x : ℝ × ℝ) (a b : ℝ × ℝ → ℝ) (ha : DifferentiableAt ℝ a x)
    (hb : DifferentiableAt ℝ b x) (hne : b x ≠ 0) : DifferentiableAt ℝ (fun z => a z / b z) x := by
  simp only [div_eq_mul_inv]
  exact ha.mul (hb.inv hne)

/-- First derivatives of `m log p_d` (SP 3044-3050). -/
theorem F1 (m d : ℝ) (hd : d ≠ 0) (x : ℝ × ℝ) :
    B0579.pd 0 (fun z => m * Real.log (Qf d z)) x = m * (Pf d x / Qf d x) := by
  have hne : Qf d x ≠ 0 := (Qf_pos d x).ne'
  have hdiff : DifferentiableAt ℝ (fun z => m * Real.log (Qf d z)) x :=
    ((diff_Qf d x).log hne).const_mul m
  have hD := ((Qf_t1 d hd x).log hne).const_mul m
  exact pd0_eq _ x _ hdiff hD

theorem F2 (m d : ℝ) (x : ℝ × ℝ) :
    B0579.pd 1 (fun z => m * Real.log (Qf d z)) x = m * (2 * x.2 / Qf d x) := by
  have hne : Qf d x ≠ 0 := (Qf_pos d x).ne'
  have hdiff : DifferentiableAt ℝ (fun z => m * Real.log (Qf d z)) x :=
    ((diff_Qf d x).log hne).const_mul m
  have hD := ((Qf_t2 d x).log hne).const_mul m
  exact pd1_eq _ x _ hdiff hD

/-- Second derivatives of `m log p_d`: the `(0,0)` entry. -/
theorem S00 (m d : ℝ) (hd : d ≠ 0) (x : ℝ × ℝ) :
    B0579.pd 0 (fun z => m * (Pf d z / Qf d z)) x =
      m * ((2 * (Real.cos (Real.pi * x.1 / d) ^ 2 - Real.sin (Real.pi * x.1 / d) ^ 2)
        * Qf d x - Pf d x * Pf d x) / Qf d x ^ 2) := by
  have hne : Qf d x ≠ 0 := (Qf_pos d x).ne'
  have hdiff : DifferentiableAt ℝ (fun z => m * (Pf d z / Qf d z)) x :=
    ((diff_quot x _ _ (diff_Pf d x) (diff_Qf d x) hne).const_mul m)
  have hD := (((Pf_t1 d hd x).div (Qf_t1 d hd x) hne).const_mul m)
  exact pd0_eq _ x _ hdiff hD

/-- The `(1,0)` entry: `∂₂` of `m ∂₁ log p_d`. -/
theorem S01 (m d : ℝ) (hd : d ≠ 0) (x : ℝ × ℝ) :
    B0579.pd 1 (fun z => m * (Pf d z / Qf d z)) x = m * (-(Pf d x * (2 * x.2)) / Qf d x ^ 2) := by
  have hne : Qf d x ≠ 0 := (Qf_pos d x).ne'
  have hdiff : DifferentiableAt ℝ (fun z => m * (Pf d z / Qf d z)) x :=
    ((diff_quot x _ _ (diff_Pf d x) (diff_Qf d x) hne).const_mul m)
  have hc : HasDerivAt (fun t : ℝ => Pf d (x.1, t)) 0 x.2 := by
    have hfun : (fun t : ℝ => Pf d (x.1, t)) = fun _ => Pf d x := rfl
    rw [hfun]
    exact hasDerivAt_const x.2 (Pf d x)
  have hD := ((hc.div (Qf_t2 d x) hne).const_mul m)
  exact pd1_eq _ x _ hdiff (hD.congr_deriv (by ring))

/-- The `(0,1)` entry: `∂₁` of `m ∂₂ log p_d`. -/
theorem S10 (m d : ℝ) (hd : d ≠ 0) (x : ℝ × ℝ) :
    B0579.pd 0 (fun z => m * (2 * z.2 / Qf d z)) x = m * (-(Pf d x * (2 * x.2)) / Qf d x ^ 2) := by
  have hne : Qf d x ≠ 0 := (Qf_pos d x).ne'
  have hdiff : DifferentiableAt ℝ (fun z => m * (2 * z.2 / Qf d z)) x :=
    ((diff_quot x _ _ (diff_lin2 x) (diff_Qf d x) hne).const_mul m)
  have hc : HasDerivAt (fun _ : ℝ => 2 * x.2) 0 x.1 := hasDerivAt_const x.1 (2 * x.2)
  have hD := ((hc.div (Qf_t1 d hd x) hne).const_mul m)
  exact pd0_eq _ x _ hdiff (hD.congr_deriv (by ring))

/-- The `(1,1)` entry: `∂₂` of `m ∂₂ log p_d`. -/
theorem S11 (m d : ℝ) (hd : d ≠ 0) (x : ℝ × ℝ) :
    B0579.pd 1 (fun z => m * (2 * z.2 / Qf d z)) x =
      m * ((2 * Qf d x - 2 * x.2 * (2 * x.2)) / Qf d x ^ 2) := by
  have hne : Qf d x ≠ 0 := (Qf_pos d x).ne'
  have hdiff : DifferentiableAt ℝ (fun z => m * (2 * z.2 / Qf d z)) x :=
    ((diff_quot x _ _ (diff_lin2 x) (diff_Qf d x) hne).const_mul m)
  have hN : HasDerivAt (fun t : ℝ => 2 * t) 2 x.2 := by
    have h := (hasDerivAt_id x.2).const_mul (2 : ℝ)
    exact h.congr_deriv (by simp)
  have hD := ((hN.div (Qf_t2 d x) hne).const_mul m)
  exact pd1_eq _ x _ hdiff (hD.congr_deriv (by ring))

/-! ## Geometric bounds on the cell -/

theorem abs_le_of_mem_cell {d : ℝ} {y : ℝ × ℝ} (hy : y ∈ B0579.cell d) : |y.1| ≤ d / 2 := by
  simp only [B0579.cell, Set.mem_prod, Set.mem_Ico, Set.mem_univ, and_true] at hy
  exact abs_le.mpr ⟨hy.1, hy.2.le⟩

/-- `|y₁ ∂₁Q_d| ≤ π Q_d` on the cell `|y₁| ≤ d/2` (Jordan's inequality). -/
theorem abs_y1_Pf_le (d : ℝ) (hd : 0 < d) (y : ℝ × ℝ) (hy : |y.1| ≤ d / 2) :
    |y.1 * Pf d y| ≤ Real.pi * Qf d y := by
  have hpi := Real.pi_pos
  have hd0 : d ≠ 0 := hd.ne'
  have hpi0 : Real.pi ≠ 0 := hpi.ne'
  have hu : |Real.pi * y.1 / d| ≤ Real.pi / 2 := by
    rw [abs_div, abs_mul, abs_of_pos hpi, abs_of_pos hd, div_le_iff₀ hd]
    nlinarith [mul_le_mul_of_nonneg_left hy hpi.le]
  have hJ := jordan _ hu
  have hid : y.1 * Pf d y
      = (d / Real.pi) ^ 2 * (2 * (Real.pi * y.1 / d) * Real.sin (Real.pi * y.1 / d)
          * Real.cos (Real.pi * y.1 / d)) := by
    unfold Pf
    field_simp <;> ring
  have hQ := tsq_le_Qf d y
  have hc1 : |Real.cos (Real.pi * y.1 / d)| ≤ 1 := Real.abs_cos_le_one _
  have hstep : 2 * |Real.pi * y.1 / d| * |Real.sin (Real.pi * y.1 / d)|
      * |Real.cos (Real.pi * y.1 / d)| ≤ Real.pi * |Real.sin (Real.pi * y.1 / d)| ^ 2 := by
    calc 2 * |Real.pi * y.1 / d| * |Real.sin (Real.pi * y.1 / d)| * |Real.cos (Real.pi * y.1 / d)|
        ≤ 2 * (Real.pi / 2 * |Real.sin (Real.pi * y.1 / d)|) * |Real.sin (Real.pi * y.1 / d)|
            * |Real.cos (Real.pi * y.1 / d)| := by gcongr
      _ = Real.pi * |Real.sin (Real.pi * y.1 / d)| ^ 2 * |Real.cos (Real.pi * y.1 / d)| := by ring
      _ ≤ Real.pi * |Real.sin (Real.pi * y.1 / d)| ^ 2 * 1 := by gcongr
      _ = Real.pi * |Real.sin (Real.pi * y.1 / d)| ^ 2 := by ring
  rw [hid, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ (d / Real.pi) ^ 2), abs_mul,
    abs_mul, abs_mul, abs_two]
  calc (d / Real.pi) ^ 2 * (2 * |Real.pi * y.1 / d| * |Real.sin (Real.pi * y.1 / d)|
          * |Real.cos (Real.pi * y.1 / d)|)
      ≤ (d / Real.pi) ^ 2 * (Real.pi * |Real.sin (Real.pi * y.1 / d)| ^ 2) := by gcongr
    _ = Real.pi * ((d / Real.pi) ^ 2 * Real.sin (Real.pi * y.1 / d) ^ 2) := by
        rw [sq_abs]; ring
    _ ≤ Real.pi * Qf d y := by gcongr

end WLB

end UnforcedLeray.Short.IIIa
