import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_grad_3_5_1_3.B3b
import Mathlib.Analysis.Calculus.Deriv.Pi
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Pow

/-!
# `PartIII-b:C/grad/3/5/1/3/3/c` C3c: first derivative bound of the lattice term `hpATm`

Source `shorter-proof-2026-11-02.tex` 4963-4980, 5063-5079.
-/

set_option autoImplicit false

noncomputable section

open Set

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- `y · (M y)`. -/
def qq (M : Mat3) (y : ℝ × ℝ) : ℝ := y.1 * (merApply M y).1 + y.2 * (merApply M y).2

/-- The scalar Gaussian prefactor `a⁻² e^{-|y|²/(4a)}`. -/
def EE (a : ℝ) (y : ℝ × ℝ) : ℝ := (a ^ 2)⁻¹ * Real.exp (-(sq2 y) / (4 * a))

/-- The vector factor of the closed form of `hpATm`. -/
def WW (a : ℝ) (M : Mat3) (y : ℝ × ℝ) : ℝ × ℝ :=
  merApply M (Jrot y) - Jrot (merApply M y) + (qq M y / (2 * a)) • Jrot y

theorem hpATm_eq' (ν : ℝ) (χ : ℝ → ℝ) (A : ℝ → Mat3) (j : ℤ) (p : Chart) :
    hpATm ν χ A j p = EE (ageA ν p.1) (xj ν j p.2) • WW (ageA ν p.1) (Ay ν χ A p.1) (xj ν j p.2) := by
  rw [hpATm_eq]; rfl

theorem mer_hasDerivAt (M : ℝ → Mat3) (M' : Mat3) (y1 y2 : ℝ → ℝ) (d1 d2 τ : ℝ)
    (hM : HasDerivAt M M' τ) (h1 : HasDerivAt y1 d1 τ) (h2 : HasDerivAt y2 d2 τ) :
    HasDerivAt (fun t => (merApply (M t) (y1 t, y2 t)).1)
      (merApply M' (y1 τ, y2 τ) + merApply (M τ) (d1, d2)).1 τ ∧
    HasDerivAt (fun t => (merApply (M t) (y1 t, y2 t)).2)
      (merApply M' (y1 τ, y2 τ) + merApply (M τ) (d1, d2)).2 τ := by
  have hm : ∀ i k, HasDerivAt (fun t => M t i k) (M' i k) τ :=
    fun i k => hasDerivAt_pi.1 (hasDerivAt_pi.1 hM i) k
  have e1 := ((hm 0 0).mul h1).add ((hm 0 2).mul h2)
  have e2 := ((hm 2 0).mul h1).add ((hm 2 2).mul h2)
  constructor
  · refine e1.congr_deriv ?_
    simp [merApply]; ring
  · refine e2.congr_deriv ?_
    simp [merApply]; ring

theorem merApply_hasDerivAt (M : ℝ → Mat3) (M' : Mat3) (y1 y2 : ℝ → ℝ) (d1 d2 τ : ℝ)
    (hM : HasDerivAt M M' τ) (h1 : HasDerivAt y1 d1 τ) (h2 : HasDerivAt y2 d2 τ) :
    HasDerivAt (fun t => merApply (M t) (y1 t, y2 t))
      (merApply M' (y1 τ, y2 τ) + merApply (M τ) (d1, d2)) τ := by
  obtain ⟨e1, e2⟩ := mer_hasDerivAt M M' y1 y2 d1 d2 τ hM h1 h2
  exact e1.prodMk e2

theorem EE_hasDerivAt (a y1 y2 : ℝ → ℝ) (a' d1 d2 τ : ℝ) (ha : HasDerivAt a a' τ)
    (h1 : HasDerivAt y1 d1 τ) (h2 : HasDerivAt y2 d2 τ) (hne : a τ ≠ 0) :
    HasDerivAt (fun t => EE (a t) (y1 t, y2 t))
      (EE (a τ) (y1 τ, y2 τ) * (-2 * a' / a τ
        + (-(2 * (y1 τ * d1 + y2 τ * d2)) / (4 * a τ) + sq2 (y1 τ, y2 τ) * a' / (4 * a τ ^ 2)))) τ := by
  have hnum : HasDerivAt (fun t => -(y1 t ^ 2 + y2 t ^ 2))
      (-(2 * y1 τ * d1 + 2 * y2 τ * d2)) τ := by
    have e : (fun t => -(y1 t ^ 2 + y2 t ^ 2)) = fun t => -(y1 t * y1 t + y2 t * y2 t) := by
      funext t; ring
    rw [e]
    exact (((h1.mul h1).add (h2.mul h2)).neg).congr_deriv (by ring)
  have hden : HasDerivAt (fun t => 4 * a t) (4 * a') τ := ha.const_mul 4
  have hu := hnum.fun_div hden (by simpa using hne)
  have hq := (ha.pow 2).inv (by simpa using hne)
  have hf := hq.mul hu.exp
  have hfun : (fun t => EE (a t) (y1 t, y2 t)) =
      (a ^ 2)⁻¹ * fun x => Real.exp (-(y1 x ^ 2 + y2 x ^ 2) / (4 * a x)) := by
    funext t; simp [EE, sq2]
  rw [hfun]
  refine hf.congr_deriv ?_
  simp only [EE, sq2, Pi.pow_apply, Pi.inv_apply]
  field_simp
  ring

/-- Derivative of `qq`. -/
def qqd (M M' : Mat3) (y y' : ℝ × ℝ) : ℝ :=
  y'.1 * (merApply M y).1 + y.1 * (merApply M' y + merApply M y').1
    + y'.2 * (merApply M y).2 + y.2 * (merApply M' y + merApply M y').2

/-- Derivative of `WW`. -/
def WWd (a a' : ℝ) (M M' : Mat3) (y y' : ℝ × ℝ) : ℝ × ℝ :=
  (merApply M' (Jrot y) + merApply M (Jrot y')) - (Jrot (merApply M' y) + Jrot (merApply M y'))
    + (qqd M M' y y' / (2 * a) - qq M y * a' / (2 * a ^ 2)) • Jrot y
    + (qq M y / (2 * a)) • Jrot y'

theorem WW_hasDerivAt (a y1 y2 : ℝ → ℝ) (M : ℝ → Mat3) (a' d1 d2 τ : ℝ) (M' : Mat3)
    (ha : HasDerivAt a a' τ) (hM : HasDerivAt M M' τ)
    (h1 : HasDerivAt y1 d1 τ) (h2 : HasDerivAt y2 d2 τ) (hne : a τ ≠ 0) :
    HasDerivAt (fun t => WW (a t) (M t) (y1 t, y2 t))
      (WWd (a τ) a' (M τ) M' (y1 τ, y2 τ) (d1, d2)) τ := by
  have hA := merApply_hasDerivAt M M' y1 y2 d1 d2 τ hM h1 h2
  have hB := merApply_hasDerivAt M M' (fun t => -y2 t) y1 (-d2) d1 τ hM h2.neg h1
  obtain ⟨hu1, hu2⟩ := mer_hasDerivAt M M' y1 y2 d1 d2 τ hM h1 h2
  obtain ⟨hv1, hv2⟩ := mer_hasDerivAt M M' (fun t => -y2 t) y1 (-d2) d1 τ hM h2.neg h1
  have hq := (h1.mul hu1).add (h2.mul hu2)
  have hc := hq.fun_div (ha.const_mul 2) (by simpa using hne)
  have hW1 := (hv1.sub hu2.neg).add (hc.mul h2.neg)
  have hW2 := (hv2.sub hu1).add (hc.mul h1)
  have hfun : (fun t => WW (a t) (M t) (y1 t, y2 t)) = fun t =>
      ((merApply (M t) (-y2 t, y1 t)).1 - -(merApply (M t) (y1 t, y2 t)).2
        + (y1 t * (merApply (M t) (y1 t, y2 t)).1 + y2 t * (merApply (M t) (y1 t, y2 t)).2)
            / (2 * a t) * -y2 t,
       (merApply (M t) (-y2 t, y1 t)).2 - (merApply (M t) (y1 t, y2 t)).1
        + (y1 t * (merApply (M t) (y1 t, y2 t)).1 + y2 t * (merApply (M t) (y1 t, y2 t)).2)
            / (2 * a t) * y1 t) := by
    funext t
    ext <;> simp [WW, qq, Jrot, merApply] <;> ring
  rw [hfun]
  refine (hW1.prodMk hW2).congr_deriv ?_
  ext <;> simp [WWd, qqd, qq, Jrot, merApply] <;> field_simp <;> ring

/-- Sum of the absolute values of the meridional entries. -/
def Nm (M : Mat3) : ℝ := |M 0 0| + |M 0 2| + |M 2 0| + |M 2 2|

theorem Nm_nonneg (M : Mat3) : 0 ≤ Nm M := by unfold Nm; positivity

theorem Nm_le (M : Mat3) (B : ℝ) (h : ‖M‖ ≤ B) : Nm M ≤ 4 * B := by
  have e : ∀ i k, |M i k| ≤ B := fun i k => by
    rw [← Real.norm_eq_abs]
    exact ((norm_le_pi_norm (M i) k).trans (norm_le_pi_norm M i)).trans h
  unfold Nm
  linarith [e 0 0, e 0 2, e 2 0, e 2 2]

theorem dot_abs (x p : ℝ × ℝ) : |x.1 * p.1 + x.2 * p.2| ≤ 2 * ‖x‖ * ‖p‖ := by
  have h1 : |x.1| ≤ ‖x‖ := by rw [← Real.norm_eq_abs]; exact norm_fst_le x
  have h2 : |x.2| ≤ ‖x‖ := by rw [← Real.norm_eq_abs]; exact norm_snd_le x
  have h3 : |p.1| ≤ ‖p‖ := by rw [← Real.norm_eq_abs]; exact norm_fst_le p
  have h4 : |p.2| ≤ ‖p‖ := by rw [← Real.norm_eq_abs]; exact norm_snd_le p
  calc |x.1 * p.1 + x.2 * p.2| ≤ |x.1 * p.1| + |x.2 * p.2| := abs_add_le _ _
    _ = |x.1| * |p.1| + |x.2| * |p.2| := by rw [abs_mul, abs_mul]
    _ ≤ ‖x‖ * ‖p‖ + ‖x‖ * ‖p‖ :=
        add_le_add (mul_le_mul h1 h3 (abs_nonneg _) (norm_nonneg _))
          (mul_le_mul h2 h4 (abs_nonneg _) (norm_nonneg _))
    _ = 2 * ‖x‖ * ‖p‖ := by ring

theorem mer_norm (M : Mat3) (w : ℝ × ℝ) : ‖merApply M w‖ ≤ Nm M * ‖w‖ :=
  gp_merApply_norm_le M w

theorem qq_abs (M : Mat3) (y : ℝ × ℝ) : |qq M y| ≤ 2 * Nm M * ‖y‖ ^ 2 := by
  have h := dot_abs y (merApply M y)
  have h2 := mer_norm M y
  have hy := norm_nonneg y
  unfold qq
  nlinarith [mul_le_mul_of_nonneg_left h2 (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) hy)]

theorem qqd_abs (M M' : Mat3) (y y' : ℝ × ℝ) :
    |qqd M M' y y'| ≤ 4 * ‖y'‖ * Nm M * ‖y‖ + 2 * Nm M' * ‖y‖ ^ 2 := by
  have h1 := dot_abs y' (merApply M y)
  have h2 := dot_abs y (merApply M' y + merApply M y')
  have n1 := mer_norm M y
  have n2 := mer_norm M' y
  have n3 := mer_norm M y'
  have n4 : ‖merApply M' y + merApply M y'‖ ≤ Nm M' * ‖y‖ + Nm M * ‖y'‖ :=
    (norm_add_le _ _).trans (add_le_add n2 n3)
  have e : qqd M M' y y' = (y'.1 * (merApply M y).1 + y'.2 * (merApply M y).2)
      + (y.1 * (merApply M' y + merApply M y').1 + y.2 * (merApply M' y + merApply M y').2) := by
    unfold qqd; ring
  rw [e]
  have hy := norm_nonneg y
  have hy' := norm_nonneg y'
  have k1 : 2 * ‖y'‖ * ‖merApply M y‖ ≤ 2 * ‖y'‖ * (Nm M * ‖y‖) :=
    mul_le_mul_of_nonneg_left n1 (by positivity)
  have k2 : 2 * ‖y‖ * ‖merApply M' y + merApply M y'‖ ≤ 2 * ‖y‖ * (Nm M' * ‖y‖ + Nm M * ‖y'‖) :=
    mul_le_mul_of_nonneg_left n4 (by positivity)
  calc _ ≤ |y'.1 * (merApply M y).1 + y'.2 * (merApply M y).2|
        + |y.1 * (merApply M' y + merApply M y').1 + y.2 * (merApply M' y + merApply M y').2| :=
        abs_add_le _ _
    _ ≤ _ := by nlinarith

theorem inv_a_abs (z a : ℝ) (ha : 1 ≤ a) : |z / (2 * a)| ≤ |z| / 2 := by
  rw [abs_div, abs_of_pos (by linarith : (0:ℝ) < 2 * a)]
  exact div_le_div_of_nonneg_left (abs_nonneg z) (by norm_num) (by linarith)

theorem WW_norm (a : ℝ) (M : Mat3) (y : ℝ × ℝ) (ha : 1 ≤ a) :
    ‖WW a M y‖ ≤ 2 * Nm M * ‖y‖ + Nm M * ‖y‖ ^ 3 := by
  have n1 : ‖merApply M (Jrot y)‖ ≤ Nm M * ‖y‖ := by
    have := mer_norm M (Jrot y); rwa [gp_jrot_norm] at this
  have n2 : ‖Jrot (merApply M y)‖ ≤ Nm M * ‖y‖ := by
    rw [gp_jrot_norm]; exact mer_norm M y
  have hc : |qq M y / (2 * a)| ≤ Nm M * ‖y‖ ^ 2 := by
    refine (inv_a_abs _ a ha).trans ?_
    have := qq_abs M y
    linarith
  have n3 : ‖(qq M y / (2 * a)) • Jrot y‖ ≤ Nm M * ‖y‖ ^ 2 * ‖y‖ := by
    rw [norm_smul, gp_jrot_norm, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right hc (norm_nonneg _)
  unfold WW
  calc _ ≤ ‖merApply M (Jrot y) - Jrot (merApply M y)‖ + ‖(qq M y / (2 * a)) • Jrot y‖ :=
        norm_add_le _ _
    _ ≤ (‖merApply M (Jrot y)‖ + ‖Jrot (merApply M y)‖) + ‖(qq M y / (2 * a)) • Jrot y‖ :=
        add_le_add_left (norm_sub_le _ _) _
    _ ≤ _ := by nlinarith

theorem WWd_norm (a a' : ℝ) (M M' : Mat3) (y y' : ℝ × ℝ) (ha : 1 ≤ a) :
    ‖WWd a a' M M' y y'‖ ≤ 2 * Nm M' * ‖y‖ + 2 * Nm M * ‖y'‖
      + (2 * ‖y'‖ * Nm M * ‖y‖ + Nm M' * ‖y‖ ^ 2 + Nm M * ‖y‖ ^ 2 * |a'|) * ‖y‖
      + Nm M * ‖y‖ ^ 2 * ‖y'‖ := by
  have hy := norm_nonneg y
  have hy' := norm_nonneg y'
  have hN := Nm_nonneg M
  have hN' := Nm_nonneg M'
  have n1 : ‖merApply M' (Jrot y)‖ ≤ Nm M' * ‖y‖ := by
    have := mer_norm M' (Jrot y); rwa [gp_jrot_norm] at this
  have n2 : ‖merApply M (Jrot y')‖ ≤ Nm M * ‖y'‖ := by
    have := mer_norm M (Jrot y'); rwa [gp_jrot_norm] at this
  have n3 : ‖Jrot (merApply M' y)‖ ≤ Nm M' * ‖y‖ := by
    rw [gp_jrot_norm]; exact mer_norm M' y
  have n4 : ‖Jrot (merApply M y')‖ ≤ Nm M * ‖y'‖ := by
    rw [gp_jrot_norm]; exact mer_norm M y'
  have hc : |qq M y / (2 * a)| ≤ Nm M * ‖y‖ ^ 2 := by
    refine (inv_a_abs _ a ha).trans ?_
    have := qq_abs M y
    linarith
  have hcd : |qqd M M' y y' / (2 * a) - qq M y * a' / (2 * a ^ 2)|
      ≤ 2 * ‖y'‖ * Nm M * ‖y‖ + Nm M' * ‖y‖ ^ 2 + Nm M * ‖y‖ ^ 2 * |a'| := by
    have t1 : |qqd M M' y y' / (2 * a)| ≤ |qqd M M' y y'| / 2 := inv_a_abs _ a ha
    have t2 : |qq M y * a' / (2 * a ^ 2)| ≤ |qq M y| * |a'| / 2 := by
      rw [abs_div, abs_mul, abs_of_pos (by positivity : (0:ℝ) < 2 * a ^ 2)]
      have : (2 : ℝ) ≤ 2 * a ^ 2 := by nlinarith
      exact div_le_div_of_nonneg_left (by positivity) (by norm_num) this
    have q1 := qqd_abs M M' y y'
    have q2 := qq_abs M y
    have q3 : |qq M y| * |a'| ≤ 2 * Nm M * ‖y‖ ^ 2 * |a'| :=
      mul_le_mul_of_nonneg_right q2 (abs_nonneg _)
    calc _ ≤ |qqd M M' y y' / (2 * a)| + |qq M y * a' / (2 * a ^ 2)| := abs_sub _ _
      _ ≤ _ := by nlinarith
  have n5 : ‖(qqd M M' y y' / (2 * a) - qq M y * a' / (2 * a ^ 2)) • Jrot y‖
      ≤ (2 * ‖y'‖ * Nm M * ‖y‖ + Nm M' * ‖y‖ ^ 2 + Nm M * ‖y‖ ^ 2 * |a'|) * ‖y‖ := by
    rw [norm_smul, gp_jrot_norm, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right hcd hy
  have n6 : ‖(qq M y / (2 * a)) • Jrot y'‖ ≤ Nm M * ‖y‖ ^ 2 * ‖y'‖ := by
    rw [norm_smul, gp_jrot_norm, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right hc hy'
  unfold WWd
  calc _ ≤ ‖(merApply M' (Jrot y) + merApply M (Jrot y')) - (Jrot (merApply M' y) + Jrot (merApply M y'))
        + (qqd M M' y y' / (2 * a) - qq M y * a' / (2 * a ^ 2)) • Jrot y‖
        + ‖(qq M y / (2 * a)) • Jrot y'‖ := norm_add_le _ _
    _ ≤ (‖(merApply M' (Jrot y) + merApply M (Jrot y')) - (Jrot (merApply M' y) + Jrot (merApply M y'))‖
        + ‖(qqd M M' y y' / (2 * a) - qq M y * a' / (2 * a ^ 2)) • Jrot y‖)
        + ‖(qq M y / (2 * a)) • Jrot y'‖ := add_le_add_left (norm_add_le _ _) _
    _ ≤ ((‖merApply M' (Jrot y) + merApply M (Jrot y')‖ + ‖Jrot (merApply M' y) + Jrot (merApply M y')‖)
        + ‖(qqd M M' y y' / (2 * a) - qq M y * a' / (2 * a ^ 2)) • Jrot y‖)
        + ‖(qq M y / (2 * a)) • Jrot y'‖ := by gcongr; exact norm_sub_le _ _
    _ ≤ _ := by
        have := norm_add_le (merApply M' (Jrot y)) (merApply M (Jrot y'))
        have := norm_add_le (Jrot (merApply M' y)) (Jrot (merApply M y'))
        nlinarith

/-- The logarithmic derivative factor of `EE` along a line. -/
def ef (a a' : ℝ) (y y' : ℝ × ℝ) : ℝ :=
  -2 * a' / a + (-(2 * (y.1 * y'.1 + y.2 * y'.2)) / (4 * a) + sq2 y * a' / (4 * a ^ 2))

theorem ef_abs (a a' : ℝ) (y y' : ℝ × ℝ) (ha : 1 ≤ a) :
    |ef a a' y y'| ≤ 2 * |a'| + ‖y‖ * ‖y'‖ + ‖y‖ ^ 2 * |a'| / 2 := by
  have hy := norm_nonneg y
  have hy' := norm_nonneg y'
  have hapos : 0 < a := by linarith
  have t1 : |-2 * a' / a| ≤ 2 * |a'| := by
    rw [abs_div, abs_of_pos hapos, abs_mul]
    rw [div_le_iff₀ hapos]
    have : (1 : ℝ) * (2 * |a'|) ≤ a * (2 * |a'|) :=
      mul_le_mul_of_nonneg_right ha (by positivity)
    have h2 : |(-2 : ℝ)| = 2 := by norm_num
    rw [h2]; linarith
  have t2 : |-(2 * (y.1 * y'.1 + y.2 * y'.2)) / (4 * a)| ≤ ‖y‖ * ‖y'‖ := by
    have hd := dot_abs y y'
    rw [abs_div, abs_neg, abs_mul, abs_of_pos (by linarith : (0:ℝ) < 4 * a)]
    rw [div_le_iff₀ (by linarith)]
    have h2 : |(2 : ℝ)| = 2 := by norm_num
    rw [h2]
    nlinarith [mul_nonneg hy hy']
  have t3 : |sq2 y * a' / (4 * a ^ 2)| ≤ ‖y‖ ^ 2 * |a'| / 2 := by
    have h1 : y.1 ^ 2 ≤ ‖y‖ ^ 2 := by
      have : |y.1| ≤ ‖y‖ := by rw [← Real.norm_eq_abs]; exact norm_fst_le y
      exact (sq_abs y.1).symm.le.trans (pow_le_pow_left₀ (abs_nonneg _) this 2)
    have h2 : y.2 ^ 2 ≤ ‖y‖ ^ 2 := by
      have : |y.2| ≤ ‖y‖ := by rw [← Real.norm_eq_abs]; exact norm_snd_le y
      exact (sq_abs y.2).symm.le.trans (pow_le_pow_left₀ (abs_nonneg _) this 2)
    have hs : sq2 y ≤ 2 * ‖y‖ ^ 2 := by unfold sq2; linarith
    have hs0 : 0 ≤ sq2 y := by unfold sq2; positivity
    rw [abs_div, abs_mul, abs_of_nonneg hs0, abs_of_pos (by positivity : (0:ℝ) < 4 * a ^ 2)]
    rw [div_le_iff₀ (by positivity)]
    have ha2 : (1 : ℝ) ≤ a ^ 2 := by nlinarith
    have : sq2 y * |a'| ≤ 2 * ‖y‖ ^ 2 * |a'| := mul_le_mul_of_nonneg_right hs (abs_nonneg _)
    have : ‖y‖ ^ 2 * |a'| / 2 * (4 * a ^ 2) = 2 * ‖y‖ ^ 2 * |a'| * a ^ 2 := by ring
    nlinarith [mul_nonneg (mul_nonneg (sq_nonneg ‖y‖) (abs_nonneg a')) (sub_nonneg.2 ha2)]
  unfold ef
  calc _ ≤ |-2 * a' / a| + |-(2 * (y.1 * y'.1 + y.2 * y'.2)) / (4 * a) + sq2 y * a' / (4 * a ^ 2)| :=
        abs_add_le _ _
    _ ≤ |-2 * a' / a| + (|-(2 * (y.1 * y'.1 + y.2 * y'.2)) / (4 * a)| + |sq2 y * a' / (4 * a ^ 2)|) :=
        add_le_add le_rfl (abs_add_le _ _)
    _ ≤ _ := by linarith

theorem poly_aux (P N N' α η Y : ℝ) (hP : 1 ≤ P) (hN0 : 0 ≤ N) (hN : N ≤ P) (hN0' : 0 ≤ N')
    (hN' : N' ≤ P) (hα0 : 0 ≤ α) (hα : α ≤ P) (hη0 : 0 ≤ η) (hη : η ≤ 1) (hY : 0 ≤ Y) :
    (2 * N' * Y + 2 * N * η + (2 * η * N * Y + N' * Y ^ 2 + N * Y ^ 2 * α) * Y + N * Y ^ 2 * η)
      + (2 * α + Y * η + Y ^ 2 * α / 2) * (2 * N * Y + N * Y ^ 3)
      ≤ 6 * P ^ 2 * (1 + Y) ^ 5 := by
  have hw : 1 ≤ 1 + Y := by linarith
  have hP2 : P ≤ P ^ 2 := by nlinarith
  have hw3 : 1 ≤ (1 + Y) ^ 3 := one_le_pow₀ hw
  have hw2 : 1 ≤ (1 + Y) ^ 2 := one_le_pow₀ hw
  have hA : 2 * N' * Y + 2 * N * η + (2 * η * N * Y + N' * Y ^ 2 + N * Y ^ 2 * α) * Y + N * Y ^ 2 * η
      ≤ 2 * P ^ 2 * (1 + Y) ^ 3 := by
    have b1 : N' * Y ≤ P ^ 2 * Y := by nlinarith
    have b2 : N * η ≤ P ^ 2 := by nlinarith
    have b3 : η * N * Y * Y ≤ P ^ 2 * Y ^ 2 := by nlinarith [mul_nonneg hY hY, mul_nonneg hη0 hN0]
    have b4 : N' * Y ^ 2 * Y ≤ P ^ 2 * Y ^ 3 := by nlinarith [pow_nonneg hY 3, pow_nonneg hY 2]
    have b5 : N * Y ^ 2 * α * Y ≤ P ^ 2 * Y ^ 3 := by
      have : N * α ≤ P ^ 2 := by nlinarith
      nlinarith [pow_nonneg hY 3]
    have b6 : N * Y ^ 2 * η ≤ P ^ 2 * Y ^ 2 := by
      have : N * η ≤ P ^ 2 := by nlinarith
      nlinarith [pow_nonneg hY 2]
    nlinarith [sq_nonneg P, pow_nonneg hY 2, pow_nonneg hY 3]
  have hB : 2 * α + Y * η + Y ^ 2 * α / 2 ≤ 2 * P * (1 + Y) ^ 2 := by
    nlinarith [mul_nonneg hY hY, mul_nonneg hY hα0, mul_nonneg (mul_nonneg hY hY) hα0]
  have hC : 2 * N * Y + N * Y ^ 3 ≤ 2 * P * (1 + Y) ^ 3 := by
    nlinarith [mul_nonneg hY hN0, pow_nonneg hY 3, pow_nonneg hY 2, mul_nonneg hN0 (pow_nonneg hY 3),
      mul_nonneg (sub_nonneg.2 hN) (pow_nonneg hY 3), mul_nonneg (sub_nonneg.2 hN) hY]
  have hBC : (2 * α + Y * η + Y ^ 2 * α / 2) * (2 * N * Y + N * Y ^ 3)
      ≤ (2 * P * (1 + Y) ^ 2) * (2 * P * (1 + Y) ^ 3) := by
    apply mul_le_mul hB hC (by positivity) (by positivity)
  have h5 : (1 + Y) ^ 3 ≤ (1 + Y) ^ 5 := pow_le_pow_right₀ hw (by norm_num)
  nlinarith [mul_nonneg (sq_nonneg P) (sub_nonneg.2 h5), sq_nonneg P]

theorem line_bound (a a' : ℝ) (M M' : Mat3) (y y' : ℝ × ℝ) (P : ℝ) (ha : 1 ≤ a) (hP : 1 ≤ P)
    (hα : |a'| ≤ P) (hN : Nm M ≤ P) (hN' : Nm M' ≤ P) (hη : ‖y'‖ ≤ 1) :
    ‖EE a y • WWd a a' M M' y y' + (EE a y * ef a a' y y') • WW a M y‖
      ≤ Real.exp (-(sq2 y) / (4 * a)) * (6 * P ^ 2 * (1 + ‖y‖) ^ 5) := by
  have hy := norm_nonneg y
  have hapos : 0 < a := by linarith
  have hG : 0 < Real.exp (-(sq2 y) / (4 * a)) := Real.exp_pos _
  have hE0 : 0 ≤ EE a y := by unfold EE; positivity
  have hE1 : EE a y ≤ Real.exp (-(sq2 y) / (4 * a)) := by
    unfold EE
    have : (a ^ 2)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by nlinarith)
    nlinarith
  have hA := WWd_norm a a' M M' y y' ha
  have hB := ef_abs a a' y y' ha
  have hC := WW_norm a M y ha
  have hpoly := poly_aux P (Nm M) (Nm M') |a'| ‖y'‖ ‖y‖ hP (Nm_nonneg M) hN (Nm_nonneg M') hN'
    (abs_nonneg _) hα (norm_nonneg _) hη hy
  have hBC : |ef a a' y y'| * ‖WW a M y‖ ≤ (2 * |a'| + ‖y‖ * ‖y'‖ + ‖y‖ ^ 2 * |a'| / 2)
      * (2 * Nm M * ‖y‖ + Nm M * ‖y‖ ^ 3) :=
    mul_le_mul hB hC (norm_nonneg _) ((abs_nonneg _).trans hB)
  have hsum : ‖WWd a a' M M' y y'‖ + |ef a a' y y'| * ‖WW a M y‖ ≤ 6 * P ^ 2 * (1 + ‖y‖) ^ 5 := by
    linarith
  have hn : ‖EE a y • WWd a a' M M' y y' + (EE a y * ef a a' y y') • WW a M y‖
      ≤ EE a y * (‖WWd a a' M M' y y'‖ + |ef a a' y y'| * ‖WW a M y‖) := by
    calc _ ≤ ‖EE a y • WWd a a' M M' y y'‖ + ‖(EE a y * ef a a' y y') • WW a M y‖ :=
          norm_add_le _ _
      _ = _ := by
          rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_of_nonneg hE0]
          ring
  calc _ ≤ _ := hn
    _ ≤ EE a y * (6 * P ^ 2 * (1 + ‖y‖) ^ 5) := mul_le_mul_of_nonneg_left hsum hE0
    _ ≤ _ := mul_le_mul_of_nonneg_right hE1 (by positivity)

theorem Ay_hasDerivAt (as : ℝ) (χ : ℝ → ℝ) (hχ : IsSourceCutoffC χ) (ν : ℝ) (A : ℝ → Mat3)
    (hA : IsAffElem as A) (s : ℝ) (hs : 0 < s) :
    HasDerivAt (Ay ν χ A) (deriv (Ay ν χ A) s) s := by
  have hχd : Differentiable ℝ χ := hχ.smooth.differentiable (by simp)
  have hAd : DifferentiableAt ℝ A s :=
    (hA.smooth.differentiableOn (by norm_num)).differentiableAt (Ioi_mem_nhds hs)
  have h1 : DifferentiableAt ℝ (fun s : ℝ => χ (ν * s)) s :=
    (hχd (ν * s)).comp s (differentiableAt_id.const_mul ν)
  exact (h1.smul hAd).hasDerivAt

theorem hpATm_differentiableAt (as : ℝ) (χ : ℝ → ℝ) (hχ : IsSourceCutoffC χ) (ν : ℝ) (hν : 0 < ν)
    (A : ℝ → Mat3) (hA : IsAffElem as A) (j : ℤ) (p : Chart) (hp : 0 < p.1) :
    DifferentiableAt ℝ (hpATm ν χ A j) p := by
  have hs := (Ay_hasDerivAt as χ hχ ν A hA p.1 hp).differentiableAt
  have hm : ∀ i k, DifferentiableAt ℝ (fun q : Chart => Ay ν χ A q.1 i k) p := fun i k =>
    (differentiableAt_pi.1 (differentiableAt_pi.1 hs i) k).comp p differentiableAt_fst
  have hane : 1 + ν * p.1 ≠ 0 := by have : 0 < ν * p.1 := by positivity
                                    linarith
  have e : hpATm ν χ A j = fun q => EE (ageA ν q.1) (xj ν j q.2) •
      WW (ageA ν q.1) (Ay ν χ A q.1) (xj ν j q.2) := funext (hpATm_eq' ν χ A j)
  rw [e]
  have h00 := hm 0 0
  have h02 := hm 0 2
  have h20 := hm 2 0
  have h22 := hm 2 2
  simp only [EE, WW, qq, merApply, Jrot, xj, sq2, ageA]
  fun_prop (disch := first | exact hane | positivity | simp [hane])

theorem fderiv_chart_line (f : Chart → ℝ × ℝ) (p v : Chart) (hf : DifferentiableAt ℝ f p) :
    HasDerivAt (fun t : ℝ => f (p + t • v)) (fderiv ℝ f p v) 0 := by
  have hl : HasDerivAt (fun t : ℝ => p + t • v) v 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add p
  have h2 : HasFDerivAt f (fderiv ℝ f p) ((fun t : ℝ => p + t • v) 0) := by
    simpa using hf.hasFDerivAt
  exact h2.comp_hasDerivAt (0 : ℝ) hl

theorem hpATm_fderiv_bound_at (as : ℝ) (χ : ℝ → ℝ) (hχ : IsSourceCutoffC χ) (ν : ℝ) (hν : 0 < ν)
    (A : ℝ → Mat3) (hA : IsAffElem as A) (j : ℤ) (p : Chart) (hp : 0 < p.1) (B : ℝ)
    (hM : ‖Ay ν χ A p.1‖ ≤ B) (hM' : ‖deriv (Ay ν χ A) p.1‖ ≤ B) (hB : 0 ≤ B) :
    ‖fderiv ℝ (hpATm ν χ A j) p‖ ≤
      Real.exp (-(sq2 (xj ν j p.2)) / (4 * ageA ν p.1))
        * (6 * (1 + ν + 4 * B) ^ 2 * (1 + ‖xj ν j p.2‖) ^ 5) := by
  have hdiff := hpATm_differentiableAt as χ hχ ν hν A hA j p hp
  have ha1 : 1 ≤ ageA ν p.1 := by unfold ageA; nlinarith [mul_pos hν hp]
  have hP : 1 ≤ 1 + ν + 4 * B := by linarith
  refine ContinuousLinearMap.opNorm_le_of_unit_norm (by positivity) ?_
  intro v hv
  have hline := fderiv_chart_line _ p v hdiff
  -- the explicit line functions
  have hs : HasDerivAt (fun t : ℝ => p.1 + t * v.1) v.1 0 := by
    simpa using ((hasDerivAt_id' (0:ℝ)).mul_const v.1).const_add p.1
  have ha : HasDerivAt (fun t : ℝ => ageA ν (p.1 + t * v.1)) (ν * v.1) 0 := by
    unfold ageA
    simpa using (hs.const_mul ν).const_add 1
  have h1 : HasDerivAt (fun t : ℝ => p.2.1 + t * v.2.1 - (j : ℝ) * cOf ν) v.2.1 0 := by
    simpa using (((hasDerivAt_id' (0:ℝ)).mul_const v.2.1).const_add p.2.1).sub_const
      ((j : ℝ) * cOf ν)
  have h2 : HasDerivAt (fun t : ℝ => p.2.2 + t * v.2.2) v.2.2 0 := by
    simpa using ((hasDerivAt_id' (0:ℝ)).mul_const v.2.2).const_add p.2.2
  have hAy : HasDerivAt (fun t : ℝ => Ay ν χ A (p.1 + t * v.1)) (v.1 • deriv (Ay ν χ A) p.1) 0 := by
    have := (Ay_hasDerivAt as χ hχ ν A hA p.1 hp)
    have h0 : HasDerivAt (Ay ν χ A) (deriv (Ay ν χ A) p.1) ((fun t : ℝ => p.1 + t * v.1) 0) := by
      simpa using this
    exact h0.scomp (0:ℝ) hs
  have hne : ageA ν (p.1 + (0:ℝ) * v.1) ≠ 0 := by
    simp only [zero_mul, add_zero]; linarith
  have hE := EE_hasDerivAt (fun t : ℝ => ageA ν (p.1 + t * v.1))
    (fun t : ℝ => p.2.1 + t * v.2.1 - (j : ℝ) * cOf ν) (fun t : ℝ => p.2.2 + t * v.2.2)
    (ν * v.1) v.2.1 v.2.2 0 ha h1 h2 hne
  have hW := WW_hasDerivAt (fun t : ℝ => ageA ν (p.1 + t * v.1))
    (fun t : ℝ => p.2.1 + t * v.2.1 - (j : ℝ) * cOf ν) (fun t : ℝ => p.2.2 + t * v.2.2)
    (fun t : ℝ => Ay ν χ A (p.1 + t * v.1)) (ν * v.1) v.2.1 v.2.2 0 _ ha hAy h1 h2 hne
  have hprod := hE.smul hW
  have hfun : (fun t : ℝ => hpATm ν χ A j (p + t • v)) = fun t : ℝ =>
      EE (ageA ν (p.1 + t * v.1)) (p.2.1 + t * v.2.1 - (j : ℝ) * cOf ν, p.2.2 + t * v.2.2) •
        WW (ageA ν (p.1 + t * v.1)) (Ay ν χ A (p.1 + t * v.1))
          (p.2.1 + t * v.2.1 - (j : ℝ) * cOf ν, p.2.2 + t * v.2.2) := by
    funext t
    rw [hpATm_eq']
    simp [xj]
  rw [hfun] at hline
  have huniq := hline.unique hprod
  simp only [zero_mul, add_zero] at huniq
  rw [huniq]
  have hvn : ‖v.1‖ ≤ 1 := hv ▸ norm_fst_le v
  have hv2 : ‖((v.2.1, v.2.2) : ℝ × ℝ)‖ ≤ 1 := hv ▸ norm_snd_le v
  have hvabs : |v.1| ≤ 1 := by simpa using hvn
  have hAyn : Nm (Ay ν χ A p.1) ≤ 1 + ν + 4 * B := by linarith [Nm_le _ _ hM]
  have hD : ‖v.1 • deriv (Ay ν χ A) p.1‖ ≤ B := by
    rw [norm_smul]
    calc ‖v.1‖ * ‖deriv (Ay ν χ A) p.1‖ ≤ 1 * B :=
          mul_le_mul hvn hM' (norm_nonneg _) zero_le_one
      _ = B := one_mul B
  have hDn : Nm (v.1 • deriv (Ay ν χ A) p.1) ≤ 1 + ν + 4 * B := by linarith [Nm_le _ _ hD]
  have hα : |ν * v.1| ≤ 1 + ν + 4 * B := by
    rw [abs_mul, abs_of_pos hν]
    nlinarith [abs_nonneg v.1]
  have key := line_bound (ageA ν p.1) (ν * v.1) (Ay ν χ A p.1) (v.1 • deriv (Ay ν χ A) p.1)
    (p.2.1 - (j : ℝ) * cOf ν, p.2.2) (v.2.1, v.2.2) (1 + ν + 4 * B) ha1 hP hα hAyn hDn hv2
  simpa [xj, EE, ef] using key

/-- `PartIII-b:C/grad/3/5/1/3/3/c`: on `s0 ≤ s ≤ s1`, `‖x‖ ≤ R`, the lattice term `hpATm` is
differentiable and its derivative is bounded by `K (1 + |y|)^5 exp(-y²/(4a))`, `y = q - j c(ν)`,
`a = 1 + ν s`, with `K` independent of `j` and `p` (source 4963-4980, 5063-5079). -/
theorem hpATm_hasFDerivAt_bound (as : ℝ) (χ : ℝ → ℝ) (hχ : IsSourceCutoffC χ) (ν : ℝ) (hν : 0 < ν)
    (A : ℝ → Mat3) (hA : IsAffElem as A) (s0 s1 R B : ℝ) (hs0 : 0 < s0) (hs01 : s0 ≤ s1)
    (hBd : ∀ s ∈ Set.Icc s0 s1, ‖Ay ν χ A s‖ ≤ B ∧ ‖deriv (Ay ν χ A) s‖ ≤ B) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (j : ℤ) (p : Chart), s0 ≤ p.1 → p.1 ≤ s1 → ‖p.2‖ ≤ R →
      DifferentiableAt ℝ (hpATm ν χ A j) p ∧
      ‖fderiv ℝ (hpATm ν χ A j) p‖ ≤
        K * (1 + |p.2.1 - (j : ℝ) * cOf ν|) ^ 5 *
          Real.exp (-(p.2.1 - (j : ℝ) * cOf ν) ^ 2 / (4 * ageA ν p.1)) := by
  have hB : 0 ≤ B := (norm_nonneg _).trans (hBd s0 ⟨le_rfl, hs01⟩).1
  refine ⟨6 * (1 + ν + 4 * B) ^ 2 * (1 + max R 0) ^ 5, by positivity, ?_⟩
  intro j p h1 h2 h3
  have hp : 0 < p.1 := lt_of_lt_of_le hs0 h1
  refine ⟨hpATm_differentiableAt as χ hχ ν hν A hA j p hp, ?_⟩
  obtain ⟨hM, hM'⟩ := hBd p.1 ⟨h1, h2⟩
  refine (hpATm_fderiv_bound_at as χ hχ ν hν A hA j p hp B hM hM' hB).trans ?_
  have ha : 0 < ageA ν p.1 := by unfold ageA; nlinarith [mul_pos hν hp]
  set y1 : ℝ := p.2.1 - (j : ℝ) * cOf ν with hy1
  have hexp : Real.exp (-(sq2 (xj ν j p.2)) / (4 * ageA ν p.1)) ≤
      Real.exp (-y1 ^ 2 / (4 * ageA ν p.1)) := by
    apply Real.exp_le_exp.mpr
    have : sq2 (xj ν j p.2) = y1 ^ 2 + p.2.2 ^ 2 := by simp [sq2, xj, hy1]
    rw [this]
    apply div_le_div_of_nonneg_right _ (by positivity)
    nlinarith [sq_nonneg p.2.2]
  have hw : 1 + ‖xj ν j p.2‖ ≤ (1 + max R 0) * (1 + |y1|) := by
    have hn : ‖xj ν j p.2‖ ≤ |y1| + max R 0 := by
      have hx2 : |p.2.2| ≤ R := by
        have : |p.2.2| ≤ ‖p.2‖ := by rw [← Real.norm_eq_abs]; exact norm_snd_le p.2
        linarith
      show max ‖y1‖ ‖p.2.2‖ ≤ _
      refine max_le ?_ ?_
      · rw [Real.norm_eq_abs]; linarith [le_max_right R 0]
      · rw [Real.norm_eq_abs]; linarith [le_max_left R 0, abs_nonneg y1]
    nlinarith [le_max_right R 0, abs_nonneg y1, mul_nonneg (le_max_right R 0) (abs_nonneg y1)]
  have hw5 : (1 + ‖xj ν j p.2‖) ^ 5 ≤ ((1 + max R 0) * (1 + |y1|)) ^ 5 :=
    pow_le_pow_left₀ (by positivity) hw 5
  rw [mul_pow] at hw5
  have hP : 0 ≤ 6 * (1 + ν + 4 * B) ^ 2 := by positivity
  calc _ ≤ Real.exp (-y1 ^ 2 / (4 * ageA ν p.1)) *
        (6 * (1 + ν + 4 * B) ^ 2 * ((1 + max R 0) ^ 5 * (1 + |y1|) ^ 5)) := by
        apply mul_le_mul hexp (mul_le_mul_of_nonneg_left hw5 hP) (by positivity)
        exact (Real.exp_pos _).le
    _ = _ := by ring

end UnforcedLeray.Short.PartIIIb.Concrete
