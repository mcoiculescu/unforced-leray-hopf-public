import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_1_5

/-!
# Gaussian bounds for the lattice terms (source 4988: "the sums and their required derivatives
converge by Gaussian decay")

Pointwise polynomial bounds `|ftF1|, |ftF2|, |ftD1|, |ftD2| ≤ K · ftPh · w⁴`, `w = 1 + u² + v²`, and
the locally uniform lattice-summable majorant of `K · ftPh(t - jc, v) · w^m`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal ComplexConjugate ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

theorem pb_w (u v : ℝ) : 1 ≤ 1 + u ^ 2 + v ^ 2 ∧ |u| ≤ 1 + u ^ 2 + v ^ 2 ∧
    |v| ≤ 1 + u ^ 2 + v ^ 2 := by
  refine ⟨by nlinarith [sq_nonneg u, sq_nonneg v], ?_, ?_⟩
  · exact abs_le.2 ⟨by nlinarith [sq_nonneg (u + 1), sq_nonneg u, sq_nonneg v],
      by nlinarith [sq_nonneg (u - 1), sq_nonneg u, sq_nonneg v]⟩
  · exact abs_le.2 ⟨by nlinarith [sq_nonneg (v + 1), sq_nonneg u, sq_nonneg v],
      by nlinarith [sq_nonneg (v - 1), sq_nonneg u, sq_nonneg v]⟩

theorem pb_lin (p q u v w : ℝ) (hu : |u| ≤ w) (hv : |v| ≤ w) :
    |p * u + q * v| ≤ (|p| + |q|) * w := by
  calc |p * u + q * v| ≤ |p * u| + |q * v| := abs_add_le _ _
    _ = |p| * |u| + |q| * |v| := by rw [abs_mul, abs_mul]
    _ ≤ |p| * w + |q| * w :=
        add_le_add (mul_le_mul_of_nonneg_left hu (abs_nonneg _))
          (mul_le_mul_of_nonneg_left hv (abs_nonneg _))
    _ = (|p| + |q|) * w := by ring

theorem pb_mul {x y X Y : ℝ} (hx : |x| ≤ X) (hy : |y| ≤ Y) : |x * y| ≤ X * Y := by
  rw [abs_mul]
  exact mul_le_mul hx hy (abs_nonneg _) ((abs_nonneg _).trans hx)

theorem pb_add {x y X Y : ℝ} (hx : |x| ≤ X) (hy : |y| ≤ Y) : |x + y| ≤ X + Y :=
  (abs_add_le _ _).trans (add_le_add hx hy)

/-- Common polynomial estimates, `Mb = |B₀₀| + |B₀₂| + |B₂₀| + |B₂₂|`, `w = 1 + u² + v²`. -/
theorem pb_core (B : Mat3) (u v w Mb : ℝ) (hw : w = 1 + u ^ 2 + v ^ 2)
    (hM : Mb = |B 0 0| + |B 0 2| + |B 2 0| + |B 2 2|) :
    |ftQf B u v| ≤ 2 * Mb * w ^ 2 ∧ |ftQu B u v| ≤ 2 * Mb * w ∧ |ftQv B u v| ≤ 2 * Mb * w ∧
    |B 0 0 * u + B 0 2 * v| ≤ Mb * w ∧ |B 2 0 * u + B 2 2 * v| ≤ Mb * w := by
  obtain ⟨hw1, hu, hv⟩ := pb_w u v
  rw [← hw] at hw1 hu hv
  have a00 := abs_nonneg (B 0 0)
  have a02 := abs_nonneg (B 0 2)
  have a20 := abs_nonneg (B 2 0)
  have a22 := abs_nonneg (B 2 2)
  have hwn : 0 ≤ w := by linarith
  have l1 : |B 0 0 * u + B 0 2 * v| ≤ Mb * w := by
    refine (pb_lin _ _ u v w hu hv).trans ?_
    exact mul_le_mul_of_nonneg_right (by rw [hM]; linarith) hwn
  have l2 : |B 2 0 * u + B 2 2 * v| ≤ Mb * w := by
    refine (pb_lin _ _ u v w hu hv).trans ?_
    exact mul_le_mul_of_nonneg_right (by rw [hM]; linarith) hwn
  refine ⟨?_, ?_, ?_, l1, l2⟩
  · have := pb_add (pb_mul hu l1) (pb_mul hv l2)
    unfold ftQf
    refine this.trans (le_of_eq ?_)
    ring
  · have h := pb_lin (2 * B 0 0) (B 0 2 + B 2 0) u v w hu hv
    have e1 : |2 * B 0 0| = 2 * |B 0 0| := by rw [abs_mul]; norm_num
    have e2 := abs_add_le (B 0 2) (B 2 0)
    unfold ftQu
    have : (|2 * B 0 0| + |B 0 2 + B 2 0|) * w ≤ 2 * Mb * w := by
      apply mul_le_mul_of_nonneg_right _ hwn
      rw [hM, e1]; linarith
    have e3 : 2 * B 0 0 * u + (B 0 2 + B 2 0) * v = 2 * B 0 0 * u + (B 0 2 + B 2 0) * v := rfl
    exact h.trans this
  · have h := pb_lin (B 0 2 + B 2 0) (2 * B 2 2) u v w hu hv
    have e1 : |2 * B 2 2| = 2 * |B 2 2| := by rw [abs_mul]; norm_num
    have e2 := abs_add_le (B 0 2) (B 2 0)
    unfold ftQv
    have : (|B 0 2 + B 2 0| + |2 * B 2 2|) * w ≤ 2 * Mb * w := by
      apply mul_le_mul_of_nonneg_right _ hwn
      rw [hM, e1]; linarith
    exact h.trans this


theorem ftPh_pos (a u v : ℝ) (ha : 0 < a) : 0 < ftPh a u v := by
  unfold ftPh; positivity

set_option maxHeartbeats 1600000 in
/-- The pointwise polynomial-times-Gaussian bound for the closed forms of `fTerm` and its two
partial derivatives. -/
theorem pb_all (a : ℝ) (ha : 0 < a) (B : Mat3) : ∃ K : ℝ, 0 ≤ K ∧ ∀ u v : ℝ,
    |ftF1 a B u v| ≤ K * ftPh a u v * (1 + u ^ 2 + v ^ 2) ^ 4 ∧
    |ftF2 a B u v| ≤ K * ftPh a u v * (1 + u ^ 2 + v ^ 2) ^ 4 ∧
    |ftD1 a B u v| ≤ K * ftPh a u v * (1 + u ^ 2 + v ^ 2) ^ 4 ∧
    |ftD2 a B u v| ≤ K * ftPh a u v * (1 + u ^ 2 + v ^ 2) ^ 4 := by
  set Mb : ℝ := |B 0 0| + |B 0 2| + |B 2 0| + |B 2 2| with hM
  set q : ℝ := 1 / (2 * a) with hq
  have hq0 : 0 ≤ q := by rw [hq]; positivity
  have hMb : 0 ≤ Mb := by rw [hM]; positivity
  set CG : ℝ := 2 * Mb * q + 2 * Mb with hCG
  have hCG0 : 0 ≤ CG := by rw [hCG]; positivity
  refine ⟨CG * (1 + q) + 4 * Mb * q + Mb, by positivity, fun u v => ?_⟩
  set w : ℝ := 1 + u ^ 2 + v ^ 2 with hw
  obtain ⟨hw1, hu, hv⟩ := pb_w u v
  rw [← hw] at hw1 hu hv
  obtain ⟨hQf, hQu, hQv, l1, l2⟩ := pb_core B u v w Mb hw hM
  have hwn : 0 ≤ w := by linarith
  have hph := ftPh_pos a u v ha
  have w3 : w ≤ w ^ 3 := by simpa using pow_le_pow_right₀ hw1 (show 1 ≤ 3 by norm_num)
  have w2 : w ^ 2 ≤ w ^ 4 := pow_le_pow_right₀ hw1 (by norm_num)
  have w3' : w ^ 3 ≤ w ^ 4 := pow_le_pow_right₀ hw1 (by norm_num)
  have h2a : (0 : ℝ) < 2 * a := by positivity
  have habsdiv : ∀ x : ℝ, |x / (2 * a)| = |x| * q := by
    intro x
    rw [abs_div, abs_of_pos h2a, hq, div_eq_mul_one_div]
  have hK : |ftKap a B u v| ≤ 2 * Mb * w ^ 2 * q := by
    unfold ftKap
    rw [abs_div, abs_neg, abs_of_pos h2a, div_eq_mul_one_div, ← hq]
    exact mul_le_mul_of_nonneg_right hQf hq0
  have h3 : |-(B 2 0 * v) + B 2 2 * u| ≤ Mb * w := by
    have h := pb_lin (B 2 2) (-B 2 0) u v w hu hv
    rw [abs_neg] at h
    have e : -(B 2 0 * v) + B 2 2 * u = B 2 2 * u + -B 2 0 * v := by ring
    rw [e]
    refine h.trans (mul_le_mul_of_nonneg_right ?_ hwn)
    rw [hM]; linarith [abs_nonneg (B 0 0), abs_nonneg (B 0 2)]
  have h5 : |-(B 0 0 * v) + B 0 2 * u| ≤ Mb * w := by
    have h := pb_lin (B 0 2) (-B 0 0) u v w hu hv
    rw [abs_neg] at h
    have e : -(B 0 0 * v) + B 0 2 * u = B 0 2 * u + -B 0 0 * v := by ring
    rw [e]
    refine h.trans (mul_le_mul_of_nonneg_right ?_ hwn)
    rw [hM]; linarith [abs_nonneg (B 2 0), abs_nonneg (B 2 2)]
  have h4 : |-(B 2 0 * u + B 2 2 * v)| ≤ Mb * w := by rw [abs_neg]; exact l2
  have hKu : |ftKap a B u v * u| ≤ 2 * Mb * w ^ 2 * q * w := pb_mul hK hu
  have hKv : |ftKap a B u v * (-v)| ≤ 2 * Mb * w ^ 2 * q * w := by
    have := pb_mul hK hv
    rw [mul_neg, abs_neg]; exact this
  have hG2 : |ftKap a B u v * u + (B 0 0 * u + B 0 2 * v) + (-(B 2 0 * v) + B 2 2 * u)| ≤
      CG * w ^ 3 := by
    have := pb_add (pb_add hKu l1) h3
    refine this.trans ?_
    have e : 2 * Mb * w ^ 2 * q * w + Mb * w + Mb * w = (2 * Mb * q) * w ^ 3 + 2 * Mb * w := by
      ring
    have e2 : CG * w ^ 3 = (2 * Mb * q) * w ^ 3 + 2 * (Mb * w ^ 3) := by rw [hCG]; ring
    rw [e, e2]
    linarith [mul_le_mul_of_nonneg_left w3 hMb]
  have hG1 : |ftKap a B u v * (-v) + (-(B 2 0 * u + B 2 2 * v)) + (-(B 0 0 * v) + B 0 2 * u)| ≤
      CG * w ^ 3 := by
    have := pb_add (pb_add hKv h4) h5
    refine this.trans ?_
    have e : 2 * Mb * w ^ 2 * q * w + Mb * w + Mb * w = (2 * Mb * q) * w ^ 3 + 2 * Mb * w := by
      ring
    have e2 : CG * w ^ 3 = (2 * Mb * q) * w ^ 3 + 2 * (Mb * w ^ 3) := by rw [hCG]; ring
    rw [e, e2]
    linarith [mul_le_mul_of_nonneg_left w3 hMb]
  have hF : ∀ G : ℝ, |G| ≤ CG * w ^ 3 → |ftPh a u v * G| ≤ CG * (1 + q) * ftPh a u v * w ^ 4 := by
    intro G hG
    rw [abs_mul, abs_of_pos hph]
    calc ftPh a u v * |G| ≤ ftPh a u v * (CG * w ^ 3) := mul_le_mul_of_nonneg_left hG hph.le
      _ ≤ ftPh a u v * (CG * w ^ 4) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left w3' hCG0) hph.le
      _ ≤ CG * (1 + q) * ftPh a u v * w ^ 4 := by
          have : 0 ≤ CG * q * ftPh a u v * w ^ 4 := by positivity
          have e : CG * (1 + q) * ftPh a u v * w ^ 4 =
              ftPh a u v * (CG * w ^ 4) + CG * q * ftPh a u v * w ^ 4 := by ring
          rw [e]; linarith
  have hKfin : CG * (1 + q) ≤ CG * (1 + q) + 4 * Mb * q + Mb := by
    have : 0 ≤ 4 * Mb * q + Mb := by positivity
    linarith
  have hwq : 0 ≤ ftPh a u v * w ^ 4 := by positivity
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold ftF1
    refine (hF _ hG1).trans ?_
    have := mul_le_mul_of_nonneg_right hKfin hwq
    linarith
  · unfold ftF2
    refine (hF _ hG2).trans ?_
    have := mul_le_mul_of_nonneg_right hKfin hwq
    linarith
  · -- D1
    have hc : |-(2 * v) / (4 * a)| ≤ w * q := by
      have e : -(2 * v) / (4 * a) = -(v * q) := by rw [hq]; field_simp; ring
      rw [e, abs_neg, abs_mul, abs_of_nonneg hq0]
      exact mul_le_mul_of_nonneg_right hv hq0
    have hX : |ftQf B u v + v * ftQv B u v| ≤ 4 * Mb * w ^ 2 := by
      have := pb_add hQf (pb_mul hv hQv)
      refine this.trans (le_of_eq ?_)
      ring
    have hH : |(ftQf B u v + v * ftQv B u v) / (2 * a) - B 2 2 - B 0 0| ≤
        (4 * Mb * q + Mb) * w ^ 4 := by
      have h1 : |(ftQf B u v + v * ftQv B u v) / (2 * a)| ≤ 4 * Mb * w ^ 2 * q := by
        rw [habsdiv]; exact mul_le_mul_of_nonneg_right hX hq0
      have h2 : |(ftQf B u v + v * ftQv B u v) / (2 * a) - B 2 2 - B 0 0| ≤
          |(ftQf B u v + v * ftQv B u v) / (2 * a)| + |B 2 2| + |B 0 0| := by
        refine (abs_sub _ _).trans ?_
        have := abs_sub (((ftQf B u v + v * ftQv B u v) / (2 * a))) (B 2 2)
        linarith
      have h3 : 4 * Mb * w ^ 2 * q + |B 2 2| + |B 0 0| ≤ (4 * Mb * q + Mb) * w ^ 4 := by
        have hm : |B 2 2| + |B 0 0| ≤ Mb := by
          rw [hM]; linarith [abs_nonneg (B 0 2), abs_nonneg (B 2 0)]
        have : 0 ≤ 4 * Mb * q := by positivity
        have e1 : 1 ≤ w ^ 4 := one_le_pow₀ hw1
        linarith [mul_le_mul_of_nonneg_left w2 this, mul_le_mul_of_nonneg_left e1 hMb]
      linarith
    unfold ftD1
    have t1 : |ftPh a u v * (-(2 * v) / (4 * a)) *
        (ftKap a B u v * -v + -(B 2 0 * u + B 2 2 * v) + (-(B 0 0 * v) + B 0 2 * u))| ≤
        ftPh a u v * (q * CG) * w ^ 4 := by
      rw [abs_mul, abs_mul, abs_of_pos hph]
      have := mul_le_mul hc hG1 (abs_nonneg _) (by positivity)
      calc ftPh a u v * |-(2 * v) / (4 * a)| *
            |ftKap a B u v * -v + -(B 2 0 * u + B 2 2 * v) + (-(B 0 0 * v) + B 0 2 * u)|
          ≤ ftPh a u v * (w * q * (CG * w ^ 3)) := by
            rw [mul_assoc]
            exact mul_le_mul_of_nonneg_left (by simpa [mul_comm] using this) hph.le
        _ = ftPh a u v * (q * CG) * w ^ 4 := by ring
    have t2 : |ftPh a u v * ((ftQf B u v + v * ftQv B u v) / (2 * a) - B 2 2 - B 0 0)| ≤
        ftPh a u v * ((4 * Mb * q + Mb) * w ^ 4) := by
      rw [abs_mul, abs_of_pos hph]
      exact mul_le_mul_of_nonneg_left hH hph.le
    refine (abs_add_le _ _).trans ?_
    have hqCG : 0 ≤ q * CG := mul_nonneg hq0 hCG0
    have : ftPh a u v * (q * CG) * w ^ 4 + ftPh a u v * ((4 * Mb * q + Mb) * w ^ 4) =
        (q * CG + 4 * Mb * q + Mb) * ftPh a u v * w ^ 4 := by ring
    have hK2 : (q * CG + 4 * Mb * q + Mb) * ftPh a u v * w ^ 4 ≤
        (CG * (1 + q) + 4 * Mb * q + Mb) * ftPh a u v * w ^ 4 := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      apply mul_le_mul_of_nonneg_right _ hph.le
      linarith [hCG0]
    linarith
  · -- D2
    have hc : |-(2 * u) / (4 * a)| ≤ w * q := by
      have e : -(2 * u) / (4 * a) = -(u * q) := by rw [hq]; field_simp; ring
      rw [e, abs_neg, abs_mul, abs_of_nonneg hq0]
      exact mul_le_mul_of_nonneg_right hu hq0
    have hX : |ftQf B u v + u * ftQu B u v| ≤ 4 * Mb * w ^ 2 := by
      have := pb_add hQf (pb_mul hu hQu)
      refine this.trans (le_of_eq ?_)
      ring
    have hH : |-(ftQf B u v + u * ftQu B u v) / (2 * a) + B 0 0 + B 2 2| ≤
        (4 * Mb * q + Mb) * w ^ 4 := by
      have h1 : |-(ftQf B u v + u * ftQu B u v) / (2 * a)| ≤ 4 * Mb * w ^ 2 * q := by
        rw [neg_div, abs_neg, habsdiv]; exact mul_le_mul_of_nonneg_right hX hq0
      have h2 : |-(ftQf B u v + u * ftQu B u v) / (2 * a) + B 0 0 + B 2 2| ≤
          |-(ftQf B u v + u * ftQu B u v) / (2 * a)| + |B 0 0| + |B 2 2| := by
        refine (abs_add_le _ _).trans ?_
        have := abs_add_le (-(ftQf B u v + u * ftQu B u v) / (2 * a)) (B 0 0)
        linarith
      have h3 : 4 * Mb * w ^ 2 * q + |B 0 0| + |B 2 2| ≤ (4 * Mb * q + Mb) * w ^ 4 := by
        have hm : |B 0 0| + |B 2 2| ≤ Mb := by
          rw [hM]; linarith [abs_nonneg (B 0 2), abs_nonneg (B 2 0)]
        have : 0 ≤ 4 * Mb * q := by positivity
        have e1 : 1 ≤ w ^ 4 := one_le_pow₀ hw1
        linarith [mul_le_mul_of_nonneg_left w2 this, mul_le_mul_of_nonneg_left e1 hMb]
      linarith
    unfold ftD2
    have t1 : |ftPh a u v * (-(2 * u) / (4 * a)) *
        (ftKap a B u v * u + (B 0 0 * u + B 0 2 * v) + (-(B 2 0 * v) + B 2 2 * u))| ≤
        ftPh a u v * (q * CG) * w ^ 4 := by
      rw [abs_mul, abs_mul, abs_of_pos hph]
      have := mul_le_mul hc hG2 (abs_nonneg _) (by positivity)
      calc ftPh a u v * |-(2 * u) / (4 * a)| *
            |ftKap a B u v * u + (B 0 0 * u + B 0 2 * v) + (-(B 2 0 * v) + B 2 2 * u)|
          ≤ ftPh a u v * (w * q * (CG * w ^ 3)) := by
            rw [mul_assoc]
            exact mul_le_mul_of_nonneg_left (by simpa [mul_comm] using this) hph.le
        _ = ftPh a u v * (q * CG) * w ^ 4 := by ring
    have t2 : |ftPh a u v * (-(ftQf B u v + u * ftQu B u v) / (2 * a) + B 0 0 + B 2 2)| ≤
        ftPh a u v * ((4 * Mb * q + Mb) * w ^ 4) := by
      rw [abs_mul, abs_of_pos hph]
      exact mul_le_mul_of_nonneg_left hH hph.le
    refine (abs_add_le _ _).trans ?_
    have hqCG : 0 ≤ q * CG := mul_nonneg hq0 hCG0
    have : ftPh a u v * (q * CG) * w ^ 4 + ftPh a u v * ((4 * Mb * q + Mb) * w ^ 4) =
        (q * CG + 4 * Mb * q + Mb) * ftPh a u v * w ^ 4 := by ring
    have hK2 : (q * CG + 4 * Mb * q + Mb) * ftPh a u v * w ^ 4 ≤
        (CG * (1 + q) + 4 * Mb * q + Mb) * ftPh a u v * w ^ 4 := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      apply mul_le_mul_of_nonneg_right _ hph.le
      linarith [hCG0]
    linarith


/-- Locally uniform lattice-summable majorant of `K · ftPh(t - jc, v) · w^m`. -/
theorem lat_bound (a c : ℝ) (ha : 0 < a) (hc : 0 < c) (K : ℝ) (hK : 0 ≤ K) (m : ℕ)
    (t0 V : ℝ) :
    ∃ ub : ℤ → ℝ, Summable ub ∧ ∀ (t v : ℝ) (j : ℤ), |t - t0| < 1 → |v| ≤ V →
      K * ftPh a (t - (j : ℝ) * c) v * (1 + (t - (j : ℝ) * c) ^ 2 + v ^ 2) ^ m ≤ ub j := by
  set α : ℝ := 1 / (4 * a) with hα
  have hα0 : 0 < α := by rw [hα]; positivity
  obtain ⟨K2, hK20, hK2⟩ := gb_poly_exp α hα0 m
  have hS := gb_gauss_summable t0 (α / 4) c (by positivity) hc
  refine ⟨fun j => K * (a ^ 2)⁻¹ * (1 + V ^ 2) ^ m * K2 * Real.exp (α / 2) *
    Real.exp (-(α / 4) * (t0 - (j : ℝ) * c) ^ 2), hS.mul_left _, ?_⟩
  intro t v j ht hv
  set u : ℝ := t - (j : ℝ) * c with hu
  set p : ℝ := t0 - (j : ℝ) * c with hp
  have hd : u = p + (t - t0) := by rw [hu, hp]; ring
  have hd2 : (t - t0) ^ 2 ≤ 1 := by
    have := abs_lt.1 ht
    nlinarith [this.1, this.2]
  have hu2 : p ^ 2 / 2 - 1 ≤ u ^ 2 := by
    rw [hd]; nlinarith [sq_nonneg (p + 2 * (t - t0))]
  have hph : ftPh a u v ≤ (a ^ 2)⁻¹ * Real.exp (-α * u ^ 2) := by
    unfold ftPh
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply Real.exp_le_exp.mpr
    have : -(u ^ 2 + v ^ 2) / (4 * a) = -α * u ^ 2 - α * v ^ 2 := by rw [hα]; field_simp; ring
    rw [this]
    have : 0 ≤ α * v ^ 2 := by positivity
    linarith
  have hv2 : v ^ 2 ≤ V ^ 2 := by
    have h := pow_le_pow_left₀ (abs_nonneg v) hv 2
    simpa [sq_abs] using h
  have hw : (1 + u ^ 2 + v ^ 2) ^ m ≤ (1 + V ^ 2) ^ m * (1 + u ^ 2) ^ m := by
    rw [← mul_pow]
    apply pow_le_pow_left₀ (by positivity)
    nlinarith [sq_nonneg u, sq_nonneg V, mul_nonneg (sq_nonneg V) (sq_nonneg u)]
  have h1 := hK2 u
  have h2 : Real.exp (-(α / 2) * u ^ 2) ≤ Real.exp (α / 2) * Real.exp (-(α / 4) * p ^ 2) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith [mul_le_mul_of_nonneg_left hu2 (show 0 ≤ α / 2 by positivity)]
  have hPE : 0 ≤ (1 + u ^ 2) ^ m * Real.exp (-α * u ^ 2) := by positivity
  calc K * ftPh a u v * (1 + u ^ 2 + v ^ 2) ^ m
      ≤ K * ((a ^ 2)⁻¹ * Real.exp (-α * u ^ 2)) * ((1 + V ^ 2) ^ m * (1 + u ^ 2) ^ m) := by
        apply mul_le_mul (mul_le_mul_of_nonneg_left hph hK) hw (by positivity) (by positivity)
    _ = K * (a ^ 2)⁻¹ * (1 + V ^ 2) ^ m * ((1 + u ^ 2) ^ m * Real.exp (-α * u ^ 2)) := by ring
    _ ≤ K * (a ^ 2)⁻¹ * (1 + V ^ 2) ^ m * (K2 * Real.exp (-(α / 2) * u ^ 2)) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
    _ ≤ K * (a ^ 2)⁻¹ * (1 + V ^ 2) ^ m *
          (K2 * (Real.exp (α / 2) * Real.exp (-(α / 4) * p ^ 2))) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact mul_le_mul_of_nonneg_left h2 hK20
    _ = K * (a ^ 2)⁻¹ * (1 + V ^ 2) ^ m * K2 * Real.exp (α / 2) *
          Real.exp (-(α / 4) * (t0 - (j : ℝ) * c) ^ 2) := by rw [hp]; ring

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
