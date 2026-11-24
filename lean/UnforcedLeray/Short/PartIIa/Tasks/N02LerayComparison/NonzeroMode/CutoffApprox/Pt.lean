import UnforcedLeray.Short.PartIIa.Tasks.N02LerayComparison.NonzeroMode.CutoffApprox.Cut

/-!
# Part II-a, task `PartII-a:N02/4/1` helper: pointwise bounds for the cut-off differences

For `s = √ε ∈ (0, 1]`, `w = χ(s η)` (so `0 ≤ 1 - w ≤ s|η|`), `|∂_η w| = |χ'(sη)| s ≤ B1 s` and
`|η ∂_η w| ≤ B2`, the vector differences `cgradC 0 Φ - cgradC ε (χΦ)` and
`streamC 0 Φ - streamC ε (χΦ)` have norm at most `s K (‖Φ‖ + ‖S Φ‖ + |η| ‖∂_q Φ‖ + |η| ‖∂_η Φ‖)`
with `K = 3 + B1 + B2`. This is the pointwise form of the estimate behind `near:leray-test`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace UnforcedLeray.Short.PartIIa

open UnforcedLeray.B0220 UnforcedLeray.B0223 UnforcedLeray.B0226

lemma nzco_norm_rsmul (r : ℝ) (z : ℂ) : ‖r • z‖ = |r| * ‖z‖ := by
  rw [norm_smul, Real.norm_eq_abs]

/-- `‖(x, y)‖ ≤ ‖x‖ + ‖y‖` in `ℂ²`. -/
lemma nzco_norm_two (x y : ℂ) : ‖!₂[x, y]‖ ≤ ‖x‖ + ‖y‖ := by
  have hsq : ‖!₂[x, y]‖ ^ 2 = ‖x‖ ^ 2 + ‖y‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_two]
    simp
  nlinarith [norm_nonneg (!₂[x, y]), norm_nonneg x, norm_nonneg y,
    mul_nonneg (norm_nonneg x) (norm_nonneg y), add_nonneg (norm_nonneg x) (norm_nonneg y)]

/-- Algebraic core of the gradient estimate. -/
lemma nzco_grad_norm {s η w e B1 B2 ε : ℝ} (A B C' a : ℂ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    (hε : ε = s ^ 2) (hw0 : 0 ≤ w) (hw1 : w ≤ 1) (hw : 1 - w ≤ s * |η|) (he : |e| ≤ B1 * s)
    (hηe : |η * e| ≤ B2) (hB1 : 0 ≤ B1) (hB2 : 0 ≤ B2) :
    ‖!₂[A - (w • A - (ε : ℂ) * ((2:ℝ) • (w • B) + η • (w • C' + e • a))),
        C' - (w • C' + e • a)]‖ ≤
      s * (3 + B1 + B2) * (‖a‖ + ‖B‖ + |η| * ‖A‖ + |η| * ‖C'‖) := by
  have hε0 : 0 ≤ ε := by rw [hε]; positivity
  have hεs : ε ≤ s := by rw [hε]; nlinarith
  have hY : ‖(2:ℝ) • (w • B) + η • (w • C' + e • a)‖ ≤ 2 * ‖B‖ + |η| * ‖C'‖ + B2 * ‖a‖ := by
    have h1 : ‖(2:ℝ) • (w • B)‖ ≤ 2 * ‖B‖ := by
      rw [nzco_norm_rsmul, nzco_norm_rsmul, abs_of_nonneg hw0, abs_of_pos (two_pos : (0:ℝ) < 2)]
      nlinarith [norm_nonneg B, mul_le_of_le_one_left (norm_nonneg B) hw1]
    have h2 : ‖η • (w • C' + e • a)‖ ≤ |η| * ‖C'‖ + B2 * ‖a‖ := by
      rw [nzco_norm_rsmul]
      have h3 : ‖w • C' + e • a‖ ≤ w * ‖C'‖ + |e| * ‖a‖ := by
        refine (norm_add_le _ _).trans ?_
        rw [nzco_norm_rsmul, nzco_norm_rsmul, abs_of_nonneg hw0]
      calc |η| * ‖w • C' + e • a‖ ≤ |η| * (w * ‖C'‖ + |e| * ‖a‖) :=
            mul_le_mul_of_nonneg_left h3 (abs_nonneg _)
        _ = |η| * w * ‖C'‖ + |η * e| * ‖a‖ := by rw [abs_mul]; ring
        _ ≤ |η| * ‖C'‖ + B2 * ‖a‖ := by
            nlinarith [mul_nonneg (mul_nonneg (abs_nonneg η) (norm_nonneg C')) (sub_nonneg.2 hw1),
              mul_le_mul_of_nonneg_right hηe (norm_nonneg a)]
    calc ‖(2:ℝ) • (w • B) + η • (w • C' + e • a)‖
        ≤ ‖(2:ℝ) • (w • B)‖ + ‖η • (w • C' + e • a)‖ := norm_add_le _ _
      _ ≤ 2 * ‖B‖ + (|η| * ‖C'‖ + B2 * ‖a‖) := add_le_add h1 h2
      _ = 2 * ‖B‖ + |η| * ‖C'‖ + B2 * ‖a‖ := by ring
  have e1 : A - (w • A - (ε : ℂ) * ((2:ℝ) • (w • B) + η • (w • C' + e • a))) =
      (1 - w) • A + (ε : ℂ) * ((2:ℝ) • (w • B) + η • (w • C' + e • a)) := by
    rw [sub_smul, one_smul]
    abel
  have hX1 : ‖A - (w • A - (ε : ℂ) * ((2:ℝ) • (w • B) + η • (w • C' + e • a)))‖ ≤
      s * |η| * ‖A‖ + s * (2 * ‖B‖ + |η| * ‖C'‖ + B2 * ‖a‖) := by
    rw [e1]
    refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [nzco_norm_rsmul, abs_of_nonneg (by linarith : (0:ℝ) ≤ 1 - w)]
      exact mul_le_mul_of_nonneg_right hw (norm_nonneg A)
    · rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hε0]
      calc ε * ‖(2:ℝ) • (w • B) + η • (w • C' + e • a)‖ ≤ s * ‖(2:ℝ) • (w • B) + η • (w • C' + e • a)‖ :=
            mul_le_mul_of_nonneg_right hεs (norm_nonneg _)
        _ ≤ s * (2 * ‖B‖ + |η| * ‖C'‖ + B2 * ‖a‖) := mul_le_mul_of_nonneg_left hY hs0
        _ = s * (2 * ‖B‖ + |η| * ‖C'‖ + B2 * ‖a‖) := rfl
  have e2 : C' - (w • C' + e • a) = (1 - w) • C' - e • a := by
    rw [sub_smul, one_smul]
    abel
  have hX2 : ‖C' - (w • C' + e • a)‖ ≤ s * |η| * ‖C'‖ + B1 * s * ‖a‖ := by
    rw [e2]
    refine (norm_sub_le _ _).trans (add_le_add ?_ ?_)
    · rw [nzco_norm_rsmul, abs_of_nonneg (by linarith : (0:ℝ) ≤ 1 - w)]
      exact mul_le_mul_of_nonneg_right hw (norm_nonneg C')
    · rw [nzco_norm_rsmul]
      exact mul_le_mul_of_nonneg_right he (norm_nonneg a)
  refine (nzco_norm_two _ _).trans ?_
  nlinarith [mul_nonneg hs0 (norm_nonneg a), mul_nonneg hs0 (norm_nonneg B),
    mul_nonneg (mul_nonneg hs0 (abs_nonneg η)) (norm_nonneg A),
    mul_nonneg (mul_nonneg hs0 (abs_nonneg η)) (norm_nonneg C'),
    mul_nonneg (mul_nonneg hs0 hB1) (norm_nonneg B),
    mul_nonneg (mul_nonneg (mul_nonneg hs0 hB1) (abs_nonneg η)) (norm_nonneg A),
    mul_nonneg (mul_nonneg (mul_nonneg hs0 hB1) (abs_nonneg η)) (norm_nonneg C'),
    mul_nonneg (mul_nonneg hs0 hB2) (norm_nonneg B),
    mul_nonneg (mul_nonneg (mul_nonneg hs0 hB2) (abs_nonneg η)) (norm_nonneg A),
    mul_nonneg (mul_nonneg (mul_nonneg hs0 hB2) (abs_nonneg η)) (norm_nonneg C'), hX1, hX2]

/-- Algebraic core of the stream estimate. -/
lemma nzco_stream_norm {s η w e B1 B2 ε : ℝ} (A B C' a : ℂ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    (hε : ε = s ^ 2) (hw0 : 0 ≤ w) (hw1 : w ≤ 1) (hw : 1 - w ≤ s * |η|) (he : |e| ≤ B1 * s)
    (hηe : |η * e| ≤ B2) (hB1 : 0 ≤ B1) (hB2 : 0 ≤ B2) :
    ‖!₂[-C' - -(w • C' + e • a),
        A - (w • A - (ε : ℂ) * ((2:ℝ) • (w • B) + η • (w • C' + e • a)) + (ε : ℂ) * (w • a))]‖ ≤
      s * (3 + B1 + B2) * (‖a‖ + ‖B‖ + |η| * ‖A‖ + |η| * ‖C'‖) := by
  have hε0 : 0 ≤ ε := by rw [hε]; positivity
  have hεs : ε ≤ s := by rw [hε]; nlinarith
  have hY : ‖(2:ℝ) • (w • B) + η • (w • C' + e • a)‖ ≤ 2 * ‖B‖ + |η| * ‖C'‖ + B2 * ‖a‖ := by
    have h1 : ‖(2:ℝ) • (w • B)‖ ≤ 2 * ‖B‖ := by
      rw [nzco_norm_rsmul, nzco_norm_rsmul, abs_of_nonneg hw0, abs_of_pos (two_pos : (0:ℝ) < 2)]
      nlinarith [norm_nonneg B, mul_le_of_le_one_left (norm_nonneg B) hw1]
    have h2 : ‖η • (w • C' + e • a)‖ ≤ |η| * ‖C'‖ + B2 * ‖a‖ := by
      rw [nzco_norm_rsmul]
      have h3 : ‖w • C' + e • a‖ ≤ w * ‖C'‖ + |e| * ‖a‖ := by
        refine (norm_add_le _ _).trans ?_
        rw [nzco_norm_rsmul, nzco_norm_rsmul, abs_of_nonneg hw0]
      calc |η| * ‖w • C' + e • a‖ ≤ |η| * (w * ‖C'‖ + |e| * ‖a‖) :=
            mul_le_mul_of_nonneg_left h3 (abs_nonneg _)
        _ = |η| * w * ‖C'‖ + |η * e| * ‖a‖ := by rw [abs_mul]; ring
        _ ≤ |η| * ‖C'‖ + B2 * ‖a‖ := by
            nlinarith [mul_nonneg (mul_nonneg (abs_nonneg η) (norm_nonneg C')) (sub_nonneg.2 hw1),
              mul_le_mul_of_nonneg_right hηe (norm_nonneg a)]
    calc ‖(2:ℝ) • (w • B) + η • (w • C' + e • a)‖
        ≤ ‖(2:ℝ) • (w • B)‖ + ‖η • (w • C' + e • a)‖ := norm_add_le _ _
      _ ≤ 2 * ‖B‖ + (|η| * ‖C'‖ + B2 * ‖a‖) := add_le_add h1 h2
      _ = 2 * ‖B‖ + |η| * ‖C'‖ + B2 * ‖a‖ := by ring
  have hV : ‖(ε : ℂ) * (w • a)‖ ≤ s * ‖a‖ := by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hε0, nzco_norm_rsmul,
      abs_of_nonneg hw0]
    calc ε * (w * ‖a‖) ≤ ε * ‖a‖ := mul_le_mul_of_nonneg_left (mul_le_of_le_one_left (norm_nonneg a) hw1) hε0
      _ ≤ s * ‖a‖ := mul_le_mul_of_nonneg_right hεs (norm_nonneg a)
  have e3 : -C' - -(w • C' + e • a) = -((1 - w) • C') + e • a := by
    rw [sub_smul, one_smul]
    abel
  have hX1 : ‖-C' - -(w • C' + e • a)‖ ≤ s * |η| * ‖C'‖ + B1 * s * ‖a‖ := by
    rw [e3]
    refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [norm_neg, nzco_norm_rsmul, abs_of_nonneg (by linarith : (0:ℝ) ≤ 1 - w)]
      exact mul_le_mul_of_nonneg_right hw (norm_nonneg C')
    · rw [nzco_norm_rsmul]
      exact mul_le_mul_of_nonneg_right he (norm_nonneg a)
  have e4 : A - (w • A - (ε : ℂ) * ((2:ℝ) • (w • B) + η • (w • C' + e • a)) + (ε : ℂ) * (w • a)) =
      (1 - w) • A + (ε : ℂ) * ((2:ℝ) • (w • B) + η • (w • C' + e • a)) - (ε : ℂ) * (w • a) := by
    rw [sub_smul, one_smul]
    abel
  have hX2 : ‖A - (w • A - (ε : ℂ) * ((2:ℝ) • (w • B) + η • (w • C' + e • a)) +
      (ε : ℂ) * (w • a))‖ ≤ s * |η| * ‖A‖ + s * (2 * ‖B‖ + |η| * ‖C'‖ + B2 * ‖a‖) + s * ‖a‖ := by
    rw [e4]
    refine (norm_sub_le _ _).trans (add_le_add ?_ hV)
    refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [nzco_norm_rsmul, abs_of_nonneg (by linarith : (0:ℝ) ≤ 1 - w)]
      exact mul_le_mul_of_nonneg_right hw (norm_nonneg A)
    · rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hε0]
      calc ε * ‖(2:ℝ) • (w • B) + η • (w • C' + e • a)‖ ≤ s * ‖(2:ℝ) • (w • B) + η • (w • C' + e • a)‖ :=
            mul_le_mul_of_nonneg_right hεs (norm_nonneg _)
        _ ≤ s * (2 * ‖B‖ + |η| * ‖C'‖ + B2 * ‖a‖) := mul_le_mul_of_nonneg_left hY hs0
  refine (nzco_norm_two _ _).trans ?_
  nlinarith [mul_nonneg hs0 (norm_nonneg a), mul_nonneg hs0 (norm_nonneg B),
    mul_nonneg (mul_nonneg hs0 (abs_nonneg η)) (norm_nonneg A),
    mul_nonneg (mul_nonneg hs0 (abs_nonneg η)) (norm_nonneg C'),
    mul_nonneg (mul_nonneg hs0 hB1) (norm_nonneg B),
    mul_nonneg (mul_nonneg (mul_nonneg hs0 hB1) (abs_nonneg η)) (norm_nonneg A),
    mul_nonneg (mul_nonneg (mul_nonneg hs0 hB1) (abs_nonneg η)) (norm_nonneg C'),
    mul_nonneg (mul_nonneg hs0 hB2) (norm_nonneg B),
    mul_nonneg (mul_nonneg (mul_nonneg hs0 hB2) (abs_nonneg η)) (norm_nonneg A),
    mul_nonneg (mul_nonneg (mul_nonneg hs0 hB2) (abs_nonneg η)) (norm_nonneg C'), hX1, hX2]

/-- The gradient estimate pointwise: `‖cgradC 0 Φ - cgradC ε (χ_L Φ)‖ ≤ √ε K (...)`. -/
lemma nzco_grad_pt (ε : ℝ) {Φ : Profile → ℂ} (hΦ : ContDiff ℝ ∞ Φ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    {B1 B2 : ℝ} (hB1 : 0 ≤ B1) (hB2 : 0 ≤ B2)
    (hBd : ∀ t : ℝ, |deriv nzcoChi t| ≤ B1 ∧ |t * deriv nzcoChi t| ≤ B2) (p : Profile) :
    ‖cgradC 0 Φ p - cgradC ε (nzcoCut ε Φ) p‖ ≤
      Real.sqrt ε * (3 + B1 + B2) * (‖Φ p‖ + ‖opS Φ p‖ + |p.2.2| * ‖pdQ Φ p‖ + |p.2.2| * ‖pdEta Φ p‖) := by
  rw [nzco_cgrad_diff ε hΦ p]
  have hs0 : 0 < Real.sqrt ε := Real.sqrt_pos.2 hε
  have hs1 : Real.sqrt ε ≤ 1 := by
    calc Real.sqrt ε ≤ Real.sqrt 1 := Real.sqrt_le_sqrt hε1
      _ = 1 := Real.sqrt_one
  have hε' : ε = (Real.sqrt ε) ^ 2 := (Real.sq_sqrt hε.le).symm
  have hw : 1 - nzcoW ε p ≤ Real.sqrt ε * |p.2.2| := by
    have h := nzcoChi_one_sub_le (Real.sqrt ε * p.2.2)
    rw [abs_mul, abs_of_nonneg hs0.le] at h
    exact h
  have he : |deriv nzcoChi (Real.sqrt ε * p.2.2) * Real.sqrt ε| ≤ B1 * Real.sqrt ε := by
    rw [abs_mul, abs_of_nonneg hs0.le]
    exact mul_le_mul_of_nonneg_right (hBd _).1 hs0.le
  have hηe : |p.2.2 * (deriv nzcoChi (Real.sqrt ε * p.2.2) * Real.sqrt ε)| ≤ B2 := by
    have h : p.2.2 * (deriv nzcoChi (Real.sqrt ε * p.2.2) * Real.sqrt ε) =
        (Real.sqrt ε * p.2.2) * deriv nzcoChi (Real.sqrt ε * p.2.2) := by ring
    rw [h]
    exact (hBd _).2
  exact nzco_grad_norm (s := Real.sqrt ε) (η := p.2.2) (w := nzcoW ε p)
    (e := deriv nzcoChi (Real.sqrt ε * p.2.2) * Real.sqrt ε) (B1 := B1) (B2 := B2) (ε := ε)
    (pdQ Φ p) (opS Φ p) (pdEta Φ p) (Φ p) hs0.le hs1 hε' (nzcoChi_nonneg _) (nzcoChi_le_one _)
    hw he hηe hB1 hB2

/-- The stream estimate pointwise: `‖streamC 0 Φ - streamC ε (χ_L Φ)‖ ≤ √ε K (...)`. -/
lemma nzco_stream_pt (ε : ℝ) {Φ : Profile → ℂ} (hΦ : ContDiff ℝ ∞ Φ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    {B1 B2 : ℝ} (hB1 : 0 ≤ B1) (hB2 : 0 ≤ B2)
    (hBd : ∀ t : ℝ, |deriv nzcoChi t| ≤ B1 ∧ |t * deriv nzcoChi t| ≤ B2) (p : Profile) :
    ‖streamC 0 Φ p - streamC ε (nzcoCut ε Φ) p‖ ≤
      Real.sqrt ε * (3 + B1 + B2) * (‖Φ p‖ + ‖opS Φ p‖ + |p.2.2| * ‖pdQ Φ p‖ + |p.2.2| * ‖pdEta Φ p‖) := by
  rw [nzco_stream_diff ε hΦ p]
  have hs0 : 0 < Real.sqrt ε := Real.sqrt_pos.2 hε
  have hs1 : Real.sqrt ε ≤ 1 := by
    calc Real.sqrt ε ≤ Real.sqrt 1 := Real.sqrt_le_sqrt hε1
      _ = 1 := Real.sqrt_one
  have hε' : ε = (Real.sqrt ε) ^ 2 := (Real.sq_sqrt hε.le).symm
  have hw : 1 - nzcoW ε p ≤ Real.sqrt ε * |p.2.2| := by
    have h := nzcoChi_one_sub_le (Real.sqrt ε * p.2.2)
    rw [abs_mul, abs_of_nonneg hs0.le] at h
    exact h
  have he : |deriv nzcoChi (Real.sqrt ε * p.2.2) * Real.sqrt ε| ≤ B1 * Real.sqrt ε := by
    rw [abs_mul, abs_of_nonneg hs0.le]
    exact mul_le_mul_of_nonneg_right (hBd _).1 hs0.le
  have hηe : |p.2.2 * (deriv nzcoChi (Real.sqrt ε * p.2.2) * Real.sqrt ε)| ≤ B2 := by
    have h : p.2.2 * (deriv nzcoChi (Real.sqrt ε * p.2.2) * Real.sqrt ε) =
        (Real.sqrt ε * p.2.2) * deriv nzcoChi (Real.sqrt ε * p.2.2) := by ring
    rw [h]
    exact (hBd _).2
  exact nzco_stream_norm (s := Real.sqrt ε) (η := p.2.2) (w := nzcoW ε p)
    (e := deriv nzcoChi (Real.sqrt ε * p.2.2) * Real.sqrt ε) (B1 := B1) (B2 := B2) (ε := ε)
    (pdQ Φ p) (opS Φ p) (pdEta Φ p) (Φ p) hs0.le hs1 hε' (nzcoChi_nonneg _) (nzcoChi_le_one _)
    hw he hηe hB1 hB2

end UnforcedLeray.Short.PartIIa
