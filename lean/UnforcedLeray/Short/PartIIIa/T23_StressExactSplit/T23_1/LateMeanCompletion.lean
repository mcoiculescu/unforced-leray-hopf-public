import UnforcedLeray.Short.PartIIIa.Sub.T23_1_org

/-!
# `PartIII-a:T23/1/4`: the late mean stream completion (`lateMeanCompletion_of`)

Source of record: `the November 2 reference manuscript` lines 2719-2723 (mean
stream and its weighted derivatives of size `(1+s)^{-1/2}` on transverse scale `√(1+s)`) and
447-459 (`sct:expansion`).

Route: `meanCompletion = S - (η S_η + 2 s S_s)`, so `|meanCompletion| ≤ |S| + |η||S_η| + 2s|S_s|`.
The six pointwise Part II bounds (`MeanStreamPointwise`) at
`(m', b', l') ∈ {(0,0,0), (2n,0,0), (1,1,0), (2n+1,1,0), (0,0,1), (2n,0,1)}` with `n = ⌈m_Z/2⌉₊`
give the six bounds of `lmcc_core`; the transverse weight is
`W ≤ 2^n (1 + η^{2n}/(1+s)^n)` (`transWeight_le_two_pow`). The constants are absorbed at
`ν ≤ 1` by `lmc_poly`.
-/

open Set MeasureTheory Filter Topology
open scoped ENNReal

namespace UnforcedLeray.Short.IIIa

open UnforcedLeray.Cons.C03.Concrete UnforcedLeray.Short.IIb

/-- Algebraic core: the six pointwise bounds give the completion bound on the weight
`(1 + η^{2n}/A^n)` with `A = 1 + s`. -/
theorem lmcc_core {A : ℝ} (hA : 0 < A) (n : ℕ) {s S Sη Ss η p0 p1 p2 p3 p4 p5 : ℝ}
    (hs : 0 ≤ s) (hsA : s ≤ A)
    (h0 : |S| ≤ p0 * A ^ (-1 / 2 : ℝ))
    (h1 : η ^ (2 * n) * |S| ≤ p1 * A ^ ((n : ℝ) + (-1 / 2 : ℝ)))
    (h2 : |η| * |Sη| ≤ p2 * A ^ (-1 / 2 : ℝ))
    (h3 : η ^ (2 * n) * (|η| * |Sη|) ≤ p3 * A ^ ((n : ℝ) + (-1 / 2 : ℝ)))
    (h4 : |Ss| ≤ p4 * A ^ (-3 / 2 : ℝ))
    (h5 : η ^ (2 * n) * |Ss| ≤ p5 * A ^ ((n : ℝ) + (-3 / 2 : ℝ))) :
    (1 + η ^ (2 * n) / A ^ n) * (|S| + |η| * |Sη| + 2 * s * |Ss|) ≤
      (p0 + p1 + p2 + p3 + 2 * p4 + 2 * p5) * A ^ (-1 / 2 : ℝ) := by
  have hAn : 0 < A ^ n := pow_pos hA n
  have hsplit : ∀ a : ℝ, A ^ ((n : ℝ) + a) = A ^ n * A ^ a := fun a => by
    rw [Real.rpow_add hA, Real.rpow_natCast]
  have hAu : A * A ^ (-3 / 2 : ℝ) = A ^ (-1 / 2 : ℝ) := by
    have e : A ^ (-1 / 2 : ℝ) = A ^ (1 : ℝ) * A ^ (-3 / 2 : ℝ) := by
      rw [← Real.rpow_add hA]; norm_num
    rw [Real.rpow_one] at e
    exact e.symm
  rw [hsplit] at h1
  rw [hsplit] at h3
  rw [hsplit] at h5
  have hT1 : 2 * s * |Ss| ≤ 2 * p4 * A ^ (-1 / 2 : ℝ) := by
    calc 2 * s * |Ss| ≤ 2 * A * |Ss| :=
          mul_le_mul_of_nonneg_right (by linarith) (abs_nonneg _)
      _ ≤ 2 * A * (p4 * A ^ (-3 / 2 : ℝ)) := mul_le_mul_of_nonneg_left h4 (by linarith)
      _ = 2 * p4 * (A * A ^ (-3 / 2 : ℝ)) := by ring
      _ = 2 * p4 * A ^ (-1 / 2 : ℝ) := by rw [hAu]
  have hT2 : η ^ (2 * n) * (2 * s * |Ss|) ≤ 2 * p5 * (A ^ n * A ^ (-1 / 2 : ℝ)) := by
    have hE : 0 ≤ η ^ (2 * n) := Even.pow_nonneg (even_two_mul n) η
    calc η ^ (2 * n) * (2 * s * |Ss|) = 2 * s * (η ^ (2 * n) * |Ss|) := by ring
      _ ≤ 2 * A * (η ^ (2 * n) * |Ss|) :=
          mul_le_mul_of_nonneg_right (by linarith) (mul_nonneg hE (abs_nonneg _))
      _ ≤ 2 * A * (p5 * (A ^ n * A ^ (-3 / 2 : ℝ))) :=
          mul_le_mul_of_nonneg_left h5 (by linarith)
      _ = 2 * p5 * (A ^ n * (A * A ^ (-3 / 2 : ℝ))) := by ring
      _ = 2 * p5 * (A ^ n * A ^ (-1 / 2 : ℝ)) := by rw [hAu]
  have hbound : (η ^ (2 * n) * |S| + η ^ (2 * n) * (|η| * |Sη|) +
      η ^ (2 * n) * (2 * s * |Ss|)) / A ^ n ≤ (p1 + p3 + 2 * p5) * A ^ (-1 / 2 : ℝ) := by
    rw [div_le_iff₀ hAn]
    calc _ ≤ p1 * (A ^ n * A ^ (-1 / 2 : ℝ)) + p3 * (A ^ n * A ^ (-1 / 2 : ℝ)) +
          2 * p5 * (A ^ n * A ^ (-1 / 2 : ℝ)) := add_le_add (add_le_add h1 h3) hT2
      _ = (p1 + p3 + 2 * p5) * A ^ (-1 / 2 : ℝ) * A ^ n := by ring
  have hTT : |S| + |η| * |Sη| + 2 * s * |Ss| ≤ (p0 + p2 + 2 * p4) * A ^ (-1 / 2 : ℝ) := by
    calc _ ≤ p0 * A ^ (-1 / 2 : ℝ) + p2 * A ^ (-1 / 2 : ℝ) + 2 * p4 * A ^ (-1 / 2 : ℝ) :=
          add_le_add (add_le_add h0 h2) hT1
      _ = (p0 + p2 + 2 * p4) * A ^ (-1 / 2 : ℝ) := by ring
  have hdecomp : (1 + η ^ (2 * n) / A ^ n) * (|S| + |η| * |Sη| + 2 * s * |Ss|) =
      (|S| + |η| * |Sη| + 2 * s * |Ss|) +
        (η ^ (2 * n) * |S| + η ^ (2 * n) * (|η| * |Sη|) + η ^ (2 * n) * (2 * s * |Ss|)) / A ^ n := by
    ring
  rw [hdecomp]
  calc _ ≤ (p0 + p2 + 2 * p4) * A ^ (-1 / 2 : ℝ) + (p1 + p3 + 2 * p5) * A ^ (-1 / 2 : ℝ) :=
        add_le_add hTT hbound
    _ = (p0 + p1 + p2 + p3 + 2 * p4 + 2 * p5) * A ^ (-1 / 2 : ℝ) := by ring

/-- The Part I polynomial bound at `c = ν^{-2}`, `0 < ν ≤ 1`, with a common exponent `k ≥ 2M`. -/
theorem lmc_poly {C : ℝ} {M k : ℕ} {ν : ℝ} (hν0 : 0 < ν) (hν1 : ν ≤ 1) (hk : 2 * M ≤ k) :
    UnforcedLeray.Short.PartIIa.polyConst C M ν (ν ^ (-(2 : ℝ))) ≤ |C| * 3 ^ M * ν⁻¹ ^ k := by
  have e : ν ^ (-(2 : ℝ)) = (ν ^ 2)⁻¹ := by
    rw [Real.rpow_neg hν0.le, Real.rpow_two]
  unfold UnforcedLeray.Short.PartIIa.polyConst
  rw [e]
  refine le_trans (polyP_le_inv_pow C M hν0 hν1) ?_
  exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ ((one_le_inv₀ hν0).mpr hν1) hk)
    (by positivity)

/-- **Stream completion of the mean stream at late ages** (`PartIII-a:T23/1/4`, SP 2721-2723 and
447-459): from the pointwise Part II bound for the mean stream, `W |(1 - η∂_η - 2s∂_s)S| ≤
C ν^{-k} (1+s)^{-1/2}` for `s ≥ 1`. -/
theorem lateMeanCompletion_of (hP : UnforcedLeray.Short.PartIIa.MeanStreamPointwise) :
    UnforcedLeray.Short.IIIa.LateMeanCompletion := by
  intro mZ hmZ
  set n : ℕ := ⌈mZ / 2⌉₊ with hn
  obtain ⟨C0, M0, ν0, hC0, hν0, H0⟩ := hP 2 0 0 0 (by norm_num)
  obtain ⟨C1, M1, ν1, hC1, hν1, H1⟩ := hP 2 (2 * n) 0 0 (by norm_num)
  obtain ⟨C2, M2, ν2, hC2, hν2, H2⟩ := hP 2 1 1 0 (by norm_num)
  obtain ⟨C3, M3, ν3, hC3, hν3, H3⟩ := hP 2 (2 * n + 1) 1 0 (by norm_num)
  obtain ⟨C4, M4, ν4, hC4, hν4, H4⟩ := hP 2 0 0 1 (by norm_num)
  obtain ⟨C5, M5, ν5, hC5, hν5, H5⟩ := hP 2 (2 * n) 0 1 (by norm_num)
  obtain ⟨νm, hνm0, ha0, ha1, ha2, ha3, ha4, ha5, ha6⟩ : ∃ νm : ℝ, 0 < νm ∧ νm ≤ ν0 ∧
      νm ≤ ν1 ∧ νm ≤ ν2 ∧ νm ≤ ν3 ∧ νm ≤ ν4 ∧ νm ≤ ν5 ∧ νm ≤ 1 :=
    ⟨min ν0 (min ν1 (min ν2 (min ν3 (min ν4 (min ν5 1))))),
      lt_min hν0 (lt_min hν1 (lt_min hν2 (lt_min hν3 (lt_min hν4 (lt_min hν5 one_pos))))),
      by simp [min_le_iff], by simp [min_le_iff], by simp [min_le_iff], by simp [min_le_iff],
      by simp [min_le_iff], by simp [min_le_iff], by simp [min_le_iff]⟩
  refine ⟨2 ^ n * (|C0| * 3 ^ M0 + |C1| * 3 ^ M1 + |C2| * 3 ^ M2 + |C3| * 3 ^ M3 +
      2 * (|C4| * 3 ^ M4) + 2 * (|C5| * 3 ^ M5)), 2 * (M0 + M1 + M2 + M3 + M4 + M5), νm,
    hνm0, ?_⟩
  intro ν hν c hc tr hbuc s hs q η
  have hν0' : 0 < ν := hν.1
  have hνle : ν ≤ νm := hν.2
  have hνa0 : ν ≤ ν0 := hνle.trans ha0
  have hνa1 : ν ≤ ν1 := hνle.trans ha1
  have hνa2 : ν ≤ ν2 := hνle.trans ha2
  have hνa3 : ν ≤ ν3 := hνle.trans ha3
  have hνa4 : ν ≤ ν4 := hνle.trans ha4
  have hνa5 : ν ≤ ν5 := hνle.trans ha5
  have hν1' : ν ≤ 1 := hνle.trans ha6
  have hcT := period_eq_trainPeriod hν0' hc
  subst hcT
  have hs0 : 0 < s := by linarith
  have hs' : 0 ≤ s := by linarith
  -- polynomial constants at `c = ν^{-2}`, absorbed into `ν^{-K}`
  have hp0 : UnforcedLeray.Short.PartIIa.polyConst C0 M0 ν (ν ^ (-(2 : ℝ))) ≤
      |C0| * 3 ^ M0 * ν⁻¹ ^ (2 * (M0 + M1 + M2 + M3 + M4 + M5)) :=
    lmc_poly hν0' hν1' (by omega)
  have hp1 : UnforcedLeray.Short.PartIIa.polyConst C1 M1 ν (ν ^ (-(2 : ℝ))) ≤
      |C1| * 3 ^ M1 * ν⁻¹ ^ (2 * (M0 + M1 + M2 + M3 + M4 + M5)) :=
    lmc_poly hν0' hν1' (by omega)
  have hp2 : UnforcedLeray.Short.PartIIa.polyConst C2 M2 ν (ν ^ (-(2 : ℝ))) ≤
      |C2| * 3 ^ M2 * ν⁻¹ ^ (2 * (M0 + M1 + M2 + M3 + M4 + M5)) :=
    lmc_poly hν0' hν1' (by omega)
  have hp3 : UnforcedLeray.Short.PartIIa.polyConst C3 M3 ν (ν ^ (-(2 : ℝ))) ≤
      |C3| * 3 ^ M3 * ν⁻¹ ^ (2 * (M0 + M1 + M2 + M3 + M4 + M5)) :=
    lmc_poly hν0' hν1' (by omega)
  have hp4 : UnforcedLeray.Short.PartIIa.polyConst C4 M4 ν (ν ^ (-(2 : ℝ))) ≤
      |C4| * 3 ^ M4 * ν⁻¹ ^ (2 * (M0 + M1 + M2 + M3 + M4 + M5)) :=
    lmc_poly hν0' hν1' (by omega)
  have hp5 : UnforcedLeray.Short.PartIIa.polyConst C5 M5 ν (ν ^ (-(2 : ℝ))) ≤
      |C5| * 3 ^ M5 * ν⁻¹ ^ (2 * (M0 + M1 + M2 + M3 + M4 + M5)) :=
    lmc_poly hν0' hν1' (by omega)
  -- the six pointwise bounds, at the fixed age `s` and the point `η`
  have hA0 : |UnforcedLeray.Short.PartI.meanStream tr s η| ≤
      UnforcedLeray.Short.PartIIa.polyConst C0 M0 ν (ν ^ (-(2 : ℝ))) * (1 + s) ^ (-1 / 2 : ℝ) := by
    have h := H0 ν hν0' hνa0 tr hbuc s hs0 η
    simp only [pow_zero, one_mul, iteratedDeriv_zero] at h
    have ex : (((0 : ℕ) : ℝ) - ((0 : ℕ) : ℝ) - 1) / 2 - ((0 : ℕ) : ℝ) = -1 / 2 := by norm_num
    rw [ex] at h
    exact h
  have hA1 : η ^ (2 * n) * |UnforcedLeray.Short.PartI.meanStream tr s η| ≤
      UnforcedLeray.Short.PartIIa.polyConst C1 M1 ν (ν ^ (-(2 : ℝ))) *
        (1 + s) ^ ((n : ℝ) + (-1 / 2 : ℝ)) := by
    have h := H1 ν hν0' hνa1 tr hbuc s hs0 η
    simp only [iteratedDeriv_zero] at h
    have ex : (((2 * n : ℕ) : ℝ) - ((0 : ℕ) : ℝ) - 1) / 2 - ((0 : ℕ) : ℝ) =
        (n : ℝ) + (-1 / 2 : ℝ) := by
      push_cast; ring
    rw [ex] at h
    calc η ^ (2 * n) * |UnforcedLeray.Short.PartI.meanStream tr s η|
        = |η| ^ (2 * n) * |UnforcedLeray.Short.PartI.meanStream tr s η| := by
          rw [Even.pow_abs (even_two_mul n) η]
      _ ≤ _ := h
  have hA2 : |η| * |deriv (fun e => UnforcedLeray.Short.PartI.meanStream tr s e) η| ≤
      UnforcedLeray.Short.PartIIa.polyConst C2 M2 ν (ν ^ (-(2 : ℝ))) * (1 + s) ^ (-1 / 2 : ℝ) := by
    have h := H2 ν hν0' hνa2 tr hbuc s hs0 η
    simp only [pow_one, iteratedDeriv_zero, iteratedDeriv_one] at h
    have ex : (((1 : ℕ) : ℝ) - ((1 : ℕ) : ℝ) - 1) / 2 - ((0 : ℕ) : ℝ) = -1 / 2 := by norm_num
    rw [ex] at h
    exact h
  have hA3 : η ^ (2 * n) * (|η| * |deriv (fun e => UnforcedLeray.Short.PartI.meanStream tr s e) η|) ≤
      UnforcedLeray.Short.PartIIa.polyConst C3 M3 ν (ν ^ (-(2 : ℝ))) *
        (1 + s) ^ ((n : ℝ) + (-1 / 2 : ℝ)) := by
    have h := H3 ν hν0' hνa3 tr hbuc s hs0 η
    simp only [iteratedDeriv_zero, iteratedDeriv_one] at h
    have ex : (((2 * n + 1 : ℕ) : ℝ) - ((1 : ℕ) : ℝ) - 1) / 2 - ((0 : ℕ) : ℝ) =
        (n : ℝ) + (-1 / 2 : ℝ) := by
      push_cast; ring
    rw [ex] at h
    have hw : |η| ^ (2 * n + 1) = η ^ (2 * n) * |η| := by
      rw [pow_succ, Even.pow_abs (even_two_mul n) η]
    calc η ^ (2 * n) * (|η| * |deriv (fun e => UnforcedLeray.Short.PartI.meanStream tr s e) η|)
        = |η| ^ (2 * n + 1) * |deriv (fun e => UnforcedLeray.Short.PartI.meanStream tr s e) η| := by
          rw [hw]; ring
      _ ≤ _ := h
  have hA4 : |deriv (fun r => UnforcedLeray.Short.PartI.meanStream tr r η) s| ≤
      UnforcedLeray.Short.PartIIa.polyConst C4 M4 ν (ν ^ (-(2 : ℝ))) * (1 + s) ^ (-3 / 2 : ℝ) := by
    have h := H4 ν hν0' hνa4 tr hbuc s hs0 η
    simp only [pow_zero, one_mul, iteratedDeriv_zero, iteratedDeriv_one] at h
    have ex : (((0 : ℕ) : ℝ) - ((0 : ℕ) : ℝ) - 1) / 2 - ((1 : ℕ) : ℝ) = -3 / 2 := by norm_num
    rw [ex] at h
    exact h
  have hA5 : η ^ (2 * n) * |deriv (fun r => UnforcedLeray.Short.PartI.meanStream tr r η) s| ≤
      UnforcedLeray.Short.PartIIa.polyConst C5 M5 ν (ν ^ (-(2 : ℝ))) *
        (1 + s) ^ ((n : ℝ) + (-3 / 2 : ℝ)) := by
    have h := H5 ν hν0' hνa5 tr hbuc s hs0 η
    simp only [iteratedDeriv_zero, iteratedDeriv_one] at h
    have ex : (((2 * n : ℕ) : ℝ) - ((0 : ℕ) : ℝ) - 1) / 2 - ((1 : ℕ) : ℝ) =
        (n : ℝ) + (-3 / 2 : ℝ) := by
      push_cast; ring
    rw [ex] at h
    calc η ^ (2 * n) * |deriv (fun r => UnforcedLeray.Short.PartI.meanStream tr r η) s|
        = |η| ^ (2 * n) * |deriv (fun r => UnforcedLeray.Short.PartI.meanStream tr r η) s| := by
          rw [Even.pow_abs (even_two_mul n) η]
      _ ≤ _ := h
  -- the core algebra
  have hcore := lmcc_core (A := 1 + s) (by linarith) n hs' (by linarith) hA0 hA1 hA2 hA3 hA4 hA5
  -- `|meanCompletion| ≤ |S| + |η||S_η| + 2s|S_s|`
  have hmc : |UnforcedLeray.Short.IIIa.meanCompletion tr s η| ≤
      |UnforcedLeray.Short.PartI.meanStream tr s η| +
        |η| * |deriv (fun e => UnforcedLeray.Short.PartI.meanStream tr s e) η| +
        2 * s * |deriv (fun r => UnforcedLeray.Short.PartI.meanStream tr r η) s| := by
    unfold UnforcedLeray.Short.IIIa.meanCompletion
    calc _ ≤ |UnforcedLeray.Short.PartI.meanStream tr s η| +
          |η * deriv (fun e => UnforcedLeray.Short.PartI.meanStream tr s e) η +
            2 * s * deriv (fun r => UnforcedLeray.Short.PartI.meanStream tr r η) s| :=
          abs_sub _ _
      _ ≤ |UnforcedLeray.Short.PartI.meanStream tr s η| +
          (|η * deriv (fun e => UnforcedLeray.Short.PartI.meanStream tr s e) η| +
            |2 * s * deriv (fun r => UnforcedLeray.Short.PartI.meanStream tr r η) s|) :=
          add_le_add (le_refl _) (abs_add_le _ _)
      _ = _ := by
          rw [abs_mul, abs_mul, abs_of_nonneg (show (0 : ℝ) ≤ 2 * s by linarith)]
          ring
  have hW := transWeight_le_two_pow mZ (s := s) hs' q η
  have hEn : 0 ≤ η ^ (2 * n) := Even.pow_nonneg (even_two_mul n) η
  have hAn : 0 < (1 + s) ^ n := pow_pos (by linarith) n
  have hnonnegb : 0 ≤ 2 ^ n * (1 + η ^ (2 * n) / (1 + s) ^ n) :=
    mul_nonneg (by positivity) (by have := div_nonneg hEn hAn.le; linarith)
  have hB0 : 0 ≤ (1 + s) ^ (-1 / 2 : ℝ) := Real.rpow_nonneg (by linarith) _
  have hK1 : UnforcedLeray.Short.PartIIa.polyConst C0 M0 ν (ν ^ (-(2 : ℝ))) +
      UnforcedLeray.Short.PartIIa.polyConst C1 M1 ν (ν ^ (-(2 : ℝ))) +
      UnforcedLeray.Short.PartIIa.polyConst C2 M2 ν (ν ^ (-(2 : ℝ))) +
      UnforcedLeray.Short.PartIIa.polyConst C3 M3 ν (ν ^ (-(2 : ℝ))) +
      2 * UnforcedLeray.Short.PartIIa.polyConst C4 M4 ν (ν ^ (-(2 : ℝ))) +
      2 * UnforcedLeray.Short.PartIIa.polyConst C5 M5 ν (ν ^ (-(2 : ℝ))) ≤
      |C0| * 3 ^ M0 * ν⁻¹ ^ (2 * (M0 + M1 + M2 + M3 + M4 + M5)) +
      |C1| * 3 ^ M1 * ν⁻¹ ^ (2 * (M0 + M1 + M2 + M3 + M4 + M5)) +
      |C2| * 3 ^ M2 * ν⁻¹ ^ (2 * (M0 + M1 + M2 + M3 + M4 + M5)) +
      |C3| * 3 ^ M3 * ν⁻¹ ^ (2 * (M0 + M1 + M2 + M3 + M4 + M5)) +
      2 * (|C4| * 3 ^ M4 * ν⁻¹ ^ (2 * (M0 + M1 + M2 + M3 + M4 + M5))) +
      2 * (|C5| * 3 ^ M5 * ν⁻¹ ^ (2 * (M0 + M1 + M2 + M3 + M4 + M5))) := by
    linarith [hp0, hp1, hp2, hp3, hp4, hp5]
  have hK : UnforcedLeray.Short.PartIIa.polyConst C0 M0 ν (ν ^ (-(2 : ℝ))) +
      UnforcedLeray.Short.PartIIa.polyConst C1 M1 ν (ν ^ (-(2 : ℝ))) +
      UnforcedLeray.Short.PartIIa.polyConst C2 M2 ν (ν ^ (-(2 : ℝ))) +
      UnforcedLeray.Short.PartIIa.polyConst C3 M3 ν (ν ^ (-(2 : ℝ))) +
      2 * UnforcedLeray.Short.PartIIa.polyConst C4 M4 ν (ν ^ (-(2 : ℝ))) +
      2 * UnforcedLeray.Short.PartIIa.polyConst C5 M5 ν (ν ^ (-(2 : ℝ))) ≤
      (|C0| * 3 ^ M0 + |C1| * 3 ^ M1 + |C2| * 3 ^ M2 + |C3| * 3 ^ M3 +
        2 * (|C4| * 3 ^ M4) + 2 * (|C5| * 3 ^ M5)) * ν⁻¹ ^ (2 * (M0 + M1 + M2 + M3 + M4 + M5)) :=
    le_of_le_of_eq hK1 (by ring)
  calc transWeight mZ (s, (q, η)) * |UnforcedLeray.Short.IIIa.meanCompletion tr s η|
      ≤ (2 ^ n * (1 + η ^ (2 * n) / (1 + s) ^ n)) *
          (|UnforcedLeray.Short.PartI.meanStream tr s η| +
            |η| * |deriv (fun e => UnforcedLeray.Short.PartI.meanStream tr s e) η| +
            2 * s * |deriv (fun r => UnforcedLeray.Short.PartI.meanStream tr r η) s|) :=
        mul_le_mul hW hmc (abs_nonneg _) hnonnegb
    _ = 2 ^ n * ((1 + η ^ (2 * n) / (1 + s) ^ n) *
          (|UnforcedLeray.Short.PartI.meanStream tr s η| +
            |η| * |deriv (fun e => UnforcedLeray.Short.PartI.meanStream tr s e) η| +
            2 * s * |deriv (fun r => UnforcedLeray.Short.PartI.meanStream tr r η) s|)) := by
        ring
    _ ≤ 2 ^ n * (((UnforcedLeray.Short.PartIIa.polyConst C0 M0 ν (ν ^ (-(2 : ℝ))) +
          UnforcedLeray.Short.PartIIa.polyConst C1 M1 ν (ν ^ (-(2 : ℝ))) +
          UnforcedLeray.Short.PartIIa.polyConst C2 M2 ν (ν ^ (-(2 : ℝ))) +
          UnforcedLeray.Short.PartIIa.polyConst C3 M3 ν (ν ^ (-(2 : ℝ))) +
          2 * UnforcedLeray.Short.PartIIa.polyConst C4 M4 ν (ν ^ (-(2 : ℝ))) +
          2 * UnforcedLeray.Short.PartIIa.polyConst C5 M5 ν (ν ^ (-(2 : ℝ)))) *
          (1 + s) ^ (-1 / 2 : ℝ))) :=
        mul_le_mul_of_nonneg_left hcore (by positivity)
    _ ≤ 2 ^ n * (((|C0| * 3 ^ M0 + |C1| * 3 ^ M1 + |C2| * 3 ^ M2 + |C3| * 3 ^ M3 +
          2 * (|C4| * 3 ^ M4) + 2 * (|C5| * 3 ^ M5)) * ν⁻¹ ^ (2 * (M0 + M1 + M2 + M3 + M4 + M5))) *
          (1 + s) ^ (-1 / 2 : ℝ)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hK hB0) (by positivity)
    _ = 2 ^ n * (|C0| * 3 ^ M0 + |C1| * 3 ^ M1 + |C2| * 3 ^ M2 + |C3| * 3 ^ M3 +
          2 * (|C4| * 3 ^ M4) + 2 * (|C5| * 3 ^ M5)) *
          ν⁻¹ ^ (2 * (M0 + M1 + M2 + M3 + M4 + M5)) * (1 + s) ^ (-1 / 2 : ℝ) := by
        ring

end UnforcedLeray.Short.IIIa
