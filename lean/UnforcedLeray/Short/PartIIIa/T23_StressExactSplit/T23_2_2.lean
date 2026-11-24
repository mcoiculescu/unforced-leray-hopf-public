import UnforcedLeray.Short.PartIIIa.Sub.T23_2_org
import UnforcedLeray.Short.PartIIa.Sub.R01
import UnforcedLeray.Short.PartIIb.Sub.R1_5
import UnforcedLeray.Units.B0190

/-!
# Part III-a, `PartIII-a:T23/2/2`: early smoothness of the stream completion

Target `earlyCompletion_of`: from `PartIIa.EarlyStreamProfile` (zero-age bounds on the mixed jets of
the stream profile, `Sub/R01.lean` line 133) and `PartI.TrainStreamSmooth`, the early bound
`IIIa.EarlyCompletion` for the raised stream `(1 - η∂_η - 2s∂_s)ψ` (`Cons.C03.raisedStream`).
Source: `the November 2 reference manuscript`, lines 2729-2735 and 439-459.

Route: `|H| ≤ |ψ| + |η||∂_ηψ| + 2s|∂_sψ|`; the transverse weight is at most `(1+η²)^m`,
`m = ⌈m_Z/2⌉₊`; the factor `|η|` is absorbed by one more power `(1+η²)^{m+1}`; the three jets
are bounded by `polyConst` with `c = ν^{-2}`, which is `≤ |C| 3^d ν^{-2d}`.
-/

open UnforcedLeray.B0184 UnforcedLeray.B0185 UnforcedLeray.B0190

namespace UnforcedLeray.Short.IIIa

/-- Triangle inequality for three terms, `|a - (b + c)| ≤ |a| + |b| + |c|`. -/
theorem earlyCompletion_abs_three (a b c : ℝ) : |a - (b + c)| ≤ |a| + |b| + |c| := by
  rw [abs_le]
  constructor <;>
    linarith [neg_abs_le a, le_abs_self a, neg_abs_le b, le_abs_self b, neg_abs_le c, le_abs_self c]

/-- Monotonicity of the constant `|C| 3^d ν^{-2d}` in the degree `d`, for `0 < ν ≤ 1`. -/
theorem earlyCompletion_const_mono (C : ℝ) {d D : ℕ} (hd : d ≤ D) {ν : ℝ} (hν : 0 < ν)
    (hν1 : ν ≤ 1) :
    |C| * 3 ^ d * ν⁻¹ ^ (2 * d) ≤ |C| * 3 ^ D * ν⁻¹ ^ (2 * D) := by
  have h1 : 1 ≤ ν⁻¹ := (one_le_inv₀ hν).mpr hν1
  have h3 : (3 : ℝ) ^ d ≤ 3 ^ D := pow_le_pow_right₀ (by norm_num) hd
  have hn : ν⁻¹ ^ (2 * d) ≤ ν⁻¹ ^ (2 * D) := pow_le_pow_right₀ h1 (by omega)
  have hC : 0 ≤ |C| := abs_nonneg C
  have hn0 : 0 ≤ ν⁻¹ ^ (2 * d) := by positivity
  have hA : |C| * 3 ^ d ≤ |C| * 3 ^ D := mul_le_mul_of_nonneg_left h3 hC
  calc |C| * 3 ^ d * ν⁻¹ ^ (2 * d) ≤ |C| * 3 ^ D * ν⁻¹ ^ (2 * d) :=
        mul_le_mul_of_nonneg_right hA hn0
    _ ≤ |C| * 3 ^ D * ν⁻¹ ^ (2 * D) :=
        mul_le_mul_of_nonneg_left hn (by positivity)

theorem earlyCompletion_of (hE : UnforcedLeray.Short.PartIIa.EarlyStreamProfile)
    (hS : UnforcedLeray.Short.PartI.TrainStreamSmooth) :
    UnforcedLeray.Short.IIIa.EarlyCompletion := by
  intro mZ hmZ
  set m : ℕ := ⌈mZ / 2⌉₊ with hm
  obtain ⟨ν₀', C₀, d₀, hν₀', H₀⟩ := hE 2 m 0 0 0 (by norm_num)
  obtain ⟨ν₁, C₁, d₁, hν₁, H₁⟩ := hE 2 (m + 1) 1 0 0 (by norm_num)
  obtain ⟨ν₂, C₂, d₂, hν₂, H₂⟩ := hE 2 m 0 0 1 (by norm_num)
  set D : ℕ := max d₀ (max d₁ d₂) with hD
  have hMpos : 0 < min (min (min ν₀' ν₁) ν₂) 1 :=
    lt_min (lt_min (lt_min hν₀' hν₁) hν₂) one_pos
  have hM0 : min (min (min ν₀' ν₁) ν₂) 1 ≤ ν₀' :=
    le_trans (le_trans (min_le_left _ _) (min_le_left _ _)) (min_le_left _ _)
  have hM1 : min (min (min ν₀' ν₁) ν₂) 1 ≤ ν₁ :=
    le_trans (le_trans (min_le_left _ _) (min_le_left _ _)) (min_le_right _ _)
  have hM2 : min (min (min ν₀' ν₁) ν₂) 1 ≤ ν₂ :=
    le_trans (min_le_left _ _) (min_le_right _ _)
  have hM3 : min (min (min ν₀' ν₁) ν₂) 1 ≤ 1 := min_le_right _ _
  refine ⟨(|C₀| + |C₁| + 2 * |C₂|) * 3 ^ D, 2 * D,
    min (min (min ν₀' ν₁) ν₂) 1 / 2, by positivity, ?_⟩
  intro ν hν c hc tr hT s hs0 hs1 q η
  have hνpos : 0 < ν := hν.1
  have hνle : ν ≤ min (min (min ν₀' ν₁) ν₂) 1 / 2 := hν.2
  have hν1 : ν ≤ 1 := by linarith
  have hνl0 : ν < ν₀' := by linarith
  have hνl1 : ν < ν₁ := by linarith
  have hνl2 : ν < ν₂ := by linarith
  have hc' : c = ν ^ (-(2:ℝ)) := by
    rw [hc, UnforcedLeray.Short.IIIa.T23Early.rpow_neg_two hνpos]
  subst hc'
  have hpos : 0 < ν ^ (-(2:ℝ)) := Real.rpow_pos_of_pos hνpos _
  have hx : PartIIa.IsExactPlanarTrain ν (ν ^ (-(2:ℝ))) (trainProfile tr.ψ) (trainProfile tr.p) :=
    ⟨tr, hT, rfl, rfl⟩
  have hd : DifferentiableAt ℝ (trainProfile tr.ψ) ((q, (η, s)) : ProfilePoint) :=
    IIb.trainProfile_differentiableAt_of_smooth hS hνpos hpos tr hT (x := (q, (η, s))) hs0
  have eE : partialEta (trainProfile tr.ψ) ((q, (η, s)) : ProfilePoint) =
      deriv (fun t => tr.ψ s (q, t)) η :=
    IIb.partialEta_trainProfile tr hd
  have eA : partialAge (trainProfile tr.ψ) ((q, (η, s)) : ProfilePoint) =
      deriv (fun t => tr.ψ t (q, η)) s :=
    IIb.partialAge_trainProfile tr hd
  -- the three jet bounds
  have A0 : (1 + η ^ 2) ^ m * |tr.ψ s (q, η)| ≤ PartIIa.polyConst C₀ d₀ ν (ν ^ (-(2:ℝ))) := by
    have h := H₀ ν ⟨hνpos, hνl0⟩ (trainProfile tr.ψ) (trainProfile tr.p) hx
      ((q, (η, s)) : ProfilePoint) hs0 hs1
    simp only [Function.iterate_zero, Function.iterate_one, id_eq] at h
    exact h
  have A1 : (1 + η ^ 2) ^ (m + 1) *
      |partialEta (trainProfile tr.ψ) ((q, (η, s)) : ProfilePoint)| ≤
      PartIIa.polyConst C₁ d₁ ν (ν ^ (-(2:ℝ))) := by
    have h := H₁ ν ⟨hνpos, hνl1⟩ (trainProfile tr.ψ) (trainProfile tr.p) hx
      ((q, (η, s)) : ProfilePoint) hs0 hs1
    simp only [Function.iterate_zero, Function.iterate_one, id_eq] at h
    exact h
  have A2 : (1 + η ^ 2) ^ m *
      |partialAge (trainProfile tr.ψ) ((q, (η, s)) : ProfilePoint)| ≤
      PartIIa.polyConst C₂ d₂ ν (ν ^ (-(2:ℝ))) := by
    have h := H₂ ν ⟨hνpos, hνl2⟩ (trainProfile tr.ψ) (trainProfile tr.p) hx
      ((q, (η, s)) : ProfilePoint) hs0 hs1
    simp only [Function.iterate_zero, Function.iterate_one, id_eq] at h
    exact h
  rw [eE] at A1
  rw [eA] at A2
  have B0 : PartIIa.polyConst C₀ d₀ ν (ν ^ (-(2:ℝ))) ≤ |C₀| * 3 ^ d₀ * ν⁻¹ ^ (2 * d₀) :=
    T23Early.polyConst_two_le C₀ d₀ hνpos hν1
  have B1 : PartIIa.polyConst C₁ d₁ ν (ν ^ (-(2:ℝ))) ≤ |C₁| * 3 ^ d₁ * ν⁻¹ ^ (2 * d₁) :=
    T23Early.polyConst_two_le C₁ d₁ hνpos hν1
  have B2 : PartIIa.polyConst C₂ d₂ ν (ν ^ (-(2:ℝ))) ≤ |C₂| * 3 ^ d₂ * ν⁻¹ ^ (2 * d₂) :=
    T23Early.polyConst_two_le C₂ d₂ hνpos hν1
  have M0 : |C₀| * 3 ^ d₀ * ν⁻¹ ^ (2 * d₀) ≤ |C₀| * 3 ^ D * ν⁻¹ ^ (2 * D) :=
    earlyCompletion_const_mono C₀ (le_max_left d₀ _) hνpos hν1
  have M1 : |C₁| * 3 ^ d₁ * ν⁻¹ ^ (2 * d₁) ≤ |C₁| * 3 ^ D * ν⁻¹ ^ (2 * D) :=
    earlyCompletion_const_mono C₁ (le_trans (le_max_left d₁ d₂) (le_max_right d₀ _)) hνpos hν1
  have M2 : |C₂| * 3 ^ d₂ * ν⁻¹ ^ (2 * d₂) ≤ |C₂| * 3 ^ D * ν⁻¹ ^ (2 * D) :=
    earlyCompletion_const_mono C₂ (le_trans (le_max_right d₁ d₂) (le_max_right d₀ _)) hνpos hν1
  -- the weight
  have hW : transWeight mZ (s, (q, η)) ≤ (1 + η ^ 2) ^ m :=
    T23Early.transWeight_le_jap hmZ hs0.le q η
  have hW0 : 0 ≤ transWeight mZ (s, (q, η)) := T23Early.transWeight_nonneg mZ _
  have hP : 0 ≤ (1 + η ^ 2) ^ m := by positivity
  -- the pointwise decomposition of the completion
  have hR : |UnforcedLeray.Cons.C03.raisedStream tr.ψ s q η| ≤
      |tr.ψ s (q, η)| + |η| * |deriv (fun t => tr.ψ s (q, t)) η|
        + 2 * s * |deriv (fun t => tr.ψ t (q, η)) s| := by
    unfold UnforcedLeray.Cons.C03.raisedStream
    have h1 := earlyCompletion_abs_three (tr.ψ s (q, η)) (η * deriv (fun t => tr.ψ s (q, t)) η)
      (2 * s * deriv (fun t => tr.ψ t (q, η)) s)
    have h3 : |η * deriv (fun t => tr.ψ s (q, t)) η| = |η| * |deriv (fun t => tr.ψ s (q, t)) η| :=
      abs_mul _ _
    have h4 : |2 * s * deriv (fun t => tr.ψ t (q, η)) s| =
        2 * s * |deriv (fun t => tr.ψ t (q, η)) s| := by
      rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 2), abs_of_nonneg hs0.le]
    have h5 : |tr.ψ s (q, η) - (η * deriv (fun t => tr.ψ s (q, t)) η +
        2 * s * deriv (fun t => tr.ψ t (q, η)) s)| ≤ |tr.ψ s (q, η)| +
        |η * deriv (fun t => tr.ψ s (q, t)) η| + |2 * s * deriv (fun t => tr.ψ t (q, η)) s| := h1
    linarith
  have hWR : transWeight mZ (s, (q, η)) * |UnforcedLeray.Cons.C03.raisedStream tr.ψ s q η| ≤
      (1 + η ^ 2) ^ m * (|tr.ψ s (q, η)| + |η| * |deriv (fun t => tr.ψ s (q, t)) η|
        + 2 * s * |deriv (fun t => tr.ψ t (q, η)) s|) :=
    mul_le_mul hW hR (abs_nonneg _) hP
  -- absorb the factor η into one more weight power
  have S4 : (1 + η ^ 2) ^ m * |η| * |deriv (fun t => tr.ψ s (q, t)) η| ≤
      (1 + η ^ 2) ^ (m + 1) * |deriv (fun t => tr.ψ s (q, t)) η| := by
    rw [pow_succ]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (T23Early.abs_le_one_add_sq η) hP) (abs_nonneg _)
  -- the s-factor is at most one
  have hA0 : 0 ≤ (1 + η ^ 2) ^ m * |deriv (fun t => tr.ψ t (q, η)) s| := by positivity
  have S5 : 2 * s * ((1 + η ^ 2) ^ m * |deriv (fun t => tr.ψ t (q, η)) s|) ≤
      2 * ((1 + η ^ 2) ^ m * |deriv (fun t => tr.ψ t (q, η)) s|) := by
    nlinarith [mul_nonneg (sub_nonneg.2 hs1) hA0]
  have hsplit : (1 + η ^ 2) ^ m * (|tr.ψ s (q, η)| + |η| * |deriv (fun t => tr.ψ s (q, t)) η|
        + 2 * s * |deriv (fun t => tr.ψ t (q, η)) s|) =
      (1 + η ^ 2) ^ m * |tr.ψ s (q, η)|
      + (1 + η ^ 2) ^ m * |η| * |deriv (fun t => tr.ψ s (q, t)) η|
      + 2 * s * ((1 + η ^ 2) ^ m * |deriv (fun t => tr.ψ t (q, η)) s|) := by ring
  have hfin : |C₀| * 3 ^ D * ν⁻¹ ^ (2 * D) + |C₁| * 3 ^ D * ν⁻¹ ^ (2 * D)
      + 2 * (|C₂| * 3 ^ D * ν⁻¹ ^ (2 * D))
      = (|C₀| + |C₁| + 2 * |C₂|) * 3 ^ D * ν⁻¹ ^ (2 * D) := by ring
  have hsum : (1 + η ^ 2) ^ m * |tr.ψ s (q, η)|
      + (1 + η ^ 2) ^ m * |η| * |deriv (fun t => tr.ψ s (q, t)) η|
      + 2 * s * ((1 + η ^ 2) ^ m * |deriv (fun t => tr.ψ t (q, η)) s|)
      ≤ PartIIa.polyConst C₀ d₀ ν (ν ^ (-(2:ℝ))) + PartIIa.polyConst C₁ d₁ ν (ν ^ (-(2:ℝ)))
        + 2 * PartIIa.polyConst C₂ d₂ ν (ν ^ (-(2:ℝ))) := by
    linarith [A0, S4, A1, S5, A2]
  calc transWeight mZ (s, (q, η)) * |UnforcedLeray.Cons.C03.raisedStream tr.ψ s q η|
      ≤ (1 + η ^ 2) ^ m * (|tr.ψ s (q, η)| + |η| * |deriv (fun t => tr.ψ s (q, t)) η|
        + 2 * s * |deriv (fun t => tr.ψ t (q, η)) s|) := hWR
    _ = (1 + η ^ 2) ^ m * |tr.ψ s (q, η)|
      + (1 + η ^ 2) ^ m * |η| * |deriv (fun t => tr.ψ s (q, t)) η|
      + 2 * s * ((1 + η ^ 2) ^ m * |deriv (fun t => tr.ψ t (q, η)) s|) := hsplit
    _ ≤ PartIIa.polyConst C₀ d₀ ν (ν ^ (-(2:ℝ))) + PartIIa.polyConst C₁ d₁ ν (ν ^ (-(2:ℝ)))
        + 2 * PartIIa.polyConst C₂ d₂ ν (ν ^ (-(2:ℝ))) := hsum
    _ ≤ |C₀| * 3 ^ D * ν⁻¹ ^ (2 * D) + |C₁| * 3 ^ D * ν⁻¹ ^ (2 * D)
        + 2 * (|C₂| * 3 ^ D * ν⁻¹ ^ (2 * D)) := by
        linarith [B0, B1, B2, M0, M1, M2]
    _ = (|C₀| + |C₁| + 2 * |C₂|) * 3 ^ D * ν⁻¹ ^ (2 * D) := hfin

end UnforcedLeray.Short.IIIa
