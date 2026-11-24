import UnforcedLeray.Short.PartIIIa.Sub.T23_2_org
import UnforcedLeray.Short.PartIIa.Sub.R01
import UnforcedLeray.Short.PartIIb.Sub.R1_5
import UnforcedLeray.Units.B0190

/-!
# Part III-a, `PartIII-a:T23/2/1`: early smoothness of the train velocity

Target `earlyVel_of`: from `PartIIa.EarlyStreamProfile` (zero-age bounds on the mixed jets of the
stream profile, `Sub/R01.lean` line 133) and `PartI.TrainStreamSmooth`, the early velocity bound
`IIIa.EarlyVel` (`Sub/T23_2_org.lean`).  Source: `the November 2 reference manuscript`,
lines 2734-2735 and 439-459.

Route: `v = (-∂_η ψ, ∂_q ψ)` on the train (`streamV1_trainProfile`, `streamV2_trainProfile`),
`‖v‖ ≤ |v₀| + |v₁|`, the transverse weight is at most `(1+η²)^m` with `m = ⌈m_Z/2⌉₊`, and the
two stream jets are bounded by `polyConst` with `c = ν^{-2}`, which is `≤ |C| 3^d ν^{-2d}`.
-/

open UnforcedLeray.B0184 UnforcedLeray.B0185 UnforcedLeray.B0190

namespace UnforcedLeray.Short.IIIa

/-- Monotonicity of the constant `|C| 3^d ν^{-2d}` in the degree `d`, for `0 < ν ≤ 1`. -/
theorem earlyVel_const_mono (C : ℝ) {d D : ℕ} (hd : d ≤ D) {ν : ℝ} (hν : 0 < ν) (hν1 : ν ≤ 1) :
    |C| * 3 ^ d * ν⁻¹ ^ (2 * d) ≤ |C| * 3 ^ D * ν⁻¹ ^ (2 * D) := by
  have h1 : 1 ≤ ν⁻¹ := (one_le_inv₀ hν).mpr hν1
  have h3 : (3 : ℝ) ^ d ≤ 3 ^ D := pow_le_pow_right₀ (by norm_num) hd
  have hn : ν⁻¹ ^ (2 * d) ≤ ν⁻¹ ^ (2 * D) := pow_le_pow_right₀ h1 (by omega)
  have hC : 0 ≤ |C| := abs_nonneg C
  have hn0 : 0 ≤ ν⁻¹ ^ (2 * d) := by positivity
  have h30 : (0 : ℝ) ≤ 3 ^ d := by positivity
  have hA : |C| * 3 ^ d ≤ |C| * 3 ^ D := mul_le_mul_of_nonneg_left h3 hC
  calc |C| * 3 ^ d * ν⁻¹ ^ (2 * d) ≤ |C| * 3 ^ D * ν⁻¹ ^ (2 * d) :=
        mul_le_mul_of_nonneg_right hA hn0
    _ ≤ |C| * 3 ^ D * ν⁻¹ ^ (2 * D) :=
        mul_le_mul_of_nonneg_left hn (by positivity)

theorem earlyVel_of (hE : UnforcedLeray.Short.PartIIa.EarlyStreamProfile)
    (hS : UnforcedLeray.Short.PartI.TrainStreamSmooth) : UnforcedLeray.Short.IIIa.EarlyVel := by
  intro mZ hmZ
  set m : ℕ := ⌈mZ / 2⌉₊ with hm
  obtain ⟨ν₁, C₁, d₁, hν₁, H₁⟩ := hE 2 m 1 0 0 (by norm_num)
  obtain ⟨ν₂, C₂, d₂, hν₂, H₂⟩ := hE 2 m 0 1 0 (by norm_num)
  set D : ℕ := max d₁ d₂ with hD
  have hMpos : 0 < min (min ν₁ ν₂) 1 := lt_min (lt_min hν₁ hν₂) one_pos
  have hM1 : min (min ν₁ ν₂) 1 ≤ ν₁ := le_trans (min_le_left _ _) (min_le_left _ _)
  have hM2 : min (min ν₁ ν₂) 1 ≤ ν₂ := le_trans (min_le_left _ _) (min_le_right _ _)
  have hM3 : min (min ν₁ ν₂) 1 ≤ 1 := min_le_right _ _
  refine ⟨(|C₁| + |C₂|) * 3 ^ D, 2 * D, min (min ν₁ ν₂) 1 / 2, by positivity, ?_⟩
  intro ν hν c hc tr hT s hs0 hs1 q η
  have hνpos : 0 < ν := hν.1
  have hνle : ν ≤ min (min ν₁ ν₂) 1 / 2 := hν.2
  have hν1 : ν ≤ 1 := by linarith
  have hνl1 : ν < ν₁ := by linarith
  have hνl2 : ν < ν₂ := by linarith
  have hc' : c = ν ^ (-(2:ℝ)) := by rw [hc, UnforcedLeray.Short.IIIa.T23Early.rpow_neg_two hνpos]
  subst hc'
  have hpos : 0 < ν ^ (-(2:ℝ)) := Real.rpow_pos_of_pos hνpos _
  have hx : PartIIa.IsExactPlanarTrain ν (ν ^ (-(2:ℝ))) (trainProfile tr.ψ) (trainProfile tr.p) :=
    ⟨tr, hT, rfl, rfl⟩
  have hd : DifferentiableAt ℝ (trainProfile tr.ψ) ((q, (η, s)) : ProfilePoint) :=
    IIb.trainProfile_differentiableAt_of_smooth hS hνpos hpos tr hT (x := (q, (η, s))) hs0
  -- velocity components in terms of the stream jets
  have hv0 : tr.v s (q, η) 0 = -partialEta (trainProfile tr.ψ) ((q, (η, s)) : ProfilePoint) :=
    (streamV1_trainProfile tr hs0.le hd).symm
  have hv1 : tr.v s (q, η) 1 = partialQ (trainProfile tr.ψ) ((q, (η, s)) : ProfilePoint) :=
    (streamV2_trainProfile tr hs0.le hd).symm
  -- the two jet bounds
  have A1 : (1 + η ^ 2) ^ m * |partialEta (trainProfile tr.ψ) ((q, (η, s)) : ProfilePoint)| ≤
      PartIIa.polyConst C₁ d₁ ν (ν ^ (-(2:ℝ))) := by
    have h := H₁ ν ⟨hνpos, hνl1⟩ (trainProfile tr.ψ) (trainProfile tr.p) hx
      ((q, (η, s)) : ProfilePoint) hs0 hs1
    simpa only [Function.iterate_zero, Function.iterate_one, id_eq] using h
  have A2 : (1 + η ^ 2) ^ m * |partialQ (trainProfile tr.ψ) ((q, (η, s)) : ProfilePoint)| ≤
      PartIIa.polyConst C₂ d₂ ν (ν ^ (-(2:ℝ))) := by
    have h := H₂ ν ⟨hνpos, hνl2⟩ (trainProfile tr.ψ) (trainProfile tr.p) hx
      ((q, (η, s)) : ProfilePoint) hs0 hs1
    simpa only [Function.iterate_zero, Function.iterate_one, id_eq] using h
  have B1 : PartIIa.polyConst C₁ d₁ ν (ν ^ (-(2:ℝ))) ≤ |C₁| * 3 ^ d₁ * ν⁻¹ ^ (2 * d₁) :=
    T23Early.polyConst_two_le C₁ d₁ hνpos hν1
  have B2 : PartIIa.polyConst C₂ d₂ ν (ν ^ (-(2:ℝ))) ≤ |C₂| * 3 ^ d₂ * ν⁻¹ ^ (2 * d₂) :=
    T23Early.polyConst_two_le C₂ d₂ hνpos hν1
  have M1 : |C₁| * 3 ^ d₁ * ν⁻¹ ^ (2 * d₁) ≤ |C₁| * 3 ^ D * ν⁻¹ ^ (2 * D) :=
    earlyVel_const_mono C₁ (le_max_left d₁ d₂) hνpos hν1
  have M2 : |C₂| * 3 ^ d₂ * ν⁻¹ ^ (2 * d₂) ≤ |C₂| * 3 ^ D * ν⁻¹ ^ (2 * D) :=
    earlyVel_const_mono C₂ (le_max_right d₁ d₂) hνpos hν1
  -- the weight and the norm
  have hW : transWeight mZ (s, (q, η)) ≤ (1 + η ^ 2) ^ m :=
    T23Early.transWeight_le_jap hmZ hs0.le q η
  have hW0 : 0 ≤ transWeight mZ (s, (q, η)) := T23Early.transWeight_nonneg mZ _
  have hnorm : ‖tr.v s (q, η)‖ ≤ |partialEta (trainProfile tr.ψ) ((q, (η, s)) : ProfilePoint)|
      + |partialQ (trainProfile tr.ψ) ((q, (η, s)) : ProfilePoint)| := by
    refine (T23Early.norm_vec2_le _).trans ?_
    rw [hv0, hv1, abs_neg]
  have hP : 0 ≤ (1 + η ^ 2) ^ m := by positivity
  have key : transWeight mZ (s, (q, η)) * ‖tr.v s (q, η)‖ ≤
      (1 + η ^ 2) ^ m * (|partialEta (trainProfile tr.ψ) ((q, (η, s)) : ProfilePoint)|
      + |partialQ (trainProfile tr.ψ) ((q, (η, s)) : ProfilePoint)|) :=
    mul_le_mul hW hnorm (norm_nonneg _) hP
  have hsplit : (1 + η ^ 2) ^ m * (|partialEta (trainProfile tr.ψ) ((q, (η, s)) : ProfilePoint)|
      + |partialQ (trainProfile tr.ψ) ((q, (η, s)) : ProfilePoint)|) =
      (1 + η ^ 2) ^ m * |partialEta (trainProfile tr.ψ) ((q, (η, s)) : ProfilePoint)|
      + (1 + η ^ 2) ^ m * |partialQ (trainProfile tr.ψ) ((q, (η, s)) : ProfilePoint)| := by ring
  have hfin : |C₁| * 3 ^ D * ν⁻¹ ^ (2 * D) + |C₂| * 3 ^ D * ν⁻¹ ^ (2 * D)
      = (|C₁| + |C₂|) * 3 ^ D * ν⁻¹ ^ (2 * D) := by ring
  calc transWeight mZ (s, (q, η)) * ‖tr.v s (q, η)‖
      ≤ (1 + η ^ 2) ^ m * (|partialEta (trainProfile tr.ψ) ((q, (η, s)) : ProfilePoint)|
      + |partialQ (trainProfile tr.ψ) ((q, (η, s)) : ProfilePoint)|) := key
    _ = (1 + η ^ 2) ^ m * |partialEta (trainProfile tr.ψ) ((q, (η, s)) : ProfilePoint)|
      + (1 + η ^ 2) ^ m * |partialQ (trainProfile tr.ψ) ((q, (η, s)) : ProfilePoint)| := hsplit
    _ ≤ PartIIa.polyConst C₁ d₁ ν (ν ^ (-(2:ℝ))) + PartIIa.polyConst C₂ d₂ ν (ν ^ (-(2:ℝ))) :=
        add_le_add A1 A2
    _ ≤ |C₁| * 3 ^ D * ν⁻¹ ^ (2 * D) + |C₂| * 3 ^ D * ν⁻¹ ^ (2 * D) :=
        add_le_add (B1.trans M1) (B2.trans M2)
    _ = (|C₁| + |C₂|) * 3 ^ D * ν⁻¹ ^ (2 * D) := hfin

end UnforcedLeray.Short.IIIa
