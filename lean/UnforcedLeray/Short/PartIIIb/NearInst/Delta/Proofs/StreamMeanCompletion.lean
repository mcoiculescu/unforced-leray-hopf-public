import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_near_delta_5_1
import UnforcedLeray.Short.PartIIIb.NearInst.FlatTrain.Defs
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_1.MeanSlice
import UnforcedLeray.Short.PartI.Tasks.TrainClass.BUCMeanStreamSmooth
import UnforcedLeray.Short.PartI.Tasks.OverlapHighNorm
import UnforcedLeray.Short.PartI.Tasks.OverlapFluctuationDecay
import UnforcedLeray.Short.PartI.Tasks.OverlapMeanPrimitive
import UnforcedLeray.Short.PartI.Tasks.OverlapMeanDecay
import UnforcedLeray.Short.PartI.Tasks.TrainOverlapProof
import UnforcedLeray.Short.PartI.Tasks.TrainVorticityTail
import UnforcedLeray.Short.PartI.Tasks.TrainStreamTails
import UnforcedLeray.Short.PartI.Tasks.TrainFluctuationDecayProof
import UnforcedLeray.Short.PartI.Tasks.TrainMeanExpansionProof

/-!
# `PartIII-b:C/near/delta/5/1/1`: `StreamMeanCompletion` (source lines 2703-2729)

Source of record: `the November 2 reference manuscript`, lines 2703-2729 and
447-459 (`sct:expansion`).

Proves `streamMeanCompletion_of` from `PartI.TrainMeanExpansion` (at `p = ∞`, upgraded to a
pointwise bound via `PartI.bucMeanStreamSmooth` and `contDiff_iteratedDeriv_slice`) and assembles
the unconditional target `streamMeanCompletion : StreamMeanCompletion`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.NearInst.Delta

open UnforcedLeray.Short.PartIIIb UnforcedLeray.Short.PartIIIb.Concrete
  UnforcedLeray.Cons.C03

/-- Pointwise weighted derivative bound for the mean stream from `PartI.TrainMeanExpansion` at
`p = ∞` and smoothness of the BUC mean stream (`PartI.bucMeanStreamSmooth`). -/
theorem smc_mean_pt (hM : UnforcedLeray.Short.PartI.TrainMeanExpansion) (m b ℓ : ℕ) :
    ∃ (C : ℝ) (M : ℕ) (ν₀ : ℝ), 0 < C ∧ 0 < ν₀ ∧
      ∀ (ν c : ℝ) (tr : UnforcedLeray.B0140.TrainSol ν c), 0 < ν → ν ≤ ν₀ →
        c = (ν ^ 2)⁻¹ → UnforcedLeray.Short.PartI.IsBUCTrain tr →
        ∀ s : ℝ, 0 < s → ∀ η : ℝ,
          |η| ^ m * |iteratedDeriv b
              (fun e => iteratedDeriv ℓ (fun r => UnforcedLeray.Short.PartI.meanStream tr r e) s) η| ≤
            UnforcedLeray.Short.PartI.polyP C M ν c * (1 + s) ^ (((m : ℝ) - b - 1) / 2 - ℓ) := by
  obtain ⟨C, M, ν₀, hC, hν₀, H⟩ := hM 2 (by norm_num) 0 m b ℓ ⊤ le_top
  refine ⟨C, M, ν₀, hC, hν₀, ?_⟩
  intro ν c tr hν hνle hc hbuc s hs η
  have hc' : c = UnforcedLeray.Short.PartI.trainPeriod 2 ν :=
    hc.trans (UnforcedLeray.Short.PartIIIb.NearInst.trainPeriod_two hν).symm
  subst hc'
  have hcpos : 0 < UnforcedLeray.Short.PartI.trainPeriod 2 ν := by
    rw [UnforcedLeray.Short.PartIIIb.NearInst.trainPeriod_two hν]
    positivity
  have hsm := UnforcedLeray.Short.PartI.bucMeanStreamSmooth ν
    (UnforcedLeray.Short.PartI.trainPeriod 2 ν) hν hcpos tr hbuc
  have hg := UnforcedLeray.Short.PartIIIb.Concrete.contDiff_iteratedDeriv_slice
    (fun r e => UnforcedLeray.Short.PartI.meanStream tr r e) hsm ℓ s hs
  have hd : Continuous (fun e : ℝ => iteratedDeriv b
      (fun e' => iteratedDeriv ℓ (fun r => UnforcedLeray.Short.PartI.meanStream tr r e') s) e) :=
    hg.continuous_iteratedDeriv b (by exact_mod_cast le_top)
  have hcont : Continuous (fun e : ℝ => e ^ m * iteratedDeriv b
      (fun e' => iteratedDeriv ℓ (fun r => UnforcedLeray.Short.PartI.meanStream tr r e') s) e) :=
    (continuous_pow m).mul hd
  obtain ⟨_, _, _, H4⟩ := H ν hν hνle tr hbuc
  have hL := H4 s hs.le
  simp only [ENNReal.toReal_top, inv_zero, zero_div, add_zero] at hL
  have hP0 : 0 ≤ UnforcedLeray.Short.PartI.polyP C M ν
      (UnforcedLeray.Short.PartI.trainPeriod 2 ν) := by
    unfold UnforcedLeray.Short.PartI.polyP
    have h1 : 0 ≤ ν⁻¹ := inv_nonneg.mpr hν.le
    exact mul_nonneg hC.le (pow_nonneg (by linarith) M)
  have hK0 : 0 ≤ UnforcedLeray.Short.PartI.polyP C M ν
      (UnforcedLeray.Short.PartI.trainPeriod 2 ν) *
      (1 + s) ^ (((m : ℝ) - b - 1) / 2 - ℓ) :=
    mul_nonneg hP0 (Real.rpow_nonneg (by linarith) _)
  have key := UnforcedLeray.Short.PartIIIb.NearInst.abs_le_of_eLpNorm_top_le hcont hK0 hL η
  rwa [abs_mul, abs_pow] at key

/-- Algebraic core: the six pointwise bounds give the completion bound on the weight
`(1 + η^{2n}/A^n)` with `A = 1 + s`. -/
theorem smc_core {A : ℝ} (hA : 0 < A) (n : ℕ) {s S Sη Ss η p0 p1 p2 p3 p4 p5 : ℝ}
    (_hs : 0 ≤ s) (hsA : s ≤ A)
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
  rw [hsplit] at h1 h3 h5
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

theorem polyP_mono_exp {C ν c : ℝ} (hC : 0 ≤ C) (hν : 0 < ν) (hc : 0 ≤ c) {M K : ℕ}
    (hMK : M ≤ K) :
    UnforcedLeray.Short.PartI.polyP C M ν c ≤ UnforcedLeray.Short.PartI.polyP C K ν c := by
  unfold UnforcedLeray.Short.PartI.polyP
  have h1 : 1 ≤ 1 + c + ν⁻¹ := by
    have : 0 ≤ ν⁻¹ := inv_nonneg.mpr hν.le
    linarith
  exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ h1 hMK) hC

theorem sqrt_mul_one_add_rpow_neg_half_le_one {s : ℝ} (hs : 0 ≤ s) :
    Real.sqrt s * (1 + s) ^ (-1 / 2 : ℝ) ≤ 1 := by
  have h1s : 0 < 1 + s := by linarith
  have hsq : Real.sqrt s ≤ Real.sqrt (1 + s) := Real.sqrt_le_sqrt (by linarith)
  have hpos : 0 < Real.sqrt (1 + s) := Real.sqrt_pos.mpr h1s
  have heq : (1 + s) ^ (-1 / 2 : ℝ) = (Real.sqrt (1 + s))⁻¹ := by
    rw [show (-1 / 2 : ℝ) = -(1 / 2 : ℝ) by ring, Real.rpow_neg h1s.le, ← Real.sqrt_eq_rpow]
  rw [heq, ← div_eq_mul_inv, div_le_one hpos]
  exact hsq

/-- Conditional form: `StreamMeanCompletion` from `PartI.TrainMeanExpansion`. -/
theorem streamMeanCompletion_of (h : UnforcedLeray.Short.PartI.TrainMeanExpansion) :
    UnforcedLeray.Short.PartIIIb.NearInst.Delta.StreamMeanCompletion := by
  intro mZ hmZ
  set n : ℕ := ⌈mZ / 2⌉₊ with hn
  obtain ⟨C0, M0, ν0, hC0, hν0, H0⟩ := smc_mean_pt h 0 0 0
  obtain ⟨C1, M1, ν1, hC1, hν1, H1⟩ := smc_mean_pt h (2 * n) 0 0
  obtain ⟨C2, M2, ν2, hC2, hν2, H2⟩ := smc_mean_pt h 1 1 0
  obtain ⟨C3, M3, ν3, hC3, hν3, H3⟩ := smc_mean_pt h (2 * n + 1) 1 0
  obtain ⟨C4, M4, ν4, hC4, hν4, H4⟩ := smc_mean_pt h 0 0 1
  obtain ⟨C5, M5, ν5, hC5, hν5, H5⟩ := smc_mean_pt h (2 * n) 0 1
  obtain ⟨νm, hνm0, ha0, ha1, ha2, ha3, ha4, ha5⟩ :
      ∃ νm : ℝ, 0 < νm ∧ νm ≤ ν0 ∧ νm ≤ ν1 ∧ νm ≤ ν2 ∧ νm ≤ ν3 ∧ νm ≤ ν4 ∧ νm ≤ ν5 :=
    ⟨min ν0 (min ν1 (min ν2 (min ν3 (min ν4 ν5)))),
      lt_min hν0 (lt_min hν1 (lt_min hν2 (lt_min hν3 (lt_min hν4 hν5)))),
      by simp [min_le_iff], by simp [min_le_iff], by simp [min_le_iff],
      by simp [min_le_iff], by simp [min_le_iff], by simp [min_le_iff]⟩
  set K : ℕ := M0 + M1 + M2 + M3 + M4 + M5
  refine ⟨2 ^ n * (C0 + C1 + C2 + C3 + 2 * C4 + 2 * C5), K, νm, hνm0, ?_⟩
  intro ν c tr hν0' hνle hc hbuc s hs0 q η
  have hs' : 0 ≤ s := hs0.le
  have hc0 : 0 ≤ c := by rw [hc]; positivity
  have hp0 : UnforcedLeray.Short.PartI.polyP C0 M0 ν c ≤
      UnforcedLeray.Short.PartI.polyP C0 K ν c :=
    polyP_mono_exp hC0.le hν0' hc0 (by omega)
  have hp1 : UnforcedLeray.Short.PartI.polyP C1 M1 ν c ≤
      UnforcedLeray.Short.PartI.polyP C1 K ν c :=
    polyP_mono_exp hC1.le hν0' hc0 (by omega)
  have hp2 : UnforcedLeray.Short.PartI.polyP C2 M2 ν c ≤
      UnforcedLeray.Short.PartI.polyP C2 K ν c :=
    polyP_mono_exp hC2.le hν0' hc0 (by omega)
  have hp3 : UnforcedLeray.Short.PartI.polyP C3 M3 ν c ≤
      UnforcedLeray.Short.PartI.polyP C3 K ν c :=
    polyP_mono_exp hC3.le hν0' hc0 (by omega)
  have hp4 : UnforcedLeray.Short.PartI.polyP C4 M4 ν c ≤
      UnforcedLeray.Short.PartI.polyP C4 K ν c :=
    polyP_mono_exp hC4.le hν0' hc0 (by omega)
  have hp5 : UnforcedLeray.Short.PartI.polyP C5 M5 ν c ≤
      UnforcedLeray.Short.PartI.polyP C5 K ν c :=
    polyP_mono_exp hC5.le hν0' hc0 (by omega)
  have hA0 : |UnforcedLeray.Short.PartI.meanStream tr s η| ≤
      UnforcedLeray.Short.PartI.polyP C0 M0 ν c * (1 + s) ^ (-1 / 2 : ℝ) := by
    have h := H0 ν c tr hν0' (hνle.trans ha0) hc hbuc s hs0 η
    simp only [pow_zero, one_mul, iteratedDeriv_zero] at h
    have ex : (((0 : ℕ) : ℝ) - ((0 : ℕ) : ℝ) - 1) / 2 - ((0 : ℕ) : ℝ) = -1 / 2 := by norm_num
    rwa [ex] at h
  have hA1 : η ^ (2 * n) * |UnforcedLeray.Short.PartI.meanStream tr s η| ≤
      UnforcedLeray.Short.PartI.polyP C1 M1 ν c * (1 + s) ^ ((n : ℝ) + (-1 / 2 : ℝ)) := by
    have h := H1 ν c tr hν0' (hνle.trans ha1) hc hbuc s hs0 η
    simp only [iteratedDeriv_zero] at h
    have ex : (((2 * n : ℕ) : ℝ) - ((0 : ℕ) : ℝ) - 1) / 2 - ((0 : ℕ) : ℝ) =
        (n : ℝ) + (-1 / 2 : ℝ) := by push_cast; ring
    rw [ex] at h
    calc η ^ (2 * n) * |UnforcedLeray.Short.PartI.meanStream tr s η|
        = |η| ^ (2 * n) * |UnforcedLeray.Short.PartI.meanStream tr s η| := by
          rw [Even.pow_abs (even_two_mul n) η]
      _ ≤ _ := h
  have hA2 : |η| * |deriv (fun e => UnforcedLeray.Short.PartI.meanStream tr s e) η| ≤
      UnforcedLeray.Short.PartI.polyP C2 M2 ν c * (1 + s) ^ (-1 / 2 : ℝ) := by
    have h := H2 ν c tr hν0' (hνle.trans ha2) hc hbuc s hs0 η
    simp only [pow_one, iteratedDeriv_zero, iteratedDeriv_one] at h
    have ex : (((1 : ℕ) : ℝ) - ((1 : ℕ) : ℝ) - 1) / 2 - ((0 : ℕ) : ℝ) = -1 / 2 := by norm_num
    rwa [ex] at h
  have hA3 : η ^ (2 * n) * (|η| * |deriv (fun e => UnforcedLeray.Short.PartI.meanStream tr s e) η|) ≤
      UnforcedLeray.Short.PartI.polyP C3 M3 ν c * (1 + s) ^ ((n : ℝ) + (-1 / 2 : ℝ)) := by
    have h := H3 ν c tr hν0' (hνle.trans ha3) hc hbuc s hs0 η
    simp only [iteratedDeriv_zero, iteratedDeriv_one] at h
    have ex : (((2 * n + 1 : ℕ) : ℝ) - ((1 : ℕ) : ℝ) - 1) / 2 - ((0 : ℕ) : ℝ) =
        (n : ℝ) + (-1 / 2 : ℝ) := by push_cast; ring
    rw [ex] at h
    have hw : |η| ^ (2 * n + 1) = η ^ (2 * n) * |η| := by
      rw [pow_succ, Even.pow_abs (even_two_mul n) η]
    calc η ^ (2 * n) * (|η| * |deriv (fun e => UnforcedLeray.Short.PartI.meanStream tr s e) η|)
        = |η| ^ (2 * n + 1) * |deriv (fun e => UnforcedLeray.Short.PartI.meanStream tr s e) η| := by
          rw [hw]; ring
      _ ≤ _ := h
  have hA4 : |deriv (fun r => UnforcedLeray.Short.PartI.meanStream tr r η) s| ≤
      UnforcedLeray.Short.PartI.polyP C4 M4 ν c * (1 + s) ^ (-3 / 2 : ℝ) := by
    have h := H4 ν c tr hν0' (hνle.trans ha4) hc hbuc s hs0 η
    simp only [pow_zero, one_mul, iteratedDeriv_zero, iteratedDeriv_one] at h
    have ex : (((0 : ℕ) : ℝ) - ((0 : ℕ) : ℝ) - 1) / 2 - ((1 : ℕ) : ℝ) = -3 / 2 := by norm_num
    rwa [ex] at h
  have hA5 : η ^ (2 * n) * |deriv (fun r => UnforcedLeray.Short.PartI.meanStream tr r η) s| ≤
      UnforcedLeray.Short.PartI.polyP C5 M5 ν c * (1 + s) ^ ((n : ℝ) + (-3 / 2 : ℝ)) := by
    have h := H5 ν c tr hν0' (hνle.trans ha5) hc hbuc s hs0 η
    simp only [iteratedDeriv_zero, iteratedDeriv_one] at h
    have ex : (((2 * n : ℕ) : ℝ) - ((0 : ℕ) : ℝ) - 1) / 2 - ((1 : ℕ) : ℝ) =
        (n : ℝ) + (-3 / 2 : ℝ) := by push_cast; ring
    rw [ex] at h
    calc η ^ (2 * n) * |deriv (fun r => UnforcedLeray.Short.PartI.meanStream tr r η) s|
        = |η| ^ (2 * n) * |deriv (fun r => UnforcedLeray.Short.PartI.meanStream tr r η) s| := by
          rw [Even.pow_abs (even_two_mul n) η]
      _ ≤ _ := h
  have hcore := smc_core (A := 1 + s) (by linarith) n hs' (by linarith) hA0 hA1 hA2 hA3 hA4 hA5
  have hmc : |raisedStream (fun r z => UnforcedLeray.Short.PartI.meanStream tr r z.2) s q η| ≤
      |UnforcedLeray.Short.PartI.meanStream tr s η| +
        |η| * |deriv (fun e => UnforcedLeray.Short.PartI.meanStream tr s e) η| +
        2 * s * |deriv (fun r => UnforcedLeray.Short.PartI.meanStream tr r η) s| := by
    unfold raisedStream
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
  have hW := UnforcedLeray.Short.PartIIIb.NearInst.transWeight_le_two_pow mZ (s := s) hs' q η
  have hEn : 0 ≤ η ^ (2 * n) := Even.pow_nonneg (even_two_mul n) η
  have hAn : 0 < (1 + s) ^ n := pow_pos (by linarith) n
  have hnonnegb : 0 ≤ 2 ^ n * (1 + η ^ (2 * n) / (1 + s) ^ n) :=
    mul_nonneg (by positivity) (by have := div_nonneg hEn hAn.le; linarith)
  have hB0 : 0 ≤ (1 + s) ^ (-1 / 2 : ℝ) := Real.rpow_nonneg (by linarith) _
  have hK : 2 ^ n * (UnforcedLeray.Short.PartI.polyP C0 M0 ν c +
      UnforcedLeray.Short.PartI.polyP C1 M1 ν c +
      UnforcedLeray.Short.PartI.polyP C2 M2 ν c +
      UnforcedLeray.Short.PartI.polyP C3 M3 ν c +
      2 * UnforcedLeray.Short.PartI.polyP C4 M4 ν c +
      2 * UnforcedLeray.Short.PartI.polyP C5 M5 ν c) ≤
      UnforcedLeray.Short.PartI.polyP (2 ^ n * (C0 + C1 + C2 + C3 + 2 * C4 + 2 * C5)) K ν c := by
    have hsum : UnforcedLeray.Short.PartI.polyP C0 M0 ν c +
        UnforcedLeray.Short.PartI.polyP C1 M1 ν c +
        UnforcedLeray.Short.PartI.polyP C2 M2 ν c +
        UnforcedLeray.Short.PartI.polyP C3 M3 ν c +
        2 * UnforcedLeray.Short.PartI.polyP C4 M4 ν c +
        2 * UnforcedLeray.Short.PartI.polyP C5 M5 ν c ≤
        UnforcedLeray.Short.PartI.polyP C0 K ν c +
        UnforcedLeray.Short.PartI.polyP C1 K ν c +
        UnforcedLeray.Short.PartI.polyP C2 K ν c +
        UnforcedLeray.Short.PartI.polyP C3 K ν c +
        2 * UnforcedLeray.Short.PartI.polyP C4 K ν c +
        2 * UnforcedLeray.Short.PartI.polyP C5 K ν c := by
      linarith [hp0, hp1, hp2, hp3, hp4, hp5]
    calc _ ≤ 2 ^ n * (UnforcedLeray.Short.PartI.polyP C0 K ν c +
          UnforcedLeray.Short.PartI.polyP C1 K ν c +
          UnforcedLeray.Short.PartI.polyP C2 K ν c +
          UnforcedLeray.Short.PartI.polyP C3 K ν c +
          2 * UnforcedLeray.Short.PartI.polyP C4 K ν c +
          2 * UnforcedLeray.Short.PartI.polyP C5 K ν c) :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
      _ = UnforcedLeray.Short.PartI.polyP (2 ^ n * (C0 + C1 + C2 + C3 + 2 * C4 + 2 * C5)) K ν c := by
        unfold UnforcedLeray.Short.PartI.polyP; ring
  have hP_nonneg : 0 ≤ UnforcedLeray.Short.PartI.polyP
      (2 ^ n * (C0 + C1 + C2 + C3 + 2 * C4 + 2 * C5)) K ν c := by
    unfold UnforcedLeray.Short.PartI.polyP
    have : 0 ≤ ν⁻¹ := inv_nonneg.mpr hν0'.le
    exact mul_nonneg (by positivity) (pow_nonneg (by linarith) K)
  have hWR : UnforcedLeray.Short.IIIa.transWeight mZ (s, (q, η)) *
      |raisedStream (fun r z => UnforcedLeray.Short.PartI.meanStream tr r z.2) s q η| ≤
      UnforcedLeray.Short.PartI.polyP (2 ^ n * (C0 + C1 + C2 + C3 + 2 * C4 + 2 * C5)) K ν c *
        (1 + s) ^ (-1 / 2 : ℝ) := by
    calc UnforcedLeray.Short.IIIa.transWeight mZ (s, (q, η)) *
          |raisedStream (fun r z => UnforcedLeray.Short.PartI.meanStream tr r z.2) s q η|
        ≤ (2 ^ n * (1 + η ^ (2 * n) / (1 + s) ^ n)) *
            (|UnforcedLeray.Short.PartI.meanStream tr s η| +
              |η| * |deriv (fun e => UnforcedLeray.Short.PartI.meanStream tr s e) η| +
              2 * s * |deriv (fun r => UnforcedLeray.Short.PartI.meanStream tr r η) s|) :=
          mul_le_mul hW hmc (abs_nonneg _) hnonnegb
      _ = 2 ^ n * ((1 + η ^ (2 * n) / (1 + s) ^ n) *
            (|UnforcedLeray.Short.PartI.meanStream tr s η| +
              |η| * |deriv (fun e => UnforcedLeray.Short.PartI.meanStream tr s e) η| +
              2 * s * |deriv (fun r => UnforcedLeray.Short.PartI.meanStream tr r η) s|)) := by ring
      _ ≤ 2 ^ n * ((UnforcedLeray.Short.PartI.polyP C0 M0 ν c +
            UnforcedLeray.Short.PartI.polyP C1 M1 ν c +
            UnforcedLeray.Short.PartI.polyP C2 M2 ν c +
            UnforcedLeray.Short.PartI.polyP C3 M3 ν c +
            2 * UnforcedLeray.Short.PartI.polyP C4 M4 ν c +
            2 * UnforcedLeray.Short.PartI.polyP C5 M5 ν c) * (1 + s) ^ (-1 / 2 : ℝ)) :=
          mul_le_mul_of_nonneg_left hcore (by positivity)
      _ = (2 ^ n * (UnforcedLeray.Short.PartI.polyP C0 M0 ν c +
            UnforcedLeray.Short.PartI.polyP C1 M1 ν c +
            UnforcedLeray.Short.PartI.polyP C2 M2 ν c +
            UnforcedLeray.Short.PartI.polyP C3 M3 ν c +
            2 * UnforcedLeray.Short.PartI.polyP C4 M4 ν c +
            2 * UnforcedLeray.Short.PartI.polyP C5 M5 ν c)) * (1 + s) ^ (-1 / 2 : ℝ) := by ring
      _ ≤ UnforcedLeray.Short.PartI.polyP (2 ^ n * (C0 + C1 + C2 + C3 + 2 * C4 + 2 * C5)) K ν c *
            (1 + s) ^ (-1 / 2 : ℝ) :=
          mul_le_mul_of_nonneg_right hK hB0
  calc Real.sqrt s * UnforcedLeray.Short.IIIa.transWeight mZ (s, (q, η)) *
        |raisedStream (fun r z => UnforcedLeray.Short.PartI.meanStream tr r z.2) s q η|
      = Real.sqrt s * (UnforcedLeray.Short.IIIa.transWeight mZ (s, (q, η)) *
          |raisedStream (fun r z => UnforcedLeray.Short.PartI.meanStream tr r z.2) s q η|) := by ring
    _ ≤ Real.sqrt s * (UnforcedLeray.Short.PartI.polyP
          (2 ^ n * (C0 + C1 + C2 + C3 + 2 * C4 + 2 * C5)) K ν c * (1 + s) ^ (-1 / 2 : ℝ)) :=
        mul_le_mul_of_nonneg_left hWR (Real.sqrt_nonneg s)
    _ = UnforcedLeray.Short.PartI.polyP (2 ^ n * (C0 + C1 + C2 + C3 + 2 * C4 + 2 * C5)) K ν c *
          (Real.sqrt s * (1 + s) ^ (-1 / 2 : ℝ)) := by ring
    _ ≤ UnforcedLeray.Short.PartI.polyP (2 ^ n * (C0 + C1 + C2 + C3 + 2 * C4 + 2 * C5)) K ν c * 1 :=
        mul_le_mul_of_nonneg_left (sqrt_mul_one_add_rpow_neg_half_le_one hs') hP_nonneg
    _ = UnforcedLeray.Short.PartI.polyP (2 ^ n * (C0 + C1 + C2 + C3 + 2 * C4 + 2 * C5)) K ν c :=
        mul_one _

/-- **Target (`PartIII-b:C/near/delta/5/1/1`)**: weighted bound for the stream completion of the
mean stream (`StreamMeanCompletion`, source lines 2703-2729), from `PartI.TrainMeanExpansion`. -/
theorem streamMeanCompletion :
    UnforcedLeray.Short.PartIIIb.NearInst.Delta.StreamMeanCompletion := by
  have hHN := UnforcedLeray.Short.PartI.overlap_highnorm_uniform
  have hFD0 := UnforcedLeray.Short.PartI.overlap_fluctuation_decay hHN
  have hMP := UnforcedLeray.Short.PartI.overlap_mean_primitive
  have hMD := UnforcedLeray.Short.PartI.overlap_mean_decay hHN hFD0 hMP
  have hOv := UnforcedLeray.Short.PartI.trainOverlap_proof hFD0 hMD
  have hVort := UnforcedLeray.Short.PartI.train_vorticity_gaussian_tail hOv
  have hTails := UnforcedLeray.Short.PartI.train_stream_velocity_pressure_tails hOv hVort
  have hFD := UnforcedLeray.Short.PartI.trainFluctuationDecay_proof hTails hFD0 hOv
  have hME := UnforcedLeray.Short.PartI.trainMeanExpansion_proof hTails hFD hMP
  exact streamMeanCompletion_of hME

end UnforcedLeray.Short.PartIIIb.NearInst.Delta
