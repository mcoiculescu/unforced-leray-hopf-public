import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_near_delta_5_1
import UnforcedLeray.Short.PartIIIa.T23_StressExactSplit.T23_1.LateFluctCompletion
import UnforcedLeray.Short.PartI.Tasks.TrainClass.BUCMeanStreamSmooth
import UnforcedLeray.Short.PartI.Tasks.OverlapHighNorm
import UnforcedLeray.Short.PartI.Tasks.OverlapFluctuationDecay
import UnforcedLeray.Short.PartI.Tasks.OverlapMeanPrimitive
import UnforcedLeray.Short.PartI.Tasks.OverlapMeanDecay
import UnforcedLeray.Short.PartI.Tasks.TrainOverlapProof
import UnforcedLeray.Short.PartI.Tasks.TrainVorticityTail
import UnforcedLeray.Short.PartI.Tasks.TrainStreamTails
import UnforcedLeray.Short.PartI.Tasks.TrainFluctuationDecayProof

/-!
# `PartIII-b:C/near/delta/5/1/2`: `StreamFluctCompletion` (source lines 2703-2729)

Source of record: `the November 2 reference manuscript`, lines 2703-2729 and
439-446 (`sct:fluctuation`).

Proves `streamFluctCompletion_of` from `PartI.TrainFluctuationDecay` and assembles the
unconditional target `streamFluctCompletion : StreamFluctCompletion`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.NearInst.Delta

open UnforcedLeray.Short.PartIIIb UnforcedLeray.Short.PartIIIb.Concrete
  UnforcedLeray.Cons.C03 UnforcedLeray.Short.IIIa

private theorem sqrt_mul_one_add_rpow_neg_half_le_one {s : ℝ} (hs : 0 ≤ s) :
    Real.sqrt s * (1 + s) ^ (-1 / 2 : ℝ) ≤ 1 := by
  have h1s : 0 < 1 + s := by linarith
  have hsq : Real.sqrt s ≤ Real.sqrt (1 + s) := Real.sqrt_le_sqrt (by linarith)
  have hpos : 0 < Real.sqrt (1 + s) := Real.sqrt_pos.mpr h1s
  have heq : (1 + s) ^ (-1 / 2 : ℝ) = (Real.sqrt (1 + s))⁻¹ := by
    rw [show (-1 / 2 : ℝ) = -(1 / 2 : ℝ) by ring, Real.rpow_neg h1s.le, ← Real.sqrt_eq_rpow]
  rw [heq, ← div_eq_mul_inv, div_le_one hpos]
  exact hsq

private theorem mul_inv_pow_le_polyP {C ν c : ℝ} (hC : 0 ≤ C) (N : ℕ) (hν : 0 < ν) (hc : 0 ≤ c) :
    C * ν⁻¹ ^ N ≤ UnforcedLeray.Short.PartI.polyP C N ν c := by
  unfold UnforcedLeray.Short.PartI.polyP
  have h1 : ν⁻¹ ≤ 1 + c + ν⁻¹ := by linarith
  have h0 : 0 ≤ ν⁻¹ := inv_nonneg.mpr hν.le
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ h0 h1 N) hC

/-- Conditional form: `StreamFluctCompletion` from `PartI.TrainFluctuationDecay`. -/
theorem streamFluctCompletion_of (h : UnforcedLeray.Short.PartI.TrainFluctuationDecay) :
    UnforcedLeray.Short.PartIIIb.NearInst.Delta.StreamFluctCompletion := by
  intro mZ hmZ
  have hmZ0 : 0 ≤ mZ := by linarith
  obtain ⟨C0, N0, κ0, ν0, hC0, hκ0, hν0, H0⟩ := h 2 (by norm_num) (⌈mZ⌉₊ + 1) 0 0
  obtain ⟨C1, N1, κ1, ν1, hC1, hκ1, hν1, H1⟩ := h 2 (by norm_num) (⌈mZ⌉₊ + 1) 1 0
  obtain ⟨C2, N2, κ2, ν2, hC2, hκ2, hν2, H2⟩ := h 2 (by norm_num) (⌈mZ⌉₊ + 1) 0 1
  set C_out : ℝ :=
    (|C0| * 3 ^ N0 + |C2| * 3 ^ N2 + 2 * (|C1| * 3 ^ N1)) *
      (1 + 2 * (min κ0 (min κ1 κ2))⁻¹) ^ 2
  set K_out : ℕ := 2 * (N0 + N1 + N2) + 10
  refine ⟨C_out, K_out, min (min ν0 ν1) (min ν2 1),
    lt_min (lt_min hν0 hν1) (lt_min hν2 one_pos), ?_⟩
  intro ν c tr hν0' hνle hc hbuc s hs0 q η
  have hνa : ν ≤ ν0 := (hνle.trans (min_le_left _ _)).trans (min_le_left _ _)
  have hνb : ν ≤ ν1 := (hνle.trans (min_le_left _ _)).trans (min_le_right _ _)
  have hνc : ν ≤ ν2 := (hνle.trans (min_le_right _ _)).trans (min_le_left _ _)
  have hν1' : ν ≤ 1 := (hνle.trans (min_le_right _ _)).trans (min_le_right _ _)
  have hcT := period_eq_trainPeriod hν0' hc
  subst hcT
  have hc2 : UnforcedLeray.Short.PartI.trainPeriod 2 ν = (ν ^ 2)⁻¹ := hc
  have hcpos : 0 < UnforcedLeray.Short.PartI.trainPeriod 2 ν := by
    rw [hc2]; positivity
  have hA : 0 < 1 + s := by linarith only [hs0]
  have hs2 : (0 : ℝ) ≤ 2 * s := mul_nonneg (by norm_num) hs0.le
  have hsm := UnforcedLeray.Short.PartI.bucMeanStreamSmooth ν _ hν0' hcpos tr hbuc
  have hH0 := H0 ν hν0' hνa tr hbuc s hs0
  have hH1 := H1 ν hν0' hνb tr hbuc s hs0
  have hH2 := H2 ν hν0' hνc tr hbuc s hs0
  dsimp only at hH0 hH1 hH2
  have ht1 : 1 ≤ ν⁻¹ := (one_le_inv₀ hν0').2 hν1'
  have hκpos : 0 < min κ0 (min κ1 κ2) := lt_min hκ0 (lt_min hκ1 hκ2)
  have hdiff : DifferentiableAt ℝ (fluctStream tr s) (q, η) := by
    have hG : DifferentiableAt ℝ
        (fun x : ℝ × ℝ => UnforcedLeray.Short.PartI.meanStream tr x.1 x.2) (s, η) :=
      (hsm.contDiffAt (IsOpen.mem_nhds (isOpen_Ioi.prod isOpen_univ)
        (Set.mk_mem_prod hs0 (Set.mem_univ _)))).differentiableAt (by simp)
    have hG2 : DifferentiableAt ℝ
        (fun z : ℝ × ℝ => UnforcedLeray.Short.PartI.meanStream tr s z.2) (q, η) :=
      DifferentiableAt.comp (q, η)
        (g := fun x : ℝ × ℝ => UnforcedLeray.Short.PartI.meanStream tr x.1 x.2)
        (f := fun z : ℝ × ℝ => (s, z.2)) hG (by fun_prop)
    exact ((tr.isTrain.stream_differentiable s hs0.le) (q, η)).sub hG2
  have hK0nn : 0 ≤ UnforcedLeray.Short.PartI.polyP C0 N0 ν
      (UnforcedLeray.Short.PartI.trainPeriod 2 ν) *
      Real.exp (-(κ0 * ν * s / (UnforcedLeray.Short.PartI.trainPeriod 2 ν) ^ 2)) :=
    mul_nonneg (lfc_polyP_nonneg hC0.le N0 hν0' hcpos.le) (Real.exp_nonneg _)
  have hK1nn : 0 ≤ UnforcedLeray.Short.PartI.polyP C1 N1 ν
      (UnforcedLeray.Short.PartI.trainPeriod 2 ν) *
      Real.exp (-(κ1 * ν * s / (UnforcedLeray.Short.PartI.trainPeriod 2 ν) ^ 2)) :=
    mul_nonneg (lfc_polyP_nonneg hC1.le N1 hν0' hcpos.le) (Real.exp_nonneg _)
  have hK2nn : 0 ≤ UnforcedLeray.Short.PartI.polyP C2 N2 ν
      (UnforcedLeray.Short.PartI.trainPeriod 2 ν) *
      Real.exp (-(κ2 * ν * s / (UnforcedLeray.Short.PartI.trainPeriod 2 ν) ^ 2)) :=
    mul_nonneg (lfc_polyP_nonneg hC2.le N2 hν0' hcpos.le) (Real.exp_nonneg _)
  have pt0 : Real.sqrt (UnforcedLeray.Train.jap (⌈mZ⌉₊ + 1) (q, η)) * |fluctStream tr s (q, η)| ≤
      UnforcedLeray.Short.PartI.polyP C0 N0 ν (UnforcedLeray.Short.PartI.trainPeriod 2 ν) *
      Real.exp (-(κ0 * ν * s / (UnforcedLeray.Short.PartI.trainPeriod 2 ν) ^ 2)) := by
    have h := lfc_pointwise_of_wSup hK0nn hH0.1.2 (q, η)
    rw [lfc_norm_ageJet_zero, Real.norm_eq_abs] at h
    exact h
  have pt1 : Real.sqrt (UnforcedLeray.Train.jap (⌈mZ⌉₊ + 1) (q, η)) *
      |deriv (fun r => fluctStream tr r (q, η)) s| ≤
      UnforcedLeray.Short.PartI.polyP C1 N1 ν (UnforcedLeray.Short.PartI.trainPeriod 2 ν) *
      Real.exp (-(κ1 * ν * s / (UnforcedLeray.Short.PartI.trainPeriod 2 ν) ^ 2)) := by
    have h := lfc_pointwise_of_wSup hK1nn hH1.1.2 (q, η)
    rw [lfc_norm_ageJet_one_zero, Real.norm_eq_abs] at h
    exact h
  have pt2 : Real.sqrt (UnforcedLeray.Train.jap (⌈mZ⌉₊ + 1) (q, η)) *
      ‖fderiv ℝ (fluctStream tr s) (q, η)‖ ≤
      UnforcedLeray.Short.PartI.polyP C2 N2 ν (UnforcedLeray.Short.PartI.trainPeriod 2 ν) *
      Real.exp (-(κ2 * ν * s / (UnforcedLeray.Short.PartI.trainPeriod 2 ν) ^ 2)) := by
    have h := lfc_pointwise_of_wSup hK2nn hH2.1.2 (q, η)
    rw [lfc_norm_ageJet_zero_one] at h
    exact h
  have hWM := lfc_W_le hmZ0 hs0.le q η
  have hWη := lfc_W_eta hmZ0 hs0.le q η
  have hW0 : 0 ≤ UnforcedLeray.Short.IIIa.transWeight mZ (s, (q, η)) := by
    unfold UnforcedLeray.Short.IIIa.transWeight; positivity
  have hder := lfc_abs_deriv_le (fluctStream tr s) q η hdiff
  have hraw : |UnforcedLeray.Cons.C03.raisedStream (fluctStream tr) s q η| ≤
      |fluctStream tr s (q, η)| + |η| * ‖fderiv ℝ (fluctStream tr s) (q, η)‖ +
        2 * s * |deriv (fun t => fluctStream tr t (q, η)) s| := by
    unfold UnforcedLeray.Cons.C03.raisedStream
    have h1 : |η * deriv (fun t => fluctStream tr s (q, t)) η +
        2 * s * deriv (fun t => fluctStream tr t (q, η)) s| ≤
        |η| * ‖fderiv ℝ (fluctStream tr s) (q, η)‖ +
          2 * s * |deriv (fun t => fluctStream tr t (q, η)) s| := by
      calc _ ≤ |η * deriv (fun t => fluctStream tr s (q, t)) η| +
            |2 * s * deriv (fun t => fluctStream tr t (q, η)) s| := abs_add_le _ _
        _ = |η| * |deriv (fun t => fluctStream tr s (q, t)) η| +
            2 * s * |deriv (fun t => fluctStream tr t (q, η)) s| := by
          rw [abs_mul, abs_mul, abs_of_nonneg hs2]
        _ ≤ |η| * ‖fderiv ℝ (fluctStream tr s) (q, η)‖ +
            2 * s * |deriv (fun t => fluctStream tr t (q, η)) s| :=
          add_le_add (mul_le_mul_of_nonneg_left hder (abs_nonneg η)) le_rfl
    calc _ ≤ |fluctStream tr s (q, η)| + |η * deriv (fun t => fluctStream tr s (q, t)) η +
            2 * s * deriv (fun t => fluctStream tr t (q, η)) s| := abs_sub _ _
      _ ≤ _ := (add_le_add le_rfl h1).trans_eq (add_assoc _ _ _).symm
  have e0 : UnforcedLeray.Short.IIIa.transWeight mZ (s, (q, η)) * |fluctStream tr s (q, η)| ≤
      UnforcedLeray.Short.PartI.polyP C0 N0 ν (UnforcedLeray.Short.PartI.trainPeriod 2 ν) *
      Real.exp (-(κ0 * ν * s / (UnforcedLeray.Short.PartI.trainPeriod 2 ν) ^ 2)) :=
    le_trans (mul_le_mul_of_nonneg_right hWM (abs_nonneg _)) pt0
  have e2 : UnforcedLeray.Short.IIIa.transWeight mZ (s, (q, η)) * |η| *
      ‖fderiv ℝ (fluctStream tr s) (q, η)‖ ≤
      UnforcedLeray.Short.PartI.polyP C2 N2 ν (UnforcedLeray.Short.PartI.trainPeriod 2 ν) *
      Real.exp (-(κ2 * ν * s / (UnforcedLeray.Short.PartI.trainPeriod 2 ν) ^ 2)) :=
    le_trans (mul_le_mul_of_nonneg_right hWη (norm_nonneg _)) pt2
  have e1' : UnforcedLeray.Short.IIIa.transWeight mZ (s, (q, η)) *
      |deriv (fun t => fluctStream tr t (q, η)) s| ≤
      UnforcedLeray.Short.PartI.polyP C1 N1 ν (UnforcedLeray.Short.PartI.trainPeriod 2 ν) *
      Real.exp (-(κ1 * ν * s / (UnforcedLeray.Short.PartI.trainPeriod 2 ν) ^ 2)) :=
    le_trans (mul_le_mul_of_nonneg_right hWM (abs_nonneg _)) pt1
  have e1 : 2 * s * (UnforcedLeray.Short.IIIa.transWeight mZ (s, (q, η)) *
      |deriv (fun t => fluctStream tr t (q, η)) s|) ≤
      2 * s * (UnforcedLeray.Short.PartI.polyP C1 N1 ν (UnforcedLeray.Short.PartI.trainPeriod 2 ν) *
      Real.exp (-(κ1 * ν * s / (UnforcedLeray.Short.PartI.trainPeriod 2 ν) ^ 2))) :=
    mul_le_mul_of_nonneg_left e1' hs2
  have hmain : UnforcedLeray.Short.IIIa.transWeight mZ (s, (q, η)) *
      |UnforcedLeray.Cons.C03.raisedStream (fluctStream tr) s q η| ≤
      UnforcedLeray.Short.PartI.polyP C0 N0 ν (UnforcedLeray.Short.PartI.trainPeriod 2 ν) *
        Real.exp (-(κ0 * ν * s / (UnforcedLeray.Short.PartI.trainPeriod 2 ν) ^ 2)) +
      UnforcedLeray.Short.PartI.polyP C2 N2 ν (UnforcedLeray.Short.PartI.trainPeriod 2 ν) *
        Real.exp (-(κ2 * ν * s / (UnforcedLeray.Short.PartI.trainPeriod 2 ν) ^ 2)) +
      2 * s * (UnforcedLeray.Short.PartI.polyP C1 N1 ν (UnforcedLeray.Short.PartI.trainPeriod 2 ν) *
        Real.exp (-(κ1 * ν * s / (UnforcedLeray.Short.PartI.trainPeriod 2 ν) ^ 2))) := by
    have hW0' := mul_le_mul_of_nonneg_left hraw hW0
    have hsplit : UnforcedLeray.Short.IIIa.transWeight mZ (s, (q, η)) *
        (|fluctStream tr s (q, η)| + |η| * ‖fderiv ℝ (fluctStream tr s) (q, η)‖ +
          2 * s * |deriv (fun t => fluctStream tr t (q, η)) s|) =
        UnforcedLeray.Short.IIIa.transWeight mZ (s, (q, η)) * |fluctStream tr s (q, η)| +
          UnforcedLeray.Short.IIIa.transWeight mZ (s, (q, η)) * |η| *
            ‖fderiv ℝ (fluctStream tr s) (q, η)‖ +
          2 * s * (UnforcedLeray.Short.IIIa.transWeight mZ (s, (q, η)) *
            |deriv (fun t => fluctStream tr t (q, η)) s|) := by
      ring
    exact le_trans hW0' (hsplit ▸ add_le_add (add_le_add e0 e2) e1)
  have eE0 : Real.exp (-(κ0 * ν * s / (UnforcedLeray.Short.PartI.trainPeriod 2 ν) ^ 2)) ≤
      Real.exp (-((min κ0 (min κ1 κ2) * ν ^ 5) * s)) := by
    have e : κ0 * ν * s / (UnforcedLeray.Short.PartI.trainPeriod 2 ν) ^ 2 = κ0 * ν ^ 5 * s := by
      rw [hc2, inv_pow, div_inv_eq_mul]; ring
    rw [e]
    apply Real.exp_le_exp.2
    exact neg_le_neg (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (min_le_left κ0 (min κ1 κ2)) (pow_nonneg hν0'.le 5)) hs0.le)
  have eE1 : Real.exp (-(κ1 * ν * s / (UnforcedLeray.Short.PartI.trainPeriod 2 ν) ^ 2)) ≤
      Real.exp (-((min κ0 (min κ1 κ2) * ν ^ 5) * s)) := by
    have e : κ1 * ν * s / (UnforcedLeray.Short.PartI.trainPeriod 2 ν) ^ 2 = κ1 * ν ^ 5 * s := by
      rw [hc2, inv_pow, div_inv_eq_mul]; ring
    rw [e]
    apply Real.exp_le_exp.2
    exact neg_le_neg (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right ((min_le_right κ0 (min κ1 κ2)).trans (min_le_left κ1 κ2))
        (pow_nonneg hν0'.le 5)) hs0.le)
  have eE2 : Real.exp (-(κ2 * ν * s / (UnforcedLeray.Short.PartI.trainPeriod 2 ν) ^ 2)) ≤
      Real.exp (-((min κ0 (min κ1 κ2) * ν ^ 5) * s)) := by
    have e : κ2 * ν * s / (UnforcedLeray.Short.PartI.trainPeriod 2 ν) ^ 2 = κ2 * ν ^ 5 * s := by
      rw [hc2, inv_pow, div_inv_eq_mul]; ring
    rw [e]
    apply Real.exp_le_exp.2
    exact neg_le_neg (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right ((min_le_right κ0 (min κ1 κ2)).trans (min_le_right κ1 κ2))
        (pow_nonneg hν0'.le 5)) hs0.le)
  have hdec := lfc_decay_exp (mul_pos hκpos (pow_pos hν0' 5)) hs0.le
  have hP0 : UnforcedLeray.Short.PartI.polyP C0 N0 ν (UnforcedLeray.Short.PartI.trainPeriod 2 ν) ≤
      |C0| * 3 ^ N0 * ν⁻¹ ^ (2 * (N0 + N1 + N2)) := by
    rw [hc2]
    exact le_trans (UnforcedLeray.Short.IIIa.polyP_le_inv_pow C0 N0 hν0' hν1')
      (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ ht1 (by omega)) (by positivity))
  have hP1 : UnforcedLeray.Short.PartI.polyP C1 N1 ν (UnforcedLeray.Short.PartI.trainPeriod 2 ν) ≤
      |C1| * 3 ^ N1 * ν⁻¹ ^ (2 * (N0 + N1 + N2)) := by
    rw [hc2]
    exact le_trans (UnforcedLeray.Short.IIIa.polyP_le_inv_pow C1 N1 hν0' hν1')
      (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ ht1 (by omega)) (by positivity))
  have hP2 : UnforcedLeray.Short.PartI.polyP C2 N2 ν (UnforcedLeray.Short.PartI.trainPeriod 2 ν) ≤
      |C2| * 3 ^ N2 * ν⁻¹ ^ (2 * (N0 + N1 + N2)) := by
    rw [hc2]
    exact le_trans (UnforcedLeray.Short.IIIa.polyP_le_inv_pow C2 N2 hν0' hν1')
      (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ ht1 (by omega)) (by positivity))
  have hP0nn : 0 ≤ UnforcedLeray.Short.PartI.polyP C0 N0 ν
      (UnforcedLeray.Short.PartI.trainPeriod 2 ν) :=
    lfc_polyP_nonneg hC0.le N0 hν0' hcpos.le
  have hP1nn : 0 ≤ UnforcedLeray.Short.PartI.polyP C1 N1 ν
      (UnforcedLeray.Short.PartI.trainPeriod 2 ν) :=
    lfc_polyP_nonneg hC1.le N1 hν0' hcpos.le
  have hP2nn : 0 ≤ UnforcedLeray.Short.PartI.polyP C2 N2 ν
      (UnforcedLeray.Short.PartI.trainPeriod 2 ν) :=
    lfc_polyP_nonneg hC2.le N2 hν0' hcpos.le
  have hPsum : UnforcedLeray.Short.PartI.polyP C0 N0 ν (UnforcedLeray.Short.PartI.trainPeriod 2 ν) +
      UnforcedLeray.Short.PartI.polyP C2 N2 ν (UnforcedLeray.Short.PartI.trainPeriod 2 ν) +
      2 * UnforcedLeray.Short.PartI.polyP C1 N1 ν (UnforcedLeray.Short.PartI.trainPeriod 2 ν) ≤
      (|C0| * 3 ^ N0 + |C2| * 3 ^ N2 + 2 * (|C1| * 3 ^ N1)) * ν⁻¹ ^ (2 * (N0 + N1 + N2)) := by
    have h := add_le_add (add_le_add hP0 hP2)
      (mul_le_mul_of_nonneg_left hP1 (by norm_num : (0 : ℝ) ≤ 2))
    exact h.trans_eq (by ring)
  have hGle : (1 + 2 * (min κ0 (min κ1 κ2) * ν ^ 5)⁻¹) ^ 2 ≤
      (1 + 2 * (min κ0 (min κ1 κ2))⁻¹) ^ 2 * ν⁻¹ ^ 10 := by
    have ht5 : 1 ≤ ν⁻¹ ^ 5 := one_le_pow₀ ht1
    have e : (min κ0 (min κ1 κ2) * ν ^ 5)⁻¹ = (min κ0 (min κ1 κ2))⁻¹ * ν⁻¹ ^ 5 := by
      rw [mul_inv, ← inv_pow]
    have h1 : 1 + 2 * (min κ0 (min κ1 κ2) * ν ^ 5)⁻¹ ≤
        (1 + 2 * (min κ0 (min κ1 κ2))⁻¹) * ν⁻¹ ^ 5 := by
      rw [e]
      have key : (1 + 2 * (min κ0 (min κ1 κ2))⁻¹) * ν⁻¹ ^ 5 =
          1 + 2 * ((min κ0 (min κ1 κ2))⁻¹ * ν⁻¹ ^ 5) + (ν⁻¹ ^ 5 - 1) := by ring
      rw [key]
      linarith only [ht5]
    have hk : 0 ≤ (min κ0 (min κ1 κ2) * ν ^ 5)⁻¹ :=
      inv_nonneg.2 (mul_nonneg hκpos.le (pow_nonneg hν0'.le 5))
    have hnn : 0 ≤ 1 + 2 * (min κ0 (min κ1 κ2) * ν ^ 5)⁻¹ := by
      linarith only [hk]
    have h2 := pow_le_pow_left₀ hnn h1 2
    calc (1 + 2 * (min κ0 (min κ1 κ2) * ν ^ 5)⁻¹) ^ 2
        ≤ ((1 + 2 * (min κ0 (min κ1 κ2))⁻¹) * ν⁻¹ ^ 5) ^ 2 := h2
      _ = (1 + 2 * (min κ0 (min κ1 κ2))⁻¹) ^ 2 * ν⁻¹ ^ 10 := by ring
  have hu0 : 0 ≤ (1 + s) ^ (-1 / 2 : ℝ) := Real.rpow_nonneg hA.le _
  have hG0 : 0 ≤ (1 + 2 * (min κ0 (min κ1 κ2) * ν ^ 5)⁻¹) ^ 2 := by positivity
  have hQ : 0 ≤ ν⁻¹ ^ (2 * (N0 + N1 + N2)) := pow_nonneg (inv_nonneg.2 hν0'.le) _
  have hKc : 0 ≤ |C0| * 3 ^ N0 + |C2| * 3 ^ N2 + 2 * (|C1| * 3 ^ N1) := by positivity
  have hstep1 : UnforcedLeray.Short.IIIa.transWeight mZ (s, (q, η)) *
        |UnforcedLeray.Cons.C03.raisedStream (fluctStream tr) s q η| ≤
      UnforcedLeray.Short.PartI.polyP C0 N0 ν (UnforcedLeray.Short.PartI.trainPeriod 2 ν) *
          Real.exp (-((min κ0 (min κ1 κ2) * ν ^ 5) * s)) +
        UnforcedLeray.Short.PartI.polyP C2 N2 ν (UnforcedLeray.Short.PartI.trainPeriod 2 ν) *
          Real.exp (-((min κ0 (min κ1 κ2) * ν ^ 5) * s)) +
        2 * UnforcedLeray.Short.PartI.polyP C1 N1 ν (UnforcedLeray.Short.PartI.trainPeriod 2 ν) *
          ((1 + s) * Real.exp (-((min κ0 (min κ1 κ2) * ν ^ 5) * s))) := by
    have f0 := mul_le_mul_of_nonneg_left eE0 hP0nn
    have f2 := mul_le_mul_of_nonneg_left eE2 hP2nn
    have f1 : 2 * s * (UnforcedLeray.Short.PartI.polyP C1 N1 ν
        (UnforcedLeray.Short.PartI.trainPeriod 2 ν) *
        Real.exp (-(κ1 * ν * s / (UnforcedLeray.Short.PartI.trainPeriod 2 ν) ^ 2))) ≤
        2 * UnforcedLeray.Short.PartI.polyP C1 N1 ν (UnforcedLeray.Short.PartI.trainPeriod 2 ν) *
          ((1 + s) * Real.exp (-((min κ0 (min κ1 κ2) * ν ^ 5) * s))) := by
      have a1 := mul_le_mul_of_nonneg_left eE1 hP1nn
      have a2 := mul_le_mul_of_nonneg_left a1 hs2
      have a3 : 2 * s * (UnforcedLeray.Short.PartI.polyP C1 N1 ν
          (UnforcedLeray.Short.PartI.trainPeriod 2 ν) *
          Real.exp (-((min κ0 (min κ1 κ2) * ν ^ 5) * s))) ≤
          2 * UnforcedLeray.Short.PartI.polyP C1 N1 ν (UnforcedLeray.Short.PartI.trainPeriod 2 ν) *
            ((1 + s) * Real.exp (-((min κ0 (min κ1 κ2) * ν ^ 5) * s))) := by
        have hid : 2 * UnforcedLeray.Short.PartI.polyP C1 N1 ν
            (UnforcedLeray.Short.PartI.trainPeriod 2 ν) *
            ((1 + s) * Real.exp (-((min κ0 (min κ1 κ2) * ν ^ 5) * s))) =
            2 * s * (UnforcedLeray.Short.PartI.polyP C1 N1 ν
              (UnforcedLeray.Short.PartI.trainPeriod 2 ν) *
              Real.exp (-((min κ0 (min κ1 κ2) * ν ^ 5) * s))) +
            2 * (UnforcedLeray.Short.PartI.polyP C1 N1 ν
              (UnforcedLeray.Short.PartI.trainPeriod 2 ν) *
              Real.exp (-((min κ0 (min κ1 κ2) * ν ^ 5) * s))) := by ring
        rw [hid]
        exact le_add_of_nonneg_right
          (mul_nonneg (by norm_num) (mul_nonneg hP1nn (Real.exp_nonneg _)))
      exact le_trans a2 a3
    exact le_trans hmain (add_le_add (add_le_add f0 f2) f1)
  have hstep2 : UnforcedLeray.Short.PartI.polyP C0 N0 ν (UnforcedLeray.Short.PartI.trainPeriod 2 ν) *
          Real.exp (-((min κ0 (min κ1 κ2) * ν ^ 5) * s)) +
        UnforcedLeray.Short.PartI.polyP C2 N2 ν (UnforcedLeray.Short.PartI.trainPeriod 2 ν) *
          Real.exp (-((min κ0 (min κ1 κ2) * ν ^ 5) * s)) +
        2 * UnforcedLeray.Short.PartI.polyP C1 N1 ν (UnforcedLeray.Short.PartI.trainPeriod 2 ν) *
          ((1 + s) * Real.exp (-((min κ0 (min κ1 κ2) * ν ^ 5) * s))) ≤
      UnforcedLeray.Short.PartI.polyP C0 N0 ν (UnforcedLeray.Short.PartI.trainPeriod 2 ν) *
          ((1 + 2 * (min κ0 (min κ1 κ2) * ν ^ 5)⁻¹) ^ 2 * (1 + s) ^ (-1 / 2 : ℝ)) +
        UnforcedLeray.Short.PartI.polyP C2 N2 ν (UnforcedLeray.Short.PartI.trainPeriod 2 ν) *
          ((1 + 2 * (min κ0 (min κ1 κ2) * ν ^ 5)⁻¹) ^ 2 * (1 + s) ^ (-1 / 2 : ℝ)) +
        2 * UnforcedLeray.Short.PartI.polyP C1 N1 ν (UnforcedLeray.Short.PartI.trainPeriod 2 ν) *
          ((1 + 2 * (min κ0 (min κ1 κ2) * ν ^ 5)⁻¹) ^ 2 * (1 + s) ^ (-1 / 2 : ℝ)) := by
    have g0 := mul_le_mul_of_nonneg_left hdec.2 hP0nn
    have g2 := mul_le_mul_of_nonneg_left hdec.2 hP2nn
    have g1 := mul_le_mul_of_nonneg_left hdec.1
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hP1nn)
    exact add_le_add (add_le_add g0 g2) g1
  have hstep3 : (UnforcedLeray.Short.PartI.polyP C0 N0 ν (UnforcedLeray.Short.PartI.trainPeriod 2 ν) +
          UnforcedLeray.Short.PartI.polyP C2 N2 ν (UnforcedLeray.Short.PartI.trainPeriod 2 ν) +
          2 * UnforcedLeray.Short.PartI.polyP C1 N1 ν (UnforcedLeray.Short.PartI.trainPeriod 2 ν)) *
          ((1 + 2 * (min κ0 (min κ1 κ2) * ν ^ 5)⁻¹) ^ 2 * (1 + s) ^ (-1 / 2 : ℝ)) ≤
      ((|C0| * 3 ^ N0 + |C2| * 3 ^ N2 + 2 * (|C1| * 3 ^ N1)) * ν⁻¹ ^ (2 * (N0 + N1 + N2))) *
          ((1 + 2 * (min κ0 (min κ1 κ2))⁻¹) ^ 2 * ν⁻¹ ^ 10 * (1 + s) ^ (-1 / 2 : ℝ)) :=
    mul_le_mul hPsum (mul_le_mul_of_nonneg_right hGle hu0) (mul_nonneg hG0 hu0) (mul_nonneg hKc hQ)
  have hlast : ((|C0| * 3 ^ N0 + |C2| * 3 ^ N2 + 2 * (|C1| * 3 ^ N1)) * ν⁻¹ ^ (2 * (N0 + N1 + N2))) *
          ((1 + 2 * (min κ0 (min κ1 κ2))⁻¹) ^ 2 * ν⁻¹ ^ 10 * (1 + s) ^ (-1 / 2 : ℝ)) =
      C_out * ν⁻¹ ^ K_out * (1 + s) ^ (-1 / 2 : ℝ) := by
    dsimp [C_out, K_out]
    rw [pow_add]; ring
  have hmid : (UnforcedLeray.Short.PartI.polyP C0 N0 ν (UnforcedLeray.Short.PartI.trainPeriod 2 ν) +
          UnforcedLeray.Short.PartI.polyP C2 N2 ν (UnforcedLeray.Short.PartI.trainPeriod 2 ν) +
          2 * UnforcedLeray.Short.PartI.polyP C1 N1 ν (UnforcedLeray.Short.PartI.trainPeriod 2 ν)) *
          ((1 + 2 * (min κ0 (min κ1 κ2) * ν ^ 5)⁻¹) ^ 2 * (1 + s) ^ (-1 / 2 : ℝ)) =
      UnforcedLeray.Short.PartI.polyP C0 N0 ν (UnforcedLeray.Short.PartI.trainPeriod 2 ν) *
          ((1 + 2 * (min κ0 (min κ1 κ2) * ν ^ 5)⁻¹) ^ 2 * (1 + s) ^ (-1 / 2 : ℝ)) +
        UnforcedLeray.Short.PartI.polyP C2 N2 ν (UnforcedLeray.Short.PartI.trainPeriod 2 ν) *
          ((1 + 2 * (min κ0 (min κ1 κ2) * ν ^ 5)⁻¹) ^ 2 * (1 + s) ^ (-1 / 2 : ℝ)) +
        2 * UnforcedLeray.Short.PartI.polyP C1 N1 ν (UnforcedLeray.Short.PartI.trainPeriod 2 ν) *
          ((1 + 2 * (min κ0 (min κ1 κ2) * ν ^ 5)⁻¹) ^ 2 * (1 + s) ^ (-1 / 2 : ℝ)) := by
    ring
  have hbound : UnforcedLeray.Short.IIIa.transWeight mZ (s, (q, η)) *
      |UnforcedLeray.Cons.C03.raisedStream (fluctStream tr) s q η| ≤
      C_out * ν⁻¹ ^ K_out * (1 + s) ^ (-1 / 2 : ℝ) :=
    le_trans hstep1 (le_trans hstep2 (le_trans (le_of_eq hmid.symm)
      (le_trans hstep3 (le_of_eq hlast))))
  have hCout : 0 ≤ C_out := by dsimp [C_out]; positivity
  have hCK : 0 ≤ C_out * ν⁻¹ ^ K_out := mul_nonneg hCout (pow_nonneg (inv_nonneg.2 hν0'.le) K_out)
  calc Real.sqrt s * UnforcedLeray.Short.IIIa.transWeight mZ (s, (q, η)) *
        |raisedStream (fun r z => tr.ψ r z -
          UnforcedLeray.Short.PartI.hmean (UnforcedLeray.Short.PartI.trainPeriod 2 ν)
            (tr.ψ r) z.2) s q η|
      = Real.sqrt s * (UnforcedLeray.Short.IIIa.transWeight mZ (s, (q, η)) *
          |UnforcedLeray.Cons.C03.raisedStream (fluctStream tr) s q η|) := by
        change Real.sqrt s * UnforcedLeray.Short.IIIa.transWeight mZ (s, (q, η)) *
            |UnforcedLeray.Cons.C03.raisedStream (fluctStream tr) s q η| = _
        ring
    _ ≤ Real.sqrt s * (C_out * ν⁻¹ ^ K_out * (1 + s) ^ (-1 / 2 : ℝ)) :=
        mul_le_mul_of_nonneg_left hbound (Real.sqrt_nonneg s)
    _ = (C_out * ν⁻¹ ^ K_out) * (Real.sqrt s * (1 + s) ^ (-1 / 2 : ℝ)) := by ring
    _ ≤ (C_out * ν⁻¹ ^ K_out) * 1 :=
        mul_le_mul_of_nonneg_left (sqrt_mul_one_add_rpow_neg_half_le_one hs0.le) hCK
    _ = C_out * ν⁻¹ ^ K_out := mul_one _
    _ ≤ UnforcedLeray.Short.PartI.polyP C_out K_out ν
          (UnforcedLeray.Short.PartI.trainPeriod 2 ν) :=
        mul_inv_pow_le_polyP hCout K_out hν0' hcpos.le

/-- **Target (`PartIII-b:C/near/delta/5/1/2`)**: weighted bound for the stream completion of the
fluctuation stream (`StreamFluctCompletion`, source lines 2703-2729). -/
theorem streamFluctCompletion :
    UnforcedLeray.Short.PartIIIb.NearInst.Delta.StreamFluctCompletion := by
  have hHN : UnforcedLeray.Short.PartI.OverlapHighNormUniform :=
    UnforcedLeray.Short.PartI.overlap_highnorm_uniform
  have hFD0 : UnforcedLeray.Short.PartI.OverlapFluctuationDecay :=
    UnforcedLeray.Short.PartI.overlap_fluctuation_decay hHN
  have hMP : UnforcedLeray.Short.PartI.OverlapMeanPrimitive :=
    UnforcedLeray.Short.PartI.overlap_mean_primitive
  have hMD : UnforcedLeray.Short.PartI.OverlapMeanDecay :=
    UnforcedLeray.Short.PartI.overlap_mean_decay hHN hFD0 hMP
  have hOv : UnforcedLeray.Short.PartI.TrainOverlap :=
    UnforcedLeray.Short.PartI.trainOverlap_proof hFD0 hMD
  have hVort : UnforcedLeray.Short.PartI.TrainVorticityGaussianTail :=
    UnforcedLeray.Short.PartI.train_vorticity_gaussian_tail hOv
  have hTails : UnforcedLeray.Short.PartI.TrainStreamVelocityPressureTails :=
    UnforcedLeray.Short.PartI.train_stream_velocity_pressure_tails hOv hVort
  exact streamFluctCompletion_of
    (UnforcedLeray.Short.PartI.trainFluctuationDecay_proof hTails hFD0 hOv)

end UnforcedLeray.Short.PartIIIb.NearInst.Delta
