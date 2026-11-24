import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_8_2_1_3.Bound.Fin2

/-!
# The nine entries (`PartIII-b:C/rep/8/2/1/3/b`, helper 9)

Source lines 5460-5465, 5036-5045.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete.RingFrameD2BoundAux

open UnforcedLeray.Short.PartIIIb.Concrete UnforcedLeray.Axi
open UnforcedLeray.Short.PartIIIb.Concrete.RingChartRawD2Sub

theorem flatDir_zero : flatDir 0 = ((1 : ℝ), (0 : ℝ)) := by simp [flatDir]
theorem flatDir_two : flatDir 2 = ((0 : ℝ), (1 : ℝ)) := by simp [flatDir]

theorem lead_qq {F : Zc → Merid} (hF : ContDiff ℝ ∞ F) (z : Zc) :
    Gop 1 0 0 0 0 (Gop 1 0 0 0 0 F) z =
      fderiv ℝ (fderiv ℝ F) z ((0 : ℝ), ((1 : ℝ), (0 : ℝ))) ((0 : ℝ), ((1 : ℝ), (0 : ℝ))) := by
  rw [dir_eq_Dq F]
  rw [dir_eq_Dq (fun z' => fderiv ℝ F z' ((0 : ℝ), ((1 : ℝ), (0 : ℝ))))]
  exact fderiv_dir_dir hF _ _ z

theorem lead_qe {F : Zc → Merid} (hF : ContDiff ℝ ∞ F) (z : Zc) :
    Gop 1 0 0 0 0 (Zo F) z =
      fderiv ℝ (fderiv ℝ F) z ((0 : ℝ), ((1 : ℝ), (0 : ℝ))) ((0 : ℝ), ((0 : ℝ), (1 : ℝ))) := by
  rw [dir_eq_Zo F]
  rw [dir_eq_Dq (fun z' => fderiv ℝ F z' ((0 : ℝ), ((0 : ℝ), (1 : ℝ))))]
  exact fderiv_dir_dir hF _ _ z

theorem lead_eq {F : Zc → Merid} (hF : ContDiff ℝ ∞ F) (z : Zc) :
    Zo (Gop 1 0 0 0 0 F) z =
      fderiv ℝ (fderiv ℝ F) z ((0 : ℝ), ((0 : ℝ), (1 : ℝ))) ((0 : ℝ), ((1 : ℝ), (0 : ℝ))) := by
  rw [dir_eq_Dq F]
  rw [dir_eq_Zo (fun z' => fderiv ℝ F z' ((0 : ℝ), ((1 : ℝ), (0 : ℝ))))]
  exact fderiv_dir_dir hF _ _ z

theorem lead_ee {F : Zc → Merid} (hF : ContDiff ℝ ∞ F) (z : Zc) :
    Zo (Zo F) z =
      fderiv ℝ (fderiv ℝ F) z ((0 : ℝ), ((0 : ℝ), (1 : ℝ))) ((0 : ℝ), ((0 : ℝ), (1 : ℝ))) := by
  rw [dir_eq_Zo F]
  rw [dir_eq_Zo (fun z' => fderiv ℝ F z' ((0 : ℝ), ((0 : ℝ), (1 : ℝ))))]
  exact fderiv_dir_dir hF _ _ z

/-- Template for the four entries with a nonzero flat part. -/
theorem second_template (L : ReturnLevel) (z : Zc) (j l : Fin 3) (E : Merid)
    (hring : ringFrameD2 L.ε (bSqrt (bRaw L)) (phi z) j l = wt (3 / 2) z • merSp E)
    (lead : Merid)
    (hlead : lead = fderiv ℝ (fderiv ℝ (trainFv L)) z ((0 : ℝ), flatDir j) ((0 : ℝ), flatDir l)) :
    ‖ringFrameD2 L.ε (bSqrt (bRaw L)) (phi z) j l -
        (phi z).1 ^ (3 / 2 : ℝ) • vecSp (flatD2 L (phi z).1 (phi z).2 j l)‖ =
      wt (3 / 2) z * ‖E - lead‖ := by
  have hflat : (phi z).1 ^ (3 / 2 : ℝ) • vecSp (flatD2 L (phi z).1 (phi z).2 j l) =
      wt (3 / 2) z • merSp lead := by
    show (Real.exp z.1) ^ (3 / 2 : ℝ) • vecSp (flatD2 L (Real.exp z.1) z.2 j l) = _
    rw [← wt_three_half, vecSp_flatD2, hlead]
  rw [hring, hflat, ← smul_sub, ← merSp_sub, norm_smul, norm_merSp, Real.norm_eq_abs,
    abs_of_pos (wt_pos _ _)]

theorem fin_mul {ε t w M : ℝ} (hw : 1 ≤ w) (hε : 0 ≤ ε) (ht : 0 ≤ t) (hM : 0 ≤ M) {c : ℝ}
    (hc : 0 ≤ c) (hc' : c ≤ 343) :
    t * (ε * (c * M)) ≤ 343 * ε * t * w ^ 3 * M := by
  have h3 : 1 ≤ w ^ 3 := one_le_pow₀ hw
  have : c * M ≤ 343 * w ^ 3 * M := by
    have : c ≤ 343 * w ^ 3 := by nlinarith
    exact mul_le_mul_of_nonneg_right this hM
  have := mul_le_mul_of_nonneg_left this (mul_nonneg ht hε)
  nlinarith

theorem diff00 (L : ReturnLevel) (h1 : L.ε ≤ 1) (z : Zc) :
    ‖ringFrameD2 L.ε (bSqrt (bRaw L)) (phi z) 0 0 -
        (phi z).1 ^ (3 / 2 : ℝ) • vecSp (flatD2 L (phi z).1 (phi z).2 0 0)‖ ≤
      343 * L.ε * wt (3 / 2) z * (1 + |z.2.2|) ^ 3 * Mz L z := by
  rw [second_template L z 0 0 (Pm L.ε 2 (Pm L.ε 1 (rawPhi L)) z)
    (by rw [ringFrameD2_00, DrhoDrho_B, merSp_smul])
    (Gop 1 0 0 0 0 (Gop 1 0 0 0 0 (trainFv L)) z)
    (by rw [lead_qq (contDiff_trainFv L), flatDir_zero])]
  have e := entry00_gen L.ε_pos.le h1 (contDiff_trainFv L) (contDiff_hTil L) z
  rw [← rawPhi_eq] at e
  have hw : 1 ≤ 1 + |z.2.2| := by linarith [abs_nonneg z.2.2]
  have n := num1 hw L.ε_pos.le (J_nonneg 2 (trainFv L) z) (J_nonneg 3 (trainFpsi L) z) (hJ2h L z)
  have ht := (wt_pos (3 / 2) z).le
  unfold Mz
  nlinarith [mul_le_mul_of_nonneg_left (e.trans n) ht]

theorem diff02 (L : ReturnLevel) (h1 : L.ε ≤ 1) (z : Zc) :
    ‖ringFrameD2 L.ε (bSqrt (bRaw L)) (phi z) 0 2 -
        (phi z).1 ^ (3 / 2 : ℝ) • vecSp (flatD2 L (phi z).1 (phi z).2 0 2)‖ ≤
      343 * L.ε * wt (3 / 2) z * (1 + |z.2.2|) ^ 3 * Mz L z := by
  rw [second_template L z 0 2 (Pm L.ε 2 (Zo (rawPhi L)) z)
    (by rw [ringFrameD2_02, DrhoDz_B, merSp_smul])
    (Gop 1 0 0 0 0 (Zo (trainFv L)) z)
    (by rw [lead_qe (contDiff_trainFv L), flatDir_zero, flatDir_two])]
  have e := entry02_gen L.ε_pos.le h1 (contDiff_trainFv L) (contDiff_hTil L) z
  rw [← rawPhi_eq] at e
  have hw : 1 ≤ 1 + |z.2.2| := by linarith [abs_nonneg z.2.2]
  have n := num2 hw L.ε_pos.le (J_nonneg 2 (trainFv L) z) (J_nonneg 3 (trainFpsi L) z) (hJ2h L z)
  have ht := (wt_pos (3 / 2) z).le
  unfold Mz
  nlinarith [mul_le_mul_of_nonneg_left (e.trans n) ht]

theorem diff20 (L : ReturnLevel) (h1 : L.ε ≤ 1) (z : Zc) :
    ‖ringFrameD2 L.ε (bSqrt (bRaw L)) (phi z) 2 0 -
        (phi z).1 ^ (3 / 2 : ℝ) • vecSp (flatD2 L (phi z).1 (phi z).2 2 0)‖ ≤
      343 * L.ε * wt (3 / 2) z * (1 + |z.2.2|) ^ 3 * Mz L z := by
  rw [second_template L z 2 0 (Zo (Pm L.ε 1 (rawPhi L)) z)
    (by rw [ringFrameD2_20, DzDrho_B, merSp_smul])
    (Zo (Gop 1 0 0 0 0 (trainFv L)) z)
    (by rw [lead_eq (contDiff_trainFv L), flatDir_zero, flatDir_two])]
  have e := entry20_gen L.ε_pos.le h1 (contDiff_trainFv L) (contDiff_hTil L) z
  rw [← rawPhi_eq] at e
  have hw : 1 ≤ 1 + |z.2.2| := by linarith [abs_nonneg z.2.2]
  have n := num2 hw L.ε_pos.le (J_nonneg 2 (trainFv L) z) (J_nonneg 3 (trainFpsi L) z) (hJ2h L z)
  have ht := (wt_pos (3 / 2) z).le
  unfold Mz
  nlinarith [mul_le_mul_of_nonneg_left (e.trans n) ht]

theorem diff22 (L : ReturnLevel) (h1 : L.ε ≤ 1) (z : Zc) :
    ‖ringFrameD2 L.ε (bSqrt (bRaw L)) (phi z) 2 2 -
        (phi z).1 ^ (3 / 2 : ℝ) • vecSp (flatD2 L (phi z).1 (phi z).2 2 2)‖ ≤
      343 * L.ε * wt (3 / 2) z * (1 + |z.2.2|) ^ 3 * Mz L z := by
  rw [second_template L z 2 2 (Zo (Zo (rawPhi L)) z)
    (by rw [ringFrameD2_22, DzDz_B, merSp_smul])
    (Zo (Zo (trainFv L)) z)
    (by rw [lead_ee (contDiff_trainFv L), flatDir_two])]
  have e := entry22_gen L.ε_pos.le (contDiff_trainFv L) (contDiff_hTil L) z
  rw [← rawPhi_eq] at e
  have hw : 1 ≤ 1 + |z.2.2| := by linarith [abs_nonneg z.2.2]
  have n := num3 hw L.ε_pos.le (J_nonneg 2 (trainFv L) z) (J_nonneg 3 (trainFpsi L) z) (hJ2h L z)
  have ht := (wt_pos (3 / 2) z).le
  unfold Mz
  nlinarith [mul_le_mul_of_nonneg_left (e.trans n) ht]

end UnforcedLeray.Short.PartIIIb.Concrete.RingFrameD2BoundAux
