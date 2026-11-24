import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_8_2_1_3.Bound.Fin3

/-!
# The five entries with a hoop index (`PartIII-b:C/rep/8/2/1/3/b`, helper 10)

Source lines 5036-5045, 5460-5465: `(0,1),(1,0),(1,1),(1,2),(2,1)`, whose flat part vanishes.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete.RingFrameD2BoundAux

open UnforcedLeray.Short.PartIIIb.Concrete UnforcedLeray.Axi
open UnforcedLeray.Short.PartIIIb.Concrete.RingChartRawD2Sub

theorem vecSp_zero' : vecSp (0 : Vec3) = 0 := by
  ext i; simp [vecSp]

theorem wt_split (z : Zc) : wt (3 / 2) z = wt (1 / 2) z * wt 1 z := by
  rw [wt_mul]; norm_num

theorem hA (L : ReturnLevel) (z : Zc) :
    L.ε * Real.sqrt (phi z).1 * (Drho L.ε (bSqrt (bRaw L)) (phi z)) 0 -
        L.ε ^ 2 * (phi z).1 * (bSqrt (bRaw L) (phi z)) 0 =
      L.ε * wt (3 / 2) z * (Pm L.ε 2 (rawPhi L) z) 0 := by
  have hs : Real.sqrt (phi z).1 = wt (1 / 2) z := (wt_half z).symm
  have h1 : (phi z).1 = wt 1 z := (wt_one z).symm
  rw [hs, h1, Drho_B, lift_B, Pm_step, wt_split]
  simp only [PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul]
  ring

theorem hC (L : ReturnLevel) (z : Zc) :
    L.ε * Real.sqrt (phi z).1 * (Drho L.ε (bSqrt (bRaw L)) (phi z)) 1 =
      L.ε * wt (3 / 2) z * (Pm L.ε 1 (rawPhi L) z) 1 := by
  have hs : Real.sqrt (phi z).1 = wt (1 / 2) z := (wt_half z).symm
  rw [hs, Drho_B, wt_split]
  simp only [PiLp.smul_apply, smul_eq_mul]
  ring

theorem hZ (L : ReturnLevel) (z : Zc) :
    L.ε * Real.sqrt (phi z).1 * (Dz (bSqrt (bRaw L)) (phi z)) 0 =
      L.ε * wt (3 / 2) z * (Zo (rawPhi L) z) 0 := by
  have hs : Real.sqrt (phi z).1 = wt (1 / 2) z := (wt_half z).symm
  rw [hs, Dz_B, wt_split]
  simp only [PiLp.smul_apply, smul_eq_mul]
  ring

theorem absA_le (L : ReturnLevel) (h1 : L.ε ≤ 1) (z : Zc) :
    |L.ε * wt (3 / 2) z * (Pm L.ε 2 (rawPhi L) z) 0| ≤
      L.ε * wt (3 / 2) z * (49 * (1 + |z.2.2|) ^ 2 * Mz L z) := by
  rw [abs_mul, abs_of_nonneg (mul_nonneg L.ε_pos.le (wt_pos _ _).le)]
  refine mul_le_mul_of_nonneg_left ((comp_le _ 0).trans (fb_P L h1 2 (by norm_num) z))
    (mul_nonneg L.ε_pos.le (wt_pos _ _).le)

theorem absC_le (L : ReturnLevel) (h1 : L.ε ≤ 1) (z : Zc) :
    |L.ε * wt (3 / 2) z * (Pm L.ε 1 (rawPhi L) z) 1| ≤
      L.ε * wt (3 / 2) z * (49 * (1 + |z.2.2|) ^ 2 * Mz L z) := by
  rw [abs_mul, abs_of_nonneg (mul_nonneg L.ε_pos.le (wt_pos _ _).le)]
  refine mul_le_mul_of_nonneg_left ((comp_le _ 1).trans (fb_P L h1 1 (by norm_num) z))
    (mul_nonneg L.ε_pos.le (wt_pos _ _).le)

theorem absZ_le (L : ReturnLevel) (h1 : L.ε ≤ 1) (z : Zc) :
    |L.ε * wt (3 / 2) z * (Zo (rawPhi L) z) 0| ≤
      L.ε * wt (3 / 2) z * (7 * (1 + |z.2.2|) * Mz L z) := by
  rw [abs_mul, abs_of_nonneg (mul_nonneg L.ε_pos.le (wt_pos _ _).le)]
  refine mul_le_mul_of_nonneg_left ((comp_le _ 0).trans (fb_Z L h1 z))
    (mul_nonneg L.ε_pos.le (wt_pos _ _).le)

theorem fo_final {ε t w M K : ℝ} (hw : 1 ≤ w) (hε : 0 ≤ ε) (ht : 0 ≤ t) (hM : 0 ≤ M)
    (hK : K ≤ 343) (hK0 : 0 ≤ K) (X : ℝ) (hX : X ≤ ε * t * (K * w ^ 2 * M)) :
    X ≤ 343 * ε * t * w ^ 3 * M := by
  have h2 : w ^ 2 ≤ w ^ 3 := pow_le_pow_right₀ hw (by norm_num)
  have h1 : K * w ^ 2 * M ≤ 343 * w ^ 3 * M := by
    have : K * w ^ 2 ≤ 343 * w ^ 3 := by
      have : (0:ℝ) ≤ w ^ 2 := by positivity
      nlinarith
    exact mul_le_mul_of_nonneg_right this hM
  have := mul_le_mul_of_nonneg_left h1 (mul_nonneg hε ht)
  nlinarith

theorem diff01 (L : ReturnLevel) (h1 : L.ε ≤ 1) (z : Zc) :
    ‖ringFrameD2 L.ε (bSqrt (bRaw L)) (phi z) 0 1 -
        (phi z).1 ^ (3 / 2 : ℝ) • vecSp (flatD2 L (phi z).1 (phi z).2 0 1)‖ ≤
      343 * L.ε * wt (3 / 2) z * (1 + |z.2.2|) ^ 3 * Mz L z := by
  rw [flatD2_right_one, vecSp_zero', smul_zero, sub_zero, ringFrameD2_01, hA, norm_vecSp_mid]
  have hw : 1 ≤ 1 + |z.2.2| := by linarith [abs_nonneg z.2.2]
  exact fo_final (K := 49) hw L.ε_pos.le (wt_pos _ _).le (Mz_nonneg L z) (by norm_num)
    (by norm_num) _ (absA_le L h1 z)

theorem diff10 (L : ReturnLevel) (h1 : L.ε ≤ 1) (z : Zc) :
    ‖ringFrameD2 L.ε (bSqrt (bRaw L)) (phi z) 1 0 -
        (phi z).1 ^ (3 / 2 : ℝ) • vecSp (flatD2 L (phi z).1 (phi z).2 1 0)‖ ≤
      343 * L.ε * wt (3 / 2) z * (1 + |z.2.2|) ^ 3 * Mz L z := by
  rw [flatD2_left_one, vecSp_zero', smul_zero, sub_zero, ringFrameD2_10, hA, norm_vecSp_mid]
  have hw : 1 ≤ 1 + |z.2.2| := by linarith [abs_nonneg z.2.2]
  exact fo_final (K := 49) hw L.ε_pos.le (wt_pos _ _).le (Mz_nonneg L z) (by norm_num)
    (by norm_num) _ (absA_le L h1 z)

theorem absZ_le' (L : ReturnLevel) (h1 : L.ε ≤ 1) (z : Zc) :
    |L.ε * wt (3 / 2) z * (Zo (rawPhi L) z) 0| ≤
      L.ε * wt (3 / 2) z * (49 * (1 + |z.2.2|) ^ 2 * Mz L z) := by
  refine (absZ_le L h1 z).trans ?_
  have hw : 1 ≤ 1 + |z.2.2| := by linarith [abs_nonneg z.2.2]
  have hw7 : 7 * (1 + |z.2.2|) ≤ 49 * (1 + |z.2.2|) ^ 2 := by nlinarith
  exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hw7 (Mz_nonneg L z))
    (mul_nonneg L.ε_pos.le (wt_pos _ _).le)

theorem diff12 (L : ReturnLevel) (h1 : L.ε ≤ 1) (z : Zc) :
    ‖ringFrameD2 L.ε (bSqrt (bRaw L)) (phi z) 1 2 -
        (phi z).1 ^ (3 / 2 : ℝ) • vecSp (flatD2 L (phi z).1 (phi z).2 1 2)‖ ≤
      343 * L.ε * wt (3 / 2) z * (1 + |z.2.2|) ^ 3 * Mz L z := by
  rw [flatD2_left_one, vecSp_zero', smul_zero, sub_zero, ringFrameD2_12, hZ, norm_vecSp_mid]
  have hw : 1 ≤ 1 + |z.2.2| := by linarith [abs_nonneg z.2.2]
  exact fo_final (K := 49) hw L.ε_pos.le (wt_pos _ _).le (Mz_nonneg L z) (by norm_num)
    (by norm_num) _ (absZ_le' L h1 z)

theorem diff21 (L : ReturnLevel) (h1 : L.ε ≤ 1) (z : Zc) :
    ‖ringFrameD2 L.ε (bSqrt (bRaw L)) (phi z) 2 1 -
        (phi z).1 ^ (3 / 2 : ℝ) • vecSp (flatD2 L (phi z).1 (phi z).2 2 1)‖ ≤
      343 * L.ε * wt (3 / 2) z * (1 + |z.2.2|) ^ 3 * Mz L z := by
  rw [flatD2_right_one, vecSp_zero', smul_zero, sub_zero, ringFrameD2_21, hZ, norm_vecSp_mid]
  have hw : 1 ≤ 1 + |z.2.2| := by linarith [abs_nonneg z.2.2]
  exact fo_final (K := 49) hw L.ε_pos.le (wt_pos _ _).le (Mz_nonneg L z) (by norm_num)
    (by norm_num) _ (absZ_le' L h1 z)

theorem diff11 (L : ReturnLevel) (h1 : L.ε ≤ 1) (z : Zc) :
    ‖ringFrameD2 L.ε (bSqrt (bRaw L)) (phi z) 1 1 -
        (phi z).1 ^ (3 / 2 : ℝ) • vecSp (flatD2 L (phi z).1 (phi z).2 1 1)‖ ≤
      343 * L.ε * wt (3 / 2) z * (1 + |z.2.2|) ^ 3 * Mz L z := by
  rw [flatD2_left_one, vecSp_zero', smul_zero, sub_zero, ringFrameD2_11, hA, hC]
  refine (norm_vecSp_le _ _).trans ?_
  have hw : 1 ≤ 1 + |z.2.2| := by linarith [abs_nonneg z.2.2]
  refine fo_final (K := 98) hw L.ε_pos.le (wt_pos _ _).le (Mz_nonneg L z) (by norm_num)
    (by norm_num) _ ?_
  have := absA_le L h1 z
  have := absC_le L h1 z
  nlinarith

end UnforcedLeray.Short.PartIIIb.Concrete.RingFrameD2BoundAux
