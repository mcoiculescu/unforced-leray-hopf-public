import UnforcedLeray.Short.PartIIIa.Sub.T21_c2_2_5_2
import UnforcedLeray.Short.PartIIb.Tasks.CylEnergy.DiffusionBound.Limit
import UnforcedLeray.Short.PartIIb.Tasks.CylEnergy.DiffusionBound.Common

/-!
# Leaf `PartIII-a:T21/c2/2/5/2/2` (`diffLimit`): removing the cut-off in `DiffGreenCut`.

Source: `the November 2 reference manuscript` lines 2950-2954. Template:
`PartII-b` `dbLimit` (`Tasks/CylEnergy/DiffusionBound/Limit.lean`). Apply the cut-off Green
inequality to `G = g²`, let `n → ∞` (`dbl_cut_tendsto`, `dbl_E_tendsto`), and use
`Δ(g²) = 2gΔg + 2|∇g|²`, `p ≥ 0`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology UnforcedLeray.Short.IIb
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

namespace LimitAux

open DbCommon

theorem lapG_abs_le {g : B0579.Plane → ℝ}
    (hGL : ∀ x, lapP (fun y => g y ^ 2) x =
      2 * g x * lapP g x + 2 * (B0579.pd 0 g x ^ 2 + B0579.pd 1 g x ^ 2))
    (x : B0579.Plane) : |lapP (fun y => g y ^ 2) x| ≤ 6 * (dbS g x * dbS g x) := by
  obtain ⟨h1, h2, h3, h4⟩ := abs_le_dbS g x
  have e1 : |g x * lapP g x| ≤ dbS g x * dbS g x := by
    rw [abs_mul]
    exact mul_le_mul h1 h4 (abs_nonneg _) (dbS_nonneg g x)
  have e2 : B0579.pd 0 g x ^ 2 ≤ dbS g x * dbS g x := sq_le_dbS_mul h2
  have e3 : B0579.pd 1 g x ^ 2 ≤ dbS g x * dbS g x := sq_le_dbS_mul h3
  have e4 : 0 ≤ B0579.pd 0 g x ^ 2 := sq_nonneg _
  have e5 : 0 ≤ B0579.pd 1 g x ^ 2 := sq_nonneg _
  have hS : 0 ≤ dbS g x * dbS g x := mul_nonneg (dbS_nonneg g x) (dbS_nonneg g x)
  have u := abs_le.1 e1
  rw [hGL x, abs_le]
  constructor <;> linarith [u.1, u.2]

theorem bound_pLapG {g p : B0579.Plane → ℝ} {m Kp : ℝ} (hKp : 0 ≤ Kp)
    (hGL : ∀ x, lapP (fun y => g y ^ 2) x =
      2 * g x * lapP g x + 2 * (B0579.pd 0 g x ^ 2 + B0579.pd 1 g x ^ 2))
    (hPb0 : ∀ x, |p x| ≤ Kp * B0579.jb x ^ m) (x : B0579.Plane) :
    |p x * lapP (fun y => g y ^ 2) x| ≤ (6 * Kp) * (dbS g x * dbS g x * B0579.jb x ^ m) := by
  have hw : 0 ≤ B0579.jb x ^ m := Real.rpow_nonneg (B0579.jb_pos x).le m
  rw [abs_mul]
  calc |p x| * |lapP (fun y => g y ^ 2) x|
      ≤ (Kp * B0579.jb x ^ m) * (6 * (dbS g x * dbS g x)) :=
        mul_le_mul (hPb0 x) (lapG_abs_le hGL x) (abs_nonneg _) (mul_nonneg hKp hw)
    _ = (6 * Kp) * (dbS g x * dbS g x * B0579.jb x ^ m) := by ring

theorem bound_sqLap {g p : B0579.Plane → ℝ} {m Kp : ℝ} (hKp : 0 ≤ Kp)
    (hPb2 : ∀ x, |lapP p x| ≤ Kp * B0579.jb x ^ m) (x : B0579.Plane) :
    |g x ^ 2 * lapP p x| ≤ Kp * (dbS g x * dbS g x * B0579.jb x ^ m) := by
  have h1 : |g x| ≤ dbS g x := (abs_le_dbS g x).1
  rw [abs_mul, abs_of_nonneg (sq_nonneg _)]
  calc g x ^ 2 * |lapP p x| ≤ (dbS g x * dbS g x) * (Kp * B0579.jb x ^ m) :=
        mul_le_mul (sq_le_dbS_mul h1) (hPb2 x) (abs_nonneg _)
          (mul_nonneg (dbS_nonneg g x) (dbS_nonneg g x))
    _ = Kp * (dbS g x * dbS g x * B0579.jb x ^ m) := by ring

theorem bound_H {g p : B0579.Plane → ℝ} {m Kp : ℝ} (hKp : 0 ≤ Kp)
    (hPb0 : ∀ x, |p x| ≤ Kp * B0579.jb x ^ m) (hPb1 : ∀ x, |B0579.pd 1 p x| ≤ Kp * B0579.jb x ^ m)
    (x : B0579.Plane) :
    |p x * (2 * g x * B0579.pd 1 g x) - g x ^ 2 * B0579.pd 1 p x| ≤
      (3 * Kp) * (dbS g x * dbS g x * B0579.jb x ^ m) := by
  have hw : 0 ≤ B0579.jb x ^ m := Real.rpow_nonneg (B0579.jb_pos x).le m
  have h1 : |g x| ≤ dbS g x := (abs_le_dbS g x).1
  have h3 : |B0579.pd 1 g x| ≤ dbS g x := (abs_le_dbS g x).2.2.1
  have hS : 0 ≤ dbS g x * dbS g x := mul_nonneg (dbS_nonneg g x) (dbS_nonneg g x)
  have e1 : |2 * g x * B0579.pd 1 g x| ≤ 2 * (dbS g x * dbS g x) := by
    have e : |2 * g x * B0579.pd 1 g x| = 2 * (|g x| * |B0579.pd 1 g x|) := by
      rw [abs_mul, abs_mul, abs_two]
      ring
    rw [e]
    exact mul_le_mul_of_nonneg_left (mul_le_mul h1 h3 (abs_nonneg _) (dbS_nonneg g x))
      (by norm_num)
  have t1 : |p x * (2 * g x * B0579.pd 1 g x)| ≤
      (Kp * B0579.jb x ^ m) * (2 * (dbS g x * dbS g x)) := by
    rw [abs_mul]
    exact mul_le_mul (hPb0 x) e1 (abs_nonneg _) (mul_nonneg hKp hw)
  have t2 : |g x ^ 2 * B0579.pd 1 p x| ≤ (dbS g x * dbS g x) * (Kp * B0579.jb x ^ m) := by
    rw [abs_mul, abs_of_nonneg (sq_nonneg _)]
    exact mul_le_mul (sq_le_dbS_mul h1) (hPb1 x) (abs_nonneg _) hS
  have u1 := abs_le.1 t1
  have u2 := abs_le.1 t2
  rw [abs_le]
  constructor <;> linarith [u1.1, u1.2, u2.1, u2.2]

theorem bound_gLapP {g p : B0579.Plane → ℝ} {m Kp : ℝ} (hKp : 0 ≤ Kp)
    (hPb0 : ∀ x, |p x| ≤ Kp * B0579.jb x ^ m) (x : B0579.Plane) :
    |g x * lapP g x * p x| ≤ Kp * (dbS g x * dbS g x * B0579.jb x ^ m) := by
  have h1 : |g x| ≤ dbS g x := (abs_le_dbS g x).1
  have h4 : |lapP g x| ≤ dbS g x := (abs_le_dbS g x).2.2.2
  rw [abs_mul, abs_mul]
  calc |g x| * |lapP g x| * |p x|
      ≤ (dbS g x * dbS g x) * (Kp * B0579.jb x ^ m) :=
        mul_le_mul (mul_le_mul h1 h4 (abs_nonneg _) (dbS_nonneg g x)) (hPb0 x) (abs_nonneg _)
          (mul_nonneg (dbS_nonneg g x) (dbS_nonneg g x))
    _ = Kp * (dbS g x * dbS g x * B0579.jb x ^ m) := by ring

end LimitAux

open LimitAux DbCommon in
/-- **Leaf `diffLimit`** (SP 2950-2954): removing the cut-off, `DiffLimitStmt`. -/
theorem diffLimit : DiffLimitStmt := by
  intro hcut hsq hχD c m p hc hp g hg
  obtain ⟨χ, hχC, hχs, hχ01, hχ1, K, hK⟩ := hχD
  obtain ⟨hGC, hGL, hG1⟩ := hsq g hg.smooth
  obtain ⟨Kp0, hKp0⟩ := hp.growth
  obtain ⟨Kp, hKp, hPall⟩ : ∃ Kp : ℝ, 0 ≤ Kp ∧ ∀ x : B0579.Plane,
      |p x| + |B0579.pd 0 p x| + |B0579.pd 1 p x| + |lapP p x| ≤ Kp * B0579.jb x ^ m :=
    ⟨max Kp0 0, le_max_right _ _, fun x =>
      (hKp0 x).trans (mul_le_mul_of_nonneg_right (le_max_left _ _)
        (Real.rpow_nonneg (B0579.jb_pos x).le m))⟩
  have hPb0 : ∀ x : B0579.Plane, |p x| ≤ Kp * B0579.jb x ^ m := fun x => by
    linarith [hPall x, abs_nonneg (B0579.pd 0 p x), abs_nonneg (B0579.pd 1 p x),
      abs_nonneg (lapP p x)]
  have hPb1 : ∀ x : B0579.Plane, |B0579.pd 1 p x| ≤ Kp * B0579.jb x ^ m := fun x => by
    linarith [hPall x, abs_nonneg (B0579.pd 0 p x), abs_nonneg (B0579.pd 1 p x),
      abs_nonneg (p x), abs_nonneg (lapP p x)]
  have hPb2 : ∀ x : B0579.Plane, |lapP p x| ≤ Kp * B0579.jb x ^ m := fun x => by
    linarith [hPall x, abs_nonneg (B0579.pd 0 p x), abs_nonneg (B0579.pd 1 p x),
      abs_nonneg (p x), abs_nonneg (lapP p x)]
  have hgc : Continuous g := hg.smooth.continuous
  have hpc : Continuous p := hp.smooth.continuous
  have hLp : Continuous (lapP p) := continuous_lapP hp.smooth
  have hLG : Continuous (lapP (fun y => g y ^ 2)) := continuous_lapP hGC
  have hLg : Continuous (lapP g) := continuous_lapP hg.smooth
  have hp1 : Continuous (B0579.pd 1 p) := continuous_pd_of_c2 hp.smooth 1
  have hG1c : Continuous (B0579.pd 1 (fun y => g y ^ 2)) := continuous_pd_of_c2 hGC 1
  -- integrability of the integrands on the cell
  have I1 : IntegrableOn (fun x : B0579.Plane => p x * lapP (fun y => g y ^ 2) x)
      (B0579.cell c) :=
    cell_int_dbS (m := m) (K := 6 * Kp) hg (by linarith) (hpc.mul hLG)
      (fun x _ => bound_pLapG (g := g) (p := p) hKp hGL hPb0 x)
  have I2 : IntegrableOn (fun x : B0579.Plane => g x ^ 2 * lapP p x) (B0579.cell c) :=
    cell_int_dbS (m := m) (K := Kp) hg hKp ((hgc.pow 2).mul hLp)
      (fun x _ => bound_sqLap (g := g) (p := p) hKp hPb2 x)
  have IC : IntegrableOn (fun x : B0579.Plane => g x * lapP g x * p x) (B0579.cell c) :=
    cell_int_dbS (m := m) (K := Kp) hg hKp ((hgc.mul hLg).mul hpc)
      (fun x _ => bound_gLapP (g := g) (p := p) hKp hPb0 x)
  have IH : IntegrableOn (fun x : B0579.Plane =>
      p x * B0579.pd 1 (fun y => g y ^ 2) x - g x ^ 2 * B0579.pd 1 p x) (B0579.cell c) :=
    cell_int_dbS (m := m) (K := 3 * Kp) hg (by linarith)
      ((hpc.mul hG1c).sub ((hgc.pow 2).mul hp1))
      (fun x _ => by
        simp only [hG1 x]
        exact bound_H (g := g) (p := p) hKp hPb0 hPb1 x)
  have IF : IntegrableOn (fun x : B0579.Plane =>
      p x * lapP (fun y => g y ^ 2) x - g x ^ 2 * lapP p x) (B0579.cell c) :=
    Integrable.sub I1 I2
  -- the cut-off limit
  have hL := dbl_cut_tendsto c χ (fun n => (hχC n).continuous) hχ01 hχ1 _ IF
  have hE := dbl_E_tendsto c χ K hχ01 hK
    (fun x : B0579.Plane => p x * B0579.pd 1 (fun y => g y ^ 2) x - g x ^ 2 * B0579.pd 1 p x) IH
  have hE' : Tendsto (fun n : ℕ => -(∫ x in B0579.cell c,
      2 * χ n x.2 * deriv (χ n) x.2 *
        (p x * B0579.pd 1 (fun y => g y ^ 2) x - g x ^ 2 * B0579.pd 1 p x))) atTop (𝓝 0) := by
    have h := hE.neg
    rw [neg_zero] at h
    exact h
  have hcutn : ∀ n : ℕ, (∫ x in B0579.cell c, χ n x.2 ^ 2 *
      (p x * lapP (fun y => g y ^ 2) x - g x ^ 2 * lapP p x)) ≤
      -(∫ x in B0579.cell c, 2 * χ n x.2 * deriv (χ n) x.2 *
        (p x * B0579.pd 1 (fun y => g y ^ 2) x - g x ^ 2 * B0579.pd 1 p x)) :=
    fun n => hcut c m p hc hp (fun y => g y ^ 2) hGC
      (fun x => by
        show g (x.1 + c, x.2) ^ 2 = g x ^ 2
        rw [hg.periodic x])
      (fun x => sq_nonneg (g x)) (χ n) (hχC n) (hχs n)
  have key : ∫ x in B0579.cell c,
      (p x * lapP (fun y => g y ^ 2) x - g x ^ 2 * lapP p x) ≤ 0 :=
    le_of_tendsto_of_tendsto hL hE' (Eventually.of_forall hcutn)
  rw [integral_sub I1 I2] at key
  -- pointwise: `2 g Δg p ≤ p Δ(g²)`
  have hpt : ∀ x : B0579.Plane, 2 * (g x * lapP g x * p x) ≤
      p x * lapP (fun y => g y ^ 2) x := by
    intro x
    rw [hGL x]
    nlinarith [mul_nonneg (hp.nonneg x)
      (add_nonneg (sq_nonneg (B0579.pd 0 g x)) (sq_nonneg (B0579.pd 1 g x)))]
  have hmono : ∫ x in B0579.cell c, 2 * (g x * lapP g x * p x) ≤
      ∫ x in B0579.cell c, p x * lapP (fun y => g y ^ 2) x :=
    integral_mono (Integrable.const_mul IC 2) I1 (fun x => hpt x)
  rw [integral_const_mul] at hmono
  linarith [hmono, key]

end UnforcedLeray.Short.IIIa
