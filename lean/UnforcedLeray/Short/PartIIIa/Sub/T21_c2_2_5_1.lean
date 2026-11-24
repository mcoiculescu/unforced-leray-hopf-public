import UnforcedLeray.Short.PartIIIa.Sub.T21_c2_2_5
import UnforcedLeray.Short.PartIIIa.Clock.FreeMoving.Rate.FmrIsoRadial
import UnforcedLeray.Short.PartIIIa.Clock.FreeMoving.Rate.FmrBracket.LapP
import UnforcedLeray.Short.PartIIb.Tasks.CylEnergy.DiffusionBound.Common
import UnforcedLeray.Short.PartIIb.Tasks.CylEnergy.TransportIBP

/-!
# `PartIII-a:T21/c2/2/5/1`: `FmrIBPInt`, decomposed (SP 2950-2954)

The decay of `CylSmoothDecay` against the polynomial growth `|p|, |∂p|, |Δp| ≤ K jb^m` of the
dilated weight `p = movWeight m a` gives all four integrabilities (`DbCommon.cell_int_dbS`).
Leaf: `MwGrowth` (the growth bound).  Proved here: `movWeight_contDiff2`, `fmrIBPInt_of`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology UnforcedLeray.Short.IIb
open scoped ENNReal

namespace UnforcedLeray.Short.IIIa

/-- **Leaf `MwGrowth`** (SP 2950-2954): the dilated weight `p = (1+|x|²/a)^m` and its first
derivatives and Laplacian are bounded by `K jb^m`, `jb = 1+q²+η²` (explicit formulas
`fmrIso_pd0`, `fmrIso_pd1`, `fmrBracket_lapP`; `w=1+|x|²/a ≤ max 1 (1/a) · jb`, `|x_j|/a ≤ √(w/a)`,
`w ≥ 1`). -/
def MwGrowth : Prop :=
  ∀ m a : ℝ, 0 ≤ m → 0 < a → ∃ K : ℝ, ∀ x : B0579.Plane,
    |movWeight m a x| + |B0579.pd 0 (movWeight m a) x| + |B0579.pd 1 (movWeight m a) x| +
      |lapP (movWeight m a) x| ≤ K * B0579.jb x ^ m

theorem movWeight_base_pos (a : ℝ) (ha : 0 < a) (x : B0579.Plane) :
    0 < 1 + (x.1 ^ 2 + x.2 ^ 2) / a := by
  have : 0 ≤ (x.1 ^ 2 + x.2 ^ 2) / a := div_nonneg (by positivity) ha.le
  linarith

theorem movWeight_contDiff2 (m a : ℝ) (ha : 0 < a) : ContDiff ℝ 2 (movWeight m a) := by
  unfold movWeight
  have h : ContDiff ℝ 2 (fun y : B0579.Plane => 1 + (y.1 ^ 2 + y.2 ^ 2) / a) := by fun_prop
  exact h.rpow_const_of_ne (fun x => (movWeight_base_pos a ha x).ne')

theorem fmrIBPInt_of (hG : MwGrowth) : FmrIBPInt := by
  intro ν c tr σ hσ hc hν hM m a hm ha g hg
  obtain ⟨M, hM⟩ := hM
  obtain ⟨K, hK⟩ := hG m a hm ha
  have hp2 := movWeight_contDiff2 m a ha
  have hgc : Continuous g := hg.smooth.continuous
  have hlapg : Continuous (lapP g) := DbCommon.continuous_lapP hg.smooth
  have hg0 : Continuous (B0579.pd 0 g) := DbCommon.continuous_pd_of_c2 hg.smooth 0
  have hg1 : Continuous (B0579.pd 1 g) := DbCommon.continuous_pd_of_c2 hg.smooth 1
  have hp : Continuous (movWeight m a) := hp2.continuous
  have hp0 : Continuous (B0579.pd 0 (movWeight m a)) := DbCommon.continuous_pd_of_c2 hp2 0
  have hp1 : Continuous (B0579.pd 1 (movWeight m a)) := DbCommon.continuous_pd_of_c2 hp2 1
  have hlapp : Continuous (lapP (movWeight m a)) := DbCommon.continuous_lapP hp2
  have hv := (TransportIBP.contDiff_slice tr hσ).continuous
  have hv0 : Continuous (fun x : B0579.Plane => tr.v σ x 0) := by fun_prop
  have hv1 : Continuous (fun x : B0579.Plane => tr.v σ x 1) := by fun_prop
  have hM0 : 0 ≤ M := by
    have := hM 0
    exact (add_nonneg (abs_nonneg _) (abs_nonneg _)).trans this
  have hK0 : 0 ≤ K := by
    by_contra hneg
    push_neg at hneg
    have := hK (0, 0)
    have h1 : 0 < B0579.jb ((0, 0) : B0579.Plane) ^ m := Real.rpow_pos_of_pos (B0579.jb_pos _) m
    nlinarith [abs_nonneg (movWeight m a (0, 0)), abs_nonneg (B0579.pd 0 (movWeight m a) (0, 0)),
      abs_nonneg (B0579.pd 1 (movWeight m a) (0, 0)), abs_nonneg (lapP (movWeight m a) (0, 0))]
  have hw0 := fun x : B0579.Plane => Real.rpow_nonneg (B0579.jb_pos x).le m
  have hpb : ∀ x : B0579.Plane, |movWeight m a x| ≤ K * B0579.jb x ^ m ∧
      |B0579.pd 0 (movWeight m a) x| ≤ K * B0579.jb x ^ m ∧
      |B0579.pd 1 (movWeight m a) x| ≤ K * B0579.jb x ^ m ∧
      |lapP (movWeight m a) x| ≤ K * B0579.jb x ^ m := by
    intro x
    have := hK x
    have a1 := abs_nonneg (movWeight m a x)
    have a2 := abs_nonneg (B0579.pd 0 (movWeight m a) x)
    have a3 := abs_nonneg (B0579.pd 1 (movWeight m a) x)
    have a4 := abs_nonneg (lapP (movWeight m a) x)
    refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith
  have hvb : ∀ x : B0579.Plane, |tr.v σ x 0| ≤ M ∧ |tr.v σ x 1| ≤ M := by
    intro x
    have := hM x
    exact ⟨by linarith [abs_nonneg (tr.v σ x 1)], by linarith [abs_nonneg (tr.v σ x 0)]⟩
  have hS := fun x : B0579.Plane => DbCommon.abs_le_dbS g x
  have hS0 := DbCommon.dbS_nonneg g
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine DbCommon.cell_int_dbS (m := m) (K := K) hg hK0 ((hgc.pow 2).mul hlapp) (fun x _ => ?_)
    rw [abs_mul, abs_pow]
    have h1 : |g x| ^ 2 ≤ DbCommon.dbS g x * DbCommon.dbS g x := by
      rw [sq]; exact mul_le_mul (hS x).1 (hS x).1 (abs_nonneg _) (hS0 x)
    calc |g x| ^ 2 * |lapP (movWeight m a) x|
        ≤ (DbCommon.dbS g x * DbCommon.dbS g x) * (K * B0579.jb x ^ m) :=
          mul_le_mul h1 (hpb x).2.2.2 (abs_nonneg _) (mul_nonneg (hS0 x) (hS0 x))
      _ = K * (DbCommon.dbS g x * DbCommon.dbS g x * B0579.jb x ^ m) := by ring
  · refine DbCommon.cell_int_dbS (m := m) (K := 2 * M * K) hg (by positivity)
      ((hgc.pow 2).mul ((hv0.mul hp0).add (hv1.mul hp1))) (fun x _ => ?_)
    rw [abs_mul, abs_pow]
    have h1 : |g x| ^ 2 ≤ DbCommon.dbS g x * DbCommon.dbS g x := by
      rw [sq]; exact mul_le_mul (hS x).1 (hS x).1 (abs_nonneg _) (hS0 x)
    have h2 : |tr.v σ x 0 * B0579.pd 0 (movWeight m a) x +
        tr.v σ x 1 * B0579.pd 1 (movWeight m a) x| ≤ 2 * M * (K * B0579.jb x ^ m) := by
      refine (abs_add_le _ _).trans ?_
      rw [abs_mul, abs_mul]
      have e0 := mul_le_mul (hvb x).1 (hpb x).2.1 (abs_nonneg _) hM0
      have e1 := mul_le_mul (hvb x).2 (hpb x).2.2.1 (abs_nonneg _) hM0
      linarith
    calc |g x| ^ 2 * |tr.v σ x 0 * B0579.pd 0 (movWeight m a) x +
          tr.v σ x 1 * B0579.pd 1 (movWeight m a) x|
        ≤ (DbCommon.dbS g x * DbCommon.dbS g x) * (2 * M * (K * B0579.jb x ^ m)) :=
          mul_le_mul h1 h2 (abs_nonneg _) (mul_nonneg (hS0 x) (hS0 x))
      _ = (2 * M * K) * (DbCommon.dbS g x * DbCommon.dbS g x * B0579.jb x ^ m) := by ring
  · refine DbCommon.cell_int_dbS (m := m) (K := K) hg hK0 ((hgc.mul hlapg).mul hp) (fun x _ => ?_)
    rw [abs_mul, abs_mul]
    have h1 : |g x| * |lapP g x| ≤ DbCommon.dbS g x * DbCommon.dbS g x :=
      mul_le_mul (hS x).1 (hS x).2.2.2 (abs_nonneg _) (hS0 x)
    calc |g x| * |lapP g x| * |movWeight m a x|
        ≤ (DbCommon.dbS g x * DbCommon.dbS g x) * (K * B0579.jb x ^ m) :=
          mul_le_mul h1 (hpb x).1 (abs_nonneg _) (mul_nonneg (hS0 x) (hS0 x))
      _ = K * (DbCommon.dbS g x * DbCommon.dbS g x * B0579.jb x ^ m) := by ring
  · refine DbCommon.cell_int_dbS (m := m) (K := 2 * M * K) hg (by positivity)
      ((hgc.mul ((hv0.mul hg0).add (hv1.mul hg1))).mul hp) (fun x _ => ?_)
    rw [abs_mul, abs_mul]
    have h2 : |tr.v σ x 0 * B0579.pd 0 g x + tr.v σ x 1 * B0579.pd 1 g x| ≤
        2 * M * DbCommon.dbS g x := by
      refine (abs_add_le _ _).trans ?_
      rw [abs_mul, abs_mul]
      have e0 := mul_le_mul (hvb x).1 (hS x).2.1 (abs_nonneg _) hM0
      have e1 := mul_le_mul (hvb x).2 (hS x).2.2.1 (abs_nonneg _) hM0
      linarith
    have h1 : |g x| * |tr.v σ x 0 * B0579.pd 0 g x + tr.v σ x 1 * B0579.pd 1 g x| ≤
        DbCommon.dbS g x * (2 * M * DbCommon.dbS g x) :=
      mul_le_mul (hS x).1 h2 (abs_nonneg _) (hS0 x)
    calc |g x| * |tr.v σ x 0 * B0579.pd 0 g x + tr.v σ x 1 * B0579.pd 1 g x| *
          |movWeight m a x|
        ≤ (DbCommon.dbS g x * (2 * M * DbCommon.dbS g x)) * (K * B0579.jb x ^ m) :=
          mul_le_mul h1 (hpb x).1 (abs_nonneg _)
            (mul_nonneg (hS0 x) (mul_nonneg (mul_nonneg (by norm_num) hM0) (hS0 x)))
      _ = (2 * M * K) * (DbCommon.dbS g x * DbCommon.dbS g x * B0579.jb x ^ m) := by ring

end UnforcedLeray.Short.IIIa
