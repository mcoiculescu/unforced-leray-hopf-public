import Mathlib.Analysis.Calculus.SmoothSeries
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_asrc_ra_8.Split.BkMajSummable

/-!
# `PartIII-b:C/asrc/ra/8/1/3` : leaf (G1) `LatticeFDerivSum`

Source of record: `the November 2 reference manuscript` (73 pages), 4978
("The sums and their required derivatives converge by Gaussian decay").

Termwise differentiation of a lattice sum on `ℝ × ℝ`, using a majorant that is uniform on the unit
ball around the base point. For `z` in `ball x 1` the Gaussian majorant at `z` is bounded by a
constant times the majorant at `x` with `a` replaced by `2a`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- Pointwise comparison of the Gaussian weights on the unit ball (abstract form). -/
lemma bkG1_ball_pt (a : ℝ) (ha : 0 < a) (w p : ℝ × ℝ) (h1 : |w.1 - p.1| < 1)
    (h2 : |w.2 - p.2| < 1) (hn : ‖w‖ ≤ ‖p‖ + 1) :
    (1 + ‖w‖) ^ 6 * Real.exp (-(sq2 w) / (4 * a))
      ≤ 64 * Real.exp (1 / (2 * a)) * ((1 + ‖p‖) ^ 6 * Real.exp (-(sq2 p) / (4 * (2 * a)))) := by
  have hd1 : (w.1 - p.1) ^ 2 ≤ 1 := by
    nlinarith [abs_nonneg (w.1 - p.1), sq_abs (w.1 - p.1)]
  have hd2 : (w.2 - p.2) ^ 2 ≤ 1 := by
    nlinarith [abs_nonneg (w.2 - p.2), sq_abs (w.2 - p.2)]
  have hkey : sq2 p / 2 - 2 ≤ sq2 w := by
    unfold sq2
    nlinarith [sq_nonneg (p.1 - 2 * w.1), sq_nonneg (p.2 - 2 * w.2), hd1, hd2]
  have hexp : -(sq2 w) / (4 * a) ≤ 1 / (2 * a) + -(sq2 p) / (4 * (2 * a)) := by
    have e1 : -(sq2 w) / (4 * a) = (-(sq2 w)) * (1 / (4 * a)) := by ring
    have e2 : 1 / (2 * a) + -(sq2 p) / (4 * (2 * a))
        = 2 * (1 / (4 * a)) + (-(sq2 p) / 2) * (1 / (4 * a)) := by ring
    rw [e1, e2]
    have ht : 0 ≤ 1 / (4 * a) := by positivity
    nlinarith [mul_le_mul_of_nonneg_right hkey ht]
  have hE : Real.exp (-(sq2 w) / (4 * a))
      ≤ Real.exp (1 / (2 * a)) * Real.exp (-(sq2 p) / (4 * (2 * a))) := by
    rw [← Real.exp_add]
    exact Real.exp_le_exp.mpr hexp
  have hP : (1 + ‖w‖) ^ 6 ≤ 64 * (1 + ‖p‖) ^ 6 := by
    have h0 : 0 ≤ 1 + ‖w‖ := by positivity
    have h3 : 1 + ‖w‖ ≤ 2 * (1 + ‖p‖) := by linarith [norm_nonneg p]
    calc (1 + ‖w‖) ^ 6 ≤ (2 * (1 + ‖p‖)) ^ 6 := pow_le_pow_left₀ h0 h3 6
      _ = 64 * (1 + ‖p‖) ^ 6 := by ring
  calc (1 + ‖w‖) ^ 6 * Real.exp (-(sq2 w) / (4 * a))
      ≤ (64 * (1 + ‖p‖) ^ 6) * (Real.exp (1 / (2 * a)) * Real.exp (-(sq2 p) / (4 * (2 * a)))) :=
        mul_le_mul hP hE (by positivity) (by positivity)
    _ = 64 * Real.exp (1 / (2 * a)) * ((1 + ‖p‖) ^ 6 * Real.exp (-(sq2 p) / (4 * (2 * a)))) := by
        ring

/-- The Gaussian majorant at a point of the unit ball around `x` is bounded by a constant times
the majorant at `x` with `a` replaced by `2a`. -/
lemma bkG1_ball (ν a : ℝ) (ha : 0 < a) (j : ℤ) (x z : ℝ × ℝ) (hz : z ∈ Metric.ball x 1) :
    bkMaj ν a j z ≤ 64 * Real.exp (1 / (2 * a)) * bkMaj ν (2 * a) j x := by
  have hzx : ‖z - x‖ < 1 := by
    rw [← dist_eq_norm]
    exact Metric.mem_ball.mp hz
  have hwp : xj ν j z - xj ν j x = z - x := Prod.ext (by simp only [xj, Prod.fst_sub]; ring) rfl
  have hn1 : |(xj ν j z).1 - (xj ν j x).1| < 1 := by
    have h := norm_fst_le (z - x)
    have hh : (xj ν j z).1 - (xj ν j x).1 = z.1 - x.1 := by simp only [xj]; ring
    rw [Prod.fst_sub, Real.norm_eq_abs] at h
    rw [hh]
    linarith
  have hn2 : |(xj ν j z).2 - (xj ν j x).2| < 1 := by
    have h := norm_snd_le (z - x)
    have hh : (xj ν j z).2 - (xj ν j x).2 = z.2 - x.2 := rfl
    rw [Prod.snd_sub, Real.norm_eq_abs] at h
    rw [hh]
    linarith
  have hn : ‖xj ν j z‖ ≤ ‖xj ν j x‖ + 1 := by
    have h := norm_sub_norm_le (xj ν j z) (xj ν j x)
    rw [hwp] at h
    linarith
  have key := bkG1_ball_pt a ha (xj ν j z) (xj ν j x) hn1 hn2 hn
  unfold bkMaj
  exact key

/-- **(G1)** Termwise differentiation of a Gaussian lattice sum (source 4978). -/
theorem latticeFDerivSum : LatticeFDerivSum := by
  unfold LatticeFDerivSum
  intro E _i1 _i2 _i3 ν a K f hν ha hdiff hf0 hf1 x
  have ha0 : 0 < a := by linarith
  have h2a : 0 < 2 * a := by linarith
  have hU : Summable (fun j : ℤ => |K| * (64 * Real.exp (1 / (2 * a))) * bkMaj ν (2 * a) j x) :=
    (bkMajSummable ν (2 * a) x hν h2a).mul_left (|K| * (64 * Real.exp (1 / (2 * a))))
  have hbound : ∀ j : ℤ, ∀ z ∈ Metric.ball x 1,
      ‖fderiv ℝ (f j) z‖ ≤ |K| * (64 * Real.exp (1 / (2 * a))) * bkMaj ν (2 * a) j x := by
    intro j z hz
    have hb0 : 0 ≤ bkMaj ν a j z := by unfold bkMaj; positivity
    have h1 : ‖fderiv ℝ (f j) z‖ ≤ K * bkMaj ν a j z := hf1 j z
    have h2 : K * bkMaj ν a j z ≤ |K| * bkMaj ν a j z :=
      mul_le_mul_of_nonneg_right (le_abs_self K) hb0
    have h3 : |K| * bkMaj ν a j z ≤ |K| * (64 * Real.exp (1 / (2 * a)) * bkMaj ν (2 * a) j x) :=
      mul_le_mul_of_nonneg_left (bkG1_ball ν a ha0 j x z hz) (abs_nonneg K)
    have h4 : |K| * (64 * Real.exp (1 / (2 * a)) * bkMaj ν (2 * a) j x)
        = |K| * (64 * Real.exp (1 / (2 * a))) * bkMaj ν (2 * a) j x := by ring
    linarith
  have hbound0 : ∀ j : ℤ, ∀ z ∈ Metric.ball x 1,
      ‖f j z‖ ≤ |K| * (64 * Real.exp (1 / (2 * a))) * bkMaj ν (2 * a) j x := by
    intro j z hz
    have hb0 : 0 ≤ bkMaj ν a j z := by unfold bkMaj; positivity
    have h1 : ‖f j z‖ ≤ K * bkMaj ν a j z := hf0 j z
    have h2 : K * bkMaj ν a j z ≤ |K| * bkMaj ν a j z :=
      mul_le_mul_of_nonneg_right (le_abs_self K) hb0
    have h3 : |K| * bkMaj ν a j z ≤ |K| * (64 * Real.exp (1 / (2 * a)) * bkMaj ν (2 * a) j x) :=
      mul_le_mul_of_nonneg_left (bkG1_ball ν a ha0 j x z hz) (abs_nonneg K)
    have h4 : |K| * (64 * Real.exp (1 / (2 * a)) * bkMaj ν (2 * a) j x)
        = |K| * (64 * Real.exp (1 / (2 * a))) * bkMaj ν (2 * a) j x := by ring
    linarith
  have hmem : x ∈ Metric.ball x 1 := Metric.mem_ball_self one_pos
  have hD : Summable (fun j : ℤ => ‖fderiv ℝ (f j) x‖) :=
    Summable.of_nonneg_of_le (fun j => norm_nonneg _) (fun j => hbound j x hmem) hU
  have hN : Summable (fun j : ℤ => ‖f j x‖) :=
    Summable.of_nonneg_of_le (fun j => norm_nonneg _) (fun j => hbound0 j x hmem) hU
  have hS : Summable (fun j : ℤ => f j x) := hN.of_norm
  refine ⟨?_, hD, hN⟩
  exact hasFDerivAt_tsum_of_isPreconnected hU Metric.isOpen_ball (convex_ball x 1).isPreconnected
    (fun n z _ => (hdiff n z).hasFDerivAt) (fun n z hz => hbound n z hz) hmem hS hmem

end UnforcedLeray.Short.PartIIIb.Concrete
