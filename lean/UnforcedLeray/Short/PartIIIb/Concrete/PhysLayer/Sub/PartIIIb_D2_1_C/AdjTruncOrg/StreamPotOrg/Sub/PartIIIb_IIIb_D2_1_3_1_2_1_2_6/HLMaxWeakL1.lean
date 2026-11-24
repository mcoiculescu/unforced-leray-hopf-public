import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.AdjTruncOrg.StreamPotOrg.Sub.PartIIIb_IIIb_D2_1_3_1_2_1_2_6.Defs
import Mathlib.MeasureTheory.Covering.Vitali
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.OuterMeasure.Basic
import Mathlib.Topology.Bases
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Data.ENNReal.Operations
import Mathlib.Data.ENNReal.Real

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Metric Function
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

lemma vol_five (x : Space) (ρ : ℝ) :
    volume (ball x (5 * ρ)) = 125 * volume (ball x ρ) := by
  rw [EuclideanSpace.volume_ball_fin_three, EuclideanSpace.volume_ball_fin_three,
    ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 5)]
  have h5 : ENNReal.ofReal 5 = 5 := by simp
  rw [h5]
  ring

lemma radius_bound (y : Space) (t M : ℝ≥0∞) (ht0 : 0 < t) (htt : t ≠ ⊤) (hMt : M ≠ ⊤)
    (ρ : ℝ) (hρ : 0 < ρ) (h : t * volume (ball y ρ) < M) :
    ρ ≤ 1 + M.toReal / (t.toReal * (Real.pi * 4 / 3)) := by
  have hs : 0 < t.toReal := ENNReal.toReal_pos ht0.ne' htt
  have hc : 0 < Real.pi * 4 / 3 := by positivity
  have hX : 0 ≤ ρ ^ 3 * (Real.pi * 4 / 3) := mul_nonneg (pow_nonneg hρ.le 3) hc.le
  have hvol : volume (ball y ρ) = ENNReal.ofReal (ρ ^ 3 * (Real.pi * 4 / 3)) := by
    rw [EuclideanSpace.volume_ball_fin_three, ENNReal.ofReal_mul (pow_nonneg hρ.le 3),
      ENNReal.ofReal_pow hρ.le]
  have h' : ENNReal.ofReal (t.toReal * (ρ ^ 3 * (Real.pi * 4 / 3))) < M := by
    rw [ENNReal.ofReal_mul hs.le, ENNReal.ofReal_toReal htt, ← hvol]
    exact h
  have h2 : t.toReal * (ρ ^ 3 * (Real.pi * 4 / 3)) < M.toReal :=
    (ENNReal.ofReal_lt_iff_lt_toReal (mul_nonneg hs.le hX) hMt).mp h'
  have hKpos : 0 < t.toReal * (Real.pi * 4 / 3) := mul_pos hs hc
  have hMr : 0 ≤ M.toReal := ENNReal.toReal_nonneg
  have hq : t.toReal * (Real.pi * 4 / 3) * (M.toReal / (t.toReal * (Real.pi * 4 / 3)))
      = M.toReal := by
    field_simp
  have h3 : t.toReal * (Real.pi * 4 / 3) * ρ ^ 3 < M.toReal := by
    have e : t.toReal * (Real.pi * 4 / 3) * ρ ^ 3 = t.toReal * (ρ ^ 3 * (Real.pi * 4 / 3)) := by
      ring
    rw [e]
    exact h2
  by_contra hcon
  push_neg at hcon
  have hq0 : 0 ≤ M.toReal / (t.toReal * (Real.pi * 4 / 3)) := div_nonneg hMr hKpos.le
  have h1 : 1 ≤ ρ := by linarith
  have h4 : ρ ≤ ρ ^ 3 := by
    nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ ρ)
      (mul_nonneg (by linarith : (0:ℝ) ≤ ρ - 1) (by linarith : (0:ℝ) ≤ ρ + 1))]
  have h5 : t.toReal * (Real.pi * 4 / 3) * ρ ≤ t.toReal * (Real.pi * 4 / 3) * ρ ^ 3 :=
    mul_le_mul_of_nonneg_left h4 hKpos.le
  have h6 : t.toReal * (Real.pi * 4 / 3) * (1 + M.toReal / (t.toReal * (Real.pi * 4 / 3)))
      < t.toReal * (Real.pi * 4 / 3) * ρ :=
    mul_lt_mul_of_pos_left hcon hKpos
  nlinarith [hq, h3, h5, h6, hKpos, hMr]

theorem hlMaxWeakL1 : HLMaxWeakL1 := by
  intro G hG t ht0 htt
  by_cases hMt : (∫⁻ z, G z) = ⊤
  · rw [hMt, ENNReal.mul_top (by norm_num)]
    exact le_top
  set M := ∫⁻ z, G z with hM
  set E := {y : Space | t < hlMax G y} with hE
  have hρ : ∀ y ∈ E, ∃ r : ℝ, 0 < r ∧ t * volume (ball y r) < ∫⁻ z in ball y r, G z := by
    intro y hy
    have hy' : t < hlMax G y := hy
    unfold hlMax at hy'
    obtain ⟨r, hr⟩ := lt_iSup_iff.mp hy'
    refine ⟨r.1, r.2, ?_⟩
    have hV0 : volume (ball y r.1) ≠ 0 := (measure_ball_pos volume y r.2).ne'
    have hVt : volume (ball y r.1) ≠ ⊤ := measure_ball_lt_top.ne
    have h1 : t * volume (ball y r.1)
        < ((volume (ball y r.1))⁻¹ * ∫⁻ z in ball y r.1, G z) * volume (ball y r.1) := by
        rw [mul_comm (t), mul_comm ((volume (ball y r.1))⁻¹ * ∫⁻ z in ball y r.1, G z)]
        exact ENNReal.mul_lt_mul_right hV0 hVt hr
    have h2 : ((volume (ball y r.1))⁻¹ * ∫⁻ z in ball y r.1, G z) * volume (ball y r.1)
        = ∫⁻ z in ball y r.1, G z := by
      rw [mul_right_comm, ENNReal.inv_mul_cancel hV0 hVt, one_mul]
    exact h1.trans_eq h2
  choose! ρ hρpos hρlt using hρ
  have hRb : ∀ y ∈ E, ρ y ≤ 1 + M.toReal / (t.toReal * (Real.pi * 4 / 3)) := fun y hy =>
    radius_bound y t M ht0 htt hMt (ρ y) (hρpos y hy)
      ((hρlt y hy).trans_le (setLIntegral_le_lintegral _ _))
  obtain ⟨u, huE, hu_disj, hcov⟩ :=
    Vitali.exists_disjoint_subfamily_covering_enlargement_ball E id ρ _ hRb 5 (by norm_num)
  have hu_count : u.Countable := hu_disj.countable_of_isOpen (fun a _ => isOpen_ball)
    (fun a ha => Metric.nonempty_ball.mpr (hρpos a (huE ha)))
  haveI : Countable u := hu_count.to_subtype
  have hcovE : E ⊆ ⋃ b ∈ u, ball b (5 * ρ b) := by
    intro y hy
    obtain ⟨b, hb, hsub⟩ := hcov y hy
    exact mem_biUnion hb (hsub (mem_ball_self (hρpos y hy)))
  have hdisj : Pairwise (Disjoint on fun b : u => ball (b : Space) (ρ b)) :=
    fun a b hab => hu_disj a.2 b.2 (fun h => hab (Subtype.ext h))
  have hsum : ∑' b : u, ∫⁻ z in ball (b : Space) (ρ b), G z ≤ M := by
    rw [← lintegral_iUnion (fun b : u => measurableSet_ball) hdisj G]
    exact setLIntegral_le_lintegral _ _
  calc t * volume E ≤ t * ∑' b : u, volume (ball (b : Space) (5 * ρ b)) :=
        mul_le_mul_of_nonneg_left ((measure_mono hcovE).trans
          (measure_biUnion_le volume hu_count _)) (zero_le)
    _ = ∑' b : u, t * volume (ball (b : Space) (5 * ρ b)) := ENNReal.tsum_mul_left.symm
    _ = ∑' b : u, 125 * (t * volume (ball (b : Space) (ρ b))) :=
        tsum_congr (fun b => by rw [vol_five]; ring)
    _ = 125 * ∑' b : u, t * volume (ball (b : Space) (ρ b)) := ENNReal.tsum_mul_left
    _ ≤ 125 * ∑' b : u, ∫⁻ z in ball (b : Space) (ρ b), G z :=
        mul_le_mul_of_nonneg_left (ENNReal.tsum_le_tsum fun b => (hρlt b (huE b.2)).le) zero_le
    _ ≤ 125 * M := mul_le_mul_of_nonneg_left hsum zero_le

end UnforcedLeray.Short.PartIIIb.Concrete
