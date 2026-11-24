import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.Sub.MollCommDefs

/-!
# `ShiftTestPhase`: the periodised translate of a bump is a phase test

Source `the November 2 reference manuscript` lines 1351-1362, 1556-1583.
Helper lemmas (locally finite sums over translates of a compactly supported kernel) are
proved here and reused by `ShiftTestOpEq`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace

/-- A compactly supported function on `ℝ × ℝ³` is bounded by `R` off its support. -/
lemma exists_radius_of_hasCompactSupport {κ : ℝ × Space → ℝ} (hκ : HasCompactSupport κ) :
    ∃ R : ℝ, ∀ z, κ z ≠ 0 → ‖z‖ ≤ R := by
  obtain ⟨R, hR⟩ := hκ.isCompact.isBounded.subset_closedBall (0 : ℝ × Space)
  refine ⟨R, fun z hz => ?_⟩
  have h := hR (subset_tsupport κ (Function.mem_support.2 hz))
  simpa using h

/-- Local finiteness: near `w0`, the periodised sum over `k ∈ ℤ` of translates of a compactly
supported `κ` is a finite sum. -/
lemma shiftSum_eventuallyEq_finset {κ : ℝ × Space → ℝ} (hκ : HasCompactSupport κ) {P : ℝ}
    (hP : 0 < P) (x w0 : ℝ × Space) :
    ∃ S : Finset ℤ, (fun w : ℝ × Space => ∑' k : ℤ, κ (x - w + ((k : ℝ) * P, 0))) =ᶠ[𝓝 w0]
      (fun w => ∑ k ∈ S, κ (x - w + ((k : ℝ) * P, 0))) := by
  obtain ⟨R, hR⟩ := exists_radius_of_hasCompactSupport hκ
  obtain ⟨N, hN⟩ := exists_nat_ge ((R + ‖x‖ + ‖w0‖ + 1) / P)
  refine ⟨Finset.Icc (-(N : ℤ)) (N : ℤ), ?_⟩
  filter_upwards [Metric.ball_mem_nhds w0 one_pos] with w hw
  have hwn : ‖w‖ ≤ ‖w0‖ + 1 := by
    have h1 := mem_ball_iff_norm.1 hw
    have h2 := norm_sub_norm_le w w0
    linarith
  apply tsum_eq_sum
  intro k hk
  by_contra hne
  have hv := hR _ hne
  set v := x - w + ((k : ℝ) * P, 0) with hvdef
  have hfst : (k : ℝ) * P = v.1 - x.1 + w.1 := by
    simp [hvdef]
    ring
  have hb1 : ‖(k : ℝ) * P‖ ≤ R + ‖x‖ + ‖w0‖ + 1 := by
    rw [hfst]
    have a1 := norm_add_le (v.1 - x.1) w.1
    have a2 := norm_sub_le v.1 x.1
    have a3 := norm_fst_le v
    have a4 := norm_fst_le x
    have a6 : ‖w.1‖ ≤ ‖w‖ := norm_fst_le w
    linarith
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos hP] at hb1
  have hk2 : |(k : ℝ)| ≤ (N : ℝ) := by
    have : |(k : ℝ)| ≤ (R + ‖x‖ + ‖w0‖ + 1) / P := by
      rw [le_div_iff₀ hP]
      linarith
    linarith
  have hk3 : |k| ≤ (N : ℤ) := by
    have h' : ((|k| : ℤ) : ℝ) ≤ ((N : ℤ) : ℝ) := by
      rw [Int.cast_abs]; push_cast; exact hk2
    exact_mod_cast h'
  exact hk (Finset.mem_Icc.2 (abs_le.1 hk3))

/-- The periodised sum of translates of a smooth compactly supported kernel is smooth. -/
lemma shiftSum_contDiff {κ : ℝ × Space → ℝ} (hκs : ContDiff ℝ ∞ κ)
    (hκ : HasCompactSupport κ) {P : ℝ} (hP : 0 < P) (x : ℝ × Space) :
    ContDiff ℝ ∞ (fun w : ℝ × Space => ∑' k : ℤ, κ (x - w + ((k : ℝ) * P, 0))) := by
  rw [contDiff_iff_contDiffAt]
  intro w0
  obtain ⟨S, hS⟩ := shiftSum_eventuallyEq_finset hκ hP x w0
  have hfin : ContDiff ℝ ∞ (fun w : ℝ × Space => ∑ k ∈ S, κ (x - w + ((k : ℝ) * P, 0))) := by
    apply ContDiff.sum
    intro k _
    exact hκs.comp ((contDiff_const.sub contDiff_id).add contDiff_const)
  exact (hfin.contDiffAt).congr_of_eventuallyEq hS

/-- The periodised translate of `ρ` is a phase test. -/
theorem shiftTestPhase : ShiftTestPhase := by
  intro P hP ρ x e
  have hκs : ContDiff ℝ ∞ (ρ.normed volume) := ρ.contDiff_normed
  have hκ : HasCompactSupport (ρ.normed volume) := ρ.hasCompactSupport_normed
  obtain ⟨R0, hR0⟩ := exists_radius_of_hasCompactSupport hκ
  refine ⟨?_, ?_, ?_⟩
  · unfold shiftTest shiftKer
    exact (shiftSum_contDiff hκs hκ hP x).smul contDiff_const
  · intro τ y
    unfold shiftTest shiftKer
    congr 1
    calc ∑' k : ℤ, (ρ.normed volume) (x - ((τ + P, y) : ℝ × Space) + ((k : ℝ) * P, 0))
        = ∑' k : ℤ, (ρ.normed volume) (x - (τ, y) + (((k - 1 : ℤ) : ℝ) * P, 0)) := by
          apply tsum_congr
          intro k
          congr 1
          push_cast
          ext <;> simp <;> ring
      _ = ∑' k : ℤ, (ρ.normed volume) (x - (τ, y) + ((k : ℝ) * P, 0)) :=
          Equiv.tsum_eq (Equiv.subRight (1 : ℤ))
            (fun k : ℤ => (ρ.normed volume) (x - (τ, y) + ((k : ℝ) * P, 0)))
  · refine ⟨R0 + ‖x.2‖, fun τ y hy => ?_⟩
    unfold shiftTest shiftKer
    have hterm : ∀ k : ℤ, (ρ.normed volume) (x - (τ, y) + ((k : ℝ) * P, 0)) = 0 := by
      intro k
      by_contra hne
      have h1 := hR0 _ hne
      have h2 := norm_snd_le (x - (τ, y) + ((k : ℝ) * P, 0))
      have h3 : (x - (τ, y) + ((k : ℝ) * P, 0)).2 = x.2 - y := by
        simp
      rw [h3] at h2
      have h4 := norm_sub_le x.2 (x.2 - y)
      have h5 : x.2 - (x.2 - y) = y := by abel
      rw [h5] at h4
      linarith
    simp [hterm]

end UnforcedLeray.Short.PartIIIb.Concrete
