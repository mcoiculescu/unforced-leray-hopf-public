import UnforcedLeray.Analysis.Sturm.PotentialDecay
import Mathlib.Tactic

/-! A uniform tail cutoff for the actual Gaussian potential, derived from its
proved limits at both ends rather than supplied as an estimate hypothesis. -/
noncomputable section
open Set Filter
open scoped Topology
namespace UnforcedLeray.Rayleigh
open GaussianPotential Sturm

theorem exists_potential_tail_bound {ε : ℝ} (hε : 0 < ε) :
    ∃ R : ℝ, 0 < R ∧ ∀ t : ℝ, t ∉ Icc (-R) R → Wlog t ≤ ε := by
  have htop : ∀ᶠ t : ℝ in atTop, Wlog t < ε :=
    tendsto_Wlog_atTop.eventually (gt_mem_nhds hε)
  have hbot : ∀ᶠ t : ℝ in atBot, Wlog t < ε :=
    tendsto_Wlog_atBot.eventually (gt_mem_nhds hε)
  obtain ⟨a, ha⟩ := eventually_atTop.mp htop
  obtain ⟨b, hb⟩ := eventually_atBot.mp hbot
  let R : ℝ := max 1 (max a (-b))
  have hR1 : 1 ≤ R := le_max_left _ _
  have hRa : a ≤ R := (le_max_left _ _).trans (le_max_right _ _)
  have hRb : -b ≤ R := (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨R, by linarith, ?_⟩
  intro t ht
  have ht' : t < -R ∨ R < t := by
    simpa only [mem_Icc, not_and_or, not_le] using ht
  rcases ht' with ht | ht
  · exact (hb t (by linarith)).le
  · exact (ha t (by linarith)).le

end UnforcedLeray.Rayleigh
