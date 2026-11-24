import UnforcedLeray.Short.PartI.Sub.PartI_T09

/-!
# `PartI:T09` leaf 2: the continuity (bootstrap) argument (`BootstrapContinuity`)

Source of record: `shorter-proof-2026-11-02.tex`, line 355 (closure of the bootstrap by continuity
from the datum). Pure real analysis: let `T = {x ∈ [0,S] | g ≤ h on [0,x]}`, take `x* = sSup T`,
show `g ≤ h` on `[0,x*]` (closedness of `{g - h ≤ 0}` on `[0,S]`), use the hypothesis at `x*`
to get strict inequality there, and push past `x*` by continuity unless `x* = S`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal ContDiff Topology

namespace UnforcedLeray.Short.PartI

theorem bootstrapContinuity_proof : BootstrapContinuity := by
  intro S hS g h hg hh hhpos hg0 hstep s0 hs0
  set T : Set ℝ := {x | x ∈ Icc 0 S ∧ ∀ r ∈ Icc 0 x, g r ≤ h r} with hT
  have h0T : (0 : ℝ) ∈ T := by
    refine ⟨⟨le_rfl, hS⟩, fun r hr => ?_⟩
    have hr0 : r = 0 := le_antisymm hr.2 hr.1
    rw [hr0]
    exact hg0
  have hbdd : BddAbove T := ⟨S, fun x hx => hx.1.2⟩
  have hne : T.Nonempty := ⟨0, h0T⟩
  set xs : ℝ := sSup T with hxs
  have hxsS : xs ≤ S := csSup_le hne (fun x hx => hx.1.2)
  have hxs0 : 0 ≤ xs := le_csSup hbdd h0T
  have hlt : ∀ r ∈ Ico 0 xs, g r ≤ h r := by
    intro r hr
    obtain ⟨x, hxT, hrx⟩ := exists_lt_of_lt_csSup hne hr.2
    exact hxT.2 r ⟨hr.1, hrx.le⟩
  have hD : ∀ r ∈ Icc 0 xs, g r ≤ h r := by
    intro r hr
    rcases eq_or_lt_of_le hr.2 with hrx | hrx
    · rcases eq_or_lt_of_le hr.1 with h0 | hpos
      · rw [← h0]
        exact hg0
      · have hne' : (0 : ℝ) ≠ xs := by
          rw [← hrx]
          exact hpos.ne
        have hP : IsClosed (Icc 0 S ∩ (fun r => g r - h r) ⁻¹' Iic 0) :=
          (hg.sub hh).preimage_isClosed_of_isClosed isClosed_Icc isClosed_Iic
        have hsub : Ico 0 xs ⊆ Icc 0 S ∩ (fun r => g r - h r) ⁻¹' Iic 0 := fun r hr' =>
          ⟨⟨hr'.1, hr'.2.le.trans hxsS⟩, sub_nonpos.2 (hlt r hr')⟩
        have hmem : xs ∈ closure (Ico 0 xs) := by
          rw [closure_Ico hne']
          exact ⟨hxs0, le_rfl⟩
        have hcl := closure_mono hsub hmem
        rw [hP.closure_eq] at hcl
        have hxsle : g xs - h xs ≤ 0 := hcl.2
        rw [hrx]
        linarith
    · obtain ⟨x, hxT, hrx'⟩ := exists_lt_of_lt_csSup hne hrx
      exact hxT.2 r ⟨hr.1, hrx'.le⟩
  have hxsS' : xs = S := by
    by_contra hne_S
    have hlt' : xs < S := lt_of_le_of_ne hxsS hne_S
    have hxsI : xs ∈ Icc 0 S := ⟨hxs0, hxsS⟩
    have hneg : g xs - h xs < 0 := by
      have := hhpos xs hxsI
      have := hstep xs hxsI hD
      linarith
    have hcont : ContinuousWithinAt (fun r => g r - h r) (Icc 0 S) xs :=
      (hg.sub hh) xs hxsI
    have hev : ∀ᶠ r in 𝓝[Icc 0 S] xs, g r - h r < 0 :=
      Filter.Tendsto.eventually hcont (eventually_lt_nhds hneg)
    rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at hev
    obtain ⟨δ, hδ, hball⟩ := hev
    have hy1 : xs < min S (xs + δ / 2) := lt_min hlt' (by linarith)
    have hyS : min S (xs + δ / 2) ≤ S := min_le_left _ _
    have hyT : min S (xs + δ / 2) ∈ T := by
      refine ⟨⟨hxs0.trans hy1.le, hyS⟩, fun r hr => ?_⟩
      by_cases hrx : r ≤ xs
      · exact hD r ⟨hr.1, hrx⟩
      · have hxr : xs < r := not_le.1 hrx
        have hrS : r ∈ Icc 0 S := ⟨hr.1, hr.2.trans hyS⟩
        have hr_le : r ≤ xs + δ / 2 := hr.2.trans (min_le_right _ _)
        have hdist : dist r xs < δ := by
          rw [Real.dist_eq, abs_of_nonneg (by linarith)]
          linarith
        have hneg' : g r - h r < 0 := hball hdist hrS
        linarith
    have hle : min S (xs + δ / 2) ≤ xs := le_csSup hbdd hyT
    linarith
  have hsle : s0 ≤ xs := by
    rw [hxsS']
    exact hs0.2
  exact hstep s0 hs0 (fun r hr => hD r ⟨hr.1, hr.2.trans hsle⟩)

end UnforcedLeray.Short.PartI
