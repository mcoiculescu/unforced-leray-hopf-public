import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_7_2_1_2

/-!
# `PartIII-a:T21/2/7/2/1/2`, task `endAgeAeCell`: the end slice is a version of `φ t` on the cell

Proves `EndAgeAeCell` (measure theory, `IsAdjointWeak.strongCont` at the end age, SP 3060): if `g`
is continuous on `[t, s) × ℝ²`, its slices before `s` are versions of `φ r`, and `φ r → φ t` in
`X_{-m,c}` as `r → t+`, then `g(t, ·) = φ t` almost everywhere on the cell.

Proof: along `r_n = t + (s - t)/(n + 2)` the `L²(cellMeasure c (-m))` convergence gives convergence in
measure (`tendstoInMeasure_of_tendsto_eLpNorm`), hence an a.e. convergent subsequence
(`TendstoInMeasure.exists_seq_tendsto_ae`). Along the same subsequence the slices `g(r_n, ·)`
converge pointwise to `g(t, ·)` (`endSlice_tendsto`). The slices agree with the versions `φ r_n`
a.e. (countably many, `ae_all_iff`), so the two limits coincide a.e. The cell measure and the
restriction of Lebesgue measure to the cell are equivalent (`B0579.ac_cellMeasure`,
`B0579.cellMeasure_ac`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

theorem endAgeAeCell : UnforcedLeray.Short.IIIa.EndAgeAeCell := by
  intro c m t s hts φ g hg hae hmem hT
  -- the sequence `r n ↓ t` inside `(t, s)`
  obtain ⟨r, hr_def⟩ : ∃ r : ℕ → ℝ, r = fun n : ℕ => t + (s - t) / ((n : ℝ) + 2) := ⟨_, rfl⟩
  have hrkey : ∀ n : ℕ, r n = t + (s - t) / ((n : ℝ) + 2) := fun n => by rw [hr_def]
  have hrmem : ∀ n, r n ∈ Ioo t s := by
    intro n
    have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    have hpos : 0 < (s - t) / ((n : ℝ) + 2) := div_pos (sub_pos.2 hts) (by linarith)
    have hlt : (s - t) / ((n : ℝ) + 2) < s - t :=
      div_lt_self (sub_pos.2 hts) (by linarith)
    rw [hrkey n]
    exact ⟨by linarith, by linarith⟩
  have hrlim : Tendsto r atTop (𝓝 t) := by
    have hdiv : Tendsto (fun n : ℕ => (s - t) / ((n : ℝ) + 2)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop
        (tendsto_atTop_add_const_right _ (2 : ℝ) tendsto_natCast_atTop_atTop)
    have h2 : Tendsto (fun n : ℕ => t + (s - t) / ((n : ℝ) + 2)) atTop (𝓝 (t + 0)) :=
      tendsto_const_nhds.add hdiv
    rw [add_zero] at h2
    rw [hr_def]
    exact h2
  have hr_within : Tendsto r atTop (𝓝[Ioo t s] t) :=
    tendsto_nhdsWithin_iff.2 ⟨hrlim, Eventually.of_forall hrmem⟩
  -- the cell measure and Lebesgue measure on the cell are mutually absolutely continuous
  have hμv : B0579.cellMeasure c (-m) ≪ volume :=
    (B0579.cellMeasure_ac c (-m)).trans (Measure.absolutelyContinuous_of_le Measure.restrict_le_self)
  have hcont : ∀ n, Continuous fun x : ℝ × ℝ => g (r n, x) := by
    intro n
    exact endSlice_continuous hg ⟨(hrmem n).1.le, (hrmem n).2⟩
  have heqn : ∀ n, ∀ᵐ x ∂(B0579.cellMeasure c (-m)), g (r n, x) = φ (r n) x := by
    intro n
    exact hμv.ae_le (hae (r n) (hrmem n) : ∀ᵐ x ∂volume, g (r n, x) = φ (r n) x)
  have hmeas : ∀ n, AEStronglyMeasurable (φ (r n)) (B0579.cellMeasure c (-m)) := fun n =>
    (hcont n).aestronglyMeasurable.congr (heqn n)
  have hφt : AEStronglyMeasurable (φ t) (B0579.cellMeasure c (-m)) := hmem.aestronglyMeasurable
  have hfg : Tendsto (fun n => eLpNorm (φ (r n) - φ t) 2 (B0579.cellMeasure c (-m))) atTop
      (𝓝 0) := hT.comp hr_within
  have hTIM : TendstoInMeasure (B0579.cellMeasure c (-m)) (fun n => φ (r n)) atTop (φ t) :=
    tendstoInMeasure_of_tendsto_eLpNorm (by norm_num : (2 : ℝ≥0∞) ≠ 0) hmeas hφt hfg
  obtain ⟨ns, hns, hconv⟩ := hTIM.exists_seq_tendsto_ae
  have hgr : ∀ᵐ x ∂(B0579.cellMeasure c (-m)), ∀ n, g (r n, x) = φ (r n) x :=
    ae_all_iff.2 heqn
  have hr_gt : Tendsto (fun k => r (ns k)) atTop (𝓝[>] t) :=
    tendsto_nhdsWithin_iff.2 ⟨hrlim.comp hns.tendsto_atTop,
      Eventually.of_forall fun k => (hrmem (ns k)).1⟩
  have hmain : ∀ᵐ x ∂(B0579.cellMeasure c (-m)), g (t, x) = φ t x := by
    filter_upwards [hconv, hgr] with x hx1 hx2
    have hA : Tendsto (fun k => g (r (ns k), x)) atTop (𝓝 (g (t, x))) :=
      (endSlice_tendsto hts hg x).comp hr_gt
    have hB : Tendsto (fun k => g (r (ns k), x)) atTop (𝓝 (φ t x)) :=
      hx1.congr (fun k => (hx2 (ns k)).symm)
    exact tendsto_nhds_unique hA hB
  exact (B0579.ac_cellMeasure c (-m)).ae_le hmain

end UnforcedLeray.Short.IIIa
