import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_4_2_3_2_3_2.Core
import Mathlib.Topology.ContinuousMap.SecondCountableSpace

/-!
# Countable approximating family of cylinder tests (helper for `pepsC0SliceDivFreeAE`)
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal InnerProductSpace ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

theorem hj3_isCylTest_zero (c : ℝ) : UnforcedLeray.B0579.IsCylTest c (fun _ => (0 : ℝ)) :=
  ⟨contDiff_const, fun _ => rfl, ⟨0, fun _ _ => rfl⟩⟩

/-- A countable family of cylinder tests vanishing for `|η| > N`, whose pairs of partial
derivatives approximate every such test uniformly on `[0,c] × [-N,N]`. -/
theorem hj3_sep {c : ℝ} (N : ℕ) :
    ∃ T : Set (ℝ × ℝ → ℝ), T.Countable ∧
      (∀ φ ∈ T, UnforcedLeray.B0579.IsCylTest c φ ∧ ∀ x : ℝ × ℝ, (N : ℝ) < |x.2| → φ x = 0) ∧
      ∀ ψ : ℝ × ℝ → ℝ, UnforcedLeray.B0579.IsCylTest c ψ →
        (∀ x : ℝ × ℝ, (N : ℝ) < |x.2| → ψ x = 0) →
        ∀ ε > 0, ∃ φ ∈ T, ∀ x ∈ Icc 0 c ×ˢ Icc (-(N : ℝ)) (N : ℝ),
          dist ((UnforcedLeray.B0579.pd 0 ψ x, UnforcedLeray.B0579.pd 1 ψ x) : ℝ × ℝ)
            ((UnforcedLeray.B0579.pd 0 φ x, UnforcedLeray.B0579.pd 1 φ x) : ℝ × ℝ) < ε := by
  classical
  set K : Set (ℝ × ℝ) := Icc 0 c ×ˢ Icc (-(N : ℝ)) (N : ℝ) with hKdef
  have hK : IsCompact K := isCompact_Icc.prod isCompact_Icc
  haveI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  obtain ⟨D, hDc, hDd⟩ := TopologicalSpace.exists_countable_dense C(K, ℝ × ℝ)
  haveI : Countable D := hDc.to_subtype
  let P : C(K, ℝ × ℝ) → ℝ → (ℝ × ℝ → ℝ) → Prop := fun d δ φ =>
    UnforcedLeray.B0579.IsCylTest c φ ∧ (∀ x : ℝ × ℝ, (N : ℝ) < |x.2| → φ x = 0) ∧
      ∀ x : K, dist ((UnforcedLeray.B0579.pd 0 φ x.1, UnforcedLeray.B0579.pd 1 φ x.1) : ℝ × ℝ)
        (d x) < δ
  let G : C(K, ℝ × ℝ) → ℕ → (ℝ × ℝ → ℝ) := fun d n =>
    if h : ∃ φ, P d (1 / ((n : ℝ) + 1)) φ then Classical.choose h else fun _ => 0
  have hGmem : ∀ (d : C(K, ℝ × ℝ)) (n : ℕ), UnforcedLeray.B0579.IsCylTest c (G d n) ∧
      ∀ x : ℝ × ℝ, (N : ℝ) < |x.2| → G d n x = 0 := by
    intro d n
    simp only [G]
    split_ifs with h
    · exact ⟨(Classical.choose_spec h).1, (Classical.choose_spec h).2.1⟩
    · exact ⟨hj3_isCylTest_zero c, fun _ _ => rfl⟩
  have hGspec : ∀ (d : C(K, ℝ × ℝ)) (n : ℕ), (∃ φ, P d (1 / ((n : ℝ) + 1)) φ) → P d (1 / ((n : ℝ) + 1)) (G d n) := by
    intro d n h
    simp only [G]
    rw [dif_pos h]
    exact Classical.choose_spec h
  refine ⟨Set.range (fun p : D × ℕ => G p.1 p.2), Set.countable_range _, ?_, ?_⟩
  · rintro φ ⟨p, rfl⟩
    exact hGmem p.1 p.2
  · intro ψ hψ hvan ε hε
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt (half_pos hε)
    have hδ : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    have hcont : Continuous (fun x : K => ((UnforcedLeray.B0579.pd 0 ψ x.1,
        UnforcedLeray.B0579.pd 1 ψ x.1) : ℝ × ℝ)) :=
      ((hj3_pd_continuous hψ 0).comp continuous_subtype_val).prodMk
        ((hj3_pd_continuous hψ 1).comp continuous_subtype_val)
    obtain ⟨d, hdD, hdist⟩ := hDd.exists_dist_lt (⟨_, hcont⟩ : C(K, ℝ × ℝ)) hδ
    have hex : ∃ φ, P d (1 / ((n : ℝ) + 1)) φ :=
      ⟨ψ, hψ, hvan, fun x => lt_of_le_of_lt (ContinuousMap.dist_apply_le_dist (f := (⟨_, hcont⟩ : C(K, ℝ × ℝ))) x) hdist⟩
    refine ⟨G d n, ⟨(⟨d, hdD⟩, n), rfl⟩, ?_⟩
    intro x hx
    have hG' := (hGspec d n hex).2.2 ⟨x, hx⟩
    have h1 : dist ((UnforcedLeray.B0579.pd 0 ψ x, UnforcedLeray.B0579.pd 1 ψ x) : ℝ × ℝ)
        (d ⟨x, hx⟩) < 1 / ((n : ℝ) + 1) :=
      lt_of_le_of_lt (ContinuousMap.dist_apply_le_dist (f := (⟨_, hcont⟩ : C(K, ℝ × ℝ))) ⟨x, hx⟩)
        hdist
    have h2 : dist (d ⟨x, hx⟩)
        ((UnforcedLeray.B0579.pd 0 (G d n) x, UnforcedLeray.B0579.pd 1 (G d n) x) : ℝ × ℝ)
        < 1 / ((n : ℝ) + 1) := by
      rw [dist_comm]; exact hG'
    have h3 := dist_triangle ((UnforcedLeray.B0579.pd 0 ψ x, UnforcedLeray.B0579.pd 1 ψ x) :
      ℝ × ℝ) (d ⟨x, hx⟩) ((UnforcedLeray.B0579.pd 0 (G d n) x,
        UnforcedLeray.B0579.pd 1 (G d n) x) : ℝ × ℝ)
    linarith

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
