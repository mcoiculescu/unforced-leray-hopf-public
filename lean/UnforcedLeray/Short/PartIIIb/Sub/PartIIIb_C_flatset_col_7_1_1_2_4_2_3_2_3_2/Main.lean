import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_4_2_3_2_3_2.Slice
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_4_2_3_2_3_1

/-!
# The a.e. slice divergence-free property (helper for `pepsC0SliceDivFreeAE`)
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal InnerProductSpace ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

theorem hj3_main {c : ℝ} (hc : 0 < c)
    (b : UnforcedLeray.B0220.HSpace c UnforcedLeray.B0223.MeridC)
    (hb : b ∈ UnforcedLeray.Short.PartIIa.solenoidalHC 0 c) :
    ∀ᵐ s ∂(volume.restrict (Ioi (0 : ℝ))), ∀ ψ : ℝ × ℝ → ℝ,
      UnforcedLeray.B0579.IsCylTest c ψ →
      ∫ x in stripSet c,
        ((b : UnforcedLeray.B0220.Profile → UnforcedLeray.B0223.MeridC) (s, x) 0 *
            ((UnforcedLeray.B0579.pd 0 ψ x : ℝ) : ℂ) +
          (b : UnforcedLeray.B0220.Profile → UnforcedLeray.B0223.MeridC) (s, x) 1 *
            ((UnforcedLeray.B0579.pd 1 ψ x : ℝ) : ℂ)) = 0 := by
  choose T hTc hTcls hTapp using fun N : ℕ => hj3_sep (c := c) N
  have hAE1 : ∀ᵐ s ∂(volume.restrict (Ioi (0 : ℝ))), ∀ N : ℕ, ∀ φ ∈ T N,
      ∫ x in stripSet c,
        ((b : UnforcedLeray.B0220.Profile → UnforcedLeray.B0223.MeridC) (s, x) 0 *
            ((UnforcedLeray.B0579.pd 0 φ x : ℝ) : ℂ) +
          (b : UnforcedLeray.B0220.Profile → UnforcedLeray.B0223.MeridC) (s, x) 1 *
            ((UnforcedLeray.B0579.pd 1 φ x : ℝ) : ℂ)) = 0 :=
    ae_all_iff.2 fun N => (ae_ball_iff (hTc N)).2 fun φ hφ =>
      hj3_core hc b hb (hTcls N φ hφ).1
  have hF : MemLp (fun p => toMC
      (((b : UnforcedLeray.B0220.Profile → UnforcedLeray.B0223.MeridC) p).ofLp)) 2
      (UnforcedLeray.B0220.measureH c) := by
    simpa [toMC] using Lp.memLp b
  have hAE2 := pepsC0SliceMemLp c hc
    (fun p => ((b : UnforcedLeray.B0220.Profile → UnforcedLeray.B0223.MeridC) p).ofLp) hF
  filter_upwards [hAE1, hAE2] with s hs1 hs2
  intro ψ hψ
  have hs2' : MemLp (fun x : ℝ × ℝ =>
      (b : UnforcedLeray.B0220.Profile → UnforcedLeray.B0223.MeridC) (s, x))
      2 (volume.restrict (stripSet c)) := by
    simpa [toMC] using hs2
  obtain ⟨R, hR⟩ := hψ.band
  set N : ℕ := ⌈R⌉₊ with hNdef
  have hvan : ∀ x : ℝ × ℝ, (N : ℝ) < |x.2| → ψ x = 0 := fun x hx =>
    hR x (lt_of_le_of_lt (Nat.le_ceil R) hx)
  set B : ℝ × ℝ → UnforcedLeray.B0223.MeridC :=
    fun x => (b : UnforcedLeray.B0220.Profile → UnforcedLeray.B0223.MeridC) (s, x) with hBdef
  show ∫ x in stripSet c, hj3H B ψ x = 0
  have hBi : IntegrableOn (fun x => ‖B x‖) (hj3Block c (N : ℝ)) (volume.restrict (stripSet c)) := by
    have h1 : MemLp (fun x => ‖B x‖) 2 (volume.restrict (stripSet c)) := hs2'.norm
    haveI : IsFiniteMeasure ((volume.restrict (stripSet c)).restrict (hj3Block c (N : ℝ))) :=
      isFiniteMeasure_restrict.2 (ne_top_of_le_ne_top
        (hj3Block_compact c (N : ℝ)).measure_lt_top.ne (Measure.restrict_apply_le _ _))
    exact MemLp.integrable (by norm_num) (h1.restrict _)
  have hBm : AEStronglyMeasurable B (volume.restrict (stripSet c)) := hs2'.aestronglyMeasurable
  set C : ℝ := ∫ x in hj3Block c (N : ℝ), ‖B x‖ ∂(volume.restrict (stripSet c)) with hCdef
  have hC0 : 0 ≤ C := integral_nonneg fun x => norm_nonneg _
  have key : ∀ ε > 0, ‖∫ x in stripSet c, hj3H B ψ x‖ ≤ 2 * ε * C := by
    intro ε hε
    obtain ⟨φ, hφT, hφapp⟩ := hTapp N ψ hψ hvan ε hε
    have hφc := hTcls N φ hφT
    have hgφ : ∫ x in stripSet c, hj3H B φ x = 0 := hs1 N φ hφT
    have hψK := hj3_strip_to_block (c := c) (N := (N : ℝ)) (B := B) hvan
    have hφK := hj3_strip_to_block (c := c) (N := (N : ℝ)) (B := B) hφc.2
    have hdiff := hj3_slice_diff (c := c) (N := (N : ℝ)) (ε := ε) hBi hBm hψ hφc.1 hφapp
    have hφ0 : ∫ x in hj3Block c (N : ℝ), hj3H B φ x ∂(volume.restrict (stripSet c)) = 0 := by
      rw [← hφK]; exact hgφ
    rw [hψK]
    calc ‖∫ x in hj3Block c (N : ℝ), hj3H B ψ x ∂(volume.restrict (stripSet c))‖
        = ‖∫ x in hj3Block c (N : ℝ), hj3H B ψ x ∂(volume.restrict (stripSet c)) -
            ∫ x in hj3Block c (N : ℝ), hj3H B φ x ∂(volume.restrict (stripSet c))‖ := by
          rw [hφ0, sub_zero]
      _ ≤ 2 * ε * C := hdiff
  by_contra hne
  have hr : 0 < ‖∫ x in stripSet c, hj3H B ψ x‖ := norm_pos_iff.2 hne
  have hk := key (‖∫ x in stripSet c, hj3H B ψ x‖ / (4 * (C + 1))) (by positivity)
  set r : ℝ := ‖∫ x in stripSet c, hj3H B ψ x‖ with hrdef
  have e : 2 * (r / (4 * (C + 1))) * C = r * (C / (2 * (C + 1))) := by
    field_simp
    ring
  have hlt : C / (2 * (C + 1)) < 1 := by
    rw [div_lt_one (by positivity)]
    linarith
  have hfin : r * (C / (2 * (C + 1))) < r := by nlinarith
  linarith [hk, e, hfin]

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
