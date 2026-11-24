import UnforcedLeray.Short.PartIIIa.Sub.AdjInterior.STSmooth.Defs
import UnforcedLeray.Short.PartIIIa.Tasks.AdjSmooth.Interior.STSmoothRep.CutoffGlobal
import UnforcedLeray.Short.PartIIIa.Tasks.AdjSmooth.Interior.STSmoothRep.GlobalEmbedding
import Mathlib.Analysis.Calculus.BumpFunction.Basic
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.Analysis.Calculus.ContDiff.Defs

/-!
# `PartIII-a:T21/2/7/2/1/1/8/5`: local `C^∞` versions of `H^∞_loc(U)` (`stLocalSmoothOfSob`)

Source: SP 3060-3061 (`the November 2 reference manuscript`).

For `p ∈ U` choose `r > 0` with `closedBall p (2r) ⊆ U`, and the bump `ζ` with `ζ = 1` on
`closedBall p r` and `tsupport ζ = closedBall p (2r)`.  `ζ • F` is in `H^∞(ℝ × ℝ²)`
(`stCutoffGlobal`), so for every `k` it has a `C^k` version `G k` (`stGlobalEmbedding`).  On the
the ball `B = ball p r`, `G 0` and `G k` are continuous and a.e. equal to `ζ • F = F`, hence equal
on `B` (`Measure.eqOn_open_of_ae_eq`).  So `G 0` is `C^k` on `B` for every `k`, i.e. `C^∞`, and
`G 0 = F` a.e. on `B`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Metric
open scoped ContDiff

namespace UnforcedLeray.Short.IIIa

theorem stLocalSmoothOfSob : STLocalSmoothOfSob := by
  intro U hU F hF
  unfold STLocalSmooth
  intro p hp
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hU p hp
  obtain ⟨r, hr_pos, hr_lt⟩ : ∃ r : ℝ, 0 < r ∧ 2 * r < ε :=
    ⟨ε / 3, by linarith, by linarith⟩
  obtain ⟨ζb, hrIn, hrOut⟩ : ∃ ζb : ContDiffBump p, ζb.rIn = r ∧ ζb.rOut = 2 * r :=
    ⟨⟨r, 2 * r, hr_pos, by linarith⟩, rfl, rfl⟩
  have hsubU : closedBall p (2 * r) ⊆ U :=
    (Metric.closedBall_subset_ball hr_lt).trans hball
  have hsub : ball p r ⊆ U :=
    Metric.ball_subset_closedBall.trans
      ((Metric.closedBall_subset_closedBall (x := p) (show r ≤ 2 * r by linarith)).trans hsubU)
  have htsupp : tsupport (⇑ζb) ⊆ U := by
    rw [ζb.tsupport_eq, hrOut]
    exact hsubU
  have hglob : IsSTSobolevGlobal (fun q => (⇑ζb) q • F q) :=
    stCutoffGlobal U hU F hF (⇑ζb) ζb.contDiff ζb.hasCompactSupport htsupp
  have key : ∀ k : ℕ, ∃ G : STSpace → ℂ, ContDiff ℝ k G ∧
      G =ᵐ[volume] (fun q => (⇑ζb) q • F q) := fun k => stGlobalEmbedding _ hglob k
  choose G hGk hGae using key
  have hEq : ∀ k : ℕ, EqOn (G 0) (G k) (ball p r) := by
    intro k
    have hae : G 0 =ᵐ[volume.restrict (ball p r)] G k :=
      (((hGae 0).trans (hGae k).symm)).restrict
    have hc0 : ContinuousOn (G 0) (ball p r) := (hGk 0).continuous.continuousOn
    have hck : ContinuousOn (G k) (ball p r) := (hGk k).continuous.continuousOn
    exact Measure.eqOn_open_of_ae_eq hae Metric.isOpen_ball hc0 hck
  have hsmooth : ContDiffOn ℝ ∞ (G 0) (ball p r) := by
    rw [contDiffOn_infty]
    intro k
    exact ((hGk k).contDiffOn).congr (fun x hx => hEq k hx)
  refine ⟨r, hr_pos, hsub, G 0, hsmooth, ?_⟩
  filter_upwards [hGae 0] with q hq
  intro hmem
  have hin : q ∈ closedBall p ζb.rIn := by
    rw [hrIn]
    exact Metric.ball_subset_closedBall hmem
  have h1 : (⇑ζb) q = 1 := ζb.one_of_mem_closedBall hin
  rw [hq, h1, one_smul]

end UnforcedLeray.Short.IIIa
