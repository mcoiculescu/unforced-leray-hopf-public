import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_6_3_4.VtvFubiniInner.Exch
import Mathlib.Analysis.Calculus.BumpFunction.Basic
import Mathlib.Analysis.Calculus.ContDiff.Basic

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray
open scoped ContDiff ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst.FubiniInner

theorem bump_cyl (c R : ℝ) :
    ∃ χ : ℝ × ℝ → ℝ, B0579.IsCylTest c χ ∧ ∀ x : ℝ × ℝ, |x.2| ≤ R → χ x = 1 := by
  let f : ContDiffBump (0 : ℝ) := ⟨|R| + 1, |R| + 2, by positivity, by linarith⟩
  refine ⟨fun x => f x.2, ⟨?_, fun x => rfl, ⟨|R| + 2, fun x hx => ?_⟩⟩, fun x hx => ?_⟩
  · exact f.contDiff.comp contDiff_snd
  · apply f.zero_of_le_dist
    rw [Real.dist_eq, sub_zero]
    exact hx.le
  · apply f.one_of_mem_closedBall
    rw [Metric.mem_closedBall, Real.dist_eq, sub_zero]
    show |x.2| ≤ |R| + 1
    linarith [le_abs_self R]

theorem Tstep {c : ℝ} {A : ℝ × ℝ → ℂ}
    (hA : ∀ ψ : ℝ × ℝ → ℝ, B0579.IsCylTest c ψ → IntegrableOn (fun x => A x * (ψ x : ℂ)) (B0579.cell c))
    {H : ℝ × (ℝ × ℝ) → ℝ} (hH : ContDiff ℝ ∞ H) {s1 s2 R : ℝ}
    (hz : ∀ p : ℝ × (ℝ × ℝ), (p.1 < s1 ∨ s2 < p.1 ∨ R < |p.2.2|) → H p = 0)
    {r : ℝ} (hr : 0 < r) :
    Integrable (fun s : ℝ => if r ≤ s then ∫ x in B0579.cell c, A x * (Ds H (s, x) : ℂ) else 0)
        (volume.restrict (Ioi (0 : ℝ))) ∧
      ∫ s in Ioi (0 : ℝ), (if r ≤ s then ∫ x in B0579.cell c, A x * (Ds H (s, x) : ℂ) else 0) =
        - ∫ x in B0579.cell c, A x * (H (r, x) : ℂ) := by
  obtain ⟨χ, hχ, hχ1⟩ := bump_cyl c R
  have hU : IsOpen {p : ℝ × (ℝ × ℝ) | p.1 < s1 ∨ s2 < p.1 ∨ R < |p.2.2|} := by
    refine (isOpen_lt continuous_fst continuous_const).union ?_
    exact (isOpen_lt continuous_const continuous_fst).union
      (isOpen_lt continuous_const (continuous_abs.comp (continuous_snd.comp continuous_snd)))
  have hDz := zero_Ds hU hz
  have hswap : ∀ (J : ℝ × ℝ → ℝ), (∀ x : ℝ × ℝ, R < |x.2| → J x = 0) → ∀ x : ℝ × ℝ,
      A x * (J x : ℂ) = (A x * (χ x : ℂ)) * (J x : ℂ) := by
    intro J hJ x
    by_cases hx : |x.2| ≤ R
    · rw [hχ1 x hx]; simp
    · have hx' : R < |x.2| := not_le.1 hx
      rw [hJ x hx']; simp
  obtain ⟨h1, h2⟩ := exch (hA χ hχ) hH hz hr
  have e1 : (fun s : ℝ => if r ≤ s then ∫ x in B0579.cell c, A x * (Ds H (s, x) : ℂ) else 0) =
      (fun s : ℝ => if r ≤ s then ∫ x in B0579.cell c, (A x * (χ x : ℂ)) * (Ds H (s, x) : ℂ)
        else 0) := by
    funext s
    split_ifs
    · refine integral_congr_ae (Eventually.of_forall fun x => ?_)
      exact hswap (fun y => Ds H (s, y)) (fun y hy => hDz (s, y) (Or.inr (Or.inr hy))) x
    · rfl
  have e2 : ∫ x in B0579.cell c, A x * (H (r, x) : ℂ) =
      ∫ x in B0579.cell c, (A x * (χ x : ℂ)) * (H (r, x) : ℂ) :=
    integral_congr_ae (Eventually.of_forall fun x =>
      hswap (fun y => H (r, y)) (fun y hy => hz (r, y) (Or.inr (Or.inr hy))) x)
  rw [e1, e2]
  exact ⟨h1, h2⟩

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst.FubiniInner
