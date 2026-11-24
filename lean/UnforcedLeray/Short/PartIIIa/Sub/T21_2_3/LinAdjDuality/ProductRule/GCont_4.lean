import UnforcedLeray.Short.PartIIIa.Sub.T21_2_3.LinAdjDuality.ProductRule.PairCont

/-!
# Joint `C²` regularity of the cut-off adjoint (SP 3074-3075, `PartIII-a:T21/2/3/1/5/3/4`)

The cut-off `χ_R(x) = ζ(2 - η²/R²)` is smooth in `x`, and `φ` is jointly smooth on
`[t, s) × ℝ²`. On `[t, r] × ℝ²` with `r < s` the product `χ_R φ(ρ, x)` is therefore jointly `C²`,
and it vanishes for `|η| > 2R` (`LadPRPairAux.cut_zero`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff Interval

namespace UnforcedLeray.Short.IIIa

namespace GCont4Aux

/-- The transverse cut-off `x ↦ χ_R(x)` is smooth on `ℝ²`. -/
lemma contDiff_ladCut' (R : ℝ) : ContDiff ℝ ∞ (fun x : ℝ × ℝ => ladCut R x) := by
  unfold ladCut
  exact Real.smoothTransition.contDiff.comp
    (contDiff_const.sub ((contDiff_snd.pow 2).div_const (R ^ 2)))

end GCont4Aux

open GCont4Aux in
/-- **Leaf 4** (joint `C²` of the cut-off adjoint on `[t, r] × ℝ²`, and its vanishing for
`|η| > 2R`). -/
theorem ladCutPhi_jointC2 {c t s R : ℝ} {φ : ℝ → ℝ × ℝ → ℂ} (hR : 0 < R) (hs : ContDiffOn ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => φ p.1 p.2) (Set.Ico t s ×ˢ Set.univ)) {r : ℝ} (hr : r < s) : ContDiffOn ℝ 2 (fun p : ℝ × (ℝ × ℝ) => ladCutPhi φ R p.1 p.2) (Set.Icc t r ×ˢ Set.univ) ∧ ∀ ρ x, 2 * R < |x.2| → ladCutPhi φ R ρ x = 0 := by
  refine ⟨?_, fun ρ x hx => ?_⟩
  · have hsub : Icc t r ×ˢ (univ : Set (ℝ × ℝ)) ⊆ Ico t s ×ˢ (univ : Set (ℝ × ℝ)) :=
      prod_mono (fun ρ hρ => ⟨hρ.1, lt_of_le_of_lt hρ.2 hr⟩) (subset_univ _)
    have hφ : ContDiffOn ℝ 2 (fun p : ℝ × (ℝ × ℝ) => φ p.1 p.2) (Icc t r ×ˢ univ) :=
      (hs.mono hsub).of_le (by simp)
    have hcut : ContDiff ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => ((ladCut R p.2 : ℝ) : ℂ)) :=
      Complex.ofRealCLM.contDiff.comp ((contDiff_ladCut' R).comp contDiff_snd)
    have hcut2 : ContDiff ℝ 2 (fun p : ℝ × (ℝ × ℝ) => ((ladCut R p.2 : ℝ) : ℂ)) :=
      hcut.of_le (by simp)
    exact hcut2.contDiffOn.mul hφ
  · unfold ladCutPhi
    rw [LadPRPairAux.cut_zero hR hx]
    simp
