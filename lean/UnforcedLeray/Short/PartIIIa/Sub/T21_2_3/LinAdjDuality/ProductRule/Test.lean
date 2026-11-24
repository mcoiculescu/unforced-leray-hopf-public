import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_3_1_5
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_3.LinAdjDuality.CutProps

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff Interval

namespace UnforcedLeray.Short.IIIa

namespace LadPRTestAux

lemma cutPhi_smooth {φ : ℝ → ℝ × ℝ → ℂ} {t s : ℝ}
    (hφ : ContDiffOn ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => φ p.1 p.2) (Ico t s ×ˢ univ))
    {ρ : ℝ} (hρ : ρ ∈ Ico t s) (R : ℝ) (hc : ContDiff ℝ ∞ (ladCut R)) :
    ContDiff ℝ ∞ (fun x : ℝ × ℝ => ladCutPhi φ R ρ x) := by
  have hg : ContDiff ℝ ∞ (fun x : ℝ × ℝ => φ ρ x) :=
    hφ.comp_contDiff (contDiff_const.prodMk contDiff_id) (fun x => ⟨hρ, mem_univ _⟩)
  have hc' : ContDiff ℝ ∞ (fun x : ℝ × ℝ => ((ladCut R x : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp hc
  exact hc'.mul hg

lemma isCylTest_re_im {c : ℝ} {F : ℝ × ℝ → ℂ} (hs : ContDiff ℝ ∞ F)
    (hp : ∀ x : ℝ × ℝ, F (x.1 + c, x.2) = F x) (R' : ℝ)
    (hb : ∀ x : ℝ × ℝ, R' < |x.2| → F x = 0) :
    B0579.IsCylTest c (fun x => (F x).re) ∧ B0579.IsCylTest c (fun x => (F x).im) := by
  refine ⟨⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩⟩
  · exact Complex.reCLM.contDiff.comp hs
  · intro x; simp only [hp x]
  · exact ⟨R', fun x hx => by simp [hb x hx]⟩
  · exact Complex.imCLM.contDiff.comp hs
  · intro x; simp only [hp x]
  · exact ⟨R', fun x hx => by simp [hb x hx]⟩

end LadPRTestAux

open LadPRTestAux in
theorem ladPRTest : LadPRTest := by
  intro c t s φ hc hφ hper R hR ρ hρ
  obtain ⟨K, hK0, hK⟩ := ladCutProps
  obtain ⟨hc1, _, _, hc4, _, _⟩ := hK R hR
  have hsm := cutPhi_smooth hφ hρ R (hc1 c).smooth
  have hpe : ∀ x : ℝ × ℝ, ladCutPhi φ R ρ (x.1 + c, x.2) = ladCutPhi φ R ρ x := by
    intro x
    simp only [ladCutPhi, (hc1 c).periodic x, hper ρ hρ x]
  have hb : ∀ x : ℝ × ℝ, 2 * R < |x.2| → ladCutPhi φ R ρ x = 0 := by
    intro x hx
    have hR0 : 0 < 2 * R := by linarith
    have h1 : 2 * R ^ 2 ≤ x.2 ^ 2 := by nlinarith [sq_abs x.2, abs_nonneg x.2]
    have h2 : ladCut R x = 0 := hc4 x h1
    simp [ladCutPhi, h2]
  exact isCylTest_re_im hsm hpe (2 * R) hb

end UnforcedLeray.Short.IIIa
