import UnforcedLeray.Short.PartIIa.Calc.JetClass

set_option autoImplicit false

noncomputable section

open Set Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.PartIIa.Jet

open UnforcedLeray.B0184 UnforcedLeray.B0185 UnforcedLeray.B0188 UnforcedLeray.B0190

theorem smoothClosure : SmoothClosure := by
  unfold SmoothClosure
  intro F G hF hG
  unfold JSmooth at hF hG ⊢
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro ν c hν hc tr htr
    exact (hF ν c hν hc tr htr).add (hG ν c hν hc tr htr)
  · intro ν c hν hc tr htr
    exact (hF ν c hν hc tr htr).mul (hG ν c hν hc tr htr)
  · intro k ν c hν hc tr htr
    exact (hF ν c hν hc tr htr).const_smul k
  · intro ν c hν hc tr htr
    exact (contDiffOn_const.mul (hF ν c hν hc tr htr))
  · intro ν c hν hc tr htr
    have hE := contDiffOn_fderiv_apply (hF ν c hν hc tr htr) eηDir
    have hA := contDiffOn_fderiv_apply (hF ν c hν hc tr htr) esDir
    have h1 : ContDiffOn ℝ ∞ (fun x : ProfilePoint => x.2.1) {x : ProfilePoint | 0 < x.2.2} :=
      (contDiff_fst.comp contDiff_snd).contDiffOn
    have h2 : ContDiffOn ℝ ∞ (fun x : ProfilePoint => 2 * x.2.2) {x : ProfilePoint | 0 < x.2.2} :=
      contDiffOn_const.mul (contDiff_snd.comp contDiff_snd).contDiffOn
    show ContDiffOn ℝ ∞ (fun x : ProfilePoint =>
      x.2.1 * fderiv ℝ (F ν c tr) x eηDir + 2 * x.2.2 * fderiv ℝ (F ν c tr) x esDir)
      {x : ProfilePoint | 0 < x.2.2}
    exact (h1.mul hE).add (h2.mul hA)
  · intro ν c hν hc tr htr
    have hE := contDiffOn_fderiv_apply (hF ν c hν hc tr htr) eηDir
    exact hE
  · intro ν c hν hc tr htr
    have hQ := contDiffOn_fderiv_apply (hF ν c hν hc tr htr) eqDir
    exact hQ

end UnforcedLeray.Short.PartIIa.Jet
