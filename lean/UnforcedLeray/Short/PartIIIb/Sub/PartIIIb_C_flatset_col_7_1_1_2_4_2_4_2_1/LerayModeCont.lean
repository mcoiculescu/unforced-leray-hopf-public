import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_4_2_4_2_1.FlatLerayDefs
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_4_2_4_2_1.ModePotentials
import UnforcedLeray.Short.PartIIa.Tasks.N02LerayComparison.NonzeroMode.ModeBounds.Decay

/-!
# `LerayModeCont` (organize task `PartIII-b:C/flatset/col/7/1/1/2/4/2/4/2/1/1/11`)

Source of record `the November 2 reference manuscript`
lines 1713-1716: each solenoidal mode coefficient `(-∂_η ψ_n, i k_n ψ_n)` is continuous in `(s, η)`
(`n = 0` gives the zero field; `n ≠ 0` uses the smoothness of `ψ_n` from `ModePotentials`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst.FlatLeray

open UnforcedLeray.B0220 UnforcedLeray.B0223 UnforcedLeray.Short.PartIIa

theorem lerayModeCont : LerayModeCont := by
  intro c hc f hf n
  by_cases hn : n = 0
  · subst hn
    have hfun : lerayMode c f 0 = fun _ => 0 := by
      funext x
      simp [lerayMode]
    rw [hfun]
    exact continuous_const
  · have hpsi : ContDiff ℝ ∞ (psiN c f n) :=
      nzmb_decay_smooth _ (modePotentials c hc f hf n hn).2.1
    have hfun : lerayMode c f n = fun x : ℝ × ℝ => !₂[-dEta2 (psiN c f n) x,
        Complex.I * ((nzk c n : ℂ) * psiN c f n x)] := by
      funext x
      simp only [lerayMode, hn, if_false]
    rw [hfun]
    have hd : Continuous fun x : ℝ × ℝ => dEta2 (psiN c f n) x := by
      unfold dEta2
      exact (hpsi.continuous_fderiv (by simp)).clm_apply continuous_const
    have hc1 : Continuous fun x : ℝ × ℝ => -dEta2 (psiN c f n) x := hd.neg
    have hc2 : Continuous fun x : ℝ × ℝ => Complex.I * ((nzk c n : ℂ) * psiN c f n x) :=
      continuous_const.mul (continuous_const.mul hpsi.continuous)
    refine (PiLp.continuous_toLp (p := 2) (β := fun _ : Fin 2 => ℂ)).comp (continuous_pi fun i => ?_)
    fin_cases i
    · exact hc1
    · exact hc2

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst.FlatLeray
