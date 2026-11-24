import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_4_2_4_2_1.FlatLerayDefs
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_4_2_4_2_1.ModePotentials
import UnforcedLeray.Short.PartIIa.Tasks.N02LerayComparison.NonzeroMode.FinPotentials.Deriv
import UnforcedLeray.Short.PartIIa.Tasks.N02LerayComparison.NonzeroMode.ModeBounds.Decay

/-!
# `TruncStreamEq` (organize task `PartIII-b:C/flatset/col/7/1/1/2/4/2/4/2/1/1/13`)

Source of record `the November 2 reference manuscript`
lines 1713-1716, 1744-1745: the stream field of the finite potential sum `Σ_{0<|n|≤N} e_n ψ_n`
equals the finite solenoidal sum `lerayTrunc c f N` (with `ε = 0`, the `ε`-terms vanish).
The `q`- and `η`-derivatives of a finite mode sum are the mode sums of the derivatives
(`nzFpDeriv`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst.FlatLeray

open UnforcedLeray.B0220 UnforcedLeray.B0223 UnforcedLeray.Short.PartIIa

theorem truncStreamEq : TruncStreamEq := by
  intro c hc f hf N p
  have hsm : ∀ n ∈ truncSet N, ContDiff ℝ ∞ (psiN c f n) := by
    intro n hn
    have hn0 : n ≠ 0 := Finset.ne_of_mem_erase hn
    exact nzmb_decay_smooth _ (modePotentials c hc f hf n hn0).2.1
  obtain ⟨hpd, hpe⟩ := nzFpDeriv c hc (truncSet N) (psiN c f) hsm
  have hLM : ∀ n ∈ truncSet N, lerayMode c f n (p.1, p.2.2) =
      !₂[-dEta2 (psiN c f n) (p.1, p.2.2),
        Complex.I * ((nzk c n : ℂ) * psiN c f n (p.1, p.2.2))] := by
    intro n hn
    simp only [lerayMode, Finset.ne_of_mem_erase hn, ite_false]
  unfold streamC lerayTrunc
  rw [hpd, hpe]
  rw [Finset.sum_congr rfl (fun n hn => by rw [hLM n hn])]
  ext i
  fin_cases i
  · simp [nzModeSum, eN, dEta2, smul_eq_mul, Finset.sum_apply]
  · simp [nzModeSum, eN, smul_eq_mul, Finset.sum_apply]

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst.FlatLeray
