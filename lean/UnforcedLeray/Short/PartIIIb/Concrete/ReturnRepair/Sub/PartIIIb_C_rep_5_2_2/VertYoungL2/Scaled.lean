import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_5_2_2.VertYoungL2.Kern
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_2_4_5.L2
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_2_4_5.L3
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_2_4_5.Of

/-!
# `PartIII-b:C/rep/5/2/2/8` helper: the scaled Young bound in `L²` for the vertical kernel

`L²` version of `vertKernYoungScaled_of` (`Of.lean`): Young with `(b, p, q) = (11/7, 22/19, 2)`,
`1 + 1/2 = 19/22 + 7/11`, the dilation `λ^{-1+19/22} = λ^{-3/22}` (`VertDil`, `L3.lean`),
the kernel bound `vertKernLb7` (`Kern.lean`) and the generic 1D Young `vert1DYoung` (`L2.lean`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem vertKernYoungScaled2 : ∃ C : ℝ, 0 ≤ C ∧ ∀ rIn D : ℝ, 0 < rIn → 0 < D →
    ∀ l : ℝ, 0 < l → l < 1 → ∀ g' : ℝ → ℝ≥0∞, Measurable g' →
      lqNorm1 2 (fun z => ∫⁻ s : ℝ, vertKern rIn D (z - l * s) * g' s) ≤
        ENNReal.ofReal (C * (rIn / D) * D ^ (-2 + 7 / 11 : ℝ)) *
          (ENNReal.ofReal (l ^ (-(3 / 22) : ℝ)) * lqNorm1 (22 / 19) g') := by
  obtain ⟨c, hc, hKb⟩ := vertKernLb7
  refine ⟨c + 1, by linarith, ?_⟩
  intro rIn D hrIn hD0 l hl0 hl1 g' hg'
  have hepos : 0 < (c + 1) * (rIn / D) * D ^ (-2 + 7 / 11 : ℝ) := by positivity
  have hlpos : 0 < l ^ (-(3 / 22) : ℝ) := by positivity
  by_cases htop : lqNorm1 (22 / 19) g' = ⊤
  · rw [htop, ENNReal.mul_top (ENNReal.ofReal_pos.mpr hlpos).ne',
      ENNReal.mul_top (ENNReal.ofReal_pos.mpr hepos).ne']
    exact le_top
  · obtain ⟨hD1, hD2⟩ := vertDil l hl0
    set S := vertKern rIn D with hS
    set gl : ℝ → ℝ≥0∞ := fun w => g' (l⁻¹ * w) with hgl
    have hglm : Measurable gl := hg'.comp (measurable_const.mul measurable_id)
    have hSm : Measurable S := by
      rw [hS]; unfold vertKern
      exact ENNReal.measurable_ofReal.comp (by fun_prop)
    have hSt : ∀ x, S x ≠ ⊤ := fun x => by rw [hS]; unfold vertKern; exact ENNReal.ofReal_ne_top
    have hdil : lqNorm1 (22 / 19) gl = ENNReal.ofReal (l ^ (1 / (22 / 19 : ℝ))) * lqNorm1 (22 / 19) g' :=
      hD2 _ (by norm_num) g'
    have hgltop : lqNorm1 (22 / 19) gl ≠ ⊤ := by
      rw [hdil]; exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top htop
    have hfun : (fun z => ∫⁻ s : ℝ, S (z - l * s) * g' s) =
        fun z => ENNReal.ofReal l⁻¹ * ∫⁻ w : ℝ, S (z - w) * gl w := funext fun z => hD1 S g' z
    rw [hfun, lqNorm1_const_mul (by norm_num) ENNReal.ofReal_ne_top]
    have hy := vert1DYoung S gl hSm hSt hglm (11 / 7) (22 / 19) 2 (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) hgltop
    have hKb' := hKb rIn D hrIn hD0
    have hid : ENNReal.ofReal (l ^ (-(3 / 22) : ℝ)) =
        ENNReal.ofReal l⁻¹ * ENNReal.ofReal (l ^ (1 / (22 / 19 : ℝ))) := by
      rw [← ENNReal.ofReal_mul (by positivity)]
      congr 1
      rw [← Real.rpow_neg_one, ← Real.rpow_add hl0]
      norm_num
    have hle : lqNorm1 (11 / 7) S ≤
        ENNReal.ofReal ((c + 1) * (rIn / D) * D ^ (-2 + 7 / 11 : ℝ)) := by
      refine hKb'.trans (ENNReal.ofReal_le_ofReal ?_)
      have : 0 ≤ (rIn / D) * D ^ (-2 + 7 / 11 : ℝ) := by positivity
      nlinarith
    calc ENNReal.ofReal l⁻¹ * lqNorm1 2 (fun z => ∫⁻ w : ℝ, S (z - w) * gl w)
        ≤ ENNReal.ofReal l⁻¹ * (lqNorm1 (11 / 7) S * lqNorm1 (22 / 19) gl) := by gcongr
      _ ≤ ENNReal.ofReal l⁻¹ * (ENNReal.ofReal ((c + 1) * (rIn / D) * D ^ (-2 + 7 / 11 : ℝ)) *
            lqNorm1 (22 / 19) gl) := by gcongr
      _ = _ := by
        rw [hdil, hid]
        ring

end UnforcedLeray.Short.PartIIIb.Concrete
