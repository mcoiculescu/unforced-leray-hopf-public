import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.Ward.Bg.PresY2.Defs
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.FDeriv.Basic

/-!
# Hölder for `U·∇U` in `L²` (source 5246, with 2607-2612)

For `f ∈ C¹` with `‖f‖₄, ‖Df‖₄ ≤ C`, the field `y ↦ Df(y) f(y)` is in `L²` with norm at most
`C * C`.  The pointwise bound `‖Df(y) f(y)‖ ≤ ‖Df(y)‖ ‖f(y)‖` and the Hölder inequality with
exponents `(4, 4, 2)` give the bound.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- **Hölder for `U·∇U`** (`prodL2OfL4_proved`). -/
theorem prodL2OfL4_proved : ProdL2OfL4 := by
  intro f C hf h4 hD4
  haveI holder : ENNReal.HolderTriple 4 4 2 := by
    apply ENNReal.HolderTriple.of_toReal
    norm_num [Real.holderTriple_iff]
  have hcont : Continuous f := hf.continuous
  have hDcont : Continuous (fun y => fderiv ℝ f y) := hf.continuous_fderiv one_ne_zero
  have hmeas : AEStronglyMeasurable (fun y => fderiv ℝ f y (f y)) volume :=
    (hDcont.clm_apply hcont).aestronglyMeasurable
  have hpt : ∀ y : Space, ‖fderiv ℝ f y (f y)‖₊ ≤ (1 : NNReal) * ‖fderiv ℝ f y‖₊ * ‖f y‖₊ := by
    intro y
    have h1 : ‖fderiv ℝ f y (f y)‖ ≤ ‖fderiv ℝ f y‖ * ‖f y‖ :=
      (fderiv ℝ f y).le_opNorm (f y)
    have h2 : ‖fderiv ℝ f y (f y)‖₊ ≤ ‖fderiv ℝ f y‖₊ * ‖f y‖₊ := by
      rw [← NNReal.coe_le_coe, NNReal.coe_mul]
      simpa using h1
    rw [one_mul]
    exact h2
  have key : eLpNorm (fun y => fderiv ℝ f y (f y)) 2 volume ≤
      (1 : ENNReal) * eLpNorm (fun y => fderiv ℝ f y) 4 volume * eLpNorm f 4 volume := by
    have := eLpNorm_le_eLpNorm_mul_eLpNorm_of_nnnorm (μ := volume) (p := 4) (q := 4) (r := 2)
      hDcont.aestronglyMeasurable hcont.aestronglyMeasurable
      (fun (A : Space →L[ℝ] Space) (v : Space) => A v) 1 (ae_of_all _ hpt)
    simpa only [ENNReal.coe_one, one_mul] using this
  have hbound : eLpNorm (fun y => fderiv ℝ f y (f y)) 2 volume ≤ ENNReal.ofReal (C * C) := by
    refine key.trans ?_
    have hmul : (1 : ENNReal) * eLpNorm (fun y => fderiv ℝ f y) 4 volume * eLpNorm f 4 volume ≤
        ENNReal.ofReal C * ENNReal.ofReal C := by
      rw [one_mul]
      gcongr
    refine hmul.trans ?_
    rcases le_total 0 C with hC | hC
    · exact le_of_eq (ENNReal.ofReal_mul hC).symm
    · rw [ENNReal.ofReal_of_nonpos hC, zero_mul]
      exact zero_le
  exact ⟨⟨hmeas, lt_of_le_of_lt hbound ENNReal.ofReal_lt_top⟩, hbound⟩

end UnforcedLeray.Short.PartIIIb.Concrete
