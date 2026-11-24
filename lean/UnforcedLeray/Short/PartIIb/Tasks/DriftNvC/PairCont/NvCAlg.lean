import UnforcedLeray.Short.PartIIb.Tasks.NvCNorm

/-!
# `PartII-b:T08/3` helpers: additivity and measurability of the complex ring lift `NvC`
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal

namespace UnforcedLeray.Short.IIb

theorem NvC_sub (R : ℝ) (f g : CProf) :
    NvC R (fun x => f x - g x) = fun z => NvC R f z - NvC R g z := by
  funext z
  have h1 : (fun w => reM (f w - g w)) = (fun w => reM (f w)) - (fun w => reM (g w)) := by
    funext w; ext i; simp [reM]
  have h2 : (fun w => imM (f w - g w)) = (fun w => imM (f w)) - (fun w => imM (g w)) := by
    funext w; ext i; simp [imM]
  have hr : ∀ a b : Space, B0412.realC (a - b) = B0412.realC a - B0412.realC b := by
    intro a b; ext i; simp [B0412.realC_apply]
  simp only [NvC, h1, h2, Axi.Nv_sub, hr, smul_sub]
  abel

theorem continuous_reM : Continuous reM :=
  (PiLp.continuous_toLp 2 _).comp (continuous_pi fun i =>
    Complex.continuous_re.comp (EuclideanSpace.proj i : CMerid →L[ℂ] ℂ).continuous)

theorem continuous_imM : Continuous imM :=
  (PiLp.continuous_toLp 2 _).comp (continuous_pi fun i =>
    Complex.continuous_im.comp (EuclideanSpace.proj i : CMerid →L[ℂ] ℂ).continuous)

theorem continuous_realC' : Continuous B0412.realC := by
  unfold B0412.realC
  exact continuous_finset_sum _ fun i _ =>
    (Complex.continuous_ofReal.comp (EuclideanSpace.proj i : Space →L[ℝ] ℝ).continuous).smul
      continuous_const

theorem measurable_NvC (R : ℝ) {b : CProf} (hb : Measurable b) : Measurable (NvC R b) := by
  have h1 := Axi.measurable_Nv R (b := fun z => reM (b z)) (continuous_reM.measurable.comp hb)
  have h2 := Axi.measurable_Nv R (b := fun z => imM (b z)) (continuous_imM.measurable.comp hb)
  exact (continuous_realC'.measurable.comp h1).add
    ((continuous_realC'.measurable.comp h2).const_smul Complex.I)

end UnforcedLeray.Short.IIb
