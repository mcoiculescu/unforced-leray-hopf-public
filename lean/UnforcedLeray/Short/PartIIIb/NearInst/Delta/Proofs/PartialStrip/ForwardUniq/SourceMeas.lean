import UnforcedLeray.Short.PartIIIb.NearInst.Delta.Proofs.PartialStrip.ForwardUniq.Props

/-!
# `FUSourceMeas` (item `PartIII-b:C/near/delta/9/1/10`)

The meridional block `merBlockC (zsum F)` of a flat source `F ∈ Z` is measurable (source
3569-3571).  The coercion of an `Lp` element is its `AEEqFun.cast`, which is strongly measurable
(`MeasureTheory.Lp.stronglyMeasurable`: the representative is `AEStronglyMeasurable.mk`), so
`zsum F = F.fst + F.snd` is strongly measurable.  The entries of `nsSym` are coordinate functionals
of `Ten3 = EuclideanSpace ℝ (Fin 3 × Fin 3)` and `symRZ`, hence measurable, and the complex
coercion is measurable.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.NearInst.Delta

open UnforcedLeray.Short.PartIIIb.Concrete UnforcedLeray.Short.PartIIIb.NearInst

theorem fuSourceMeas : UnforcedLeray.Short.PartIIIb.NearInst.Delta.FUSourceMeas := by
  intro c mZ ρb F i j
  have hfst : StronglyMeasurable (F.fst : Chart → Ten3) := MeasureTheory.Lp.stronglyMeasurable F.fst
  have hsnd : StronglyMeasurable (F.snd : Chart → Ten3) := MeasureTheory.Lp.stronglyMeasurable F.snd
  have hT : Measurable (zsum F) := (hfst.add hsnd).measurable
  have hco : ∀ ab : Fin 3 × Fin 3, Measurable fun x : Ten3 => x ab :=
    fun ab => (PiLp.continuous_apply 2 (fun _ : Fin 3 × Fin 3 => ℝ) ab).measurable
  have hnent : ∀ a b : Fin 3, Measurable fun x : Ten3 => nsSym x a b := by
    intro a b
    fin_cases a <;> fin_cases b <;> simp [nsSym, symRZ] <;>
      first
        | exact measurable_const
        | exact hco _
        | exact ((hco _).add (hco _)).div_const 2
  have hm : Measurable fun p => nsSym (zsum F p) (merIdx i) (merIdx j) :=
    (hnent (merIdx i) (merIdx j)).comp hT
  exact Complex.measurable_ofReal.comp hm

end UnforcedLeray.Short.PartIIIb.NearInst.Delta
