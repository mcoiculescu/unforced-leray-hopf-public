import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_2.Pres.RawLiftRegular.Chart
import UnforcedLeray.Lib.AxisymmetricB.Lift
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Smoothness of the ring lift `N_v` off the axis (task `PartIII-b:C/rep/8/2/pres/6/2/2`)

Source `the November 2 reference manuscript`
lines 1205-1225 (the lift is smooth off the axis for positive time).

`Nv R b τ y = √(age R y) • frameL y (b (chart R τ y))` and `frameL y v = v 0 • eR y + v 1 • e3`.
Off the axis: `chart` is `C^∞` into `Ioi 0 ×ˢ univ` (`chart_contDiffOn_offAxis`, `age_pos`), so
`b ∘ chart` is `C^∞`; `age` is `C^∞` and positive, hence `√age` is `C^∞`; `eR` is `C^∞` off the
axis (`contDiffOn_eR`); the coordinate projections of `b ∘ chart` are `C^∞` by composing with the
continuous linear maps `EuclideanSpace.proj`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- **Smoothness of the ring lift `N_v` off the axis** (source 1205-1225). -/
theorem nv_contDiffOn (R : ℝ) (hR : R ≠ 0) (b : ℝ × (ℝ × ℝ) → UnforcedLeray.Axi.Merid)
    (hb : ContDiffOn ℝ ∞ b (Set.Ioi 0 ×ˢ Set.univ)) :
    ContDiffOn ℝ ∞ (fun x : ℝ × Space => UnforcedLeray.Axi.Nv R b x.1 x.2)
      {x : ℝ × Space | x.2 ∉ UnforcedLeray.Axi.axis} := by
  have hc : ContDiffOn ℝ ∞ (fun x : ℝ × Space => chart R x.1 x.2)
      {x : ℝ × Space | x.2 ∉ axis} := chart_contDiffOn_offAxis R hR
  have hsnd : ContDiffOn ℝ ∞ (fun x : ℝ × Space => x.2)
      {x : ℝ × Space | x.2 ∉ axis} := contDiff_snd.contDiffOn
  have hmaps : MapsTo (fun x : ℝ × Space => chart R x.1 x.2)
      {x : ℝ × Space | x.2 ∉ axis} (Set.Ioi 0 ×ˢ Set.univ) := by
    intro x hx
    refine ⟨?_, Set.mem_univ _⟩
    exact age_pos hR hx
  have hb' : ContDiffOn ℝ ∞ (fun x : ℝ × Space => b (chart R x.1 x.2))
      {x : ℝ × Space | x.2 ∉ axis} := hb.comp hc hmaps
  have hage : ContDiffOn ℝ ∞ (fun x : ℝ × Space => age R x.2)
      {x : ℝ × Space | x.2 ∉ axis} :=
    (offAxis_age_contDiffOn R).comp hsnd (fun x hx => hx)
  have hsq : ContDiffOn ℝ ∞ (fun x : ℝ × Space => √(age R x.2))
      {x : ℝ × Space | x.2 ∉ axis} :=
    hage.sqrt (fun x hx => (age_pos hR hx).ne')
  have heR : ContDiffOn ℝ ∞ (fun x : ℝ × Space => eR x.2)
      {x : ℝ × Space | x.2 ∉ axis} :=
    contDiffOn_eR.comp hsnd (fun x hx => hx)
  have hB0 : ContDiffOn ℝ ∞ (fun x : ℝ × Space => b (chart R x.1 x.2) 0)
      {x : ℝ × Space | x.2 ∉ axis} :=
    (EuclideanSpace.proj (0 : Fin 2) : Merid →L[ℝ] ℝ).contDiff.comp_contDiffOn hb'
  have hB1 : ContDiffOn ℝ ∞ (fun x : ℝ × Space => b (chart R x.1 x.2) 1)
      {x : ℝ × Space | x.2 ∉ axis} :=
    (EuclideanSpace.proj (1 : Fin 2) : Merid →L[ℝ] ℝ).contDiff.comp_contDiffOn hb'
  have hfun : (fun x : ℝ × Space => UnforcedLeray.Axi.Nv R b x.1 x.2) =
      fun x : ℝ × Space => √(age R x.2) •
        ((b (chart R x.1 x.2) 0) • eR x.2 + (b (chart R x.1 x.2) 1) • e3) := by
    funext x
    simp only [UnforcedLeray.Axi.Nv, frameL_apply]
  rw [hfun]
  exact hsq.smul ((hB0.smul heR).add (hB1.smul contDiffOn_const))

end UnforcedLeray.Short.PartIIIb.Concrete
