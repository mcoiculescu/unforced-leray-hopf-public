import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Realization.Sub3
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_3_1.Sub.T8_1

/-!
# `FullOutMeas` (source 3916-3921, 1688-1689)

`fullOut R c ν μ f x = (√x₁)⁻¹ • merRe (-sepW ν μ (cartLift R c f) (chartY R x) (chartTau R x))`.
For a box tensor `f` the Cartesian lift `cartLift R c f` is jointly measurable in `(τ, z)`
(`T8_1.measurable_cartLift_entry`), hence `sepW` is measurable in `(τ, y)`
(`T8_1.measurable_sepW_comp`).  Composing with the measurable chart maps gives measurability of
`fullOut f` everywhere, so in particular almost everywhere for any measure.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory UnforcedLeray.Axi Set
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.NearInst.Masked.Realization

open UnforcedLeray.Short.PartIIIb UnforcedLeray.Short.PartIIIb.Concrete
  UnforcedLeray.Short.PartIIIb.NearInst UnforcedLeray.Short.PartIIIb.NearInst.Masked

namespace FullOutMeasAux

theorem measurable_chartY_aux (R : ℝ) : Measurable (NearInst.chartY R) := by
  unfold NearInst.chartY
  have h : Measurable fun p : Chart =>
      (![R / Real.sqrt p.1, 0, p.2.2 / Real.sqrt p.1] : Fin 3 → ℝ) := by
    refine measurable_pi_lambda _ fun i => ?_
    fin_cases i <;> simp <;> fun_prop
  exact (PiLp.continuous_toLp 2 (fun _ : Fin 3 => ℝ)).measurable.comp h

theorem measurable_chartTau_aux (R : ℝ) : Measurable (NearInst.chartTau R) := by
  unfold NearInst.chartTau
  fun_prop

theorem measurable_merRe_aux : Measurable NearInst.merRe := by
  unfold NearInst.merRe
  have h : Measurable fun w : Fin 3 → ℂ => (![(w 0).re, (w 2).re] : Fin 2 → ℝ) := by
    refine measurable_pi_lambda _ fun i => ?_
    fin_cases i <;> simp <;> fun_prop
  exact (PiLp.continuous_toLp 2 (fun _ : Fin 2 => ℝ)).measurable.comp h

theorem fullOut_measurable_aux (R c ν μ : ℝ) (f : Chart → Ten3) (hf : NearInst.IsBoxTensor f) :
    Measurable (Masked.fullOut R c ν μ f) := by
  have hT : ∀ j k : Fin 3, Measurable fun s : ℝ × Space =>
      NearInst.cartLift R c f s.1 s.2 j k :=
    fun j k => T8_1.measurable_cartLift_entry R c f hf.measurable j k
  have hq : Measurable fun x : Chart => (NearInst.chartTau R x, NearInst.chartY R x) :=
    (measurable_chartTau_aux R).prodMk (measurable_chartY_aux R)
  have hsep : ∀ i : Fin 3, Measurable fun x : Chart =>
      UnforcedLeray.Short.IIIa.sepW ν (μ : ℂ) (NearInst.cartLift R c f)
        (NearInst.chartY R x) (NearInst.chartTau R x) i := by
    intro i
    have h1 : Measurable fun q : ℝ × Space =>
        UnforcedLeray.Short.IIIa.sepW ν (μ : ℂ) (NearInst.cartLift R c f) q.2 q.1 i :=
      T8_1.measurable_sepW_comp ν (μ : ℂ) (NearInst.cartLift R c f) i hT
    exact Measurable.comp (g := fun q : ℝ × Space =>
        UnforcedLeray.Short.IIIa.sepW ν (μ : ℂ) (NearInst.cartLift R c f) q.2 q.1 i)
      (f := fun x : Chart => (NearInst.chartTau R x, NearInst.chartY R x)) h1 hq
  have hvec : Measurable fun x : Chart =>
      -UnforcedLeray.Short.IIIa.sepW ν (μ : ℂ) (NearInst.cartLift R c f)
        (NearInst.chartY R x) (NearInst.chartTau R x) :=
    (measurable_pi_lambda _ hsep).neg
  have hmr : Measurable fun x : Chart =>
      NearInst.merRe (-UnforcedLeray.Short.IIIa.sepW ν (μ : ℂ) (NearInst.cartLift R c f)
        (NearInst.chartY R x) (NearInst.chartTau R x)) :=
    measurable_merRe_aux.comp hvec
  have hscale : Measurable fun x : Chart => (Real.sqrt x.1)⁻¹ := by
    fun_prop
  unfold Masked.fullOut
  exact hscale.smul hmr

end FullOutMeasAux

/-- **`PartIII-b:C/near/masked/18/3/1`** (`fullOutMeas`): `fullOut` is a.e. strongly measurable on
box tensors (source 3916-3921, 1688-1689). -/
theorem fullOutMeas : FullOutMeas := by
  intro R c ν μ _ _ _ _ f hf
  exact (FullOutMeasAux.fullOut_measurable_aux R c ν μ f hf).aestronglyMeasurable

end UnforcedLeray.Short.PartIIIb.NearInst.Masked.Realization
