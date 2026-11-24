import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_near_masked_14_2
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_3_1.Sub.T8_1

/-!


Joint measurability of `(l, x) ↦ farSliceOut R c δ S f l x` for a box tensor `f` (source
3996-4011). The inner `z`-integral is taken by `Measurable.lintegral_prod_right'` applied to the
jointly measurable integrand `sliceIntg` in `((l, x), z)`. The chart-lift entries
`cartLift` and the chart point `chartOf` are measurable by `T8_1.measurable_cartLift_entry`
and `T8_1.measurable_chartOf`. The remaining factors (`chartY`, `chartTau`, the norm of
`chartY - l • z`, the floor-free phase and the `ite` on `e^δ s < R²/|z'|²`) are measurable by
direct composition.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory UnforcedLeray.Axi Set
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.NearInst.Masked

open UnforcedLeray.Short.PartIIIb UnforcedLeray.Short.PartIIIb.Concrete
  UnforcedLeray.Short.PartIIIb.NearInst UnforcedLeray.Short.PartIIIb.NearInst.Delta
  UnforcedLeray.Cons.C03.Concrete UnforcedLeray.Blueprint.Planar

/-- The integrand of `farSlice` in the variables `((l, x), z)`
(definitionally `farSlice R c δ f l x = ∫⁻ z, sliceIntg R c δ f ((l, x), z)`). -/
def sliceIntg (R c δ : ℝ) (f : Chart → Ten3) (ω : (ℝ × Chart) × Space) : ℝ≥0∞ :=
  if Real.exp δ * ω.1.2.1 < R ^ 2 / (ω.2 0 ^ 2 + ω.2 1 ^ 2) then
    ENNReal.ofReal (‖NearInst.chartY R ω.1.2 - ω.1.1 • ω.2‖ ^ (-4 : ℝ) *
      UnforcedLeray.Short.IIIa.tensorNorm
        (NearInst.cartLift R c f (NearInst.chartTau R ω.1.2 + 2 * Real.log ω.1.1) ω.2))
  else 0

lemma sliceMeas_chartY (R : ℝ) : Measurable (NearInst.chartY R) := by
  unfold NearInst.chartY
  have : Measurable fun p : Chart => (![R / Real.sqrt p.1, 0, p.2.2 / Real.sqrt p.1] : Fin 3 → ℝ) := by
    refine measurable_pi_lambda _ fun i => ?_
    fin_cases i <;> simp <;> fun_prop
  exact (PiLp.continuous_toLp 2 (fun _ : Fin 3 => ℝ)).measurable.comp this

lemma sliceMeas_chartTau (R : ℝ) : Measurable (NearInst.chartTau R) := by
  unfold NearInst.chartTau
  fun_prop

lemma sliceMeas_norm (R : ℝ) :
    Measurable fun ω : (ℝ × Chart) × Space => ‖NearInst.chartY R ω.1.2 - ω.1.1 • ω.2‖ := by
  have h1 : Measurable fun ω : (ℝ × Chart) × Space => NearInst.chartY R ω.1.2 :=
    (sliceMeas_chartY R).comp (measurable_snd.comp measurable_fst)
  have h2 : Measurable fun ω : (ℝ × Chart) × Space => ω.1.1 • ω.2 :=
    (continuous_fst.smul continuous_snd).measurable.comp
      ((measurable_fst.comp measurable_fst).prodMk measurable_snd)
  exact (h1.sub h2).norm

lemma sliceMeas_tensorNorm (R c : ℝ) (f : Chart → Ten3) (hf : Measurable f) :
    Measurable fun ω : (ℝ × Chart) × Space =>
      UnforcedLeray.Short.IIIa.tensorNorm
        (NearInst.cartLift R c f (NearInst.chartTau R ω.1.2 + 2 * Real.log ω.1.1) ω.2) := by
  have hτ : Measurable fun ω : (ℝ × Chart) × Space =>
      NearInst.chartTau R ω.1.2 + 2 * Real.log ω.1.1 :=
    ((sliceMeas_chartTau R).comp (measurable_snd.comp measurable_fst)).add
      (measurable_const.mul (Real.measurable_log.comp (measurable_fst.comp measurable_fst)))
  have hq : Measurable fun ω : (ℝ × Chart) × Space =>
      (NearInst.chartTau R ω.1.2 + 2 * Real.log ω.1.1, ω.2) := hτ.prodMk measurable_snd
  unfold UnforcedLeray.Short.IIIa.tensorNorm
  apply Measurable.sqrt
  refine Finset.measurable_sum _ fun i _ => ?_
  refine Finset.measurable_sum _ fun j _ => ?_
  exact (((UnforcedLeray.Short.PartIIIb.Concrete.T8_1.measurable_cartLift_entry R c f hf i j).comp
    hq).pow_const 2)

lemma measurable_sliceIntg (R c δ : ℝ) (f : Chart → Ten3) (hf : Measurable f) :
    Measurable (sliceIntg R c δ f) := by
  unfold sliceIntg
  refine Measurable.ite ?_ ?_ measurable_const
  · exact measurableSet_lt (by fun_prop) (by fun_prop)
  · exact Measurable.ennreal_ofReal
      (((sliceMeas_norm R).pow_const _).mul (sliceMeas_tensorNorm R c f hf))

theorem farSliceMeasurable : UnforcedLeray.Short.PartIIIb.NearInst.Masked.FarSliceMeasurable := by
  intro R c δ S f hf
  have hI : Measurable (fun p : ℝ × Chart => ∫⁻ z : Space, sliceIntg R c δ f (p, z)) :=
    Measurable.lintegral_prod_right' (f := sliceIntg R c δ f)
      (measurable_sliceIntg R c δ f hf.measurable)
  have hEq : (fun p : ℝ × Chart => farSliceOut R c δ S f p.1 p.2) =
      fun p : ℝ × Chart => if p.2.1 < S then
        ENNReal.ofReal (Real.sqrt p.2.1)⁻¹ * ∫⁻ z : Space, sliceIntg R c δ f (p, z) else 0 :=
    rfl
  rw [hEq]
  refine Measurable.ite ?_ ?_ measurable_const
  · exact measurableSet_lt (measurable_snd.fst) measurable_const
  · exact (Measurable.ennreal_ofReal (by fun_prop : Measurable fun p : ℝ × Chart =>
      (Real.sqrt p.2.1)⁻¹)).mul hI

end UnforcedLeray.Short.PartIIIb.NearInst.Masked
