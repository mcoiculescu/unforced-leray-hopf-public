import UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution.WeightedHeatS0CLM
import UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution.Circulation
import UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution.FluxHeatCLM
import UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution.WeightedHeat

/-!
# Conservation of the physical cell integral by the actual Gaussian heat

The proof uses the literal B0284 convolution, periodic translation invariance of cell integrals,
and unit mass of the Gaussian kernel.
-/

set_option autoImplicit false
set_option maxHeartbeats 500000

noncomputable section

open MeasureTheory
open UnforcedLeray.GaussianVortex (Plane)

namespace UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution

private def scalarHeatIntegrand (θ : ℝ) (f : Plane → ℝ) (z w : Plane) : ℝ :=
  UnforcedLeray.B0284.heatKernel2 θ w * f (z - w)

private theorem integrable_scalarHeatIntegrand {c θ : ℝ} (hc : 0 < c) (hθ : 0 < θ)
    {f : Plane → ℝ} (hf : StronglyMeasurable f) (hper : Cyl.IsPeriodic c f)
    (hint : Integrable f (volume.restrict (Cyl.cell c))) :
    Integrable (fun q : Plane × Plane => scalarHeatIntegrand θ f q.1 q.2)
      ((volume.restrict (Cyl.cell c)).prod volume) := by
  let μ : Measure Plane := volume.restrict (Cyl.cell c)
  have habsper : Cyl.IsPeriodic c (fun z => |f z|) := by
    intro z
    change |f (z.1 + c, z.2)| = |f z|
    rw [hper z]
  have hshift : ∀ w : Plane,
      ∫ z in Cyl.cell c, |f (z - w)| = ∫ z in Cyl.cell c, |f z| := by
    intro w
    simpa only [sub_eq_add_neg] using
      Cyl.integral_cell_comp_add hc habsper (-w)
  have hkernel : Integrable (UnforcedLeray.B0284.heatKernel2 θ) volume :=
    UnforcedLeray.B0284.integrable_heatKernel2 hθ
  have hmeas : StronglyMeasurable
      (fun q : Plane × Plane => scalarHeatIntegrand θ f q.1 q.2) := by
    apply ((UnforcedLeray.B0284.measurable_heatKernel2_right θ).comp measurable_snd).stronglyMeasurable.mul
    exact hf.comp_measurable (measurable_fst.sub measurable_snd)
  rw [integrable_prod_iff' hmeas.aestronglyMeasurable]
  constructor
  · filter_upwards [] with w
    exact (integrable_translate_cell_of_periodic hc hf hper hint (-w)).const_mul _
  · have hOuterMeas : AEStronglyMeasurable
      (fun w : Plane => ∫ z in Cyl.cell c,
          ‖scalarHeatIntegrand θ f z w‖) volume :=
      (hmeas.norm.integral_prod_left' (μ := volume.restrict (Cyl.cell c))).aestronglyMeasurable
    let M : ℝ := ∫ z in Cyl.cell c, |f z|
    have hDom : Integrable (fun w : Plane =>
        |UnforcedLeray.B0284.heatKernel2 θ w| * M) volume := by
      simpa [M, Real.norm_eq_abs, mul_comm] using hkernel.norm.const_mul M
    refine hDom.mono' hOuterMeas ?_
    filter_upwards [] with w
    have hsection : Integrable (fun z : Plane =>
        scalarHeatIntegrand θ f z w) μ := by
      exact (integrable_translate_cell_of_periodic hc hf hper hint (-w)).const_mul _
    calc
      ‖∫ z in Cyl.cell c, ‖scalarHeatIntegrand θ f z w‖‖ =
          ∫ z in Cyl.cell c, ‖scalarHeatIntegrand θ f z w‖ := by
            rw [Real.norm_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
      _ =
          ∫ z in Cyl.cell c,
            |UnforcedLeray.B0284.heatKernel2 θ w| * |f (z - w)| := by
              apply integral_congr_ae
              exact Filter.Eventually.of_forall fun z => by
                simp [scalarHeatIntegrand, Real.norm_eq_abs, abs_mul]
      _ = |UnforcedLeray.B0284.heatKernel2 θ w| * M := by
        rw [integral_const_mul, hshift w]
      _ ≤ |UnforcedLeray.B0284.heatKernel2 θ w| * M := le_rfl

/-- Heat preserves one period-cell integral for every integrable periodic real scalar field. -/
theorem integral_cell_heat_first_eq {c θ : ℝ} (hc : 0 < c) (hθ : 0 < θ)
    {f : Plane → ℝ} (hf : StronglyMeasurable f) (hper : Cyl.IsPeriodic c f)
    (hint : Integrable f (volume.restrict (Cyl.cell c))) :
    ∫ z in Cyl.cell c,
      (UnforcedLeray.B0284.heat θ (fun z => (f z, (0 : ℝ))) z).1 =
        ∫ z in Cyl.cell c, f z := by
  let μ : Measure Plane := volume.restrict (Cyl.cell c)
  have hProd := integrable_scalarHeatIntegrand hc hθ hf hper hint
  have hsections := hProd.prod_right_ae
  have hformula : (fun z : Plane =>
      (UnforcedLeray.B0284.heat θ (fun z => (f z, (0 : ℝ))) z).1) =ᵐ[μ]
      fun z => ∫ w : Plane, scalarHeatIntegrand θ f z w := by
    filter_upwards [hsections] with z hz
    rw [UnforcedLeray.B0284.heat_apply_of_pos hθ]
    have hvecEq : (fun w : Plane =>
        UnforcedLeray.B0284.heatKernel2 θ w • (f (z - w), (0 : ℝ))) =
        fun w => (scalarHeatIntegrand θ f z w, (0 : ℝ)) := by
      funext w
      simp [scalarHeatIntegrand, smul_eq_mul]
    have hvec : Integrable (fun w : Plane =>
        UnforcedLeray.B0284.heatKernel2 θ w • (f (z - w), (0 : ℝ))) volume := by
      exact (hz.prodMk (integrable_zero (α := Plane) (ε' := ℝ) volume)).congr
        (Filter.Eventually.of_forall fun w => (congrFun hvecEq w).symm)
    rw [fst_integral hvec]
    exact integral_congr_ae (Filter.Eventually.of_forall fun w =>
      congrArg Prod.fst (congrFun hvecEq w))
  have hswap := integral_integral_swap
    (f := fun z w => scalarHeatIntegrand θ f z w) hProd
  calc
    ∫ z in Cyl.cell c,
        (UnforcedLeray.B0284.heat θ (fun z => (f z, (0 : ℝ))) z).1
        = ∫ z in Cyl.cell c, ∫ w : Plane, scalarHeatIntegrand θ f z w :=
          integral_congr_ae hformula
    _ = ∫ w : Plane, ∫ z in Cyl.cell c, scalarHeatIntegrand θ f z w := hswap
    _ = ∫ w : Plane,
          UnforcedLeray.B0284.heatKernel2 θ w * ∫ z in Cyl.cell c, f z := by
        apply integral_congr_ae
        filter_upwards [] with w
        change (∫ z in Cyl.cell c,
          UnforcedLeray.B0284.heatKernel2 θ w * f (z - w)) = _
        rw [integral_const_mul]
        congr 1
        simpa only [sub_eq_add_neg] using
          Cyl.integral_cell_comp_add hc hper (-w)
    _ = ∫ z in Cyl.cell c, f z := by
        rw [integral_mul_const, UnforcedLeray.B0284.integral_heatKernel2 hθ, one_mul]

/-- The zero second coordinate of the actual planar heat of a chosen weighted column holds
almost everywhere. The exceptional set is handled using the genuine scalar product-integrability
bound, so no pointwise Bochner-integral finiteness is assumed. -/
theorem heat_xColumnHeatLift_snd_ae_zero {c m θ : ℝ} (hc : 0 < c) (hm : 1 ≤ m)
    (hθ : 0 < θ) (f : UnforcedLeray.B0579.X c m) :
    (fun z => (UnforcedLeray.B0284.heat θ (xColumnHeatLift hc f) z).2) =ᵐ[volume]
      fun _ => 0 := by
  apply Filter.Eventually.of_forall
  intro z
  change (UnforcedLeray.B0284.heat θ (xColumnHeatLift hc f) z).2 = 0
  rw [UnforcedLeray.B0284.heat_apply_of_pos hθ]
  change (∫ w : Plane, UnforcedLeray.B0284.heatKernel2 θ w •
    xColumnHeatLift hc f (z - w)).2 = 0
  by_cases hi : Integrable (fun w : Plane =>
      UnforcedLeray.B0284.heatKernel2 θ w • xColumnHeatLift hc f (z - w)) volume
  · rw [snd_integral hi]
    simp [xColumnHeatLift]
  · simp [integral_undef, hi]

/-- The actual positive-age weighted heat image remains in the physical zero-circulation
subspace. -/
theorem xColumnHeatS0Positive_mem_zeroCirculation {c m θ : ℝ} (hc : 0 < c)
    (hm : 1 ≤ m) (hθ : 0 < θ) (hθ1 : θ ≤ 1) (f : UnforcedLeray.B0579.X c m)
    (hfzero : f ∈ zeroCirculationSubmodule (c := c) (m := m)
      (by linarith : 1 / 2 < m)) :
    xColumnHeatS0Positive hc hm hθ hθ1 f ∈
      zeroCirculationSubmodule (c := c) (m := m) (by linarith : 1 / 2 < m) := by
  rw [mem_zeroCirculationSubmodule_iff (by linarith : 1 / 2 < m)] at hfzero ⊢
  have hrep := xColumnPeriodicRep_ae_eq hc f
  have hrepSM := stronglyMeasurable_xColumnPeriodicRep hc f
  have hrepPer := periodic_xColumnPeriodicRep hc f
  have hrepInt := integrable_xColumnPeriodicRep hc hm f
  have hmass := integral_cell_heat_first_eq hc hθ hrepSM hrepPer hrepInt
  have hactual := coeFn_xColumnHeatS0Positive hc hm hθ hθ1 f
  have hcell : (xColumnHeatS0Positive hc hm hθ hθ1 f : Plane → ℝ) =ᵐ[
      volume.restrict (Cyl.cell c)] fun z =>
        (UnforcedLeray.B0284.heat θ (xColumnHeatLift hc f) z).1 := by
    have hactual0 : (xColumnHeatS0Positive hc hm hθ hθ1 f : Plane → ℝ) =ᵐ[
        UnforcedLeray.B0579.cellMeasure c 0] fun z =>
          (UnforcedLeray.B0284.heat θ (xColumnHeatLift hc f) z).1 :=
      (UnforcedLeray.B0579.cellMeasure_ac_cellMeasure c 0 m).ae_le hactual
    simpa [cellMeasure_zero_eq_cellVol, UnforcedLeray.B0581.cellVol, Cyl.cell, Cyl.cellμ,
      UnforcedLeray.B0579.cell, show -(c / 2) = -c / 2 by ring] using hactual0
  have hcellB : (xColumnHeatS0Positive hc hm hθ hθ1 f : Plane → ℝ) =ᵐ[
      volume.restrict (UnforcedLeray.B0579.cell c)] fun z =>
        (UnforcedLeray.B0284.heat θ (xColumnHeatLift hc f) z).1 := by
    simpa [Cyl.cell, UnforcedLeray.B0579.cell,
      show -(c / 2) = -c / 2 by ring] using hcell
  have hmassB : ∫ z in UnforcedLeray.B0579.cell c,
      (UnforcedLeray.B0284.heat θ (xColumnHeatLift hc f) z).1 =
      ∫ z in UnforcedLeray.B0579.cell c, xColumnPeriodicRep hc f z := by
    have hcellEq : Cyl.cell c = UnforcedLeray.B0579.cell c := by
      ext z
      simp [Cyl.cell, UnforcedLeray.B0579.cell,
        show -(c / 2) = -c / 2 by ring]
    rw [← hcellEq]
    change ∫ z in Cyl.cell c,
        (UnforcedLeray.B0284.heat θ
          (fun z => (xColumnPeriodicRep hc f z, (0 : ℝ))) z).1 = _
    exact hmass
  have hrepB : (xColumnPeriodicRep hc f) =ᵐ[
      volume.restrict (UnforcedLeray.B0579.cell c)] (f : Plane → ℝ) := by
    simpa [Cyl.cellμ, Cyl.cell, UnforcedLeray.B0579.cell,
      show -(c / 2) = -c / 2 by ring] using hrep
  calc
    ∫ z in UnforcedLeray.B0579.cell c,
        (xColumnHeatS0Positive hc hm hθ hθ1 f : Plane → ℝ) z
        = ∫ z in UnforcedLeray.B0579.cell c,
            (UnforcedLeray.B0284.heat θ (xColumnHeatLift hc f) z).1 :=
          integral_congr_ae hcellB
    _ = ∫ z in UnforcedLeray.B0579.cell c, xColumnPeriodicRep hc f z := by
        exact hmassB
    _ = ∫ z in UnforcedLeray.B0579.cell c, (f : Plane → ℝ) z :=
      integral_congr_ae hrepB
    _ = 0 := by
      exact hfzero

end UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution

#print axioms UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution.integral_cell_heat_first_eq
#print axioms UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution.xColumnHeatS0Positive_mem_zeroCirculation
