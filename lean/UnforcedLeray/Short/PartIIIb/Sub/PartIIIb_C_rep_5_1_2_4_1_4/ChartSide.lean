import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_5_1_2_4_1_4
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_5_1_2_4_1_3.Kernel
import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_1_1_1.L4
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_5_1_2_4_1.Defs

/-!
# `PartIII-b:C/rep/5/1/2/4/1/4/1`: the chart side of the stream majorant

Source `the November 2 reference manuscript` 4178-4186, 5585-5593.
Proves `StreamChartMajSq` (chart majorant squared, copy of `ChartMajSq` with the stream kernel)
and `StreamChartMeasurable` (joint measurability of the chart stream majorant).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete.WYStream

open UnforcedLeray.Short.PartIIIb.Concrete.WYCore (srcW omega2 ybin)

/-- Pointwise: `srcNorm(oldPhys g) σ z ≤ srcW σ z`. -/
theorem stream_srcNorm_le (R c : ℝ) (g : Chart → Ten3) (σ : ℝ) (z : Space) :
    UnforcedLeray.Short.IIIa.srcNorm (oldPhys R c g) σ z ≤
      srcW R c (fun q => ‖g q‖ₑ) σ z := by
  show ENNReal.ofReal (UnforcedLeray.Short.IIIa.tensorNorm (oldPhys R c g σ z)) ≤
    ENNReal.ofReal (age R z) * ‖g (NearInst.chartOf R c z σ)‖ₑ
  have hage : 0 ≤ age R z := by unfold age; positivity
  have he : ‖g (NearInst.chartOf R c z σ)‖ₑ = ENNReal.ofReal ‖g (NearInst.chartOf R c z σ)‖ := by
    first
      | exact (ofReal_norm' _).symm
      | simp [ofReal_norm', enorm_eq_nnnorm]
      | rfl
  rw [he, ← ENNReal.ofReal_mul hage]
  apply ENNReal.ofReal_le_ofReal
  exact cartLiftFrobBound R c g σ z

/-- `StreamChartMajSq`: the chart stream majorant squared is bounded by `s⁻¹ Ψ_s²`. -/
theorem streamChartMajSq : StreamChartMajSq := by
  intro R c θ g p
  have hsq : ∀ s : ℝ, ENNReal.ofReal ((Real.sqrt s)⁻¹) ^ (2 : ℝ) ≤ ENNReal.ofReal s⁻¹ := by
    intro s
    have hx : 0 ≤ (Real.sqrt s)⁻¹ := by positivity
    rw [ENNReal.rpow_two, ← ENNReal.ofReal_pow hx]
    rcases le_or_gt 0 s with hs | hs
    · apply ENNReal.ofReal_le_ofReal
      rw [inv_pow, Real.sq_sqrt hs]
    · rw [Real.sqrt_eq_zero'.mpr hs.le, inv_zero]
      simp
  have hA : ∀ (τ : ℝ) (y : Space), wardYStreamMaj R c θ g τ y ≤
      psiMajS R c θ (fun q => ‖g q‖ₑ) τ y := by
    intro τ y
    unfold wardYStreamMaj psiMajS
    exact lintegral_mono fun l => lintegral_mono fun z =>
      mul_le_mul' le_rfl (stream_srcNorm_le R c g _ _)
  unfold wardYStreamChartMaj
  rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 2)]
  exact mul_le_mul' (hsq p.1)
    (ENNReal.rpow_le_rpow (hA (NearInst.chartTau R p) (NearInst.chartY R p)) (by norm_num))

/-- Measurability of `(σ, z) ↦ srcNorm(oldPhys g) σ z` (the entries of `oldPhys` are measurable). -/
theorem stream_measurable_srcNorm (R c : ℝ) (g : Chart → Ten3) (hg : Measurable g) :
    Measurable (fun e : ℝ × Space => UnforcedLeray.Short.IIIa.srcNorm (oldPhys R c g) e.1 e.2) := by
  unfold UnforcedLeray.Short.IIIa.srcNorm UnforcedLeray.Short.IIIa.tensorNorm
  refine Measurable.ennreal_ofReal (Real.continuous_sqrt.measurable.comp ?_)
  refine Finset.measurable_sum _ (fun i _ => Finset.measurable_sum _ (fun j _ => ?_))
  exact (T8_1.measurable_oldPhys_entry R c g hg i j).pow_const 2

/-- Generic measurability of the stream kernel `ofReal((a² (a² + (b - c)²))⁻¹)`. -/
theorem stream_kernel_gen {α : Type*} [MeasurableSpace α] (a b c : α → ℝ)
    (ha : Measurable a) (hb : Measurable b) (hc : Measurable c) :
    Measurable (fun x => ENNReal.ofReal ((a x ^ 2 * (a x ^ 2 + (b x - c x) ^ 2))⁻¹)) := by
  have hden : Measurable (fun x => a x ^ 2 * (a x ^ 2 + (b x - c x) ^ 2)) :=
    (ha.pow_const 2).mul ((ha.pow_const 2).add ((hb.sub hc).pow_const 2))
  exact ENNReal.measurable_ofReal.comp hden.inv

/-- The kernel as a function of `(((τ, y), l), z)`: measurable. -/
theorem stream_kernel_measurable :
    Measurable (fun q : ((ℝ × Space) × ℝ) × Space =>
      ENNReal.ofReal ((ϱ q.1.1.2 ^ 2 * (ϱ q.1.1.2 ^ 2 + (q.1.1.2 2 - q.1.2 * q.2 2) ^ 2))⁻¹)) := by
  have hy : Measurable (fun q : ((ℝ × Space) × ℝ) × Space => q.1.1.2) :=
    measurable_snd.comp (measurable_fst.comp measurable_fst)
  have hl : Measurable (fun q : ((ℝ × Space) × ℝ) × Space => q.1.2) :=
    measurable_snd.comp measurable_fst
  have hz : Measurable (fun q : ((ℝ × Space) × ℝ) × Space => q.2) := measurable_snd
  have ha : Measurable (fun q : ((ℝ × Space) × ℝ) × Space => ϱ q.1.1.2) :=
    measurable_ϱ.comp hy
  have hb : Measurable (fun q : ((ℝ × Space) × ℝ) × Space => q.1.1.2 2) :=
    (measurable_coord 2).comp hy
  have hc : Measurable (fun q : ((ℝ × Space) × ℝ) × Space => q.1.2 * q.2 2) :=
    hl.mul ((measurable_coord 2).comp hz)
  exact stream_kernel_gen _ _ _ ha hb hc

/-- The phase-shifted source weight as a function of `(((τ, y), l), z)`: measurable. -/
theorem stream_src_measurable (R c : ℝ) (g : Chart → Ten3) (hg : Measurable g) :
    Measurable (fun q : ((ℝ × Space) × ℝ) × Space =>
      UnforcedLeray.Short.IIIa.srcNorm (oldPhys R c g) (q.1.1.1 + 2 * Real.log q.1.2) q.2) := by
  have h1 : Measurable (fun q : ((ℝ × Space) × ℝ) × Space => q.1.1.1 + 2 * Real.log q.1.2) := by
    have a1 : Measurable (fun q : ((ℝ × Space) × ℝ) × Space => q.1.1.1) :=
      measurable_fst.comp (measurable_fst.comp measurable_fst)
    have a2 : Measurable (fun q : ((ℝ × Space) × ℝ) × Space => 2 * Real.log q.1.2) :=
      measurable_const.mul (Real.measurable_log.comp (measurable_snd.comp measurable_fst))
    exact a1.add a2
  have hφ : Measurable (fun q : ((ℝ × Space) × ℝ) × Space => (q.1.1.1 + 2 * Real.log q.1.2, q.2)) :=
    h1.prodMk measurable_snd
  have hs := stream_measurable_srcNorm R c g hg
  have hcomp := hs.comp hφ
  exact hcomp

/-- The integrand of the stream majorant, as one measurable function of `(((τ, y), l), z)`. -/
theorem stream_integrand_measurable (R c θ : ℝ) (g : Chart → Ten3) (hg : Measurable g) :
    Measurable (fun q : ((ℝ × Space) × ℝ) × Space =>
      if ϱ q.2 < θ * ϱ q.1.1.2 then
        ENNReal.ofReal ((ϱ q.1.1.2 ^ 2 * (ϱ q.1.1.2 ^ 2 + (q.1.1.2 2 - q.1.2 * q.2 2) ^ 2))⁻¹) *
          UnforcedLeray.Short.IIIa.srcNorm (oldPhys R c g) (q.1.1.1 + 2 * Real.log q.1.2) q.2
      else 0) := by
  refine Measurable.ite ?_ ?_ ?_
  · exact measurableSet_lt (measurable_ϱ.comp measurable_snd)
      (measurable_const.mul (measurable_ϱ.comp (measurable_snd.comp (measurable_fst.comp measurable_fst))))
  · exact stream_kernel_measurable.mul (stream_src_measurable R c g hg)
  · exact measurable_const

/-- Joint measurability of the stream majorant `(τ, y) ↦ wardYStreamMaj`. -/
theorem wardYStreamMaj_measurable (R c θ : ℝ) (g : Chart → Ten3) (hg : Measurable g) :
    Measurable (fun x : ℝ × Space => wardYStreamMaj R c θ g x.1 x.2) := by
  have hH := stream_integrand_measurable R c θ g hg
  have hS : ∀ x : ℝ × Space, MeasurableSet {z : Space | ϱ z < θ * ϱ x.2} :=
    fun x => measurableSet_lt measurable_ϱ measurable_const
  have hfun : (fun x : ℝ × Space => wardYStreamMaj R c θ g x.1 x.2) =
      fun x => ∫⁻ l in Ioo (0 : ℝ) 1, ∫⁻ z, (fun q : ((ℝ × Space) × ℝ) × Space =>
        if ϱ q.2 < θ * ϱ q.1.1.2 then
          ENNReal.ofReal ((ϱ q.1.1.2 ^ 2 * (ϱ q.1.1.2 ^ 2 + (q.1.1.2 2 - q.1.2 * q.2 2) ^ 2))⁻¹) *
            UnforcedLeray.Short.IIIa.srcNorm (oldPhys R c g) (q.1.1.1 + 2 * Real.log q.1.2) q.2
        else 0) ((x, l), z) := by
    funext x
    unfold wardYStreamMaj
    refine lintegral_congr fun l => ?_
    rw [← lintegral_indicator (hS x)]
    refine lintegral_congr fun z => ?_
    simp only [Set.indicator_apply, Set.mem_setOf_eq]
  rw [hfun]
  have g1 : Measurable (fun a : (ℝ × Space) × ℝ => ∫⁻ z, (fun q : ((ℝ × Space) × ℝ) × Space =>
      if ϱ q.2 < θ * ϱ q.1.1.2 then
        ENNReal.ofReal ((ϱ q.1.1.2 ^ 2 * (ϱ q.1.1.2 ^ 2 + (q.1.1.2 2 - q.1.2 * q.2 2) ^ 2))⁻¹) *
          UnforcedLeray.Short.IIIa.srcNorm (oldPhys R c g) (q.1.1.1 + 2 * Real.log q.1.2) q.2
      else 0) (a, z)) := hH.lintegral_prod_right'
  exact g1.lintegral_prod_right'

/-- `StreamChartMeasurable`: measurability of the chart stream majorant. -/
theorem streamChartMeasurable : StreamChartMeasurable := by
  intro R c θ g hg
  unfold wardYStreamChartMaj
  refine Measurable.mul ?_ ?_
  · exact ENNReal.measurable_ofReal.comp
      ((Real.continuous_sqrt.measurable.comp measurable_fst).inv)
  · have hτ : Measurable (NearInst.chartTau R) := by
      unfold NearInst.chartTau; fun_prop
    have hY : Measurable (NearInst.chartY R) := by
      unfold NearInst.chartY; fun_prop
    have hpair : Measurable (fun p : Chart => (NearInst.chartTau R p, NearInst.chartY R p)) :=
      hτ.prodMk hY
    have hW : Measurable (fun x : ℝ × Space => wardYStreamMaj R c θ g x.1 x.2) :=
      wardYStreamMaj_measurable R c θ g hg
    show Measurable ((fun x : ℝ × Space => wardYStreamMaj R c θ g x.1 x.2) ∘
      (fun p : Chart => (NearInst.chartTau R p, NearInst.chartY R p)))
    exact hW.comp hpair

/-- Both chart-side leaves. -/
theorem streamChartSide : StreamChartMajSq ∧ StreamChartMeasurable :=
  ⟨streamChartMajSq, streamChartMeasurable⟩

end UnforcedLeray.Short.PartIIIb.Concrete.WYStream

end
