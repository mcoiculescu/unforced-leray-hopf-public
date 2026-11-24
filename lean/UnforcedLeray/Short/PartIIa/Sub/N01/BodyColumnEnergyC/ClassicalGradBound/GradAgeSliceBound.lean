import UnforcedLeray.Short.PartIIa.Sub.PartIIa_N01_9_1_3_3_2_1
import UnforcedLeray.Short.PartIIa.Sub.N01.HeatInt.HeatIntPeriodic
import UnforcedLeray.Short.PartIIa.Sub.N01.HeatInt.HeatIntRegular

/-!
# `GradAgeSliceBound` (G5)

Source `the November 2 reference manuscript`
lines 1684-1689.  `velF c u = u` by periodicity, `lintegral_ageμ`, Tonelli.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory UnforcedLeray.Axi Set Filter Topology
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIa.N01

open UnforcedLeray.B0220 (Profile HSpace measureH)
open UnforcedLeray.B0223 (MeridC)
open UnforcedLeray.Short.PartIIIb.Concrete (Chart)
open UnforcedLeray.Short.PartIIIb.NearInst.Delta (velF)
open UnforcedLeray.Short.IIIa (tnorm2)

theorem cell_eq_qCell (c : ℝ) : UnforcedLeray.B0579.cell c = qCell c := by
  unfold UnforcedLeray.B0579.cell qCell
  rw [neg_div]

theorem gradAgeSliceBound : UnforcedLeray.Short.PartIIa.N01.GradAgeSliceBound := by
  classical
  intro c ν hc hν μ F hF
  set u := smoothHeatInt c ν μ F with hu
  have hreg := heatIntRegular c ν hc hν μ F hF
  have hper := heatIntPeriodic c ν hc hν μ F hF
  have hv : velF c u = fun x i => u x i := velF_of_periodic c u hper
  set h : Fin 2 → Fin 2 → Chart → ℂ := fun i j p =>
    fderiv ℝ (fun y : ℝ × ℝ => u (p.1, y) i) p.2 (UnforcedLeray.B0579.dir j) with hh
  set G : Chart → Fin 2 → Fin 2 → ℂ := gradOf (velF c u) with hGdef
  have hG : ∀ p i j, G p i j = if 0 < p.1 then h i j p else 0 := by
    intro p i j; simp only [hGdef]; rw [hv]; rfl
  have hGm : ∀ i j, Measurable fun p : Chart => G p i j := by
    intro i j
    have hc1 : ContinuousOn (h i j) (Ioi (0 : ℝ) ×ˢ univ) :=
      (hreg.2.2 i).clm_apply continuousOn_const
    have hpm : Measurable (({p : Chart | 0 < p.1}).piecewise (h i j) fun _ => (0 : ℂ)) := by
      refine ContinuousOn.measurable_piecewise (s := {p : Chart | 0 < p.1}) ?_
        continuousOn_const (measurableSet_lt measurable_const measurable_fst)
      have : {p : Chart | 0 < p.1} = Ioi (0 : ℝ) ×ˢ univ := by ext p; simp
      rw [this]; exact hc1
    have heq : (fun p : Chart => G p i j) =
        ({p : Chart | 0 < p.1}).piecewise (h i j) fun _ => (0 : ℂ) := by
      funext p; rw [hG]; simp [Set.piecewise]
    rw [heq]; exact hpm
  have hterm : ∀ i j, Measurable fun p : Chart => ‖G p i j‖ₑ ^ 2 := fun i j =>
    (hGm i j).enorm.pow_const 2
  set f : Chart → ℝ≥0∞ := fun p => ∑ i : Fin 2, ∑ j : Fin 2, ‖G p i j‖ₑ ^ 2 with hf
  have hfm : Measurable f :=
    Finset.measurable_sum _ fun i _ => Finset.measurable_sum _ fun j _ => hterm i j
  have hA : ∀ p, ENNReal.ofReal (tnorm2 (G p) ^ 2) = f p := by
    intro p
    unfold tnorm2
    rw [Real.sq_sqrt (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => by positivity),
      ENNReal.ofReal_sum_of_nonneg (fun i _ => Finset.sum_nonneg fun j _ => by positivity)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [ENNReal.ofReal_sum_of_nonneg (fun j _ => by positivity)]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
  have ha : (-1 / 2 : ℝ) = -(1 / 2 : ℝ) := by norm_num
  have hB : ∫⁻ p, ENNReal.ofReal (tnorm2 (G p) ^ 2) ∂(ageμ c (-1 / 2)) =
      ∫⁻ p in Ioi (0 : ℝ) ×ˢ qCell c, ENNReal.ofReal (c⁻¹ * p.1 ^ (-1 / 2 : ℝ)) * f p := by
    rw [← lintegral_ageμ hc (-1 / 2) hfm]
    exact lintegral_congr hA
  -- per-entry Tonelli
  have hentry : ∀ i j, ∫⁻ p in Ioi (0 : ℝ) ×ˢ qCell c,
      ENNReal.ofReal (p.1 ^ (-(1 / 2 : ℝ))) * ‖G p i j‖ₑ ^ 2 =
      ∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal (s ^ (-(1 / 2 : ℝ))) *
        ∫⁻ x in UnforcedLeray.B0579.cell c,
          ‖fderiv ℝ (fun y : ℝ × ℝ => smoothHeatInt c ν μ F (s, y) i) x
            (UnforcedLeray.B0579.dir j)‖ₑ ^ 2 := by
    intro i j
    have hmeas : Measurable fun p : Chart => ENNReal.ofReal (p.1 ^ (-(1 / 2 : ℝ))) * ‖G p i j‖ₑ ^ 2 :=
      ((measurable_ofReal_rpow _).comp measurable_fst).mul (hterm i j)
    have e : (volume : Measure Chart).restrict (Ioi (0 : ℝ) ×ˢ qCell c) =
        (volume.restrict (Ioi (0 : ℝ))).prod ((volume : Measure (ℝ × ℝ)).restrict (qCell c)) := by
      rw [Measure.volume_eq_prod, Measure.volume_eq_prod, Measure.prod_restrict]
    rw [e, lintegral_prod _ hmeas.aemeasurable, cell_eq_qCell]
    refine setLIntegral_congr_fun measurableSet_Ioi fun s hs => ?_
    have hsm : Measurable fun x : ℝ × ℝ => ‖G (s, x) i j‖ₑ ^ 2 :=
      (hterm i j).comp measurable_prodMk_left
    simp only []
    rw [lintegral_const_mul _ hsm]
    congr 1
    refine lintegral_congr fun x => ?_
    rw [hG]
    have hs' : 0 < (s, x).1 := hs
    rw [if_pos hs']
  rw [hB]
  have hnn : (0 : ℝ) ≤ c⁻¹ := inv_nonneg.2 hc.le
  have hrw : ∀ p : Chart, ENNReal.ofReal (c⁻¹ * p.1 ^ (-1 / 2 : ℝ)) * f p =
      ENNReal.ofReal c⁻¹ * ∑ i : Fin 2, ∑ j : Fin 2,
        ENNReal.ofReal (p.1 ^ (-(1 / 2 : ℝ))) * ‖G p i j‖ₑ ^ 2 := by
    intro p
    rw [ha, ENNReal.ofReal_mul hnn, mul_assoc]
    congr 1
    simp only [hf, Finset.mul_sum]
  simp_rw [hrw]
  have hterm2 : ∀ i j, Measurable fun p : Chart =>
      ENNReal.ofReal (p.1 ^ (-(1 / 2 : ℝ))) * ‖G p i j‖ₑ ^ 2 := fun i j =>
    ((measurable_ofReal_rpow _).comp measurable_fst).mul (hterm i j)
  have hsum : Measurable fun p : Chart => ∑ i : Fin 2, ∑ j : Fin 2,
      ENNReal.ofReal (p.1 ^ (-(1 / 2 : ℝ))) * ‖G p i j‖ₑ ^ 2 :=
    Finset.measurable_sum _ fun i _ => Finset.measurable_sum _ fun j _ => hterm2 i j
  refine le_of_eq ?_
  rw [lintegral_const_mul _ hsum]
  congr 1
  rw [lintegral_finsetSum _ fun i _ => Finset.measurable_sum _ fun j _ => hterm2 i j]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [lintegral_finsetSum _ fun j _ => hterm2 i j]
  exact Finset.sum_congr rfl fun j _ => hentry i j

end UnforcedLeray.Short.PartIIa.N01
