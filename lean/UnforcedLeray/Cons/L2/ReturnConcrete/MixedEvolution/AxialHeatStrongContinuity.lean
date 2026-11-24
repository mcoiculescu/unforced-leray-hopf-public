import UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution.AxialHeatCommutatorMass
import UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution.AxialHeatIntertwining
import UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution.WeightedHeatOperatorBound
import UnforcedLeray.Lib.HeatCylinder.HeatL2StrongContinuity

/-!
# Age-zero continuity of the actual fixed-cylinder weighted heat

The conjugated heat increment is split into the actual axial commutator and the ordinary
normalized-cell Gaussian increment on the actual axial input.  The centered-cell radial/axial
comparison is kept explicit and is only used for each fixed cylinder.
-/

set_option autoImplicit false
set_option maxHeartbeats 500000

noncomputable section

open MeasureTheory
open Filter
open scoped ENNReal Topology
open UnforcedLeray.GaussianVortex (Plane)
open UnforcedLeray.B0579 hiding Plane

namespace UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution

/-- On the centered cell the radial-to-axial ratio is bounded by its explicit cylinder factor. -/
theorem radial_le_cylinder_axial_on_cell {c m : ℝ} (hc : 0 < c) (hm : 0 ≤ m)
    {z : Plane} (hz : z ∈ B0579.cell c) :
    bracket z ^ m ≤ (1 + c ^ 2 / 4) ^ (m / 2) * axialWeight m z := by
  have h := bracket_le_centered_axial hc hm hz
  simpa [axialWeight] using h

/-! The pointwise algebraic split used below is exact for the actual B0284 heat fields. -/

private def axialHeatCommutatorField {c m θ : ℝ} (hc : 0 < c) (f : X c m) : Plane → Plane :=
  fun z => axialWeight m z • B0284.heat θ (xColumnHeatLift hc f) z -
    B0284.heat θ (fun x => axialWeight m x •
      xColumnHeatLift hc f x) z

private def axialHeatIncrementField {c m θ : ℝ} (hc : 0 < c) (f : X c m) : Plane → Plane :=
  fun z => B0284.heat θ (fun x => axialWeight m x •
    xColumnHeatLift hc f x) z - axialWeight m z • xColumnHeatLift hc f z

/-- Pointwise radial heat increment bound by the actual commutator and the axial-input heat
increment. This is stated on the centered cell, where the radial/axial ratio has a finite bound. -/
theorem radialHeatIncrement_le_commutator_add_increment {c m θ : ℝ} (hc : 0 < c)
    (hm : 1 ≤ m) (f : X c m) :
    ∀ᵐ z ∂Cyl.cellμ c,
      |bracket z ^ m * (B0284.heat θ (xColumnHeatLift hc f) z).1 -
        bracket z ^ m * (xColumnHeatLift hc f z).1| ≤
        (1 + c ^ 2 / 4) ^ (m / 2) *
          ‖axialHeatCommutatorField (θ := θ) hc f z +
            axialHeatIncrementField (θ := θ) hc f z‖ := by
  filter_upwards [ae_restrict_mem (Cyl.measurableSet_cell c)] with z hz
  have hz' : z ∈ B0579.cell c := by
    simp only [Cyl.cell, Set.mem_prod, Set.mem_Ico, Set.mem_univ] at hz
    simp only [B0579.cell, Set.mem_prod, Set.mem_Ico, Set.mem_univ]
    exact ⟨⟨by linarith [hz.1.1], hz.1.2⟩, trivial⟩
  let a := axialWeight m z
  let r := bracket z ^ m
  let V := B0284.heat θ (xColumnHeatLift hc f) z
  let G := B0284.heat θ (fun x => axialWeight m x • xColumnHeatLift hc f x) z
  have ha : 0 ≤ a := by dsimp [a, axialWeight, axialBracket]; positivity
  have hr : 0 ≤ r := (bracket_rpow_pos m z).le
  have hratio := radial_le_cylinder_axial_on_cell hc (by linarith : 0 ≤ m) hz'
  have hsum : (axialHeatCommutatorField (θ := θ) hc f z +
      axialHeatIncrementField (θ := θ) hc f z).1 =
      a * V.1 - a * (xColumnHeatLift hc f z).1 := by
    simp [axialHeatCommutatorField, axialHeatIncrementField, a, V,
      smul_eq_mul]
  have hscalar : r * V.1 - r * (xColumnHeatLift hc f z).1 =
      r * (V.1 - (xColumnHeatLift hc f z).1) := by ring
  rw [hscalar]
  calc
    |r * (V.1 - (xColumnHeatLift hc f z).1)| =
        r * |V.1 - (xColumnHeatLift hc f z).1| := by
          rw [abs_mul, abs_of_nonneg hr]
    _ ≤ (1 + c ^ 2 / 4) ^ (m / 2) *
        (a * |V.1 - (xColumnHeatLift hc f z).1|) := by
          have hmul := mul_le_mul_of_nonneg_right hratio
            (abs_nonneg (V.1 - (xColumnHeatLift hc f z).1))
          calc
            r * |V.1 - (xColumnHeatLift hc f z).1| ≤
                ((1 + c ^ 2 / 4) ^ (m / 2) * axialWeight m z) *
                  |V.1 - (xColumnHeatLift hc f z).1| := by
                    simpa only [r] using hmul
            _ = (1 + c ^ 2 / 4) ^ (m / 2) *
                (a * |V.1 - (xColumnHeatLift hc f z).1|) := by
                  simp [a, mul_assoc]
    _ = (1 + c ^ 2 / 4) ^ (m / 2) *
        |a * (V.1 - (xColumnHeatLift hc f z).1)| := by
          rw [abs_mul, abs_of_nonneg ha]
    _ ≤ (1 + c ^ 2 / 4) ^ (m / 2) *
        ‖axialHeatCommutatorField (θ := θ) hc f z +
          axialHeatIncrementField (θ := θ) hc f z‖ := by
          have hsum' : a * (V.1 - (xColumnHeatLift hc f z).1) =
              (axialHeatCommutatorField (θ := θ) hc f z +
                axialHeatIncrementField (θ := θ) hc f z).1 := by
            calc
              a * (V.1 - (xColumnHeatLift hc f z).1) =
                  a * V.1 - a * (xColumnHeatLift hc f z).1 := by ring
              _ = _ := hsum.symm
          rw [hsum']
          exact mul_le_mul_of_nonneg_left
            (by
              simpa only [Real.norm_eq_abs] using
                (norm_fst_le (axialHeatCommutatorField (θ := θ) hc f z +
                  axialHeatIncrementField (θ := θ) hc f z))) (by positivity)

/-- The radial weighted output increment is bounded by the two actual normalized-cell terms. -/
theorem eLpNorm_radialHeatIncrement_le {c m θ : ℝ} (hc : 0 < c)
    (hm : 1 ≤ m) (hθ : 0 < θ) (f : X c m) :
    eLpNorm (fun z => bracket z ^ m * (B0284.heat θ (xColumnHeatLift hc f) z).1 -
        bracket z ^ m * (xColumnHeatLift hc f z).1) 2 (Cyl.cellμ c) ≤
      ENNReal.ofReal ((1 + c ^ 2 / 4) ^ (m / 2)) *
        (eLpNorm (axialHeatCommutatorField (θ := θ) hc f) 2 (Cyl.cellμ c) +
          eLpNorm (axialHeatIncrementField (θ := θ) hc f) 2 (Cyl.cellμ c)) := by
  let Cc : ℝ := (1 + c ^ 2 / 4) ^ (m / 2)
  have hCc : 0 ≤ Cc := by dsimp [Cc]; positivity
  have hpoint := radialHeatIncrement_le_commutator_add_increment (θ := θ) hc hm f
  have hpointEnorm : ∀ᵐ z ∂Cyl.cellμ c,
      ‖bracket z ^ m * (B0284.heat θ (xColumnHeatLift hc f) z).1 -
        bracket z ^ m * (xColumnHeatLift hc f z).1‖ₑ ≤
      ‖Cc * ‖axialHeatCommutatorField (θ := θ) hc f z +
        axialHeatIncrementField (θ := θ) hc f z‖‖ₑ := by
    filter_upwards [hpoint] with z hz
    rw [Real.enorm_eq_ofReal_abs, Real.enorm_eq_ofReal_abs,
      abs_of_nonneg (mul_nonneg hCc (norm_nonneg _))]
    exact ENNReal.ofReal_le_ofReal (by simpa [Cc] using hz)
  have hmono := eLpNorm_mono_enorm_ae (p := (2 : ℝ≥0∞)) hpointEnorm
  have hVsm : StronglyMeasurable (xColumnHeatLift hc f) :=
    stronglyMeasurable_xColumnHeatLift hc f
  have hGsm : StronglyMeasurable (fun x => axialWeight m x • xColumnHeatLift hc f x) :=
    (continuous_axialWeight m).stronglyMeasurable.smul hVsm
  have hVheat : StronglyMeasurable (B0284.heat θ (xColumnHeatLift hc f)) :=
    (measurable_heat_of_stronglyMeasurable hVsm).stronglyMeasurable
  have hGheat : StronglyMeasurable
      (B0284.heat θ (fun x => axialWeight m x • xColumnHeatLift hc f x)) :=
    (measurable_heat_of_stronglyMeasurable hGsm).stronglyMeasurable
  have hcomm : AEStronglyMeasurable (axialHeatCommutatorField (θ := θ) hc f) (Cyl.cellμ c) := by
    exact (continuous_axialWeight m).aestronglyMeasurable.smul hVheat.aestronglyMeasurable |>.sub
      hGheat.aestronglyMeasurable |>.mono_ac (Measure.absolutelyContinuous_of_le
        Measure.restrict_le_self)
  have hinc : AEStronglyMeasurable (axialHeatIncrementField (θ := θ) hc f) (Cyl.cellμ c) := by
    exact hGheat.aestronglyMeasurable.sub
      ((continuous_axialWeight m).aestronglyMeasurable.smul hVsm.aestronglyMeasurable) |>.mono_ac
        (Measure.absolutelyContinuous_of_le Measure.restrict_le_self)
  have hsum := eLpNorm_add_le hcomm hinc (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  calc
    _ ≤ eLpNorm (fun z => Cc *
        ‖axialHeatCommutatorField (θ := θ) hc f z +
          axialHeatIncrementField (θ := θ) hc f z‖) 2
        (Cyl.cellμ c) := by
          apply le_trans hmono
          apply eLpNorm_mono_enorm_ae (p := (2 : ℝ≥0∞))
          filter_upwards [] with z
          rw [Real.enorm_eq_ofReal_abs, abs_of_nonneg (mul_nonneg hCc (norm_nonneg _))]
    _ = ENNReal.ofReal Cc * eLpNorm
        (fun z => ‖axialHeatCommutatorField (θ := θ) hc f z +
          axialHeatIncrementField (θ := θ) hc f z‖)
        2 (Cyl.cellμ c) := by
          have hfun : (fun z => Cc *
              ‖axialHeatCommutatorField (θ := θ) hc f z +
                axialHeatIncrementField (θ := θ) hc f z‖) =
              Cc • (fun z => ‖axialHeatCommutatorField (θ := θ) hc f z +
                axialHeatIncrementField (θ := θ) hc f z‖) := by
            funext z
            simp [smul_eq_mul]
          rw [hfun, eLpNorm_const_smul, ← Real.enorm_eq_ofReal hCc]
    _ = ENNReal.ofReal Cc * eLpNorm
        (axialHeatCommutatorField (θ := θ) hc f +
          axialHeatIncrementField (θ := θ) hc f) 2
          (Cyl.cellμ c) := by
            exact congrArg (fun x : ℝ≥0∞ => ENNReal.ofReal Cc * x)
              (eLpNorm_norm (axialHeatCommutatorField (θ := θ) hc f +
                axialHeatIncrementField (θ := θ) hc f))
    _ ≤ ENNReal.ofReal Cc *
        (eLpNorm (axialHeatCommutatorField (θ := θ) hc f) 2 (Cyl.cellμ c) +
          eLpNorm (axialHeatIncrementField (θ := θ) hc f) 2 (Cyl.cellμ c)) := by
            exact mul_le_mul_of_nonneg_left (by simpa using hsum) (by positivity)
    _ = _ := by rfl

/-- The `X_m` norm of the true positive-age increment is the centered-cell norm of the literal
radial B0284 heat increment. -/
theorem norm_xColumnHeatS0Positive_sub_eq_radialIncrement {c m θ : ℝ}
    (hc : 0 < c) (hm : 1 ≤ m) (hθ : 0 < θ)
    (hθ1 : θ ≤ 1) (f : X c m) :
    ‖xColumnHeatS0Positive hc hm hθ hθ1 f - f‖ =
      (eLpNorm (fun z => bracket z ^ m * (B0284.heat θ (xColumnHeatLift hc f) z).1 -
        bracket z ^ m * (xColumnHeatLift hc f z).1) 2 (Cyl.cellμ c)).toReal := by
  rw [norm_X_eq_eLpNorm_radial_cyl hc]
  congr 1
  apply eLpNorm_congr_ae
  have hout := coeFn_xColumnHeatS0Positive hc hm hθ hθ1 f
  have hout0 := (B0579.cellMeasure_ac_cellMeasure c 0 m).ae_le hout
  have hμ : B0579.cellMeasure c 0 = Cyl.cellμ c := by
    rw [cellMeasure_zero_eq_cellVol, B0581.cellVol]
    simp [B0579.cell, Cyl.cell, Cyl.cellμ, show -(c / 2) = -c / 2 by ring]
  rw [hμ] at hout0
  have hin := xColumnPeriodicRep_ae_eq hc f
  have hsub := (B0579.cellMeasure_ac_cellMeasure c 0 m).ae_le
    (Lp.coeFn_sub (xColumnHeatS0Positive hc hm hθ hθ1 f) f)
  rw [hμ] at hsub
  filter_upwards [hout0, hin, hsub] with z ho hi hdiff
  rw [hdiff, Pi.sub_apply, ho]
  have hlift : (xColumnHeatLift hc f z).1 = (f : Plane → ℝ) z := by
    change xColumnPeriodicRep hc f z = (f : Plane → ℝ) z
    exact hi
  rw [hlift]
  ring

end UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution

#print axioms UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution.radial_le_cylinder_axial_on_cell
#print axioms UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution.radialHeatIncrement_le_commutator_add_increment
#print axioms UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution.eLpNorm_radialHeatIncrement_le
#print axioms UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution.norm_xColumnHeatS0Positive_sub_eq_radialIncrement
