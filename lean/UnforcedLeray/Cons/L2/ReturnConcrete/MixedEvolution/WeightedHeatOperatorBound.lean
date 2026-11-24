import UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution.WeightedHeatOperator

/-!
# Fixed-cylinder radial norm control for the actual Gaussian heat image

This leaf begins the weighted `X_m` operator estimate from the actual B0284 heat convolution.
The radial-to-axial comparison is made only on the centered cell and retains its explicit
cylinder factor.
-/

set_option autoImplicit false
set_option maxHeartbeats 500000

noncomputable section

open MeasureTheory
open scoped ENNReal
open UnforcedLeray.B0579

namespace UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution

/-- On the centered cell, the actual radial heat-output integrand is controlled by the axial
weighted vector output, with the exact finite-cylinder comparison factor. -/
theorem eLpNorm_heatField_radial_le_axial_cyl {c m θ : ℝ} (hc : 0 < c)
    (hm : 1 ≤ m) (hθ : 0 < θ) (f : X c m) :
    eLpNorm (fun z => bracket z ^ m * (xColumnHeatField hc hθ f z).1) 2
        (Cyl.cellμ c) ≤
      ENNReal.ofReal ((1 + c ^ 2 / 4) ^ (m / 2)) *
        eLpNorm (fun z => axialWeight m z • xColumnHeatField hc hθ f z) 2
          (Cyl.cellμ c) := by
  let g := xColumnHeatField hc hθ f
  let Cc : ℝ := (1 + c ^ 2 / 4) ^ (m / 2)
  have hCc : 0 ≤ Cc := by dsimp [Cc]; positivity
  have hpoint : ∀ᵐ z ∂Cyl.cellμ c,
      ‖bracket z ^ m * (g z).1‖ₑ ≤ ‖Cc • (axialWeight m z • g z)‖ₑ := by
    filter_upwards [ae_restrict_mem (Cyl.measurableSet_cell c)] with z hz
    have hz' : z ∈ B0579.cell c := by
      simp only [Cyl.cell, Set.mem_prod, Set.mem_Ico, Set.mem_univ] at hz
      simp only [B0579.cell, Set.mem_prod, Set.mem_Ico, Set.mem_univ]
      exact ⟨⟨by linarith [hz.1.1], hz.1.2⟩, trivial⟩
    have hweight := bracket_le_centered_axial hc (by linarith : 0 ≤ m) hz'
    have hax : 0 ≤ axialWeight m z := by
      dsimp [axialWeight, axialBracket]
      positivity
    have hrad : 0 ≤ bracket z ^ m := (bracket_rpow_pos m z).le
    have hreal : |bracket z ^ m * (g z).1| ≤ Cc * ‖axialWeight m z • g z‖ := by
      rw [abs_mul, abs_of_nonneg hrad]
      calc
        bracket z ^ m * |(g z).1| ≤ Cc * axialWeight m z * |(g z).1| :=
          mul_le_mul_of_nonneg_right hweight (abs_nonneg _)
        _ ≤ Cc * ‖axialWeight m z • g z‖ := by
          calc
            Cc * axialWeight m z * |(g z).1| =
                Cc * (axialWeight m z * |(g z).1|) := by ring
            _ ≤ Cc * (axialWeight m z * ‖g z‖) :=
              mul_le_mul_of_nonneg_left
                (mul_le_mul_of_nonneg_left (norm_fst_le (g z)) hax) hCc
            _ = Cc * ‖axialWeight m z • g z‖ := by
              rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hax]
    rw [Real.enorm_eq_ofReal_abs, ← ofReal_norm,
      norm_smul, Real.norm_of_nonneg hCc]
    exact ENNReal.ofReal_le_ofReal hreal
  have hmono := eLpNorm_mono_enorm_ae (p := (2 : ℝ≥0∞)) hpoint
  calc
    eLpNorm (fun z => bracket z ^ m * (xColumnHeatField hc hθ f z).1) 2
        (Cyl.cellμ c) =
        eLpNorm (fun z => bracket z ^ m * (g z).1) 2 (Cyl.cellμ c) := by
          rfl
    _ ≤ eLpNorm (fun z => Cc • (axialWeight m z • g z)) 2 (Cyl.cellμ c) := hmono
    _ = eLpNorm (Cc • (fun z => axialWeight m z • g z)) 2 (Cyl.cellμ c) := by
      rfl
    _ = ENNReal.ofReal Cc *
        eLpNorm (fun z => axialWeight m z • g z) 2 (Cyl.cellμ c) := by
          rw [eLpNorm_const_smul, ← Real.enorm_eq_ofReal hCc]

/-- The axial weight is dominated by the radial weight on each centered-cell input column. -/
theorem eLpNorm_axialHeatLift_le_radialInput_cyl {c m : ℝ} (hc : 0 < c)
    (hm : 1 ≤ m) (f : X c m) :
    eLpNorm (fun z => axialWeight m z • xColumnHeatLift hc f z) 2 (Cyl.cellμ c) ≤
      eLpNorm (fun z => bracket z ^ m * (f : Plane → ℝ) z) 2 (Cyl.cellμ c) := by
  have hrep := xColumnPeriodicRep_ae_eq hc f
  have hpoint : ∀ᵐ z ∂Cyl.cellμ c,
      ‖axialWeight m z • xColumnHeatLift hc f z‖ₑ ≤
        ‖bracket z ^ m * (f : Plane → ℝ) z‖ₑ := by
    filter_upwards [hrep, ae_restrict_mem (Cyl.measurableSet_cell c)] with z hz hzcell
    have hweight := axialBracket_rpow_le_bracket (by linarith : 0 ≤ m) z
    have hax : 0 ≤ axialWeight m z := by
      dsimp [axialWeight, axialBracket]
      positivity
    have hrad : 0 ≤ bracket z ^ m := (bracket_rpow_pos m z).le
    have hpair : ‖xColumnHeatLift hc f z‖ = |(f : Plane → ℝ) z| := by
      change ‖(xColumnPeriodicRep hc f z, (0 : ℝ))‖ = _
      rw [Prod.norm_def, Real.norm_eq_abs, norm_zero, max_eq_left (abs_nonneg _), hz]
    rw [← ofReal_norm, ← ofReal_norm, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg hax, hpair, Real.norm_eq_abs]
    apply ENNReal.ofReal_le_ofReal
    rw [abs_mul, abs_of_nonneg hrad]
    exact mul_le_mul_of_nonneg_right hweight (abs_nonneg _)
  exact eLpNorm_mono_enorm_ae (p := (2 : ℝ≥0∞)) hpoint

/-- Exact real-valued norm conversion for periodic `L²` fields between the centered and
normalized cylinder cells. -/
theorem eLpNorm_toReal_cyl_eq_sqrt_cell {F : Type*} [NormedAddCommGroup F]
    [MeasurableSpace F] [BorelSpace F] [SecondCountableTopology F] {c : ℝ}
    (hc : 0 < c) (f : Plane → F) (hfmeas : Measurable f)
    (hfper : B0284.IsQPeriodic c f) :
    (eLpNorm f 2 (Cyl.cellμ c)).toReal =
      Real.sqrt c * (eLpNorm f 2 (B0284.cellMeasure c)).toReal := by
  have hsq := HeatCylinder.eLpNorm_sq_cyl_eq_cellMeasure hc hfmeas hfper
  have hreal := congrArg ENNReal.toReal hsq
  rw [ENNReal.toReal_pow, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (le_of_lt hc)] at hreal
  rw [ENNReal.toReal_pow] at hreal
  have hcSqrt := Real.sq_sqrt hc.le
  have hleft : 0 ≤ (eLpNorm f 2 (Cyl.cellμ c)).toReal := ENNReal.toReal_nonneg
  have hright : 0 ≤ Real.sqrt c * (eLpNorm f 2 (B0284.cellMeasure c)).toReal :=
    mul_nonneg (Real.sqrt_nonneg c) ENNReal.toReal_nonneg
  nlinarith [hreal]

/-- The actual Gaussian heat map is bounded on the normalized axially weighted cylinder `L²`
carrier, with its literal Gaussian kernel mass. -/
theorem eLpNorm_axialHeat_normalized_le {c m θ : ℝ} (hc : 0 < c)
    (hm : 1 ≤ m) (hθ : 0 < θ) (f : X c m) :
    eLpNorm (fun z => axialWeight m z • B0284.heat θ (xColumnHeatLift hc f) z) 2
        (B0284.cellMeasure c) ≤
      (∫⁻ w : Plane, axialHeatKernel m θ w) *
        eLpNorm (fun z => axialWeight m z • xColumnHeatLift hc f z) 2
          (B0284.cellMeasure c) := by
  exact eLpNorm_axialHeat_le hc hθ (by linarith : 0 ≤ m)
    (periodic_xColumnHeatLift hc f)
    (stronglyMeasurable_xColumnHeatLift hc f).aestronglyMeasurable
    (p := 2) (by norm_num) (by norm_num)

/-- Squared fixed-cylinder radial `L²` estimate for the actual first B0284 heat component. The
normalization factors cancel exactly; the only cylinder loss is the centered radial-to-axial
factor. -/
theorem eLpNorm_radialHeatField_sq_le {c m θ : ℝ} (hc : 0 < c)
    (hm : 1 ≤ m) (hθ : 0 < θ) (f : X c m) :
    (eLpNorm (fun z => bracket z ^ m * (xColumnHeatField hc hθ f z).1) 2
      (Cyl.cellμ c)) ^ 2 ≤
      (ENNReal.ofReal ((1 + c ^ 2 / 4) ^ (m / 2))) ^ 2 *
        (∫⁻ w : Plane, axialHeatKernel m θ w) ^ 2 *
          (eLpNorm (fun z => bracket z ^ m * (f : Plane → ℝ) z) 2
            (Cyl.cellμ c)) ^ 2 := by
  let g := xColumnHeatField hc hθ f
  let a : ℝ≥0∞ := ENNReal.ofReal c
  let M : ℝ≥0∞ := ∫⁻ w : Plane, axialHeatKernel m θ w
  let A := eLpNorm (fun z => bracket z ^ m * (g z).1) 2 (Cyl.cellμ c)
  let Bo := eLpNorm (fun z => axialWeight m z • g z) 2 (Cyl.cellμ c)
  let Bn := eLpNorm (fun z => axialWeight m z • g z) 2 (B0284.cellMeasure c)
  let In := eLpNorm (fun z => axialWeight m z • xColumnHeatLift hc f z) 2
    (B0284.cellMeasure c)
  let Ic := eLpNorm (fun z => axialWeight m z • xColumnHeatLift hc f z) 2
    (Cyl.cellμ c)
  let D := eLpNorm (fun z => bracket z ^ m * (f : Plane → ℝ) z) 2 (Cyl.cellμ c)
  have ha0 : a ≠ 0 := (ENNReal.ofReal_pos.mpr hc).ne'
  have haTop : a ≠ ⊤ := ENNReal.ofReal_ne_top
  have hrad : A ≤ ENNReal.ofReal ((1 + c ^ 2 / 4) ^ (m / 2)) * Bo := by
    dsimp [A, Bo, g]
    exact eLpNorm_heatField_radial_le_axial_cyl hc hm hθ f
  have hInput : Ic ≤ D := by
    dsimp [Ic, D]
    exact eLpNorm_axialHeatLift_le_radialInput_cyl hc hm f
  have hgMeas : Measurable g := by
    dsimp [g]
    exact measurable_heat_of_stronglyMeasurable (stronglyMeasurable_xColumnHeatLift hc f)
  have hgPer : B0284.IsQPeriodic c g := by
    dsimp [g]
    exact B0284.heat_periodic (periodic_xColumnHeatLift hc f)
  have hOutAxMeas : Measurable (fun z => axialWeight m z • g z) :=
    (continuous_axialWeight m).measurable.smul hgMeas
  have hOutAxPer : B0284.IsQPeriodic c (fun z => axialWeight m z • g z) := by
    intro z
    change axialWeight m (z.1 + c, z.2) • g (z.1 + c, z.2) = _
    rw [show axialWeight m (z.1 + c, z.2) = axialWeight m z by
      simp [axialWeight, axialBracket], hgPer z]
  have hInMeas : Measurable (fun z => axialWeight m z • xColumnHeatLift hc f z) :=
    (continuous_axialWeight m).measurable.smul
      (stronglyMeasurable_xColumnHeatLift hc f).measurable
  have hInPer : B0284.IsQPeriodic c
      (fun z => axialWeight m z • xColumnHeatLift hc f z) := by
    intro z
    change axialWeight m (z.1 + c, z.2) • xColumnHeatLift hc f (z.1 + c, z.2) = _
    rw [show axialWeight m (z.1 + c, z.2) = axialWeight m z by
      simp [axialWeight, axialBracket], periodic_xColumnHeatLift hc f z]
  have hOutSq : Bo ^ 2 = a * Bn ^ 2 := by
    dsimp [Bo, Bn, a]
    exact HeatCylinder.eLpNorm_sq_cyl_eq_cellMeasure hc hOutAxMeas hOutAxPer
  have hInSq : Ic ^ 2 = a * In ^ 2 := by
    dsimp [Ic, In, a]
    exact HeatCylinder.eLpNorm_sq_cyl_eq_cellMeasure hc hInMeas hInPer
  have hAxHeat : Bn ≤ M * In := by
    dsimp [Bn, M, In, g]
    exact eLpNorm_axialHeat_normalized_le hc hm hθ f
  have hInputSq : In ^ 2 ≤ a⁻¹ * D ^ 2 := by
    dsimp [In, Ic, D, a]
    calc
      eLpNorm (fun z => axialWeight m z • xColumnHeatLift hc f z) 2
          (B0284.cellMeasure c) ^ 2 =
          a⁻¹ * (a * eLpNorm (fun z => axialWeight m z • xColumnHeatLift hc f z) 2
            (B0284.cellMeasure c) ^ 2) := by
              rw [ENNReal.inv_mul_cancel_left ha0 haTop]
      _ = a⁻¹ * (eLpNorm (fun z => axialWeight m z • xColumnHeatLift hc f z) 2
          (Cyl.cellμ c) ^ 2) := by rw [hInSq]
      _ ≤ a⁻¹ * (eLpNorm (fun z => bracket z ^ m * (f : Plane → ℝ) z) 2
          (Cyl.cellμ c) ^ 2) := by
            exact mul_le_mul_of_nonneg_left (pow_le_pow_left' hInput 2) (by positivity)
  have hAxSq : Bn ^ 2 ≤ M ^ 2 * In ^ 2 := by
    calc
      Bn ^ 2 ≤ (M * In) ^ 2 := pow_le_pow_left' hAxHeat 2
      _ = M ^ 2 * In ^ 2 := by rw [mul_pow]
  have hOutSqBound : Bo ^ 2 ≤ (a * M ^ 2) * In ^ 2 := by
    calc
      Bo ^ 2 = a * Bn ^ 2 := hOutSq
      _ ≤ a * (M ^ 2 * In ^ 2) :=
        mul_le_mul_of_nonneg_left hAxSq (by positivity)
      _ = (a * M ^ 2) * In ^ 2 := by ring
  have hCancel : a * (a⁻¹ * D ^ 2) = D ^ 2 :=
    ENNReal.mul_inv_cancel_left ha0 haTop
  have hboundAxial : Bo ^ 2 ≤ M ^ 2 * D ^ 2 := by
    calc
      Bo ^ 2 ≤ (a * M ^ 2) * In ^ 2 := hOutSqBound
      _ ≤ (a * M ^ 2) * (a⁻¹ * D ^ 2) :=
        mul_le_mul_of_nonneg_left hInputSq (by positivity)
      _ = M ^ 2 * (a * (a⁻¹ * D ^ 2)) := by ring
      _ = M ^ 2 * D ^ 2 := by rw [hCancel]
  have hradSq : A ^ 2 ≤
      (ENNReal.ofReal ((1 + c ^ 2 / 4) ^ (m / 2))) ^ 2 * Bo ^ 2 := by
    calc
      A ^ 2 ≤ (ENNReal.ofReal ((1 + c ^ 2 / 4) ^ (m / 2)) * Bo) ^ 2 :=
        pow_le_pow_left' hrad 2
      _ = (ENNReal.ofReal ((1 + c ^ 2 / 4) ^ (m / 2))) ^ 2 * Bo ^ 2 := by rw [mul_pow]
  calc
    A ^ 2 ≤ (ENNReal.ofReal ((1 + c ^ 2 / 4) ^ (m / 2))) ^ 2 * Bo ^ 2 := hradSq
    _ ≤ (ENNReal.ofReal ((1 + c ^ 2 / 4) ^ (m / 2))) ^ 2 * (M ^ 2 * D ^ 2) :=
      mul_le_mul_of_nonneg_left hboundAxial (by positivity)
    _ = (ENNReal.ofReal ((1 + c ^ 2 / 4) ^ (m / 2))) ^ 2 * M ^ 2 * D ^ 2 := by ring

/-- The weighted `X_m` heat output and the concrete normalized-cell heat CLM have the same
first-coordinate class on the weighted centered measure. -/
theorem coeFn_xColumnHeatS0Positive_eq_heatL2Rep {c m θ : ℝ} (hc : 0 < c)
    (hc1 : 1 ≤ c) (hm : 1 ≤ m) (hθ : 0 < θ) (hθ1 : θ ≤ 1) (f : X c m) :
    (xColumnHeatS0Positive hc hm hθ hθ1 f : Plane → ℝ) =ᵐ[B0579.cellMeasure c m]
      fun z => (HeatCylinder.planeRep hc (xColumnHeatL2CLM hc hc1 hm θ f) z).1 := by
  have hperiodic := xColumnPeriodicRep_ae_eq hc
    (xColumnHeatS0Positive hc hm hθ hθ1 f)
  have hrep0 : (xColumnPeriodicRep hc (xColumnHeatS0Positive hc hm hθ hθ1 f)) =ᵐ[
      B0579.cellMeasure c 0]
      (xColumnHeatS0Positive hc hm hθ hθ1 f : Plane → ℝ) := by
    simpa [cellMeasure_zero_eq_cellVol, B0581.cellVol, B0579.cell,
      Cyl.cellμ, Cyl.cell, show -(c / 2) = -c / 2 by ring] using hperiodic
  have hrepWeighted := (B0579.cellMeasure_ac_cellMeasure c m 0).ae_le hrep0
  have hactual := xColumnHeatL2CLM_apply_eq_actual_heat hc hc1 hm hθ hθ1 f
  have hactualWeighted :=
    ((B0579.cellMeasure_ac c m).trans Measure.absolutelyContinuous_restrict).ae_le hactual
  filter_upwards [hrepWeighted, hactualWeighted] with z hzRep hzHeat
  exact hzRep.symm.trans hzHeat.symm

/-- Additivity of the actual weighted positive-age heat output, transferred through its real
normalized-cell Gaussian heat CLM representative. -/
theorem xColumnHeatS0Positive_add {c m θ : ℝ} (hc : 0 < c) (hc1 : 1 ≤ c)
    (hm : 1 ≤ m) (hθ : 0 < θ) (hθ1 : θ ≤ 1) (f g : X c m) :
    xColumnHeatS0Positive hc hm hθ hθ1 (f + g) =
      xColumnHeatS0Positive hc hm hθ hθ1 f + xColumnHeatS0Positive hc hm hθ hθ1 g := by
  let y := fun v : X c m => xColumnHeatL2CLM hc hc1 hm θ v
  let r := fun v : X c m => HeatCylinder.planeRep hc (y v)
  have hy : y (f + g) = y f + y g := map_add (xColumnHeatL2CLM hc hc1 hm θ) f g
  have hcoe : (y (f + g) : Plane → Plane) =ᵐ[B0284.cellMeasure c]
      fun z => (y f : Plane → Plane) z + (y g : Plane → Plane) z := by
    rw [hy]
    exact Lp.coeFn_add (y f) (y g)
  have hr0 := (HeatCylinder.planeRep_spec hc (y (f + g))).2.2
  have hr1 := (HeatCylinder.planeRep_spec hc (y f)).2.2
  have hr2 := (HeatCylinder.planeRep_spec hc (y g)).2.2
  have hrAdd : r (f + g) =ᵐ[B0284.cellMeasure c] fun z => r f z + r g z := by
    filter_upwards [hr0, hr1, hr2, hcoe] with z h0 h1 h2 h3
    calc
      r (f + g) z = (y (f + g) : Plane → Plane) z := h0
      _ = (y f : Plane → Plane) z + (y g : Plane → Plane) z := h3
      _ = r f z + r g z := by rw [← h1, ← h2]
  have hrper0 := (HeatCylinder.planeRep_spec hc (y (f + g))).2.1
  have hrper1 := (HeatCylinder.planeRep_spec hc (y f)).2.1
  have hrper2 := (HeatCylinder.planeRep_spec hc (y g)).2.1
  have hrperSum : B0284.IsQPeriodic c (fun z => r f z + r g z) := by
    intro z
    change HeatCylinder.planeRep hc (y f) (z.1 + c, z.2) +
      HeatCylinder.planeRep hc (y g) (z.1 + c, z.2) = _
    rw [hrper1 z, hrper2 z]
  let Q : Plane → Prop := fun z => r (f + g) z = r f z + r g z
  have hperQ : B0284.IsQPeriodic c Q := by
    intro z
    change (HeatCylinder.planeRep hc (y (f + g)) (z.1 + c, z.2) =
      HeatCylinder.planeRep hc (y f) (z.1 + c, z.2) +
        HeatCylinder.planeRep hc (y g) (z.1 + c, z.2)) =
        (HeatCylinder.planeRep hc (y (f + g)) z =
          HeatCylinder.planeRep hc (y f) z + HeatCylinder.planeRep hc (y g) z)
    rw [hrper0 z, hrper1 z, hrper2 z]
  have hGlobalQ : ∀ᵐ z ∂volume, Q z :=
    B0289.ae_of_ae_cellMeasure hc hperQ hrAdd
  have hrAddGlobal : r (f + g) =ᵐ[volume] fun z => r f z + r g z := by
    change ∀ᵐ z ∂volume, r (f + g) z = (fun z => r f z + r g z) z
    exact hGlobalQ
  have hrAddWeighted :=
    ((B0579.cellMeasure_ac c m).trans Measure.absolutelyContinuous_restrict).ae_le hrAddGlobal
  have hOut0 := coeFn_xColumnHeatS0Positive_eq_heatL2Rep hc hc1 hm hθ hθ1 (f + g)
  have hOut1 := coeFn_xColumnHeatS0Positive_eq_heatL2Rep hc hc1 hm hθ hθ1 f
  have hOut2 := coeFn_xColumnHeatS0Positive_eq_heatL2Rep hc hc1 hm hθ hθ1 g
  have hpoint : (xColumnHeatS0Positive hc hm hθ hθ1 (f + g) : Plane → ℝ) =ᵐ[
      B0579.cellMeasure c m]
      fun z => (xColumnHeatS0Positive hc hm hθ hθ1 f : Plane → ℝ) z +
        (xColumnHeatS0Positive hc hm hθ hθ1 g : Plane → ℝ) z := by
    filter_upwards [hOut0, hOut1, hOut2, hrAddWeighted] with z h0 h1 h2 h3
    calc
      (xColumnHeatS0Positive hc hm hθ hθ1 (f + g) : Plane → ℝ) z = (r (f + g) z).1 := h0
      _ = (r f z + r g z).1 := congrArg Prod.fst h3
      _ = (r f z).1 + (r g z).1 := Prod.fst_add _ _
      _ = (xColumnHeatS0Positive hc hm hθ hθ1 f : Plane → ℝ) z +
          (xColumnHeatS0Positive hc hm hθ hθ1 g : Plane → ℝ) z := by
            rw [← h1, ← h2]
  apply Lp.ext
  filter_upwards [hpoint, Lp.coeFn_add
    (xColumnHeatS0Positive hc hm hθ hθ1 f)
    (xColumnHeatS0Positive hc hm hθ hθ1 g)] with z hz hadd
  exact hz.trans hadd.symm

/-- Real scalar compatibility of the actual weighted positive-age heat output. -/
theorem xColumnHeatS0Positive_smul {c m θ : ℝ} (hc : 0 < c) (hc1 : 1 ≤ c)
    (hm : 1 ≤ m) (hθ : 0 < θ) (hθ1 : θ ≤ 1) (a : ℝ) (f : X c m) :
    xColumnHeatS0Positive hc hm hθ hθ1 (a • f) =
      a • xColumnHeatS0Positive hc hm hθ hθ1 f := by
  let y := fun v : X c m => xColumnHeatL2CLM hc hc1 hm θ v
  let r := fun v : X c m => HeatCylinder.planeRep hc (y v)
  have hy : y (a • f) = a • y f := map_smul (xColumnHeatL2CLM hc hc1 hm θ) a f
  have hcoe : (y (a • f) : Plane → Plane) =ᵐ[B0284.cellMeasure c]
      fun z => a • (y f : Plane → Plane) z := by
    rw [hy]
    exact Lp.coeFn_smul a (y f)
  have hr0 := (HeatCylinder.planeRep_spec hc (y (a • f))).2.2
  have hr1 := (HeatCylinder.planeRep_spec hc (y f)).2.2
  have hrSmul : r (a • f) =ᵐ[B0284.cellMeasure c] fun z => a • r f z := by
    filter_upwards [hr0, hr1, hcoe] with z h0 h1 h2
    calc
      r (a • f) z = (y (a • f) : Plane → Plane) z := h0
      _ = a • (y f : Plane → Plane) z := h2
      _ = a • r f z := by rw [← h1]
  have hrper0 := (HeatCylinder.planeRep_spec hc (y (a • f))).2.1
  have hrper1 := (HeatCylinder.planeRep_spec hc (y f)).2.1
  let Q : Plane → Prop := fun z => r (a • f) z = a • r f z
  have hperQ : B0284.IsQPeriodic c Q := by
    intro z
    change (HeatCylinder.planeRep hc (y (a • f)) (z.1 + c, z.2) =
      a • HeatCylinder.planeRep hc (y f) (z.1 + c, z.2)) =
        (HeatCylinder.planeRep hc (y (a • f)) z = a • HeatCylinder.planeRep hc (y f) z)
    rw [hrper0 z, hrper1 z]
  have hGlobalQ : ∀ᵐ z ∂volume, Q z :=
    B0289.ae_of_ae_cellMeasure hc hperQ hrSmul
  have hrSmulGlobal : r (a • f) =ᵐ[volume] fun z => a • r f z := by
    change ∀ᵐ z ∂volume, r (a • f) z = (fun z => a • r f z) z
    exact hGlobalQ
  have hrSmulWeighted :=
    ((B0579.cellMeasure_ac c m).trans Measure.absolutelyContinuous_restrict).ae_le
      hrSmulGlobal
  have hOut0 := coeFn_xColumnHeatS0Positive_eq_heatL2Rep hc hc1 hm hθ hθ1 (a • f)
  have hOut1 := coeFn_xColumnHeatS0Positive_eq_heatL2Rep hc hc1 hm hθ hθ1 f
  have hpoint : (xColumnHeatS0Positive hc hm hθ hθ1 (a • f) : Plane → ℝ) =ᵐ[
      B0579.cellMeasure c m]
      fun z => a • (xColumnHeatS0Positive hc hm hθ hθ1 f : Plane → ℝ) z := by
    filter_upwards [hOut0, hOut1, hrSmulWeighted] with z h0 h1 h2
    calc
      (xColumnHeatS0Positive hc hm hθ hθ1 (a • f) : Plane → ℝ) z = (r (a • f) z).1 := h0
      _ = a • (r f z).1 := by
        rw [h2]
        simp only [Prod.smul_fst]
      _ = a • (xColumnHeatS0Positive hc hm hθ hθ1 f : Plane → ℝ) z := by rw [← h1]
  apply Lp.ext
  filter_upwards [hpoint, Lp.coeFn_smul a
    (xColumnHeatS0Positive hc hm hθ hθ1 f)] with z hz hsmul
  exact hz.trans hsmul.symm

/-- The actual positive-age weighted heat family as a real linear map on the radial `X_m`
space. -/
noncomputable def xColumnHeatS0PositiveLinear {c m θ : ℝ} (hc : 0 < c) (hc1 : 1 ≤ c)
    (hm : 1 ≤ m) (hθ : 0 < θ) (hθ1 : θ ≤ 1) : X c m →ₗ[ℝ] X c m where
  toFun := xColumnHeatS0Positive hc hm hθ hθ1
  map_add' := xColumnHeatS0Positive_add hc hc1 hm hθ hθ1
  map_smul' := xColumnHeatS0Positive_smul hc hc1 hm hθ hθ1

/-- The actual weighted heat output has its `X_m` norm equal to the centered radial Gaussian
integrand norm. -/
theorem norm_xColumnHeatS0Positive_eq_eLpNorm {c m θ : ℝ} (hc : 0 < c)
    (hm : 1 ≤ m) (hθ : 0 < θ) (hθ1 : θ ≤ 1) (f : X c m) :
    ‖xColumnHeatS0Positive hc hm hθ hθ1 f‖ =
      (eLpNorm (fun z => bracket z ^ m * (xColumnHeatField hc hθ f z).1) 2
        (Cyl.cellμ c)).toReal := by
  let out := xColumnHeatS0Positive hc hm hθ hθ1 f
  let g := xColumnHeatField hc hθ f
  have hleft : Cyl.cellμ c = volume.restrict (B0579.cell c) := by
    have hleft : -(c / 2) = -c / 2 := by ring
    simp [Cyl.cellμ, Cyl.cell, B0579.cell, hleft]
  have hactual := coeFn_xColumnHeatS0Positive hc hm hθ hθ1 f
  have hactualCell := (B0579.ac_cellMeasure c m).ae_le hactual
  have hweightedEq : (fun z => bracket z ^ m * (out : Plane → ℝ) z) =ᵐ[
      volume.restrict (B0579.cell c)]
      fun z => bracket z ^ m * (g z).1 := by
    filter_upwards [hactualCell] with z hz
    rw [hz]
    rfl
  rw [Lp.norm_def, B0579.eLpNorm_cellMeasure]
  have hweightedEq' : (fun z => jb z ^ (m / 2) * (out : Plane → ℝ) z) =ᵐ[
      volume.restrict (B0579.cell c)]
      fun z => bracket z ^ m * (g z).1 := by
    filter_upwards [hweightedEq] with z hz
    rw [← B0579.bracket_rpow, hz]
  rw [eLpNorm_congr_ae hweightedEq']
  rw [← hleft]

/-- For an `X_m` input, its norm is the centered radial integrand eLp norm. -/
theorem norm_X_eq_eLpNorm_radial_cyl {c m : ℝ} (hc : 0 < c) (f : X c m) :
    ‖f‖ = (eLpNorm (fun z => bracket z ^ m * (f : Plane → ℝ) z) 2
      (Cyl.cellμ c)).toReal := by
  have hleft : Cyl.cellμ c = volume.restrict (B0579.cell c) := by
    have hleft : -(c / 2) = -c / 2 := by ring
    simp [Cyl.cellμ, Cyl.cell, B0579.cell, hleft]
  rw [Lp.norm_def, B0579.eLpNorm_cellMeasure]
  rw [← hleft]
  have hfun : (fun z => jb z ^ (m / 2) * (f : Plane → ℝ) z) =ᵐ[Cyl.cellμ c]
      fun z => bracket z ^ m * (f : Plane → ℝ) z := by
    filter_upwards [] with z
    rw [← B0579.bracket_rpow]
  rw [eLpNorm_congr_ae hfun]

/-- The actual weighted positive-age heat column has a fixed-cylinder operator bound with the
literal axial Gaussian kernel mass. -/
theorem norm_xColumnHeatS0Positive_le {c m θ : ℝ} (hc : 0 < c) (hc1 : 1 ≤ c)
    (hm : 1 ≤ m) (hθ : 0 < θ) (hθ1 : θ ≤ 1) (f : X c m) :
    ‖xColumnHeatS0Positive hc hm hθ hθ1 f‖ ≤
      (1 + c ^ 2 / 4) ^ (m / 2) *
        (∫⁻ w : Plane, axialHeatKernel m θ w).toReal * ‖f‖ := by
  let Cc : ℝ := (1 + c ^ 2 / 4) ^ (m / 2)
  let M : ℝ≥0∞ := ∫⁻ w : Plane, axialHeatKernel m θ w
  let A : ℝ≥0∞ := eLpNorm (fun z => bracket z ^ m *
    (xColumnHeatField hc hθ f z).1) 2 (Cyl.cellμ c)
  let D : ℝ≥0∞ := eLpNorm (fun z => bracket z ^ m *
    (f : Plane → ℝ) z) 2 (Cyl.cellμ c)
  have hCc : 0 ≤ Cc := by dsimp [Cc]; positivity
  have hMle : M ≤ ENNReal.ofReal
      (2 ^ (m / 2) * ∫ z : Plane, axialHeatMomentDensity 1 m z) := by
    dsimp [M]
    exact axialHeatKernel_lintegral_le hθ hθ1 (by linarith : 0 ≤ m)
  have hMtop : M ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hMle
  have hleft : Cyl.cellμ c = volume.restrict (B0579.cell c) := by
    have hleft : -(c / 2) = -c / 2 := by ring
    simp [Cyl.cellμ, Cyl.cell, B0579.cell, hleft]
  have hD_eq : D = eLpNorm (f : Plane → ℝ) 2 (B0579.cellMeasure c m) := by
    dsimp [D]
    have hweight : (fun z => bracket z ^ m * (f : Plane → ℝ) z) =ᵐ[Cyl.cellμ c]
        fun z => jb z ^ (m / 2) * (f : Plane → ℝ) z := by
      filter_upwards [] with z
      rw [B0579.bracket_rpow]
    calc
      eLpNorm (fun z => bracket z ^ m * (f : Plane → ℝ) z) 2 (Cyl.cellμ c) =
          eLpNorm (fun z => jb z ^ (m / 2) * (f : Plane → ℝ) z) 2
            (Cyl.cellμ c) := eLpNorm_congr_ae hweight
      _ = eLpNorm (fun z => jb z ^ (m / 2) * (f : Plane → ℝ) z) 2
            (volume.restrict (B0579.cell c)) := by rw [hleft]
      _ = eLpNorm (f : Plane → ℝ) 2 (B0579.cellMeasure c m) :=
        (B0579.eLpNorm_cellMeasure c m (f : Plane → ℝ)).symm
  have hDtop : D ≠ ⊤ := by
    rw [hD_eq]
    exact (Lp.memLp f).eLpNorm_ne_top
  have hRtop : (ENNReal.ofReal Cc ^ 2 * M ^ 2 * D ^ 2) ≠ ⊤ := by
    exact ENNReal.mul_ne_top
      (ENNReal.mul_ne_top (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)
        (ENNReal.pow_ne_top hMtop)) (ENNReal.pow_ne_top hDtop)
  have hSq := eLpNorm_radialHeatField_sq_le hc hm hθ f
  have hTo := ENNReal.toReal_mono hRtop hSq
  have hRealSq : A.toReal ^ 2 ≤ Cc ^ 2 * M.toReal ^ 2 * D.toReal ^ 2 := by
    simpa [A, Cc, M, D, ENNReal.toReal_mul, ENNReal.toReal_pow,
      ENNReal.toReal_ofReal hCc] using hTo
  have hNormOut := norm_xColumnHeatS0Positive_eq_eLpNorm hc hm hθ hθ1 f
  have hNormIn := norm_X_eq_eLpNorm_radial_cyl hc f
  have hCoeff : 0 ≤ Cc * M.toReal := mul_nonneg hCc ENNReal.toReal_nonneg
  have hA : 0 ≤ A.toReal := ENNReal.toReal_nonneg
  have hDreal : 0 ≤ D.toReal := ENNReal.toReal_nonneg
  have hProduct : 0 ≤ Cc * M.toReal * D.toReal := mul_nonneg hCoeff hDreal
  have hNormBound : A.toReal ≤ Cc * M.toReal * D.toReal :=
    (sq_le_sq₀ hA hProduct).mp (by nlinarith [hRealSq])
  rw [hNormOut, hNormIn]
  simpa [Cc, M, D, mul_assoc] using hNormBound

/-- The positive-age actual Gaussian heat column is a bounded real-linear operator on the
weighted centered-cell space. Its bound retains the explicit finite-cylinder loss. -/
noncomputable def xColumnHeatS0PositiveCLM {c m θ : ℝ} (hc : 0 < c) (hc1 : 1 ≤ c)
    (hm : 1 ≤ m) (hθ : 0 < θ) (hθ1 : θ ≤ 1) : X c m →L[ℝ] X c m :=
  (xColumnHeatS0PositiveLinear hc hc1 hm hθ hθ1).mkContinuous
    ((1 + c ^ 2 / 4) ^ (m / 2) *
      (∫⁻ w : Plane, axialHeatKernel m θ w).toReal)
    (norm_xColumnHeatS0Positive_le hc hc1 hm hθ hθ1)

theorem xColumnHeatS0PositiveCLM_apply {c m θ : ℝ} (hc : 0 < c) (hc1 : 1 ≤ c)
    (hm : 1 ≤ m) (hθ : 0 < θ) (hθ1 : θ ≤ 1) (f : X c m) :
    xColumnHeatS0PositiveCLM hc hc1 hm hθ hθ1 f =
      xColumnHeatS0Positive hc hm hθ hθ1 f := rfl

theorem norm_xColumnHeatS0PositiveCLM_le {c m θ : ℝ} (hc : 0 < c) (hc1 : 1 ≤ c)
    (hm : 1 ≤ m) (hθ : 0 < θ) (hθ1 : θ ≤ 1) :
    ‖xColumnHeatS0PositiveCLM hc hc1 hm hθ hθ1‖ ≤
      (1 + c ^ 2 / 4) ^ (m / 2) *
        (∫⁻ w : Plane, axialHeatKernel m θ w).toReal := by
  rw [ContinuousLinearMap.opNorm_le_iff (by positivity)]
  intro f
  rw [xColumnHeatS0PositiveCLM_apply]
  exact norm_xColumnHeatS0Positive_le hc hc1 hm hθ hθ1 f


end UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution

#print axioms UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution.eLpNorm_heatField_radial_le_axial_cyl
#print axioms UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution.eLpNorm_axialHeatLift_le_radialInput_cyl
#print axioms UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution.eLpNorm_toReal_cyl_eq_sqrt_cell
#print axioms UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution.eLpNorm_axialHeat_normalized_le
#print axioms UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution.eLpNorm_radialHeatField_sq_le
#print axioms UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution.coeFn_xColumnHeatS0Positive_eq_heatL2Rep
#print axioms UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution.xColumnHeatS0Positive_add
#print axioms UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution.xColumnHeatS0Positive_smul
#print axioms UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution.norm_xColumnHeatS0Positive_eq_eLpNorm
#print axioms UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution.norm_X_eq_eLpNorm_radial_cyl
#print axioms UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution.norm_xColumnHeatS0Positive_le
#print axioms UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution.xColumnHeatS0PositiveCLM
#print axioms UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution.norm_xColumnHeatS0PositiveCLM_le
