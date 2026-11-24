import UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution.AxialHeatStrongContinuity
import UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution.AxialHeatIntertwining
import UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution.WeightedHeatSemigroup
import UnforcedLeray.Lib.HeatCylinder.HeatL2StrongContinuity

/-!
# Fixed-cylinder age-zero estimate for actual weighted heat

This leaf names the two concrete terms in the already-proved radial increment split so their
periodicity and normalized-cell limits can be tracked without changing the reviewed estimate.
-/

set_option autoImplicit false
set_option maxHeartbeats 500000

noncomputable section

open MeasureTheory
open Filter
open Set
open scoped ENNReal Topology
open UnforcedLeray.GaussianVortex (Plane)
open UnforcedLeray.B0579 hiding Plane

namespace UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution

/-- Actual axial commutator field for the selected periodic lift of an `X_m` column. -/
def actualAxialHeatCommutator {c m θ : ℝ} (hc : 0 < c) (f : X c m) : Plane → Plane :=
  fun z => axialWeight m z • B0284.heat θ (xColumnHeatLift hc f) z -
    B0284.heat θ (fun x => axialWeight m x • xColumnHeatLift hc f x) z

/-- Actual Gaussian heat increment on the same axially weighted periodic input. -/
def actualAxialHeatIncrement {c m θ : ℝ} (hc : 0 < c) (f : X c m) : Plane → Plane :=
  fun z => B0284.heat θ (fun x => axialWeight m x • xColumnHeatLift hc f x) z -
    axialWeight m z • xColumnHeatLift hc f z

private theorem actualAxialHeatCommutator_measurable {c m θ : ℝ} (hc : 0 < c)
    (f : X c m) : Measurable (actualAxialHeatCommutator (θ := θ) hc f) := by
  have hv : StronglyMeasurable (xColumnHeatLift hc f) := stronglyMeasurable_xColumnHeatLift hc f
  have hg : StronglyMeasurable (fun x => axialWeight m x • xColumnHeatLift hc f x) :=
    (continuous_axialWeight m).stronglyMeasurable.smul hv
  have hhv := measurable_heat_of_stronglyMeasurable (θ := θ) hv
  have hhg := measurable_heat_of_stronglyMeasurable (θ := θ) hg
  exact ((continuous_axialWeight m).measurable.smul hhv).sub hhg

/-- The increment estimate from the reviewed leaf expressed using the public physical fields. -/
theorem eLpNorm_radialHeatIncrement_le_actual_fields {c m θ : ℝ} (hc : 0 < c)
    (hm : 1 ≤ m) (hθ : 0 < θ) (f : X c m) :
    eLpNorm (fun z => bracket z ^ m * (B0284.heat θ (xColumnHeatLift hc f) z).1 -
        bracket z ^ m * (xColumnHeatLift hc f z).1) 2 (Cyl.cellμ c) ≤
      ENNReal.ofReal ((1 + c ^ 2 / 4) ^ (m / 2)) *
        (eLpNorm (actualAxialHeatCommutator (θ := θ) hc f) 2 (Cyl.cellμ c) +
          eLpNorm (actualAxialHeatIncrement (θ := θ) hc f) 2 (Cyl.cellμ c)) := by
  change eLpNorm (fun z => bracket z ^ m *
      (B0284.heat θ (xColumnHeatLift hc f) z).1 -
        bracket z ^ m * (xColumnHeatLift hc f z).1) 2 (Cyl.cellμ c) ≤ _
  exact eLpNorm_radialHeatIncrement_le hc hm hθ f

/-- The named commutator is exactly the operator controlled by the actual Gaussian weight
difference estimate. -/
theorem eLpNorm_actualAxialHeatCommutator_le_kernel {c m θ : ℝ} (hc : 0 < c)
    (hm : 1 ≤ m) (hθ : 0 < θ) (f : X c m) :
    eLpNorm (actualAxialHeatCommutator (θ := θ) hc f) 2 (B0284.cellMeasure c) ≤
      (∫⁻ w : Plane, axialHeatCommutatorKernel θ m w) *
        eLpNorm (fun z => axialWeight m z • xColumnHeatLift hc f z) 2
          (B0284.cellMeasure c) := by
  exact eLpNorm_axialHeatCommutator_le_kernel hc hm hθ f

/-- The named axial heat input is the actual normalized-cell heat orbit used in the second
increment term. -/
theorem actualAxialHeatIncrement_eq_heatCLM_ae {c m θ : ℝ} (hc : 0 < c)
    (hm : 1 ≤ m) (f : X c m) :
    actualAxialHeatIncrement (θ := θ) hc f =ᵐ[B0284.cellMeasure c]
      (HeatCylinder.heatL2CLM hc θ (axialWeightedHeatInput hc hm f) : Plane → Plane) -
        (axialWeightedHeatInput hc hm f : Plane → Plane) := by
  have hheat := axialWeightedHeatInput_heat_value_ae hc hm (θ := θ) f
  have hinput := coeFn_axialWeightedHeatInput hc hm f
  filter_upwards [hheat, hinput] with z hzHeat hzInput
  change B0284.heat θ (fun x => axialWeight m x • xColumnHeatLift hc f x) z -
      axialWeight m z • xColumnHeatLift hc f z = _
  rw [Pi.sub_apply, ← hzHeat, ← hzInput]

private theorem actualAxialHeatIncrement_measurable {c m θ : ℝ} (hc : 0 < c)
    (f : X c m) :
    Measurable (actualAxialHeatIncrement (θ := θ) hc f) := by
  have hg : StronglyMeasurable (fun x => axialWeight m x • xColumnHeatLift hc f x) :=
    (continuous_axialWeight m).stronglyMeasurable.smul (stronglyMeasurable_xColumnHeatLift hc f)
  have hheat := measurable_heat_of_stronglyMeasurable (θ := θ) hg
  exact hheat.sub ((continuous_axialWeight m).measurable.smul
    (stronglyMeasurable_xColumnHeatLift hc f).measurable)

private theorem actualAxialHeatIncrement_periodic {c m θ : ℝ} (hc : 0 < c)
    (f : X c m) : B0284.IsQPeriodic c (actualAxialHeatIncrement (θ := θ) hc f) := by
  have hg : B0284.IsQPeriodic c
      (fun x => axialWeight m x • xColumnHeatLift hc f x) := by
    intro z
    change axialWeight m (z.1 + c, z.2) • xColumnHeatLift hc f (z.1 + c, z.2) = _
    rw [show axialWeight m (z.1 + c, z.2) = axialWeight m z by
      simp [axialWeight, axialBracket], periodic_xColumnHeatLift hc f z]
  have hheat := B0284.heat_periodic (θ := θ) hg
  intro z
  simp only [actualAxialHeatIncrement, hheat z,
    show axialWeight m (z.1 + c, z.2) = axialWeight m z by
      simp [axialWeight, axialBracket], periodic_xColumnHeatLift hc f z]

private theorem actualAxialHeatCommutator_periodic {c m θ : ℝ} (hc : 0 < c)
    (f : X c m) : B0284.IsQPeriodic c (actualAxialHeatCommutator (θ := θ) hc f) := by
  have hv : B0284.IsQPeriodic c (xColumnHeatLift hc f) := periodic_xColumnHeatLift hc f
  have hg : B0284.IsQPeriodic c
      (fun x => axialWeight m x • xColumnHeatLift hc f x) := by
    intro z
    change axialWeight m (z.1 + c, z.2) • xColumnHeatLift hc f (z.1 + c, z.2) = _
    rw [show axialWeight m (z.1 + c, z.2) = axialWeight m z by
      simp [axialWeight, axialBracket], hv z]
  have hhv := B0284.heat_periodic (θ := θ) hv
  have hhg := B0284.heat_periodic (θ := θ) hg
  intro z
  simp only [actualAxialHeatCommutator]
  rw [show axialWeight m (z.1 + c, z.2) = axialWeight m z by
      simp [axialWeight, axialBracket], hhv z, hhg z]

/-- The actual axial heat-increment term tends to zero in centered-cell L². This is precisely
the normalized-cell strong continuity of the existing B0284 heat CLM, transferred through the
actual axial input representative. -/
theorem tendsto_actualAxialHeatIncrement_centered_norm {c m : ℝ} (hc : 0 < c)
    (hm : 1 ≤ m) (f : X c m) :
    Tendsto (fun θ : ℝ =>
      (eLpNorm (actualAxialHeatIncrement (θ := θ) hc f) 2 (Cyl.cellμ c)).toReal)
      (nhdsWithin 0 (Ioi 0)) (𝓝 0) := by
  let x := axialWeightedHeatInput hc hm f
  have hcont := HeatCylinder.tendsto_heatL2CLM_apply_zero hc x
  have hdiff : Tendsto (fun θ : ℝ => HeatCylinder.heatL2CLM hc θ x - x)
      (nhdsWithin 0 (Ioi 0)) (𝓝 0) := by
    have h := hcont.sub (tendsto_const_nhds : Tendsto (fun _ : ℝ => x)
      (nhdsWithin 0 (Ioi 0)) (𝓝 x))
    simpa using h
  have hnorm : Tendsto (fun θ : ℝ => ‖HeatCylinder.heatL2CLM hc θ x - x‖)
      (nhdsWithin 0 (Ioi 0)) (𝓝 0) := by
    change Tendsto ((fun y : Lp Plane 2 (B0284.cellMeasure c) => ‖y‖) ∘
      (fun θ : ℝ => HeatCylinder.heatL2CLM hc θ x - x))
      (nhdsWithin 0 (Ioi 0)) (𝓝 0)
    simpa only [norm_zero] using
      (continuous_norm.continuousAt.tendsto.comp hdiff)
  have hEq : ∀ θ : ℝ,
      (eLpNorm (actualAxialHeatIncrement (θ := θ) hc f) 2 (Cyl.cellμ c)).toReal =
        Real.sqrt c * ‖HeatCylinder.heatL2CLM hc θ x - x‖ := by
    intro θ
    have hm' := actualAxialHeatIncrement_measurable (θ := θ) hc f
    have hp' := actualAxialHeatIncrement_periodic (θ := θ) hc f
    rw [eLpNorm_toReal_cyl_eq_sqrt_cell hc _ hm' hp']
    rw [eLpNorm_congr_ae (actualAxialHeatIncrement_eq_heatCLM_ae hc hm (θ := θ) f)]
    rw [eLpNorm_congr_ae (Lp.coeFn_sub
      (HeatCylinder.heatL2CLM hc θ x) x).symm]
    rw [← Lp.norm_def]
  have hmul := (tendsto_const_nhds : Tendsto (fun _ : ℝ => Real.sqrt c)
      (nhdsWithin 0 (Ioi 0)) (𝓝 (Real.sqrt c))).mul hnorm
  simpa using hmul.congr' (Filter.Eventually.of_forall fun θ => (hEq θ).symm)

/-- The actual axial commutator tends to zero in centered-cell L², by the vanishing Gaussian
weight-difference mass and the fixed normalized-cell norm of the chosen physical input. -/
theorem tendsto_actualAxialHeatCommutator_centered_norm {c m : ℝ} (hc : 0 < c)
    (hm : 1 ≤ m) (f : X c m) :
    Tendsto (fun θ : ℝ =>
      (eLpNorm (actualAxialHeatCommutator (θ := θ) hc f) 2 (Cyl.cellμ c)).toReal)
      (nhdsWithin 0 (Ioi 0)) (𝓝 0) := by
  let x := axialWeightedHeatInput hc hm f
  let g : Plane → Plane := fun z => axialWeight m z • xColumnHeatLift hc f z
  have hinputAe := coeFn_axialWeightedHeatInput hc hm f
  have hinputMem : MemLp g 2 (B0284.cellMeasure c) := by
    exact (memLp_congr_ae hinputAe).mp (Lp.memLp x)
  let E : ℝ := (eLpNorm g 2 (B0284.cellMeasure c)).toReal
  have hmass := tendsto_axialHeatCommutatorKernel_lintegral_zero (by linarith : 0 ≤ m)
  have hmassReal : Tendsto (fun θ : ℝ =>
      (∫⁻ w : Plane, axialHeatCommutatorKernel θ m w).toReal)
      (nhdsWithin 0 (Ioi 0)) (𝓝 0) := by
    exact (ENNReal.continuousAt_toReal ENNReal.zero_ne_top).tendsto.comp hmass
  have hprod := hmassReal.mul
    (tendsto_const_nhds : Tendsto (fun _ : ℝ => E) (nhdsWithin 0 (Ioi 0)) (𝓝 E))
  have hcommReal : Tendsto (fun θ : ℝ =>
      (eLpNorm (actualAxialHeatCommutator (θ := θ) hc f) 2
        (B0284.cellMeasure c)).toReal)
      (nhdsWithin 0 (Ioi 0)) (𝓝 0) := by
    have hlow : ∀ᶠ θ in nhdsWithin 0 (Ioi 0),
        0 * E ≤ (eLpNorm (actualAxialHeatCommutator (θ := θ) hc f) 2
          (B0284.cellMeasure c)).toReal := by
      filter_upwards [] with θ
      simpa using ENNReal.toReal_nonneg
    have hupp : ∀ᶠ θ in nhdsWithin 0 (Ioi 0),
        (eLpNorm (actualAxialHeatCommutator (θ := θ) hc f) 2
          (B0284.cellMeasure c)).toReal ≤
            (∫⁻ w : Plane, axialHeatCommutatorKernel θ m w).toReal * E := by
      filter_upwards [self_mem_nhdsWithin] with θ hθ
      have hbound := eLpNorm_actualAxialHeatCommutator_le_kernel hc hm hθ f
      have hmassTop := axialHeatCommutatorKernel_lintegral_lt_top hθ (by linarith : 0 ≤ m)
      have hmassNeTop : (∫⁻ w : Plane, axialHeatCommutatorKernel θ m w) ≠ ⊤ :=
        lt_top_iff_ne_top.mp hmassTop
      have hinputTop := hinputMem.eLpNorm_ne_top
      have hprodTop := ENNReal.mul_ne_top hmassNeTop hinputTop
      calc
        (eLpNorm (actualAxialHeatCommutator (θ := θ) hc f) 2
            (B0284.cellMeasure c)).toReal ≤
            ((∫⁻ w : Plane, axialHeatCommutatorKernel θ m w) *
              eLpNorm g 2 (B0284.cellMeasure c)).toReal :=
                ENNReal.toReal_mono hprodTop hbound
        _ = (∫⁻ w : Plane, axialHeatCommutatorKernel θ m w).toReal * E := by
              rw [ENNReal.toReal_mul]
    have hsqueeze := tendsto_of_tendsto_of_tendsto_of_le_of_le'
      tendsto_const_nhds hprod hlow hupp
    simpa using hsqueeze
  have hEq : ∀ θ : ℝ,
      (eLpNorm (actualAxialHeatCommutator (θ := θ) hc f) 2
        (Cyl.cellμ c)).toReal = Real.sqrt c *
          (eLpNorm (actualAxialHeatCommutator (θ := θ) hc f) 2
            (B0284.cellMeasure c)).toReal := by
    intro θ
    rw [eLpNorm_toReal_cyl_eq_sqrt_cell hc _
      (actualAxialHeatCommutator_measurable (θ := θ) hc f)
      (actualAxialHeatCommutator_periodic (θ := θ) hc f)]
  have hscaled := (tendsto_const_nhds : Tendsto (fun _ : ℝ => Real.sqrt c)
      (nhdsWithin 0 (Ioi 0)) (𝓝 (Real.sqrt c))).mul hcommReal
  simpa using hscaled.congr' (Filter.Eventually.of_forall fun θ => (hEq θ).symm)

private theorem memLp_actualAxialHeatCommutator_centered {c m θ : ℝ} (hc : 0 < c)
    (hm : 1 ≤ m) (hθ : 0 < θ) (f : X c m) :
    MemLp (actualAxialHeatCommutator (θ := θ) hc f) 2 (Cyl.cellμ c) := by
  let x := axialWeightedHeatInput hc hm f
  let g : Plane → Plane := fun z => axialWeight m z • xColumnHeatLift hc f z
  have hinputAe := coeFn_axialWeightedHeatInput hc hm f
  have hinputMem : MemLp g 2 (B0284.cellMeasure c) :=
    (memLp_congr_ae hinputAe).mp (Lp.memLp x)
  have hbound := eLpNorm_actualAxialHeatCommutator_le_kernel hc hm hθ f
  have hmassTop := axialHeatCommutatorKernel_lintegral_lt_top hθ (by linarith : 0 ≤ m)
  have hmulTop := ENNReal.mul_lt_top hmassTop hinputMem.eLpNorm_ne_top.lt_top
  have hmem : MemLp (actualAxialHeatCommutator (θ := θ) hc f) 2
      (B0284.cellMeasure c) := by
    refine ⟨(actualAxialHeatCommutator_measurable (θ := θ) hc f).aestronglyMeasurable, ?_⟩
    exact lt_of_le_of_lt hbound hmulTop
  exact HeatCylinder.memLp_cyl_of_memLp_cellMeasure hc
    (actualAxialHeatCommutator_measurable (θ := θ) hc f)
    (actualAxialHeatCommutator_periodic (θ := θ) hc f) hmem

private theorem memLp_actualAxialHeatIncrement_centered {c m θ : ℝ} (hc : 0 < c)
    (hm : 1 ≤ m) (f : X c m) :
    MemLp (actualAxialHeatIncrement (θ := θ) hc f) 2 (Cyl.cellμ c) := by
  let x := axialWeightedHeatInput hc hm f
  have hval := actualAxialHeatIncrement_eq_heatCLM_ae hc hm (θ := θ) f
  have hmemDiff : MemLp (fun z =>
      (HeatCylinder.heatL2CLM hc θ x : Plane → Plane) z - (x : Plane → Plane) z)
      2 (B0284.cellMeasure c) := by
    exact (memLp_congr_ae (Lp.coeFn_sub (HeatCylinder.heatL2CLM hc θ x) x)).mp
      (Lp.memLp (HeatCylinder.heatL2CLM hc θ x - x))
  have hmemNorm : MemLp (actualAxialHeatIncrement (θ := θ) hc f) 2
      (B0284.cellMeasure c) := (memLp_congr_ae hval).mpr hmemDiff
  exact HeatCylinder.memLp_cyl_of_memLp_cellMeasure hc
    (actualAxialHeatIncrement_measurable (θ := θ) hc f)
    (actualAxialHeatIncrement_periodic (θ := θ) hc f) hmemNorm

/-- Quantitative fixed-cylinder bound for the actual weighted `X_m` heat increment, split into
the two centered-cell terms whose age-zero limits are proved above. -/
theorem norm_xColumnHeatS0Positive_sub_le_centered_terms {c m θ : ℝ} (hc : 0 < c)
    (hc1 : 1 ≤ c) (hm : 1 ≤ m) (hθ : 0 < θ) (hθ1 : θ ≤ 1) (f : X c m) :
    ‖xColumnHeatS0Positive hc hm hθ hθ1 f - f‖ ≤
      (1 + c ^ 2 / 4) ^ (m / 2) *
        ((eLpNorm (actualAxialHeatCommutator (θ := θ) hc f) 2
            (Cyl.cellμ c)).toReal +
          (eLpNorm (actualAxialHeatIncrement (θ := θ) hc f) 2
            (Cyl.cellμ c)).toReal) := by
  have hcomm := memLp_actualAxialHeatCommutator_centered (θ := θ) hc hm hθ f
  have hinc := memLp_actualAxialHeatIncrement_centered (θ := θ) hc hm f
  have hCc : 0 ≤ (1 + c ^ 2 / 4) ^ (m / 2) := by positivity
  have hRhsTop : (ENNReal.ofReal ((1 + c ^ 2 / 4) ^ (m / 2)) *
      (eLpNorm (actualAxialHeatCommutator (θ := θ) hc f) 2 (Cyl.cellμ c) +
        eLpNorm (actualAxialHeatIncrement (θ := θ) hc f) 2 (Cyl.cellμ c))) ≠ ⊤ := by
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (ENNReal.add_ne_top.mpr ⟨hcomm.eLpNorm_ne_top, hinc.eLpNorm_ne_top⟩)
  have hE := eLpNorm_radialHeatIncrement_le_actual_fields hc hm hθ f
  have hReal := ENNReal.toReal_mono hRhsTop hE
  rw [ENNReal.toReal_mul,
    ENNReal.toReal_add hcomm.eLpNorm_ne_top hinc.eLpNorm_ne_top,
    ENNReal.toReal_ofReal hCc] at hReal
  calc
    ‖xColumnHeatS0Positive hc hm hθ hθ1 f - f‖ =
        (eLpNorm (fun z => bracket z ^ m *
          (B0284.heat θ (xColumnHeatLift hc f) z).1 -
            bracket z ^ m * (xColumnHeatLift hc f z).1) 2 (Cyl.cellμ c)).toReal :=
          norm_xColumnHeatS0Positive_sub_eq_radialIncrement hc hm hθ hθ1 f
    _ ≤ (1 + c ^ 2 / 4) ^ (m / 2) *
        ((eLpNorm (actualAxialHeatCommutator (θ := θ) hc f) 2
            (Cyl.cellμ c)).toReal +
          (eLpNorm (actualAxialHeatIncrement (θ := θ) hc f) 2
            (Cyl.cellμ c)).toReal) := hReal

end UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution

#print axioms UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution.eLpNorm_radialHeatIncrement_le_actual_fields
#print axioms UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution.eLpNorm_actualAxialHeatCommutator_le_kernel
#print axioms UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution.actualAxialHeatIncrement_eq_heatCLM_ae
#print axioms UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution.tendsto_actualAxialHeatIncrement_centered_norm
#print axioms UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution.tendsto_actualAxialHeatCommutator_centered_norm
#print axioms UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution.memLp_actualAxialHeatCommutator_centered
#print axioms UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution.memLp_actualAxialHeatIncrement_centered
#print axioms UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution.norm_xColumnHeatS0Positive_sub_le_centered_terms
