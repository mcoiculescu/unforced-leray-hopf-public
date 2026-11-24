import UnforcedLeray.Lib.HeatCylinder.H3ActualLimit

/-!
# Periodic normalized representatives of train H³ values

This leaf lets the normalized-cell heat quotient and the centered-cell Sobolev value meet in one
actual L² representative, with periodic extension done from the centered quotient.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

open MeasureTheory Filter
open scoped ENNReal Topology

namespace UnforcedLeray.HeatCylinder

open UnforcedLeray.GaussianVortex (Plane)
open UnforcedLeray.Train (Vec)

private theorem h3VecMeasure_eq_cell (c : ℝ) :
    UnforcedLeray.Sob.wμ (UnforcedLeray.Sob.cylinder c).μ
      (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) = UnforcedLeray.Cyl.cellμ c := by
  rw [UnforcedLeray.Cyl.wμ_ρwW]
  simp [UnforcedLeray.Cyl.wμ]

/-- A measurable representative of the centered-cell Sobolev value. -/
private noncomputable def vectorH3ValueRep {c : ℝ}
    (x : UnforcedLeray.TrainB.VectorH3 c) : Plane → Vec :=
  AEStronglyMeasurable.mk
    (UnforcedLeray.Sob.W.value (UnforcedLeray.Sob.cylinder c)
      (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) ℝ Vec 3 2 x)
    (Lp.aestronglyMeasurable _)

private theorem vectorH3ValueRep_measurable {c : ℝ}
    (x : UnforcedLeray.TrainB.VectorH3 c) : Measurable (vectorH3ValueRep x) :=
  (Lp.aestronglyMeasurable _).measurable_mk

private theorem vectorH3ValueRep_ae_cell {c : ℝ}
    (x : UnforcedLeray.TrainB.VectorH3 c) :
    vectorH3ValueRep x =ᵐ[UnforcedLeray.Cyl.cellμ c]
      (UnforcedLeray.Sob.W.value (UnforcedLeray.Sob.cylinder c)
        (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) ℝ Vec 3 2 x : Plane → Vec) := by
  let v := UnforcedLeray.Sob.W.value (UnforcedLeray.Sob.cylinder c)
    (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) ℝ Vec 3 2 x
  have hv : AEStronglyMeasurable (v : Plane → Vec)
      (UnforcedLeray.Sob.wμ (UnforcedLeray.Sob.cylinder c).μ
        (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ))) := Lp.aestronglyMeasurable v
  have heq := hv.ae_eq_mk
  simpa only [vectorH3ValueRep, v, h3VecMeasure_eq_cell c] using heq.symm

/-- The selected measurable Sobolev value, extended periodically from the centered cell. -/
noncomputable def vectorH3PeriodicValueRep {c : ℝ} (hc : 0 < c)
    (x : UnforcedLeray.TrainB.VectorH3 c) : Plane → Vec :=
  UnforcedLeray.HeatCylinder.centeredPerLift hc (vectorH3ValueRep x)

theorem measurable_vectorH3PeriodicValueRep {c : ℝ} (hc : 0 < c)
    (x : UnforcedLeray.TrainB.VectorH3 c) : Measurable (vectorH3PeriodicValueRep hc x) :=
  UnforcedLeray.HeatCylinder.measurable_centeredPerLift hc
    (vectorH3ValueRep_measurable x)

theorem periodic_vectorH3PeriodicValueRep {c : ℝ} (hc : 0 < c)
    (x : UnforcedLeray.TrainB.VectorH3 c) :
    UnforcedLeray.B0284.IsQPeriodic c (vectorH3PeriodicValueRep hc x) := by
  intro z
  exact UnforcedLeray.HeatCylinder.centeredPerLift_periodic hc _ z

theorem vectorH3PeriodicValueRep_ae_value {c : ℝ} (hc : 0 < c)
    (x : UnforcedLeray.TrainB.VectorH3 c) :
    vectorH3PeriodicValueRep hc x =ᵐ[UnforcedLeray.Cyl.cellμ c]
      (UnforcedLeray.Sob.W.value (UnforcedLeray.Sob.cylinder c)
        (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) ℝ Vec 3 2 x : Plane → Vec) := by
  filter_upwards [ae_restrict_mem (UnforcedLeray.Cyl.measurableSet_cell c),
    vectorH3ValueRep_ae_cell x] with z hz hrep
  change centeredPerLift hc (vectorH3ValueRep x) z = _
  rw [UnforcedLeray.HeatCylinder.centeredPerLift_eq_on_cell hc _ hz]
  exact hrep

theorem memLp_vectorH3PeriodicValueRep {c : ℝ} (hc : 0 < c)
    (x : UnforcedLeray.TrainB.VectorH3 c) :
    MemLp (vectorH3PeriodicValueRep hc x) 2 (UnforcedLeray.B0284.cellMeasure c) := by
  have hmemValue : MemLp
      (UnforcedLeray.Sob.W.value (UnforcedLeray.Sob.cylinder c)
        (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) ℝ Vec 3 2 x : Plane → Vec)
      2 (UnforcedLeray.Cyl.cellμ c) := by
    simpa only [h3VecMeasure_eq_cell c] using
      (Lp.memLp (UnforcedLeray.Sob.W.value (UnforcedLeray.Sob.cylinder c)
        (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) ℝ Vec 3 2 x))
  have hmem := (memLp_congr_ae (vectorH3PeriodicValueRep_ae_value hc x)).mpr hmemValue
  exact UnforcedLeray.HeatCylinder.memLp_cellMeasure_of_memLp_cyl hc
    (measurable_vectorH3PeriodicValueRep hc x)
    (periodic_vectorH3PeriodicValueRep hc x) hmem

/-- Periodic representative and corresponding normalized-cell L² class of a vector H³ value. -/
noncomputable def vectorH3NormalizedValue {c : ℝ} (hc : 0 < c)
    (x : UnforcedLeray.TrainB.VectorH3 c) :
    Lp Vec 2 (UnforcedLeray.B0284.cellMeasure c) :=
  (memLp_vectorH3PeriodicValueRep hc x).toLp (vectorH3PeriodicValueRep hc x)

theorem vectorH3NormalizedValue_coe_ae {c : ℝ} (hc : 0 < c)
    (x : UnforcedLeray.TrainB.VectorH3 c) :
    (vectorH3NormalizedValue hc x : Plane → Vec) =ᵐ[
      UnforcedLeray.B0284.cellMeasure c] vectorH3PeriodicValueRep hc x :=
  (memLp_vectorH3PeriodicValueRep hc x).coeFn_toLp

/-- Periodic extension from the centered value quotient respects addition. -/
theorem vectorH3NormalizedValue_add {c : ℝ} (hc : 0 < c)
    (x y : UnforcedLeray.TrainB.VectorH3 c) :
    vectorH3NormalizedValue hc (x + y) =
      vectorH3NormalizedValue hc x + vectorH3NormalizedValue hc y := by
  let V := UnforcedLeray.Sob.W.value (UnforcedLeray.Sob.cylinder c)
    (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) ℝ Vec 3 2
  have hval : (V (x + y) : Plane → Vec) =ᵐ[UnforcedLeray.Cyl.cellμ c]
      (V x : Plane → Vec) + (V y : Plane → Vec) := by
    have hcoeff := Lp.coeFn_add (V x) (V y)
    have hcoeff' : (↑(V x + V y) : Plane → Vec) =ᵐ[
        UnforcedLeray.Cyl.cellμ c] (V x : Plane → Vec) + (V y : Plane → Vec) := by
      simpa only [h3VecMeasure_eq_cell c] using hcoeff
    rw [map_add V x y]
    exact hcoeff'
  have hcenter : vectorH3PeriodicValueRep hc (x + y) =ᵐ[
      UnforcedLeray.Cyl.cellμ c]
      (fun z => vectorH3PeriodicValueRep hc x z + vectorH3PeriodicValueRep hc y z) := by
    filter_upwards [vectorH3PeriodicValueRep_ae_value hc (x + y), hval,
      vectorH3PeriodicValueRep_ae_value hc x, vectorH3PeriodicValueRep_ae_value hc y]
      with z hsum hV hX hY
    change vectorH3PeriodicValueRep hc (x + y) z = _
    calc
      vectorH3PeriodicValueRep hc (x + y) z = V (x + y) z := hsum
      _ = V x z + V y z := hV
      _ = vectorH3PeriodicValueRep hc x z + vectorH3PeriodicValueRep hc y z := by
        exact congrArg₂ (· + ·) hX.symm hY.symm
  have hsumper : UnforcedLeray.B0284.IsQPeriodic c
      (fun z => vectorH3PeriodicValueRep hc x z + vectorH3PeriodicValueRep hc y z) := by
    intro z
    change vectorH3PeriodicValueRep hc x (z.1 + c, z.2) +
      vectorH3PeriodicValueRep hc y (z.1 + c, z.2) = _
    rw [periodic_vectorH3PeriodicValueRep hc x z,
      periodic_vectorH3PeriodicValueRep hc y z]
  have hglobal := ae_eq_of_ae_centered_periodic hc
    (periodic_vectorH3PeriodicValueRep hc (x + y))
    hsumper hcenter
  apply Lp.ext
  filter_upwards [vectorH3NormalizedValue_coe_ae hc (x + y),
    Lp.coeFn_add (vectorH3NormalizedValue hc x) (vectorH3NormalizedValue hc y),
    vectorH3NormalizedValue_coe_ae hc x, vectorH3NormalizedValue_coe_ae hc y,
    hglobal] with z hleft hright hx hy hrep
  calc
    (vectorH3NormalizedValue hc (x + y) : Plane → Vec) z =
        vectorH3PeriodicValueRep hc (x + y) z := hleft
    _ = vectorH3PeriodicValueRep hc x z + vectorH3PeriodicValueRep hc y z := hrep
    _ = (vectorH3NormalizedValue hc x : Plane → Vec) z +
        (vectorH3NormalizedValue hc y : Plane → Vec) z :=
      congrArg₂ (· + ·) hx.symm hy.symm
    _ = (vectorH3NormalizedValue hc x + vectorH3NormalizedValue hc y) z := hright.symm

/-- Periodic extension from the centered value quotient respects real scalars. -/
theorem vectorH3NormalizedValue_smul {c : ℝ} (hc : 0 < c)
    (r : ℝ) (x : UnforcedLeray.TrainB.VectorH3 c) :
    vectorH3NormalizedValue hc (r • x) = r • vectorH3NormalizedValue hc x := by
  let V := UnforcedLeray.Sob.W.value (UnforcedLeray.Sob.cylinder c)
    (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) ℝ Vec 3 2
  have hval : (V (r • x) : Plane → Vec) =ᵐ[UnforcedLeray.Cyl.cellμ c]
      r • (V x : Plane → Vec) := by
    have hcoeff := Lp.coeFn_smul r (V x)
    have hcoeff' : (↑(r • V x) : Plane → Vec) =ᵐ[
        UnforcedLeray.Cyl.cellμ c] r • (V x : Plane → Vec) := by
      simpa only [h3VecMeasure_eq_cell c] using hcoeff
    rw [map_smul V r x]
    exact hcoeff'
  have hcenter : vectorH3PeriodicValueRep hc (r • x) =ᵐ[
      UnforcedLeray.Cyl.cellμ c]
      (fun z => r • vectorH3PeriodicValueRep hc x z) := by
    filter_upwards [vectorH3PeriodicValueRep_ae_value hc (r • x), hval,
      vectorH3PeriodicValueRep_ae_value hc x] with z hsum hV hX
    change vectorH3PeriodicValueRep hc (r • x) z = _
    calc
      vectorH3PeriodicValueRep hc (r • x) z = V (r • x) z := hsum
      _ = r • V x z := by simpa only [Pi.smul_apply] using hV
      _ = r • vectorH3PeriodicValueRep hc x z :=
        congrArg (fun w : Vec => r • w) hX.symm
  have hsmulper : UnforcedLeray.B0284.IsQPeriodic c
      (fun z => r • vectorH3PeriodicValueRep hc x z) := by
    intro z
    change r • vectorH3PeriodicValueRep hc x (z.1 + c, z.2) = _
    rw [periodic_vectorH3PeriodicValueRep hc x z]
  have hglobal := ae_eq_of_ae_centered_periodic hc
    (periodic_vectorH3PeriodicValueRep hc (r • x))
    hsmulper hcenter
  apply Lp.ext
  filter_upwards [vectorH3NormalizedValue_coe_ae hc (r • x),
    Lp.coeFn_smul r (vectorH3NormalizedValue hc x),
    vectorH3NormalizedValue_coe_ae hc x, hglobal] with z hleft hright hx hrep
  calc
    (vectorH3NormalizedValue hc (r • x) : Plane → Vec) z =
        vectorH3PeriodicValueRep hc (r • x) z := hleft
    _ = r • vectorH3PeriodicValueRep hc x z := hrep
    _ = (r • (vectorH3NormalizedValue hc x : Plane → Vec)) z :=
      congrArg (fun w : Vec => r • w) hx.symm
    _ = (r • vectorH3NormalizedValue hc x) z := hright.symm

/- Exact centered/normalized squared-norm conversion for the periodic value representative. -/
theorem norm_sq_vectorH3NormalizedValue_eq {c : ℝ} (hc : 0 < c)
    (x : UnforcedLeray.TrainB.VectorH3 c) :
    ‖vectorH3NormalizedValue hc x‖ ^ 2 = c⁻¹ *
      ‖UnforcedLeray.Sob.W.value (UnforcedLeray.Sob.cylinder c)
        (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) ℝ Vec 3 2 x‖ ^ 2 := by
  let f := vectorH3PeriodicValueRep hc x
  have hnormN : (eLpNorm f 2 (UnforcedLeray.B0284.cellMeasure c)).toReal =
      ‖vectorH3NormalizedValue hc x‖ := by
    calc
      _ = (eLpNorm (vectorH3NormalizedValue hc x : Plane → Vec) 2
          (UnforcedLeray.B0284.cellMeasure c)).toReal := by
            congr 1
            exact eLpNorm_congr_ae
              (vectorH3NormalizedValue_coe_ae hc x).symm
      _ = ‖vectorH3NormalizedValue hc x‖ := (Lp.norm_def _).symm
  have hnormC : (eLpNorm f 2 (UnforcedLeray.Cyl.cellμ c)).toReal =
      ‖UnforcedLeray.Sob.W.value (UnforcedLeray.Sob.cylinder c)
        (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) ℝ Vec 3 2 x‖ := by
    rw [Lp.norm_def]
    change (eLpNorm (vectorH3PeriodicValueRep hc x) 2
      (UnforcedLeray.Cyl.cellμ c)).toReal = _
    rw [eLpNorm_congr_ae (vectorH3PeriodicValueRep_ae_value hc x)]
    rw [← h3VecMeasure_eq_cell c]
  have hsq := UnforcedLeray.HeatCylinder.eLpNorm_sq_cellMeasure_eq_cyl hc
    (measurable_vectorH3PeriodicValueRep hc x)
    (periodic_vectorH3PeriodicValueRep hc x)
  have hreal := congrArg ENNReal.toReal hsq
  have hreal' : (eLpNorm f 2 (UnforcedLeray.B0284.cellMeasure c)).toReal ^ 2 =
      c⁻¹ * (eLpNorm f 2 (UnforcedLeray.Cyl.cellμ c)).toReal ^ 2 := by
    rw [ENNReal.toReal_pow, ENNReal.toReal_mul, ENNReal.toReal_inv,
      ENNReal.toReal_pow, ENNReal.toReal_ofReal (le_of_lt hc)] at hreal
    exact hreal
  rw [hnormN, hnormC] at hreal'
  exact hreal'

/-- The value lift has the expected `c^{-1/2}` operator bound. -/
theorem norm_vectorH3NormalizedValue_le {c : ℝ} (hc : 0 < c)
    (x : UnforcedLeray.TrainB.VectorH3 c) :
    ‖vectorH3NormalizedValue hc x‖ ≤ Real.sqrt (c⁻¹) * ‖x‖ := by
  have hvalue := UnforcedLeray.Sob.norm_value_le x
  have hsq : ‖vectorH3NormalizedValue hc x‖ ^ 2 ≤
      (Real.sqrt (c⁻¹) * ‖x‖) ^ 2 := by
    rw [norm_sq_vectorH3NormalizedValue_eq hc x]
    have hcInv : 0 ≤ c⁻¹ := inv_nonneg.mpr (le_of_lt hc)
    have hvalueSq :
        ‖UnforcedLeray.Sob.W.value (UnforcedLeray.Sob.cylinder c)
          (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) ℝ Vec 3 2 x‖ ^ 2 ≤ ‖x‖ ^ 2 :=
      (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr hvalue
    calc
      c⁻¹ * ‖UnforcedLeray.Sob.W.value (UnforcedLeray.Sob.cylinder c)
          (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) ℝ Vec 3 2 x‖ ^ 2 ≤
        c⁻¹ * ‖x‖ ^ 2 := mul_le_mul_of_nonneg_left hvalueSq hcInv
      _ = (Real.sqrt (c⁻¹) * ‖x‖) ^ 2 := by
        rw [mul_pow, Real.sq_sqrt hcInv]
  exact (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp hsq

noncomputable def vectorH3NormalizedValueLinear {c : ℝ} (hc : 0 < c) :
    UnforcedLeray.TrainB.VectorH3 c →ₗ[ℝ] Lp Vec 2
      (UnforcedLeray.B0284.cellMeasure c) where
  toFun := vectorH3NormalizedValue hc
  map_add' := vectorH3NormalizedValue_add hc
  map_smul' := vectorH3NormalizedValue_smul hc

/-- Continuous normalized-cell realization of the centered Sobolev value, with its exact period
factor. -/
noncomputable def vectorH3NormalizedValueCLM {c : ℝ} (hc : 0 < c) :
    UnforcedLeray.TrainB.VectorH3 c →L[ℝ] Lp Vec 2
      (UnforcedLeray.B0284.cellMeasure c) :=
  (vectorH3NormalizedValueLinear hc).mkContinuous (Real.sqrt (c⁻¹)) fun x =>
    norm_vectorH3NormalizedValue_le hc x

theorem tendsto_vectorH3NormalizedValue_of_tendsto {c : ℝ} (hc : 0 < c)
    {y : ℕ → UnforcedLeray.TrainB.VectorH3 c} {x : UnforcedLeray.TrainB.VectorH3 c}
    (hy : Tendsto y atTop (𝓝 x)) :
    Tendsto (fun n => vectorH3NormalizedValue hc (y n)) atTop
      (𝓝 (vectorH3NormalizedValue hc x)) := by
  exact (vectorH3NormalizedValueCLM hc).continuous.tendsto x |>.comp hy

/-- For a smooth periodic tensor, the normalized periodic representative of the actual H³ heat
output is the actual vector-valued Gaussian quotient operator. -/
theorem vectorH3NormalizedValue_heatDivH3 {c θ : ℝ} (hc : 0 < c) (hθ : 0 < θ)
    {S : Plane → Plane × Plane} (hS : UnforcedLeray.Sob.IsCylSmooth c S) :
    vectorH3NormalizedValue hc (heatDivH3 hc hθ hS) =
      heatDivVecL2CLM hc hθ
        ((memLp_tensor_iterD_cylSmooth_normalized hc hS []).toLp S) := by
  let y := heatDivH3 hc hθ hS
  have hmem : MemLp S 2 (UnforcedLeray.B0284.cellMeasure c) := by
    simpa only [UnforcedLeray.Sob.iterD_nil] using
      memLp_tensor_iterD_cylSmooth_normalized hc hS []
  have hper : UnforcedLeray.B0284.IsQPeriodic c S := by
    intro z
    have hcoord : (z.1 + c, z.2) = z + (c, 0) := by ext <;> simp
    rw [hcoord]
    exact hS.periodic z
  have hperOut : UnforcedLeray.B0284.IsQPeriodic c
      (fun z => UnforcedLeray.Train.toVec (UnforcedLeray.B0296.heatDiv θ S z)) := by
    intro z
    exact congrArg UnforcedLeray.Train.toVec
      (UnforcedLeray.B0296.heatDiv_periodic hper z)
  have hval := heatDivH3_value_ae hc hθ hS
  have hvalCell :
      (UnforcedLeray.Sob.W.value (UnforcedLeray.Sob.cylinder c)
        (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) ℝ Vec 3 2 y : Plane → Vec) =ᵐ[
        UnforcedLeray.Cyl.cellμ c]
      (fun z => UnforcedLeray.Train.toVec (UnforcedLeray.B0296.heatDiv θ S z)) := by
    simpa only [h3VecMeasure_eq_cell c, y] using hval
  have hcenter : vectorH3PeriodicValueRep hc y =ᵐ[UnforcedLeray.Cyl.cellμ c]
      (fun z => UnforcedLeray.Train.toVec (UnforcedLeray.B0296.heatDiv θ S z)) := by
    filter_upwards [vectorH3PeriodicValueRep_ae_value hc y, hvalCell] with z hrep hvalz
    exact hrep.trans hvalz
  have hglobal := ae_eq_of_ae_centered_periodic hc
    (periodic_vectorH3PeriodicValueRep hc y) hperOut hcenter
  rw [heatDivVecL2CLM_apply_to_periodic hc hθ hper
    hS.smooth.continuous.measurable.aestronglyMeasurable hmem]
  apply Lp.ext
  filter_upwards [vectorH3NormalizedValue_coe_ae hc y,
    (periodicHeatDivVecMemLp hc hθ S hper
      hS.smooth.continuous.measurable.aestronglyMeasurable hmem).coeFn_toLp,
    hglobal] with z hleft hright hperEq
  exact hleft.trans (hperEq.trans hright.symm)

/-- Every TensorH3 input has an H³ heat-output limit whose centered value is exactly the actual
normalized-cell Gaussian quotient response. The limit is built from the retained smooth dense
approximants of that same input. -/
theorem exists_actual_heatDivH3_value {c θ : ℝ} (hc : 0 < c) (hθ : 0 < θ)
    (x : UnforcedLeray.TrainB.TensorH3 c) :
    ∃ Y : UnforcedLeray.TrainB.VectorH3 c,
      vectorH3NormalizedValue hc Y =
        heatDivVecL2CLM hc hθ (tensorH3KernelInput hc x) := by
  obtain ⟨y, T, hT, hS, hyrep, hyLim, hinLim, hCauchy⟩ :=
    exists_approximating_cauchy_heatDivH3_sequence hc hθ x
  let u : ℕ → UnforcedLeray.TrainB.VectorH3 c :=
    smoothHeatOutputSequence hc hθ hS
  have huCauchy : CauchySeq u := by
    simpa only [u] using hCauchy
  obtain ⟨Y, hY⟩ := cauchySeq_tendsto_of_complete huCauchy
  have hvalueLim := tendsto_vectorH3NormalizedValue_of_tendsto hc hY
  have hkernelLim := (heatDivVecL2CLM hc hθ).continuous.tendsto
    (tensorH3KernelInput hc x) |>.comp hinLim
  have hinputSmooth (n : ℕ) :
      tensorH3KernelInput hc (y n) =
        (memLp_tensor_iterD_cylSmooth_normalized hc (hS n) []).toLp
          (fun z => UnforcedLeray.TrainB.tensorToPlaneCLE (T n z)) := by
    let Sn : Plane → Plane × Plane :=
      fun z => UnforcedLeray.TrainB.tensorToPlaneCLE (T n z)
    have hmemSn : MemLp Sn 2 (UnforcedLeray.B0284.cellMeasure c) := by
      simpa only [UnforcedLeray.Sob.iterD_nil, Sn] using
        memLp_tensor_iterD_cylSmooth_normalized hc (hS n) []
    apply Lp.ext
    filter_upwards [tensorH3KernelInput_coe_ae_ofCylSmooth hc (hT n),
      hmemSn.coeFn_toLp] with z hclass hsn
    change (tensorH3KernelInput hc (y n) : Plane → Plane × Plane) z = _
    have hclass' : (tensorH3KernelInput hc (y n) : Plane → Plane × Plane) z = Sn z := by
      rw [← hyrep n] at hclass
      simpa [Sn] using hclass
    change ((memLp_tensor_iterD_cylSmooth_normalized hc (hS n) []).toLp Sn :
      Plane → Plane × Plane) z = _ at hsn
    exact hclass'.trans hsn.symm
  have hseqEq :
      (fun n => vectorH3NormalizedValue hc (u n)) =
        (fun n => heatDivVecL2CLM hc hθ (tensorH3KernelInput hc (y n))) := by
    funext n
    have hsmooth := vectorH3NormalizedValue_heatDivH3 hc hθ (hS n)
    calc
      vectorH3NormalizedValue hc (u n) =
          heatDivVecL2CLM hc hθ
            ((memLp_tensor_iterD_cylSmooth_normalized hc (hS n) []).toLp
              (fun z => UnforcedLeray.TrainB.tensorToPlaneCLE (T n z))) := by
        simpa [u, smoothHeatOutputSequence] using hsmooth
      _ = heatDivVecL2CLM hc hθ (tensorH3KernelInput hc (y n)) :=
        congrArg (heatDivVecL2CLM hc hθ) (hinputSmooth n).symm
  have hkernelOutput :
      Tendsto (fun n => vectorH3NormalizedValue hc (u n)) atTop
        (𝓝 (heatDivVecL2CLM hc hθ (tensorH3KernelInput hc x))) := by
    rw [hseqEq]
    exact hkernelLim
  exact ⟨Y, tendsto_nhds_unique hvalueLim hkernelOutput⟩

end UnforcedLeray.HeatCylinder

#print axioms UnforcedLeray.HeatCylinder.vectorH3NormalizedValue
#print axioms UnforcedLeray.HeatCylinder.vectorH3NormalizedValue_add
#print axioms UnforcedLeray.HeatCylinder.vectorH3NormalizedValue_smul
#print axioms UnforcedLeray.HeatCylinder.norm_sq_vectorH3NormalizedValue_eq
#print axioms UnforcedLeray.HeatCylinder.norm_vectorH3NormalizedValue_le
#print axioms UnforcedLeray.HeatCylinder.vectorH3NormalizedValueCLM
#print axioms UnforcedLeray.HeatCylinder.vectorH3NormalizedValue_heatDivH3
#print axioms UnforcedLeray.HeatCylinder.exists_actual_heatDivH3_value
