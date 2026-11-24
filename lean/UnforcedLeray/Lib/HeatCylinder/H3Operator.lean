import UnforcedLeray.Lib.HeatCylinder.H3ValueLimit

/-!
# Actual H³ heat-divergence operator

The smooth Gaussian heat-divergence response extends to the full tensor H³ graph by its actual
normalized L² realization and the proved H³ smoothing estimate.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

open MeasureTheory Filter
open scoped Topology

namespace UnforcedLeray.HeatCylinder

open UnforcedLeray.GaussianVortex (Plane)
open UnforcedLeray.Train (Vec)

private abbrev VectorValue {c : ℝ} :=
  UnforcedLeray.Sob.W.value (UnforcedLeray.Sob.cylinder c)
    (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) ℝ Vec 3 2

/-- The normalized-cell periodic value map separates the actual H³ graph classes. -/
theorem vectorH3NormalizedValue_injective {c : ℝ} (hc : 0 < c) :
    Function.Injective (vectorH3NormalizedValue hc) := by
  intro Y Z hYZ
  change (vectorH3NormalizedValueLinear hc) Y =
    (vectorH3NormalizedValueLinear hc) Z at hYZ
  have hzero : vectorH3NormalizedValue hc (Y - Z) = 0 := by
    change (vectorH3NormalizedValueLinear hc) (Y - Z) = 0
    rw [map_sub, sub_eq_zero.mpr hYZ]
  have hsq := norm_sq_vectorH3NormalizedValue_eq hc (Y - Z)
  rw [hzero, norm_zero] at hsq
  have hvalNorm : ‖VectorValue (c := c) (Y - Z)‖ = 0 := by
    have hcInv : 0 < c⁻¹ := inv_pos.mpr hc
    have hnn := norm_nonneg (VectorValue (c := c) (Y - Z))
    by_contra hne
    have hne' : ‖VectorValue (c := c) (Y - Z)‖ ≠ 0 := by simpa using hne
    have hpos : 0 < ‖VectorValue (c := c) (Y - Z)‖ :=
      lt_of_le_of_ne hnn (Ne.symm hne')
    have hmul := mul_pos hcInv (sq_pos_of_pos hpos)
    have hsq' : c⁻¹ * ‖VectorValue (c := c) (Y - Z)‖ ^ 2 = 0 := by
      nlinarith [hsq]
    exact (ne_of_gt hmul) hsq'
  have hvalZero : VectorValue (c := c) (Y - Z) = 0 := norm_eq_zero.mp hvalNorm
  have hmap := map_sub (VectorValue (c := c)) Y Z
  have hsub : VectorValue (c := c) Y - VectorValue (c := c) Z = 0 := by
    rw [← hmap]
    exact hvalZero
  have hvalEq : VectorValue (c := c) Y = VectorValue (c := c) Z := by
    exact sub_eq_zero.mp hsub
  exact UnforcedLeray.Sob.W.value_injective hvalEq

/-- The actual normalized L² Gaussian response of a rough TensorH3 input. -/
noncomputable def heatDivH3ActualL2CLM {c θ : ℝ} (hc : 0 < c) (hθ : 0 < θ) :
    UnforcedLeray.TrainB.TensorH3 c →L[ℝ]
      Lp Vec 2 (UnforcedLeray.B0284.cellMeasure c) :=
  (heatDivVecL2CLM hc hθ).comp (tensorH3KernelInputCLM hc)

/-- The H³ realization of the actual Gaussian response is unique. -/
theorem existsUnique_actual_heatDivH3_value {c θ : ℝ} (hc : 0 < c) (hθ : 0 < θ)
    (x : UnforcedLeray.TrainB.TensorH3 c) :
    ∃! Y : UnforcedLeray.TrainB.VectorH3 c,
      vectorH3NormalizedValue hc Y = heatDivH3ActualL2CLM hc hθ x := by
  obtain ⟨Y, hY⟩ := exists_actual_heatDivH3_value hc hθ x
  refine ⟨Y, ?_, ?_⟩
  · change vectorH3NormalizedValue hc Y =
      heatDivVecL2CLM hc hθ (tensorH3KernelInput hc x)
    exact hY
  · intro Z hZ
    apply vectorH3NormalizedValue_injective hc
    exact hZ.trans hY.symm

/-- Chosen actual H³ Gaussian response, characterized uniquely by its actual normalized L² value.
-/
noncomputable def actualHeatDivH3 {c θ : ℝ} (hc : 0 < c) (hθ : 0 < θ)
    (x : UnforcedLeray.TrainB.TensorH3 c) : UnforcedLeray.TrainB.VectorH3 c :=
  Classical.choose (exists_actual_heatDivH3_value hc hθ x)

theorem vectorH3NormalizedValue_actualHeatDivH3 {c θ : ℝ} (hc : 0 < c) (hθ : 0 < θ)
    (x : UnforcedLeray.TrainB.TensorH3 c) :
    vectorH3NormalizedValue hc (actualHeatDivH3 hc hθ x) =
      heatDivH3ActualL2CLM hc hθ x := by
  change vectorH3NormalizedValue hc (actualHeatDivH3 hc hθ x) =
    heatDivVecL2CLM hc hθ (tensorH3KernelInput hc x)
  exact Classical.choose_spec (exists_actual_heatDivH3_value hc hθ x)

/-- The actual H³ extension is additive because its normalized value is the actual linear L² map. -/
theorem actualHeatDivH3_add {c θ : ℝ} (hc : 0 < c) (hθ : 0 < θ)
    (x y : UnforcedLeray.TrainB.TensorH3 c) :
    actualHeatDivH3 hc hθ (x + y) =
      actualHeatDivH3 hc hθ x + actualHeatDivH3 hc hθ y := by
  apply vectorH3NormalizedValue_injective hc
  rw [vectorH3NormalizedValue_add hc,
    vectorH3NormalizedValue_actualHeatDivH3 hc hθ,
    vectorH3NormalizedValue_actualHeatDivH3 hc hθ,
    vectorH3NormalizedValue_actualHeatDivH3 hc hθ]
  change heatDivVecL2CLM hc hθ (tensorH3KernelInput hc (x + y)) =
    heatDivVecL2CLM hc hθ (tensorH3KernelInput hc x) +
      heatDivVecL2CLM hc hθ (tensorH3KernelInput hc y)
  rw [tensorH3KernelInput_add hc]
  exact map_add (heatDivVecL2CLM hc hθ) _ _

/-- The actual H³ extension respects real scalar multiplication. -/
theorem actualHeatDivH3_smul {c θ r : ℝ} (hc : 0 < c) (hθ : 0 < θ)
    (x : UnforcedLeray.TrainB.TensorH3 c) :
    actualHeatDivH3 hc hθ (r • x) = r • actualHeatDivH3 hc hθ x := by
  apply vectorH3NormalizedValue_injective hc
  rw [vectorH3NormalizedValue_smul hc,
    vectorH3NormalizedValue_actualHeatDivH3 hc hθ,
    vectorH3NormalizedValue_actualHeatDivH3 hc hθ]
  change heatDivVecL2CLM hc hθ (tensorH3KernelInput hc (r • x)) =
    r • heatDivVecL2CLM hc hθ (tensorH3KernelInput hc x)
  rw [tensorH3KernelInput_smul hc]
  exact map_smul (heatDivVecL2CLM hc hθ) r _

/-- Linear map underlying the actual rough H³ heat-divergence response. -/
noncomputable def actualHeatDivH3Linear {c θ : ℝ} (hc : 0 < c) (hθ : 0 < θ) :
    UnforcedLeray.TrainB.TensorH3 c →ₗ[ℝ] UnforcedLeray.TrainB.VectorH3 c where
  toFun := actualHeatDivH3 hc hθ
  map_add' := actualHeatDivH3_add hc hθ
  map_smul' := by
    intro r x
    exact actualHeatDivH3_smul hc hθ x

private theorem isCylSmooth_smul_zero {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {c r : ℝ} {T : Plane → F}
    (hT : UnforcedLeray.Sob.IsCylSmooth c T) :
    UnforcedLeray.Sob.IsCylSmooth c (fun z => r • T z) := by
  have hconst : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun _ : Plane => r) := contDiff_const
  refine ⟨hconst.smul hT.smooth, ?_, ?_⟩
  · intro z
    simp [hT.periodic z]
  · obtain ⟨R, hR⟩ := hT.bounded
    exact ⟨R, fun z hz => by rw [hR z hz, smul_zero]⟩

private theorem ofCylSmooth_tensor_zero {c : ℝ} (hc : 0 < c)
    (hzero : UnforcedLeray.Sob.IsCylSmooth c (fun _ : Plane =>
      (0 : UnforcedLeray.TrainB.TensorVal))) :
    UnforcedLeray.Sob.W.ofCylSmooth
      (ρ := UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) (𝕜 := ℝ)
      (F := UnforcedLeray.TrainB.TensorVal) (k := 3) (p := 2) hc
      (fun _ : Plane => 0) hzero = 0 := by
  apply UnforcedLeray.Sob.W.value_injective
  apply Lp.ext
  have hval := UnforcedLeray.Sob.W.value_ofCylSmooth
    (ρ := UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) (𝕜 := ℝ)
    (F := UnforcedLeray.TrainB.TensorVal) (k := 3) (p := 2) hc
    (fun _ : Plane => 0) hzero
  have hzeroVal := map_zero (UnforcedLeray.Sob.W.value
    (UnforcedLeray.Sob.cylinder c) (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ))
    ℝ UnforcedLeray.TrainB.TensorVal 3 2)
  rw [hzeroVal]
  filter_upwards [hval, Lp.coeFn_zero (E := UnforcedLeray.TrainB.TensorVal)
    (p := 2) (μ := UnforcedLeray.Sob.wμ (UnforcedLeray.Sob.cylinder c).μ
      (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)))] with z hz hz0
  exact hz.trans hz0.symm

theorem tendsto_smoothHeatOutputSequence_actualHeatDivH3 {c θ : ℝ}
    (hc : 0 < c) (hθ : 0 < θ) (x : UnforcedLeray.TrainB.TensorH3 c) :
    ∃ y : ℕ → UnforcedLeray.TrainB.TensorH3 c,
    ∃ T : ℕ → Plane → UnforcedLeray.TrainB.TensorVal,
    ∃ hT : ∀ n, UnforcedLeray.Sob.IsCylSmooth c (T n),
      (∀ n, y n = UnforcedLeray.Sob.W.ofCylSmooth
        (ρ := UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) (𝕜 := ℝ)
        (F := UnforcedLeray.TrainB.TensorVal) (k := 3) (p := 2) hc (T n) (hT n)) ∧
      Tendsto y atTop (𝓝 x) ∧
      ∃ S : ℕ → Plane → Plane × Plane,
      ∃ hS : ∀ n, UnforcedLeray.Sob.IsCylSmooth c (S n),
        (∀ n z, S n z = UnforcedLeray.TrainB.tensorToPlaneCLE (T n z)) ∧
        Tendsto (smoothHeatOutputSequence hc hθ hS) atTop
          (𝓝 (actualHeatDivH3 hc hθ x)) := by
  obtain ⟨y, Tval, hTensor, hSmooth, hyrep, hyLim, hinLim, hCauchy⟩ :=
    exists_approximating_cauchy_heatDivH3_sequence hc hθ x
  have hS : ∀ n, UnforcedLeray.Sob.IsCylSmooth c
      (fun z => UnforcedLeray.TrainB.tensorToPlaneCLE (Tval n z)) := hSmooth
  let u : ℕ → UnforcedLeray.TrainB.VectorH3 c := smoothHeatOutputSequence hc hθ hS
  have hu : CauchySeq u := by simpa only [u] using hCauchy
  obtain ⟨Y, hY⟩ := cauchySeq_tendsto_of_complete hu
  have hvalueLim := tendsto_vectorH3NormalizedValue_of_tendsto hc hY
  have hkernelLim := (heatDivVecL2CLM hc hθ).continuous.tendsto
    (tensorH3KernelInput hc x) |>.comp hinLim
  have hinputSmooth (n : ℕ) : tensorH3KernelInput hc (y n) =
      (memLp_tensor_iterD_cylSmooth_normalized hc (hS n) []).toLp
        (fun z => UnforcedLeray.TrainB.tensorToPlaneCLE (Tval n z)) := by
    let Sn : Plane → Plane × Plane :=
      fun z => UnforcedLeray.TrainB.tensorToPlaneCLE (Tval n z)
    have hmemSn : MemLp Sn 2 (UnforcedLeray.B0284.cellMeasure c) := by
      simpa only [UnforcedLeray.Sob.iterD_nil, Sn] using
        memLp_tensor_iterD_cylSmooth_normalized hc (hS n) []
    apply Lp.ext
    filter_upwards [tensorH3KernelInput_coe_ae_ofCylSmooth hc (hTensor n),
      hmemSn.coeFn_toLp] with z hclass hsn
    change (tensorH3KernelInput hc (y n) : Plane → Plane × Plane) z = _
    have hclass' : (tensorH3KernelInput hc (y n) : Plane → Plane × Plane) z = Sn z := by
      rw [← hyrep n] at hclass
      simpa [Sn] using hclass
    change ((memLp_tensor_iterD_cylSmooth_normalized hc (hS n) []).toLp Sn :
      Plane → Plane × Plane) z = _ at hsn
    exact hclass'.trans hsn.symm
  have hseqEq : (fun n => vectorH3NormalizedValue hc (u n)) =
      (fun n => heatDivVecL2CLM hc hθ (tensorH3KernelInput hc (y n))) := by
    funext n
    have hsmooth := vectorH3NormalizedValue_heatDivH3 hc hθ (hS n)
    calc
      vectorH3NormalizedValue hc (u n) =
          heatDivVecL2CLM hc hθ
            ((memLp_tensor_iterD_cylSmooth_normalized hc (hS n) []).toLp
              (fun z => UnforcedLeray.TrainB.tensorToPlaneCLE (Tval n z))) := by
        simpa [u, smoothHeatOutputSequence] using hsmooth
      _ = heatDivVecL2CLM hc hθ (tensorH3KernelInput hc (y n)) :=
        congrArg (heatDivVecL2CLM hc hθ) (hinputSmooth n).symm
  have hkernelOutput : Tendsto (fun n => vectorH3NormalizedValue hc (u n)) atTop
      (𝓝 (heatDivVecL2CLM hc hθ (tensorH3KernelInput hc x))) := by
    rw [hseqEq]
    exact hkernelLim
  have hYvalue := tendsto_nhds_unique hvalueLim hkernelOutput
  have hYeq : Y = actualHeatDivH3 hc hθ x :=
    vectorH3NormalizedValue_injective hc
      (hYvalue.trans (vectorH3NormalizedValue_actualHeatDivH3 hc hθ x).symm)
  have hresult : Tendsto u atTop (𝓝 (actualHeatDivH3 hc hθ x)) := by
    simpa only [hYeq] using hY
  exact ⟨y, Tval, hTensor, hyrep, hyLim,
    fun n z => UnforcedLeray.TrainB.tensorToPlaneCLE (Tval n z), hS,
    (by intro n z; rfl), hresult⟩

theorem norm_actualHeatDivH3_le {c θ : ℝ} (hc : 0 < c) (hθ : 0 < θ)
    (x : UnforcedLeray.TrainB.TensorH3 c) :
    ‖actualHeatDivH3 hc hθ x‖ ≤
      ((ENNReal.ofReal ‖(UnforcedLeray.Train.toVecL : Plane →L[ℝ] Vec)‖ *
        ENNReal.ofReal (heatDivL2Coeff θ)).toReal) * ‖x‖ := by
  obtain ⟨y, T, hT, hyrep, hyLim, S, hS, hSval, hOutLim⟩ :=
    tendsto_smoothHeatOutputSequence_actualHeatDivH3 hc hθ x
  let K : ℝ := (ENNReal.ofReal ‖(UnforcedLeray.Train.toVecL : Plane →L[ℝ] Vec)‖ *
    ENNReal.ofReal (heatDivL2Coeff θ)).toReal
  have hbound (n : ℕ) :
      ‖smoothHeatOutputSequence hc hθ hS n‖ ≤ K * ‖y n‖ := by
    let ZS : Plane → Plane × Plane := fun _ => 0
    let ZT : Plane → UnforcedLeray.TrainB.TensorVal := fun _ => 0
    have hzeroS : UnforcedLeray.Sob.IsCylSmooth c ZS := by
      simpa [ZS] using isCylSmooth_smul_zero (r := (0 : ℝ)) (hS n)
    have hzeroT : UnforcedLeray.Sob.IsCylSmooth c ZT := by
      simpa [ZT] using isCylSmooth_smul_zero (r := (0 : ℝ)) (hT n)
    have hzeroOut : heatDivH3 hc hθ hzeroS = 0 := by
      have hs := heatDivH3_smul hc hθ (r := (0 : ℝ)) (hS n)
      simpa [ZS, zero_smul] using hs
    have hsubS := UnforcedLeray.HeatCylinder.isCylSmooth_sub (hS n) hzeroS
    have hsmoothBound := norm_heatDivH3_sub_le_energy hc hθ (hS n) hzeroS hsubS
    have hsequence : smoothHeatOutputSequence hc hθ hS n =
        heatDivH3 (c := c) (θ := θ) (T := S n) hc hθ (hS n) := rfl
    have hplaneBound :
        ‖smoothHeatOutputSequence hc hθ hS n‖ ≤
          K * heatTensorH3Distance c (S n) ZS := by
      rw [hsequence]
      have hbound' : ‖heatDivH3 hc hθ (hS n)‖ ≤
          K * heatTensorH3Distance c (S n) ZS := by
        simpa only [hzeroOut, sub_zero, zero_smul, K, heatTensorH3Distance, ZS] using
          hsmoothBound
      exact hbound'
    have hcontract := heatTensorH3Distance_tensorToPlane_le (hT n) hzeroT
    have henergy : cylinderDerivativeEnergyDistance c (T n) ZT = ‖y n‖ := by
      have hgraph := cylinderDerivativeEnergyDistance_eq_norm_ofCylSmooth
        (c := c) (T := T n) (U := ZT) hc (hT n) hzeroT
      have hsubClass := ofCylSmooth_tensor_sub_eq
        (c := c) (T := T n) (U := ZT) hc (hT n) hzeroT
      have hzeroClass := ofCylSmooth_tensor_zero hc hzeroT
      rw [hgraph, hsubClass, hyrep n, hzeroClass]
      simp
    have hdist : heatTensorH3Distance c (S n) ZS ≤ ‖y n‖ := by
      have hSfun : S n = fun z => UnforcedLeray.TrainB.tensorToPlaneCLE (T n z) :=
        funext (hSval n)
      calc
        _ ≤ cylinderDerivativeEnergyDistance c (T n) ZT := by
          rw [hSfun]
          simpa only [ZS, ZT, map_zero] using hcontract
        _ = ‖y n‖ := henergy
    exact hplaneBound.trans (mul_le_mul_of_nonneg_left hdist (by
      dsimp [K]
      exact ENNReal.toReal_nonneg))
  have hnormOut : Tendsto
      (fun n => ‖smoothHeatOutputSequence hc hθ hS n‖) atTop
      (𝓝 ‖actualHeatDivH3 hc hθ x‖) :=
    (continuous_norm.tendsto (actualHeatDivH3 hc hθ x)).comp hOutLim
  have hnormIn : Tendsto (fun n => K * ‖y n‖) atTop (𝓝 (K * ‖x‖)) :=
    ((continuous_const.mul continuous_norm).tendsto x).comp hyLim
  have hlimBound := le_of_tendsto_of_tendsto hnormOut hnormIn
    (Eventually.of_forall hbound)
  simpa [K] using hlimBound

/-- Continuous linear operator given by the actual Gaussian heat-divergence response on the full
TensorH3 graph, with the smooth-input coefficient unchanged by the period-cell transfer. -/
noncomputable def actualHeatDivH3CLM {c θ : ℝ} (hc : 0 < c) (hθ : 0 < θ) :
    UnforcedLeray.TrainB.TensorH3 c →L[ℝ] UnforcedLeray.TrainB.VectorH3 c :=
  (actualHeatDivH3Linear hc hθ).mkContinuous
    ((ENNReal.ofReal ‖(UnforcedLeray.Train.toVecL : Plane →L[ℝ] Vec)‖ *
      ENNReal.ofReal (heatDivL2Coeff θ)).toReal)
    (fun x => norm_actualHeatDivH3_le hc hθ x)

@[simp] theorem actualHeatDivH3CLM_apply {c θ : ℝ} (hc : 0 < c) (hθ : 0 < θ)
    (x : UnforcedLeray.TrainB.TensorH3 c) :
    actualHeatDivH3CLM hc hθ x = actualHeatDivH3 hc hθ x := rfl

private theorem norm_actualHeatDivH3_comp_tensor_le {c θ : ℝ} (hc : 0 < c) (hθ : 0 < θ)
    (hc1 : 1 ≤ c) (u v : UnforcedLeray.TrainB.VectorH3 c) :
    ‖actualHeatDivH3CLM hc hθ (UnforcedLeray.TrainB.tensorH3Bilinear hc1 u v)‖ ≤
      ((ENNReal.ofReal ‖(UnforcedLeray.Train.toVecL : Plane →L[ℝ] Vec)‖ *
        ENNReal.ofReal (heatDivL2Coeff θ)).toReal) * 1536 * ‖u‖ * ‖v‖ := by
  let K : ℝ := (ENNReal.ofReal ‖(UnforcedLeray.Train.toVecL : Plane →L[ℝ] Vec)‖ *
    ENNReal.ofReal (heatDivL2Coeff θ)).toReal
  have hproduct : ‖UnforcedLeray.TrainB.tensorH3Bilinear hc1 u v‖ ≤
      1536 * ‖u‖ * ‖v‖ := by
    change ‖UnforcedLeray.TrainB.tensorH3ProductValue hc1 u v‖ ≤ _
    calc
      _ ≤ UnforcedLeray.TrainB.tensorH3ProductConstant * ‖u‖ * ‖v‖ :=
        UnforcedLeray.TrainB.tensorH3ProductValue_norm_le hc1 u v
      _ ≤ 1536 * ‖u‖ * ‖v‖ := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right
            (UnforcedLeray.TrainB.tensorH3ProductConstant_le_1536 (c := c))
            (norm_nonneg u)) (norm_nonneg v)
  have hK : 0 ≤ K := by dsimp [K]; exact ENNReal.toReal_nonneg
  calc
    ‖actualHeatDivH3CLM hc hθ (UnforcedLeray.TrainB.tensorH3Bilinear hc1 u v)‖ =
        ‖actualHeatDivH3 hc hθ (UnforcedLeray.TrainB.tensorH3Bilinear hc1 u v)‖ := rfl
    _ ≤ K * ‖UnforcedLeray.TrainB.tensorH3Bilinear hc1 u v‖ :=
      norm_actualHeatDivH3_le hc hθ _
    _ ≤ K * (1536 * ‖u‖ * ‖v‖) := mul_le_mul_of_nonneg_left hproduct hK
    _ = K * 1536 * ‖u‖ * ‖v‖ := by ring

noncomputable def actualHeatDivH3Bilinear {c θ : ℝ} (hc : 0 < c) (hθ : 0 < θ)
    (hc1 : 1 ≤ c) :
    UnforcedLeray.TrainB.VectorH3 c →L[ℝ]
      UnforcedLeray.TrainB.VectorH3 c →L[ℝ] UnforcedLeray.TrainB.VectorH3 c :=
  LinearMap.mkContinuous₂
    (LinearMap.mk₂ ℝ
      (fun u v => actualHeatDivH3CLM hc hθ
        (UnforcedLeray.TrainB.tensorH3Bilinear hc1 u v))
      (by
        intro u₁ u₂ v
        change actualHeatDivH3CLM hc hθ
            (UnforcedLeray.TrainB.tensorH3Bilinear hc1 (u₁ + u₂) v) = _
        rw [map_add (UnforcedLeray.TrainB.tensorH3Bilinear hc1) u₁ u₂]
        simp only [ContinuousLinearMap.add_apply, map_add])
      (by
        intro r u v
        change actualHeatDivH3CLM hc hθ
            (UnforcedLeray.TrainB.tensorH3Bilinear hc1 (r • u) v) = _
        rw [map_smul (UnforcedLeray.TrainB.tensorH3Bilinear hc1) r u]
        simp only [ContinuousLinearMap.smul_apply, map_smul])
      (by
        intro u v₁ v₂
        change actualHeatDivH3CLM hc hθ
            (UnforcedLeray.TrainB.tensorH3Bilinear hc1 u (v₁ + v₂)) = _
        rw [map_add (UnforcedLeray.TrainB.tensorH3Bilinear hc1 u) v₁ v₂]
        simp only [map_add])
      (by
        intro r u v
        change actualHeatDivH3CLM hc hθ
            (UnforcedLeray.TrainB.tensorH3Bilinear hc1 u (r • v)) = _
        rw [map_smul (UnforcedLeray.TrainB.tensorH3Bilinear hc1 u) r v]
        simp only [map_smul]))
    (((ENNReal.ofReal ‖(UnforcedLeray.Train.toVecL : Plane →L[ℝ] Vec)‖ *
      ENNReal.ofReal (heatDivL2Coeff θ)).toReal) * 1536)
    (by
      intro u v
      change ‖actualHeatDivH3CLM hc hθ
        (UnforcedLeray.TrainB.tensorH3Bilinear hc1 u v)‖ ≤ _
      exact norm_actualHeatDivH3_comp_tensor_le hc hθ hc1 u v)

theorem norm_actualHeatDivH3Bilinear_apply_le {c θ : ℝ} (hc : 0 < c) (hθ : 0 < θ)
    (hc1 : 1 ≤ c) (u v : UnforcedLeray.TrainB.VectorH3 c) :
    ‖actualHeatDivH3Bilinear hc hθ hc1 u v‖ ≤
      ((ENNReal.ofReal ‖(UnforcedLeray.Train.toVecL : Plane →L[ℝ] Vec)‖ *
        ENNReal.ofReal (heatDivL2Coeff θ)).toReal) * 1536 * ‖u‖ * ‖v‖ := by
  change ‖actualHeatDivH3CLM hc hθ
      (UnforcedLeray.TrainB.tensorH3Bilinear hc1 u v)‖ ≤ _
  exact norm_actualHeatDivH3_comp_tensor_le hc hθ hc1 u v

end UnforcedLeray.HeatCylinder

#print axioms UnforcedLeray.HeatCylinder.vectorH3NormalizedValue_injective
#print axioms UnforcedLeray.HeatCylinder.existsUnique_actual_heatDivH3_value
#print axioms UnforcedLeray.HeatCylinder.actualHeatDivH3
#print axioms UnforcedLeray.HeatCylinder.vectorH3NormalizedValue_actualHeatDivH3
#print axioms UnforcedLeray.HeatCylinder.actualHeatDivH3_add
#print axioms UnforcedLeray.HeatCylinder.actualHeatDivH3_smul
#print axioms UnforcedLeray.HeatCylinder.actualHeatDivH3Linear
#print axioms UnforcedLeray.HeatCylinder.tendsto_smoothHeatOutputSequence_actualHeatDivH3
#print axioms UnforcedLeray.HeatCylinder.norm_actualHeatDivH3_le
#print axioms UnforcedLeray.HeatCylinder.actualHeatDivH3CLM
#print axioms UnforcedLeray.HeatCylinder.actualHeatDivH3Bilinear
#print axioms UnforcedLeray.HeatCylinder.norm_actualHeatDivH3Bilinear_apply_le
